module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Dihedral.Glauberman.DicksonMaxTraceField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick

open Subgroup CFSG CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

theorem eq_one_of_pow_odd_sq {G : Type*} [Group G] {x : G} {n : ℕ} (hn : Odd n) (h1 : x ^ n = 1)
    (h2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have : x ^ (2 * m + 1) = x := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact h1

theorem hom_trivial_of_odd_gens {J G₂ : Type*} [Group J] [Group G₂] (σ : J →* G₂)
    (hexp : ∀ g : G₂, g ^ 2 = 1) {S : Set J} (hS : Subgroup.closure S = ⊤)
    (hodd : ∀ s ∈ S, ∃ n : ℕ, Odd n ∧ σ s ^ n = 1) (x : J) : σ x = 1 := by
  have hle : Subgroup.closure S ≤ σ.ker := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨n, hn, hsn⟩ := hodd s hs
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact eq_one_of_pow_odd_sq hn hsn (hexp _)
  have : x ∈ σ.ker := hle (by rw [hS]; exact Subgroup.mem_top x)
  exact this

theorem Q_comm_of_range_comm {J G Q : Type*} [Group J] [Group G] [Group Q] (ι : J →* G)
    (ψ : J →* Q) (hψ : Function.Surjective ψ) (hker : ι.ker ≤ ψ.ker)
    (hcomm : ∀ x y : J, ι x * ι y = ι y * ι x) : ∀ a b : Q, a * b = b * a := by
  intro a b
  obtain ⟨x, rfl⟩ := hψ a
  obtain ⟨y, rfl⟩ := hψ b
  have h1 : (x * y)⁻¹ * (y * x) ∈ ι.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm x y]
    simp
  have h2 := hker h1
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← map_mul, ← map_mul]
  exact h2

theorem exists_hat {J G Q : Type*} [Group J] [Group G] [Group Q] (ι : J →* G) (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (hker : ι.ker ≤ ψ.ker) :
    ∃ ψ' : ι.range →* Q, Function.Surjective ψ' ∧ ∀ x : J, ψ' (ι.rangeRestrict x) = ψ x := by
  classical
  let f : ι.range → Q := fun g => ψ (Classical.choose g.2)
  have hf : ∀ (g : ι.range) (x : J), ι x = g → f g = ψ x := by
    intro g x hx
    have hc : ι (Classical.choose g.2) = g := Classical.choose_spec g.2
    have h1 : (Classical.choose g.2)⁻¹ * x ∈ ι.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc, hx]
      simp
    have h2 := hker h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  refine ⟨{ toFun := f
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_⟩
  · have := hf 1 1 (by simp)
    simpa using this
  · intro g h
    obtain ⟨x, hx⟩ := g.2
    obtain ⟨y, hy⟩ := h.2
    have hxy : ι (x * y) = ((g * h : ι.range) : G) := by rw [map_mul, hx, hy]; rfl
    show f (g * h) = f g * f h
    rw [hf (g * h) (x * y) hxy, hf g x hx, hf h y hy, map_mul]
  · intro q
    obtain ⟨x, rfl⟩ := hψ q
    exact ⟨ι.rangeRestrict x, hf _ x rfl⟩
  · intro x
    exact hf _ x rfl

theorem Q_card_of_simple {J G Q : Type*} [Group J] [Group G] [Group Q] (ι : J →* G) (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (hker : ι.ker ≤ ψ.ker) (hsimple : IsSimpleGroup ι.range)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Nat.card ι.range = Nat.card Q := by
  obtain ⟨ψ', hψ', -⟩ := exists_hat ι ψ hψ hker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ'.ker with h | h
  · have hinj : Function.Injective ψ' := (MonoidHom.ker_eq_bot_iff ψ').mp h
    exact Nat.card_congr (Equiv.ofBijective ψ' ⟨hinj, hψ'⟩)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    obtain ⟨x, rfl⟩ := hψ' a
    obtain ⟨y, rfl⟩ := hψ' b
    have hx : x ∈ ψ'.ker := by rw [h]; exact Subgroup.mem_top x
    have hy : y ∈ ψ'.ker := by rw [h]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy]

@[expose] def slA (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def slB (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem psl2_not_comm (F : Type) [Field F] :
    ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  refine ⟨QuotientGroup.mk (slA F), QuotientGroup.mk (slB F), fun h => ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h2 := congrFun (congrFun hr 0) 1
  have hA : ((slA F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] := rfl
  have hB : ((slB F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; 1, 1] := rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hA, hB,
    Matrix.adjugate_fin_two, Matrix.mul_fin_two] at h2
  simp at h2

theorem false_of_exp_two_hom {J G : Type*} [Group J] [Group G] (ι : J →* G) {H G₂ : Type*}
    [Group H] [Group G₂] (e : ι.range ≃* H) (τ : H →* G₂) (hexp : ∀ g : G₂, g ^ 2 = 1)
    (hnt : ∃ w : H, τ w ≠ 1) {S : Set J} (hS : Subgroup.closure S = ⊤)
    (hS' : ∀ s ∈ S, ∃ n : ℕ, Odd n ∧ ι s ^ n = 1) : False := by
  let σ : J →* G₂ := τ.comp (e.toMonoidHom.comp ι.rangeRestrict)
  have htriv := hom_trivial_of_odd_gens σ hexp hS (by
    intro s hs
    obtain ⟨n, hn, hsn⟩ := hS' s hs
    refine ⟨n, hn, ?_⟩
    have h1 : (ι.rangeRestrict s) ^ n = 1 := Subtype.ext (by simpa using hsn)
    simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_pow, ← map_pow, h1, map_one, map_one])
  obtain ⟨w, hw⟩ := hnt
  obtain ⟨x, hx⟩ := ι.rangeRestrict_surjective (e.symm w)
  apply hw
  have := htriv x
  simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [hx, MulEquiv.apply_symm_apply] at this
  exact this

@[expose] def dihSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun g := match g with
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;> decide

theorem mult_zmod_two_sq (g : Multiplicative (ZMod 2)) : g ^ 2 = 1 := by
  revert g
  decide

theorem dihSign_nontrivial (n : ℕ) : ∃ w : DihedralGroup n, dihSign n w ≠ 1 :=
  ⟨DihedralGroup.sr 0, by
    show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
    decide⟩

theorem perm_sign_nontrivial : ∃ w : Equiv.Perm (Fin 4), Equiv.Perm.sign w ≠ 1 :=
  ⟨Equiv.swap 0 1, by
    rw [Equiv.Perm.sign_swap (by decide)]
    decide⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick
