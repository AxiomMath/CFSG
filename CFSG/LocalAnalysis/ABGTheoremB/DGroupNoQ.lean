module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting
import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.LieType.Steinberg.Adjoint.RankOne

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.LieType.Steinberg

universe u

section Unitriangular

variable {k : Type*} [Field k]

private theorem sl2Upper_zero' : sl2Upper (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

private theorem sl2Lower_zero' : sl2Lower (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

private theorem sl2Upper_pow' (c : k) (n : ℕ) : sl2Upper c ^ n = sl2Upper ((n : k) * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sl2Upper_zero']
  | succ n ih =>
    rw [pow_succ, ih]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Upper, coe_sl2Upper]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, add_comm]

private theorem sl2Lower_pow' (c : k) (n : ℕ) : sl2Lower c ^ n = sl2Lower ((n : k) * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sl2Lower_zero']
  | succ n ih =>
    rw [pow_succ, ih]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Lower, coe_sl2Lower]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, add_comm]

private theorem natCard_cast_eq_zero (F : Type*) [Field F] [Finite F] : (Nat.card F : F) = 0 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero F

private theorem sl2Upper_pow_card {F : Type*} [Field F] [Finite F] (c : F) :
    sl2Upper c ^ Nat.card F = 1 := by
  rw [sl2Upper_pow', natCard_cast_eq_zero, zero_mul, sl2Upper_zero']

private theorem sl2Lower_pow_card {F : Type*} [Field F] [Finite F] (c : F) :
    sl2Lower c ^ Nat.card F = 1 := by
  rw [sl2Lower_pow', natCard_cast_eq_zero, zero_mul, sl2Lower_zero']

end Unitriangular

section General

variable {H : Type u} [Group H]

private theorem mem_of_index_eq_two_of_odd {K : Subgroup H} (hK : K.index = 2) {h : H}
    (hh : Odd (orderOf h)) : h ∈ K := by
  obtain ⟨k, hk⟩ := hh
  have heq : h = h ^ (k + 1) * h ^ (k + 1) := by
    rw [← pow_add, show k + 1 + (k + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [heq]
  exact Subgroup.mul_self_mem_of_index_two hK _

private theorem le_of_index_eq_two_of_sl2 [Finite H] {K : Subgroup H} (hK : K.index = 2)
    (X : Subgroup H) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) : X ≤ K := by
  have hodd : ∀ x : X, Odd (orderOf x) → (x : H) ∈ K := fun x hx =>
    mem_of_index_eq_two_of_odd hK (by rwa [Subgroup.orderOf_coe])
  have hkerK : ∀ x : X, x ∈ φ.ker → (x : H) ∈ K := by
    intro x hx
    refine hodd x (hker.of_dvd_nat ?_)
    have := orderOf_dvd_natCard (⟨x, hx⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hlift : ∀ t : Matrix.SpecialLinearGroup (Fin 2) F, t ^ Nat.card F = 1 →
      ∃ x : X, φ x = t ∧ (x : H) ∈ K := by
    intro t ht
    obtain ⟨x, rfl⟩ := hφ t
    refine ⟨x, rfl, hodd x ?_⟩
    have h1 : x ^ Nat.card F ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, ht]
    have h2 : x ^ (Nat.card F * Nat.card φ.ker) = 1 := by
      rw [pow_mul]
      have := pow_card_eq_one' (G := φ.ker) (x := ⟨_, h1⟩)
      exact congrArg Subtype.val this
    exact (hF.mul hker).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
  intro y hy
  obtain ⟨e, a, b, c, he⟩ := Adjoint.sl2_eq_prod (φ ⟨y, hy⟩)
  obtain ⟨x₁, hx₁, hK₁⟩ := hlift _ (sl2Lower_pow_card e)
  obtain ⟨x₂, hx₂, hK₂⟩ := hlift _ (sl2Upper_pow_card a)
  obtain ⟨x₃, hx₃, hK₃⟩ := hlift _ (sl2Lower_pow_card b)
  obtain ⟨x₄, hx₄, hK₄⟩ := hlift _ (sl2Upper_pow_card c)
  have hw : φ (x₁ * x₂ * x₃ * x₄) = φ ⟨y, hy⟩ := by
    rw [map_mul, map_mul, map_mul, hx₁, hx₂, hx₃, hx₄, he]
  have hk : (x₁ * x₂ * x₃ * x₄)⁻¹ * ⟨y, hy⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hw, inv_mul_cancel]
  have hwK : ((x₁ * x₂ * x₃ * x₄ : X) : H) ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hK₁ hK₂) hK₃) hK₄
  have := K.mul_mem hwK (hkerK _ hk)
  rwa [← Subgroup.coe_mul, mul_inv_cancel_left] at this

private theorem exists_isPGroup_noncomm_of_sl2 [Finite H] (X : Subgroup H) {F : Type} [Field F]
    [Finite F] (hF : Odd (Nat.card F)) (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hφ : Function.Surjective φ) :
    ∃ S : Subgroup H, S ≤ X ∧ IsPGroup 2 S ∧ ∃ a ∈ S, ∃ b ∈ S,
      a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.exists_quaternionSubgroup F hF
  have hQ : IsPGroup 2 Q := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨P₀, hQP₀⟩ := hQ.exists_le_sylow
  obtain ⟨S', hS'⟩ := Sylow.mapSurjective_surjective hφ 2 P₀
  have hmap : (S' : Subgroup X).map φ = P₀ := by rw [← Sylow.coe_mapSurjective hφ, hS']
  have hu : ((e.symm (QuaternionGroup.a 1) : Q) : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      (S' : Subgroup X).map φ := hmap ▸ hQP₀ (e.symm _).2
  have hv : ((e.symm (QuaternionGroup.xa 0) : Q) : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      (S' : Subgroup X).map φ := hmap ▸ hQP₀ (e.symm _).2
  obtain ⟨a, ha, hau⟩ := hu
  obtain ⟨b, hb, hbv⟩ := hv
  have hsq : ∀ (x : X) (q : QuaternionGroup 2), φ x = (e.symm q : Q) → q ^ 2 ≠ 1 →
      (x : H) ^ 2 ≠ 1 := by
    intro x q hx hq h
    apply hq
    apply e.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, ← hx, ← map_pow]
    have h1 : x ^ 2 = 1 := Subtype.ext (by simpa using h)
    rw [h1, map_one, Subgroup.coe_one]
  refine ⟨(S' : Subgroup X).map X.subtype, Subgroup.map_subtype_le _, S'.isPGroup'.map _,
    a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, hsq a _ hau (by decide), hsq b _ hbv (by decide), ?_⟩
  intro h
  have h1 : a * b = b * a := Subtype.ext (by simpa using h)
  apply quaternionGroup_mul_ne (n := 2) le_rfl
  apply e.symm.injective
  apply Subtype.ext
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hau, ← hbv, ← map_mul, ← map_mul,
    h1]

private theorem dihedral_commute_of_sq_ne_one {m : ℕ} {g h : DihedralGroup m} (hg : g ^ 2 ≠ 1)
    (hh : h ^ 2 ≠ 1) : g * h = h * g := by
  rcases g with i | i
  · rcases h with j | j
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    · exact absurd (by rw [pow_two, DihedralGroup.sr_mul_self]) hh
  · exact absurd (by rw [pow_two, DihedralGroup.sr_mul_self]) hg

private theorem false_of_mulEquiv_dihedral {M : Type*} [Group M] {a b : M} (ha : a ^ 2 ≠ 1)
    (hb : b ^ 2 ≠ 1) (hab : a * b ≠ b * a) {m : ℕ} (e : M ≃* DihedralGroup m) : False := by
  have hsq : ∀ x : M, x ^ 2 ≠ 1 → e x ^ 2 ≠ 1 := fun x hx h =>
    hx (e.injective (by rw [map_pow, h, map_one]))
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact dihedral_commute_of_sq_ne_one (hsq a ha) (hsq b hb)

end General

theorem dgroup_no_sl2_section {H : Type u} [Group H] [Finite H] (hH : IsDGroup H)
    (X : Subgroup H) (F : Type) [Field F] [Finite F] (hF : Odd (Nat.card F))
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ) :
    ¬ Odd (Nat.card φ.ker) := by
  intro hker
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSX, hS, a, haS, b, hbS, ha, hb, hab⟩ := exists_isPGroup_noncomm_of_sl2 X hF φ hφ
  rcases hH with ⟨hD, -⟩ | ⟨K, hK⟩
  · obtain ⟨P, hSP⟩ := hS.exists_le_sylow
    obtain ⟨m, -, ⟨e⟩⟩ := hD P
    refine false_of_mulEquiv_dihedral (a := ⟨a, hSP haS⟩) (b := ⟨b, hSP hbS⟩) ?_ ?_ ?_ e
    · exact fun h => ha (by simpa using congrArg Subtype.val h)
    · exact fun h => hb (by simpa using congrArg Subtype.val h)
    · exact fun h => hab (by simpa using congrArg Subtype.val h)
  · have hSK : S ≤ K := hSX.trans (le_of_index_eq_two_of_sl2 hK.index_eq_two X hF φ hφ hker)
    obtain ⟨P, hSP⟩ := (hS.comap_subtype (K := K)).exists_le_sylow
    have haP : (⟨a, hSK haS⟩ : K) ∈ P := hSP haS
    have hbP : (⟨b, hSK hbS⟩ : K) ∈ P := hSP hbS
    rcases hK.sylow with ⟨n, -, hDK⟩ | ⟨n, -, hAb⟩
    · obtain ⟨m, -, ⟨e⟩⟩ := hDK P
      refine false_of_mulEquiv_dihedral (a := ⟨_, haP⟩) (b := ⟨_, hbP⟩) ?_ ?_ ?_ e
      · exact fun h => ha (by simpa using congrArg (fun x : P => ((x : K) : H)) h)
      · exact fun h => hb (by simpa using congrArg (fun x : P => ((x : K) : H)) h)
      · exact fun h => hab (by simpa using congrArg (fun x : P => ((x : K) : H)) h)
    · apply hab
      have h := isMulCommutative_iff.mp (hAb P) ⟨_, haP⟩ ⟨_, hbP⟩
      simpa using congrArg (fun x : P => ((x : K) : H)) h

theorem dgroup_no_sl2_section_of_le {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    (hH : IsDGroup H) (X : Subgroup G) (hXH : X ≤ H) (F : Type) [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hφ : Function.Surjective φ) : ¬ Odd (Nat.card φ.ker) := by
  let ι : X.subgroupOf H ≃* X := Subgroup.subgroupOfEquivOfLe hXH
  have h := dgroup_no_sl2_section hH (X.subgroupOf H) F hF (φ.comp ι.toMonoidHom)
    (hφ.comp ι.surjective)
  have hcard : Nat.card (φ.comp ι.toMonoidHom).ker = Nat.card φ.ker := by
    rw [← MonoidHom.comap_ker, show ι.toMonoidHom = (ι : X.subgroupOf H →* X) from rfl,
      Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective ι.symm.injective]
  rwa [hcard] at h

theorem Setting.isDGroupWrt_no_sl2_section {G : Type u} [Group G] [Finite G] (σ : Setting G) :
    ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ X : Subgroup G, X ≤ H → ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
        ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ →
          ¬ Odd (Nat.card φ.ker) :=
  fun H _ hHD X hXH F _ _ hF φ hφ => dgroup_no_sl2_section_of_le H hHD.1 X hXH F hF φ hφ

end CFSG.ABGTheoremB
