module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma111a

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Matrix
open scoped commutatorElement

theorem exists_finset_card_four {F : Type} [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h4
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by simpa using h4)
  exact ⟨t, ht⟩

section

variable {F : Type} [Field F] [Finite F]

theorem commutator_mul_central {G : Type*} [Group G] (a b c d : G) (hc : ∀ x, c * x = x * c)
    (hd : ∀ x, d * x = x * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  have h1 : c * (b * d) * c⁻¹ = b * d := by rw [hc]; group
  have h2 : d * a⁻¹ * d⁻¹ = a⁻¹ := by rw [hd]; group
  calc a * c * (b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹)
      = a * (c * (b * d) * c⁻¹) * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by rw [h1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

theorem sl2_eq_top_of_sup_center (h4 : 4 ≤ Nat.card F) (N : Subgroup (SpecialLinearGroup (Fin 2) F))
    [N.Normal] (hN : N ⊔ center (SpecialLinearGroup (Fin 2) F) = ⊤) : N = ⊤ := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)
  have hc : commutator (SpecialLinearGroup (Fin 2) F) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have h1 : g₁ ∈ N ⊔ center (SpecialLinearGroup (Fin 2) F) := by
      rw [hN]; exact Subgroup.mem_top g₁
    have h2 : g₂ ∈ N ⊔ center (SpecialLinearGroup (Fin 2) F) := by
      rw [hN]; exact Subgroup.mem_top g₂
    obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 h1
    obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 h2
    rw [commutator_mul_central a₁ a₂ c₁ c₂ (fun x => (Subgroup.mem_center_iff.1 hc₁ x).symm)
      (fun x => (Subgroup.mem_center_iff.1 hc₂ x).symm), commutatorElement_def]
    exact N.mul_mem (Subgroup.Normal.conj_mem ‹_› a₂ ha₂ a₁) (N.inv_mem ha₂)
  rw [hperf.commutator_eq_top] at hc
  exact top_le_iff.1 hc

theorem sl2_normal_eq_bot (h4 : 4 ≤ Nat.card F) (N : Subgroup (SpecialLinearGroup (Fin 2) F))
    [N.Normal] (hN : (-1 : SpecialLinearGroup (Fin 2) F) ∉ N) : N = ⊥ := by
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let π : SpecialLinearGroup (Fin 2) F →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) F))
  have hnorm : (N.map π).Normal := Subgroup.Normal.map ‹_› π (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ (N.map π) hnorm with h | h
  · have hle : N ≤ center (SpecialLinearGroup (Fin 2) F) := by
      intro g hg
      have : π g ∈ N.map π := ⟨g, hg, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff g).1 this
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨r, hr, hgr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hle hg)
    have hr2 : r * r = 1 := by simpa [sq] using hr
    rcases mul_self_eq_one_iff.1 hr2 with rfl | rfl
    · rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [← hgr]
      simp
    · exfalso
      apply hN
      have : g = -1 := by
        apply Subtype.ext
        rw [← hgr]
        simp only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      rw [← this]
      exact hg
  · exfalso
    apply hN
    have hsup : N ⊔ center (SpecialLinearGroup (Fin 2) F) = ⊤ := by
      refine eq_top_iff.2 fun g _ => ?_
      have : π g ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := this
      have hker : n⁻¹ * g ∈ center (SpecialLinearGroup (Fin 2) F) := by
        rw [← QuotientGroup.eq_one_iff]
        show π (n⁻¹ * g) = 1
        rw [map_mul, map_inv, hng, inv_mul_cancel]
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hn hker
    have := sl2_eq_top_of_sup_center h4 N hsup
    rw [this]
    exact Subgroup.mem_top _

end

section Restrict

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

@[expose] def restrictRep (ρ : Representation k G V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : Representation k G W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp] theorem coe_restrictRep_apply (ρ : Representation k G V) (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (g : G) (w : W) :
    ((restrictRep ρ W hW g w : W) : V) = ρ g w := rfl

end Restrict

section Involution

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

theorem finrank_ker_involution (h2 : (2 : k) ≠ 0) (T : V →ₗ[k] V) (hT : ∀ x, T (T x) = x) :
    Module.finrank k (LinearMap.ker (T - LinearMap.id)) +
      Module.finrank k (LinearMap.ker (T + LinearMap.id)) = Module.finrank k V := by
  have hsup : LinearMap.ker (T - LinearMap.id) ⊔ LinearMap.ker (T + LinearMap.id) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hy : (2 : k)⁻¹ • (x + T x) ∈ LinearMap.ker (T - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_add, hT]
      rw [sub_add_sub_cancel, sub_self, smul_zero]
    have hz : (2 : k)⁻¹ • (x - T x) ∈ LinearMap.ker (T + LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp only [LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub, hT]
      rw [add_comm (T x) x, sub_self, smul_zero]
    refine Submodule.mem_sup.2 ⟨_, hy, _, hz, ?_⟩
    rw [← smul_add]
    have : x + T x + (x - T x) = (2 : k) • x := by module
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hinf : LinearMap.ker (T - LinearMap.id) ⊓ LinearMap.ker (T + LinearMap.id) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.1 hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply] at h1 h2'
    have : (2 : k) • x = 0 := by
      have h3 : T x = x := sub_eq_zero.1 h1
      rw [h3] at h2'
      rw [two_smul]
      exact h2'
    simpa [h2] using this
  have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (T - LinearMap.id))
    (LinearMap.ker (T + LinearMap.id))
  rw [hsup, hinf] at this
  simpa using this.symm

end Involution

section Neg

variable {F : Type} [Field F]

theorem charP_of_natCard_eq [Finite F] {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) :
    CharP F p := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hF)

theorem two_ne_zero_of_card_eq [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n) :
    (2 : F) ≠ 0 := by
  intro h
  have := charP_of_natCard_eq hp hF
  have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2')

theorem sl2_neg_one_comm (g : SpecialLinearGroup (Fin 2) F) : g * (-1) = (-1) * g := by
  simp

theorem sl2_neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at this
  apply h2
  linear_combination -this

theorem sl2_neg_one_mul_self : (-1 : SpecialLinearGroup (Fin 2) F) * (-1) = 1 := by
  simp

@[expose] def weylElt (F : Type) [Field F] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_weylElt : ((weylElt F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; -1, 0] := rfl

theorem weylElt_mul_self : weylElt F * weylElt F = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, coe_weylElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Neg

theorem zmod_three_sq_add_one_ne_zero : ∀ c : ZMod 3, c * c + 1 ≠ 0 := by decide

section Main

variable {F : Type} [Field F] [Finite F]

theorem natMod_neg_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ : Representation (ZMod p) (SpecialLinearGroup (Fin 2) F) V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod p) V = 2 * n) (v : V) : ρ (-1) v = -v := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_card_eq hp hp2 hF
  set z : SpecialLinearGroup (Fin 2) F := -1 with hz
  have hTT : ∀ x, ρ z (ρ z x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, hz, sl2_neg_one_mul_self, map_one]
    rfl
  set Vp : Submodule (ZMod p) V := LinearMap.ker (ρ z - LinearMap.id) with hVp
  set Vm : Submodule (ZMod p) V := LinearMap.ker (ρ z + LinearMap.id) with hVm
  have hmemVp : ∀ x, x ∈ Vp ↔ ρ z x = x := fun x => by
    rw [hVp, LinearMap.mem_ker]; simp [sub_eq_zero]
  have hmemVm : ∀ x, x ∈ Vm ↔ ρ z x = -x := fun x => by
    rw [hVm, LinearMap.mem_ker]; simp [add_eq_zero_iff_eq_neg]
  have hsum : Module.finrank (ZMod p) Vp + Module.finrank (ZMod p) Vm = Module.finrank (ZMod p) V :=
    finrank_ker_involution h2 (ρ z) hTT
  by_contra hne
  have hVp_ne : Vp ≠ ⊥ := by
    intro hbot
    apply hne
    have hu : v + ρ z v ∈ Vp := by
      rw [hmemVp, map_add, hTT, add_comm]
    rw [hbot, Submodule.mem_bot] at hu
    exact eq_neg_of_add_eq_zero_right hu
  have hVp1 : 1 ≤ Module.finrank (ZMod p) Vp := Submodule.one_le_finrank_iff.2 hVp_ne
  have hVm_ne : Vm ≠ ⊥ := by
    intro hbot
    have hall : ρ z = 1 := by
      ext x
      have hy : x - ρ z x ∈ Vm := by
        rw [hmemVm, map_sub, hTT, neg_sub]
      rw [hbot, Submodule.mem_bot] at hy
      show ρ z x = x
      exact (sub_eq_zero.1 hy).symm
    have : ρ z = ρ 1 := by rw [hall, map_one]
    exact sl2_neg_one_ne_one h2F (hρ this)
  have hVm1 : 1 ≤ Module.finrank (ZMod p) Vm := Submodule.one_le_finrank_iff.2 hVm_ne
  have hinv : ∀ g, ∀ w ∈ Vm, ρ g w ∈ Vm := by
    intro g w hw
    rw [hmemVm] at hw ⊢
    have hg : g * z = z * g := sl2_neg_one_comm g
    calc ρ z (ρ g w) = ρ (z * g) w := by rw [map_mul]; rfl
      _ = ρ (g * z) w := by rw [hg]
      _ = ρ g (ρ z w) := by rw [map_mul]; rfl
      _ = -ρ g w := by rw [hw, map_neg]
  let ρm : Representation (ZMod p) (SpecialLinearGroup (Fin 2) F) Vm := restrictRep ρ Vm hinv
  have hρmz : ∀ w : Vm, ρm z w = -w := fun w => Subtype.ext ((hmemVm _).1 w.2)
  by_cases h4 : 4 ≤ Nat.card F
  · have hnot : z ∉ MonoidHom.ker ρm := by
      intro hk
      obtain ⟨w, hwm, hw0⟩ := (Submodule.ne_bot_iff Vm).1 hVm_ne
      have h1 : ρm z ⟨w, hwm⟩ = ⟨w, hwm⟩ := by rw [MonoidHom.mem_ker.1 hk]; rfl
      have h3 := hρmz ⟨w, hwm⟩
      rw [h1] at h3
      have h4' : (2 : ZMod p) • (⟨w, hwm⟩ : Vm) = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h3]
        exact neg_add_cancel _
      have h5 := (smul_eq_zero.1 h4').resolve_left h2
      exact hw0 (congrArg Subtype.val h5)
    have hker : MonoidHom.ker ρm = ⊥ := sl2_normal_eq_bot h4 (MonoidHom.ker ρm) hnot
    have hinj : Function.Injective ρm := (MonoidHom.ker_eq_bot_iff ρm).1 hker
    have hmodel : HasSL2Model ↥(⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)) (fun r => r = p ^ n) :=
      ⟨F, inferInstance, inferInstance, hF, ⟨(Subgroup.topEquiv).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)⟩⟩
    have := ivk_11_1a p n hp hp2 (SpecialLinearGroup (Fin 2) F) ⊤ (Or.inl hmodel) Vm ρm hinj
    omega
  · push Not at h4
    have hn : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpn : p ≤ p ^ n := Nat.le_self_pow hn p
    have hp3' : p = 3 := by omega
    subst hp3'
    have hn1 : n = 1 := by
      by_contra hn1
      have h2n : 2 ≤ n := by omega
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
      omega
    subst hn1
    have hVm1' : Module.finrank (ZMod 3) Vm = 1 := by omega
    obtain ⟨w₀, hw₀, hspan⟩ := finrank_eq_one_iff'.1 hVm1'
    obtain ⟨c, hc⟩ := hspan (ρm (weylElt F) w₀)
    have h1 : ρm (weylElt F) (ρm (weylElt F) w₀) = -w₀ := by
      rw [← Module.End.mul_apply, ← map_mul, weylElt_mul_self]
      exact hρmz w₀
    have h2' : ρm (weylElt F) (ρm (weylElt F) w₀) = (c * c) • w₀ := by
      rw [← hc, map_smul, ← hc, smul_smul]
    have h3 : (c * c + 1) • w₀ = 0 := by
      rw [add_smul, ← h2', h1, one_smul]
      exact neg_add_cancel w₀
    have hcc : c * c + 1 = 0 := (smul_eq_zero.1 h3).resolve_right hw₀
    exact zmod_three_sq_add_one_ne_zero c hcc

end Main

end CFSG.GH74.GLS.IVK.Proofs2
