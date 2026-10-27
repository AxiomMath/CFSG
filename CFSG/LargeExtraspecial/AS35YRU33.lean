module

public import CFSG.LargeExtraspecial.AS35YLSU33
public import Certificates.Certificate21200
public import CFSG.GH74.KGroups.U33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YR

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem sub_sub_eq_zero_of_disjoint {a b : V ≃ₗ[ZMod 2] V} (hab : a * b = b * a)
    (hdis : commSpace a ⊓ commSpace b = ⊥) (v : V) : a (b v - v) - (b v - v) = 0 := by
  have h1 : a (b v - v) - (b v - v) ∈ commSpace a := sub_mem_commSpace a _
  have h2 : a (b v - v) - (b v - v) ∈ commSpace b := by
    have e : a (b v - v) - (b v - v) = b (a v - v) - (a v - v) := by
      have := LinearEquiv.congr_fun hab v
      simp only [LinearEquiv.mul_apply] at this
      rw [map_sub, map_sub, this]
      abel
    rw [e]
    exact sub_mem_commSpace b _
  have h3 : a (b v - v) - (b v - v) ∈ commSpace a ⊓ commSpace b := ⟨h1, h2⟩
  rwa [hdis, Submodule.mem_bot] at h3

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_mul_of_disjoint {a b : V ≃ₗ[ZMod 2] V} (hab : a * b = b * a)
    (hdis : commSpace a ⊓ commSpace b = ⊥) :
    fixSpace (a * b) = fixSpace a ⊓ fixSpace b := by
  ext v
  simp only [Submodule.mem_inf, mem_fixSpace, LinearEquiv.mul_apply]
  constructor
  · intro h
    have h0 := sub_sub_eq_zero_of_disjoint hab hdis v
    rw [map_sub, h] at h0
    have hav : a v - v = b v - v := by
      have e : a v - v - (b v - v) = (v - a v - (b v - v)) + (2 : ZMod 2) • (a v - v) := by
        rw [two_smul]
        abel
      rw [← sub_eq_zero, e, h0, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
    have hmem : a v - v ∈ commSpace a ⊓ commSpace b :=
      ⟨sub_mem_commSpace a v, hav ▸ sub_mem_commSpace b v⟩
    rw [hdis, Submodule.mem_bot, sub_eq_zero] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem, sub_self, eq_comm, sub_eq_zero] at hav
    exact hav
  · rintro ⟨ha, hb⟩
    rw [hb, ha]

theorem finrank_commSpace_mul_of_disjoint (hQ : Q.polarBilin.Nondegenerate)
    {a b : V ≃ₗ[ZMod 2] V} (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) (hdis : commSpace a ⊓ commSpace b = ⊥) :
    finrank (ZMod 2) (commSpace (a * b)) =
      finrank (ZMod 2) (commSpace a) + finrank (ZMod 2) (commSpace b) := by
  have hperp : fixSpace (a * b) =
      LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace a ⊔ commSpace b) := by
    rw [fixSpace_mul_of_disjoint hab hdis, fixSpace_eq_orthogonal_commSpace hQ ha haa,
      fixSpace_eq_orthogonal_commSpace hQ hb hbb]
    ext v
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩ w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, LinearMap.add_apply, h1 x hx, h2 y hy, add_zero]
    · intro h
      exact ⟨fun x hx => h x (Submodule.mem_sup_left hx),
        fun y hy => h y (Submodule.mem_sup_right hy)⟩
  have h1 := finrank_commSpace_add_finrank_fixSpace (a * b)
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ (commSpace a ⊔ commSpace b)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace a) (commSpace b)
  rw [hdis, finrank_bot, add_zero] at h3
  have h4 := Submodule.finrank_le (commSpace a ⊔ commSpace b)
  rw [hperp] at h1
  omega

theorem commSpace_inf_ne_bot (hQ : Q.polarBilin.Nondegenerate) {a b : V ≃ₗ[ZMod 2] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hdb : finrank (ZMod 2) (commSpace b) = finrank (ZMod 2) (commSpace a))
    (hdab : finrank (ZMod 2) (commSpace (a * b)) = finrank (ZMod 2) (commSpace a)) :
    commSpace a ⊓ commSpace b ≠ ⊥ := by
  intro hdis
  have h := finrank_commSpace_mul_of_disjoint hQ ha hb haa hbb hab hdis
  have h1 := one_le_finrank_commSpace ha1
  omega

end Linear

section Model

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

theorem pa_mem : pa ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact subset_closure (Set.mem_insert _ _)

theorem pb_mem : pb ∈ QP.originalSubgroup := by
  rw [QP_closure]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem list_prod_mem_QP {l : List (Equiv.Perm (Fin 28))}
    (hl : ∀ x ∈ l, x = pa ∨ x = pb) : l.prod ∈ QP.originalSubgroup := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rcases hl x hx with rfl | rfl
  · exact pa_mem
  · exact pb_mem

theorem u33d0_mem : u33d0 ∈ QP.originalSubgroup := by
  rw [u33d0_eq]
  exact list_prod_mem_QP (by simp)

theorem u33d1_mem : u33d1 ∈ QP.originalSubgroup := by
  rw [u33d1_eq]
  exact list_prod_mem_QP (by simp)

theorem u33d2_mem : u33d2 ∈ QP.originalSubgroup := by
  rw [u33d2_eq]
  exact list_prod_mem_QP (by simp)

theorem u33d3_mem : u33d3 ∈ QP.originalSubgroup := by
  rw [u33d3_eq]
  exact list_prod_mem_QP (by simp)

theorem closure_u33 :
    Subgroup.closure {u33d0, u33d1, u33d2, u33d3} = QP.originalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact u33d0_mem
    · exact u33d1_mem
    · exact u33d2_mem
    · exact u33d3_mem
  · have hl : ∀ {l : List (Equiv.Perm (Fin 28))},
        (∀ x ∈ l, x ∈ ({u33d0, u33d1, u33d2, u33d3} : Set (Equiv.Perm (Fin 28)))) →
        l.prod ∈ Subgroup.closure ({u33d0, u33d1, u33d2, u33d3} : Set (Equiv.Perm (Fin 28))) :=
      fun hl => Subgroup.list_prod_mem _ fun x hx => Subgroup.subset_closure (hl x hx)
    rw [QP_closure, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, pa_eq_word]
      exact hl (by simp)
    · rw [SetLike.mem_coe, pb_eq_word]
      exact hl (by simp)

theorem exists_conj_u33d0
    {g : Equiv.Perm (Fin 28)} (hg : g ∈ QP.originalSubgroup) (hgg : g * g = 1) (hg1 : g ≠ 1) :
    ∃ c ∈ QP.originalSubgroup, c * g * c⁻¹ = u33d0 := by
  have hc := Certificates.certificate21200
  unfold u33InvConjCheck at hc
  have h := forall_of_all QP QP_ok hc g hg
  have h1 : (g * g == 1) = true := beq_iff_eq.mpr hgg
  have h2 : (g == 1) = false := beq_eq_false_iff_ne.mpr hg1
  rw [h1, h2, Bool.not_true, Bool.false_or, Bool.false_or] at h
  obtain ⟨c, hc, hcg⟩ := List.any_eq_true.mp h
  exact ⟨c, (mem_elemsT QP QP_ok c).mp hc, beq_iff_eq.mp hcg⟩

theorem card_QP : Nat.card QP.originalSubgroup = 6048 := by
  rw [card_group QP QP_ok, QP_valid.2]

end Model

section Gens

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

variable {X : Type} [Group X]

theorem exists_gens_of_equiv
    (e : X ≃* QP.originalSubgroup) {d : X} (hd1 : d ≠ 1) (hdd : d * d = 1) :
    ∃ x₀ x₁ x₂ x₃ : X, Subgroup.closure {x₀, x₁, x₂, x₃} = ⊤ ∧ x₀ * x₁ = x₁ * x₀ ∧
      (∃ h, h * d * h⁻¹ = x₀) ∧ (∃ h, h * d * h⁻¹ = x₁) ∧ (∃ h, h * d * h⁻¹ = x₂) ∧
      (∃ h, h * d * h⁻¹ = x₃) ∧ ∃ h, h * d * h⁻¹ = x₀ * x₁ := by
  set x₀ := e.symm ⟨u33d0, u33d0_mem⟩ with hx₀
  have hconj : ∀ y : X, y ≠ 1 → y * y = 1 → ∃ h, h * y * h⁻¹ = x₀ := by
    intro y hy1 hyy
    have hg1 : ((e y : QP.originalSubgroup) : Equiv.Perm (Fin 28)) ≠ 1 := by
      intro h
      apply hy1
      apply e.injective
      rw [map_one]
      exact Subtype.ext h
    have hgg : ((e y : QP.originalSubgroup) : Equiv.Perm (Fin 28)) *
        ((e y : QP.originalSubgroup) : Equiv.Perm (Fin 28)) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hyy, map_one]
      rfl
    obtain ⟨c, hc, hcg⟩ := exists_conj_u33d0 (e y).2 hgg hg1
    refine ⟨e.symm ⟨c, hc⟩, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hx₀, MulEquiv.apply_symm_apply]
    exact Subtype.ext hcg
  have hconj' : ∀ y : X, y ≠ 1 → y * y = 1 → ∃ h, h * d * h⁻¹ = y := by
    obtain ⟨h₀, hh₀⟩ := hconj d hd1 hdd
    intro y hy1 hyy
    obtain ⟨h, hh⟩ := hconj y hy1 hyy
    refine ⟨h⁻¹ * h₀, ?_⟩
    rw [← hh] at hh₀
    calc h⁻¹ * h₀ * d * (h⁻¹ * h₀)⁻¹ = h⁻¹ * (h₀ * d * h₀⁻¹) * h := by group
      _ = y := by rw [hh₀]; group
  have hinv : ∀ {p : Equiv.Perm (Fin 28)} (hp : p ∈ QP.originalSubgroup), p ≠ 1 → p * p = 1 →
      e.symm ⟨p, hp⟩ ≠ 1 ∧ e.symm ⟨p, hp⟩ * e.symm ⟨p, hp⟩ = 1 := by
    intro p hp hp1 hpp
    refine ⟨fun h => hp1 ?_, ?_⟩
    · have := congrArg (fun y => ((e y : QP.originalSubgroup) : Equiv.Perm (Fin 28))) h
      simpa using this
    · rw [← map_mul]
      have : (⟨p, hp⟩ : QP.originalSubgroup) * ⟨p, hp⟩ = 1 := Subtype.ext hpp
      rw [this, map_one]
  obtain ⟨h0a, h0b⟩ := hinv u33d0_mem u33d0_ne_one u33d0_mul_self
  obtain ⟨h1a, h1b⟩ := hinv u33d1_mem u33d1_ne_one u33d1_mul_self
  obtain ⟨h2a, h2b⟩ := hinv u33d2_mem u33d2_ne_one u33d2_mul_self
  obtain ⟨h3a, h3b⟩ := hinv u33d3_mem u33d3_ne_one u33d3_mul_self
  have h01mem : u33d0 * u33d1 ∈ QP.originalSubgroup := mul_mem u33d0_mem u33d1_mem
  obtain ⟨h4a, h4b⟩ := hinv h01mem u33d01_ne_one u33d01_mul_self
  have he01 : e.symm ⟨u33d0 * u33d1, h01mem⟩ =
      e.symm ⟨u33d0, u33d0_mem⟩ * e.symm ⟨u33d1, u33d1_mem⟩ := by
    rw [← map_mul]
    rfl
  refine ⟨x₀, e.symm ⟨u33d1, u33d1_mem⟩, e.symm ⟨u33d2, u33d2_mem⟩,
    e.symm ⟨u33d3, u33d3_mem⟩, ?_, ?_, hconj' _ h0a h0b, hconj' _ h1a h1b, hconj' _ h2a h2b,
    hconj' _ h3a h3b, ?_⟩
  ·
    set T : Set QP.originalSubgroup := {⟨u33d0, u33d0_mem⟩, ⟨u33d1, u33d1_mem⟩,
      ⟨u33d2, u33d2_mem⟩, ⟨u33d3, u33d3_mem⟩} with hT
    have hTtop : Subgroup.closure T = ⊤ := by
      apply Subgroup.map_injective QP.originalSubgroup.subtype_injective
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      refine Eq.trans ?_ closure_u33
      congr 1
      ext p
      simp [hT]
    have himage : (e.symm : QP.originalSubgroup →* X) '' T =
        {x₀, e.symm ⟨u33d1, u33d1_mem⟩, e.symm ⟨u33d2, u33d2_mem⟩,
          e.symm ⟨u33d3, u33d3_mem⟩} := by
      simp [hT, Set.image_insert_eq, hx₀]
    have h := congrArg (Subgroup.map (e.symm : QP.originalSubgroup →* X)) hTtop
    rw [MonoidHom.map_closure, himage, ← MonoidHom.range_eq_map] at h
    rw [h]
    exact MonoidHom.range_eq_top.mpr e.symm.surjective
  · apply e.injective
    rw [map_mul, map_mul, hx₀, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Subtype.ext u33d0_mul_u33d1
  · rw [← he01]
    exact hconj' _ h4a h4b

end Gens

section Sum

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem invariant_of_commSpace_le (ρ : X →* (V ≃ₗ[ZMod 2] V)) {S : Set X}
    (hS : Subgroup.closure S = ⊤) (hSS : ∀ s ∈ S, s * s = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ s ∈ S, commSpace (ρ s) ≤ U) : ∀ x : X, ∀ w ∈ U, ρ x w ∈ U := by
  have hgen : ∀ s ∈ S, ∀ w ∈ U, ρ s w ∈ U := by
    intro s hs w hw
    have h1 : ρ s w - w ∈ U := hU s hs (sub_mem_commSpace _ w)
    have := U.add_mem h1 hw
    rwa [sub_add_cancel] at this
  intro x
  have hx : x ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction'' with
  | mem s hs => exact hgen s hs
  | inv_mem s hs =>
    rw [inv_eq_of_mul_eq_one_right (hSS s hs)]
    exact hgen s hs
  | one => intro w hw; simpa using hw
  | mul a b _ _ ha hb =>
    intro w hw
    rw [map_mul, LinearEquiv.mul_apply]
    exact ha _ (hb w hw)

end Sum

theorem not_dvd_card_orthogonalGroup {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : m ≤ 2)
    (hdim : finrank (ZMod 2) V = 2 * (m + 1)) :
    ¬ 6048 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  intro hdvd
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim (ε := 1)
      (Or.inl ⟨rfl, hp⟩)
    rw [h2] at h
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = N at h hdvd
    interval_cases m <;> norm_num [Finset.prod_Icc_succ_top] at h <;> omega
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim (ε := -1)
      (Or.inr ⟨rfl, hp⟩)
    rw [h2] at h
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = N at h hdvd
    interval_cases m <;> norm_num [Finset.prod_Icc_succ_top] at h <;> omega

end AS35YR

namespace S14

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 AS35YR

theorem asc512U33ModuleInput :
    Asc512U33ModuleInput := by
  intro X _ hX V _ _ _ Q hQ ρ hρ hiso hirr d hd1 hdd hdim
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hX
  obtain ⟨x₀, x₁, x₂, x₃, hgen, hcomm, ⟨h₀, hh₀⟩, ⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, ⟨h₃, hh₃⟩, ⟨h₄, hh₄⟩⟩ :=
    exists_gens_of_equiv e hd1 hdd
  have hO : ∀ x : X, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hiso x)
  set k := finrank (ZMod 2) (commSpace (ρ d)) with hk
  have hconjdim : ∀ h : X, finrank (ZMod 2) (commSpace (ρ (h * d * h⁻¹))) = k := by
    intro h
    rw [map_mul, map_mul, map_inv]
    exact finrank_commSpace_conj _ _
  have hsq : ∀ h : X, h * d * h⁻¹ * (h * d * h⁻¹) = 1 := by
    intro h
    calc h * d * h⁻¹ * (h * d * h⁻¹) = h * (d * d) * h⁻¹ := by group
      _ = 1 := by rw [hdd]; group
  have hne : ∀ h : X, ρ (h * d * h⁻¹) ≠ 1 := by
    intro h h1
    apply hd1
    have h2 : h * d * h⁻¹ = 1 := hρ (h1.trans (map_one ρ).symm)
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group
  have hk1 : 1 ≤ k := by
    have := one_le_finrank_commSpace (hne 1)
    rwa [hconjdim] at this
  have hinv : ∀ x : X, x * x = 1 → ρ x * ρ x = 1 := fun x hx => by rw [← map_mul, hx, map_one]
  set C₀ := commSpace (ρ x₀)
  set C₁ := commSpace (ρ x₁)
  set C₂ := commSpace (ρ x₂)
  set C₃ := commSpace (ρ x₃)
  have hS : ∀ s ∈ ({x₀, x₁, x₂, x₃} : Set X), s * s = 1 := by
    rintro s (rfl | rfl | rfl | rfl)
    · rw [← hh₀]; exact hsq h₀
    · rw [← hh₁]; exact hsq h₁
    · rw [← hh₂]; exact hsq h₂
    · rw [← hh₃]; exact hsq h₃
  have hU : ∀ s ∈ ({x₀, x₁, x₂, x₃} : Set X), commSpace (ρ s) ≤ C₀ ⊔ C₁ ⊔ C₂ ⊔ C₃ := by
    rintro s (rfl | rfl | rfl | rfl)
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have htop : C₀ ⊔ C₁ ⊔ C₂ ⊔ C₃ = ⊤ := by
    rcases hirr _ (invariant_of_commSpace_le ρ hgen hS hU) with h | h
    · exfalso
      have h0 : C₀ = ⊥ := eq_bot_iff.mpr (h ▸ le_sup_left.trans (le_sup_left.trans le_sup_left))
      have h1 := one_le_finrank_commSpace (hne h₀)
      rw [hh₀] at h1
      change 1 ≤ finrank (ZMod 2) C₀ at h1
      rw [h0, finrank_bot] at h1
      omega
    · exact h
  have hd₀ : finrank (ZMod 2) C₀ = k := by rw [← hconjdim h₀, hh₀]
  have hd₁ : finrank (ZMod 2) C₁ = k := by rw [← hconjdim h₁, hh₁]
  have hd₂ : finrank (ZMod 2) C₂ = k := by rw [← hconjdim h₂, hh₂]
  have hd₃ : finrank (ZMod 2) C₃ = k := by rw [← hconjdim h₃, hh₃]
  have hd₄ : finrank (ZMod 2) (commSpace (ρ x₀ * ρ x₁)) = k := by
    rw [← map_mul, ← hconjdim h₄, hh₄]
  have hmeet : C₀ ⊓ C₁ ≠ ⊥ := commSpace_inf_ne_bot hQ (hO x₀) (hO x₁)
    (hinv x₀ (hS x₀ (by simp))) (hinv x₁ (hS x₁ (by simp)))
    (by rw [← map_mul, hcomm, map_mul]) (by rw [← hh₀]; exact hne h₀)
    (hd₁.trans hd₀.symm) (hd₄.trans hd₀.symm)
  have hmeet1 : 1 ≤ finrank (ZMod 2) (C₀ ⊓ C₁ : Submodule (ZMod 2) V) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hmeet (Submodule.finrank_eq_zero.mp h0)
  have hdimV : finrank (ZMod 2) V ≤ 7 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq C₀ C₁
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq (C₀ ⊔ C₁) C₂
    have e3 := Submodule.finrank_sup_add_finrank_inf_eq (C₀ ⊔ C₁ ⊔ C₂) C₃
    rw [htop, finrank_top] at e3
    omega
  have halt : (QuadraticMap.polarBilin Q).IsAlt := fun x => by
    change QuadraticMap.polar Q x x = 0
    rw [QuadraticMap.polar_self, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨r, hr⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hQ
  have hpos : 1 ≤ finrank (ZMod 2) V := by
    have := Submodule.finrank_le C₀
    omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hm : m ≤ 2 := by omega
  have hdim' : finrank (ZMod 2) V = 2 * (m + 1) := by omega
  have hcardX : Nat.card X = 6048 := by rw [Nat.card_congr e.toEquiv, card_QP]
  set φ : X →* TauCeti.QuadraticMap.orthogonalGroup Q := ρ.codRestrict _ hO with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact hρ (congrArg Subtype.val hab)
  have hdvd : 6048 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← hcardX, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact not_dvd_card_orthogonalGroup hQ hm hdim' hdvd

end S14

end CFSG.LargeExtraspecial
