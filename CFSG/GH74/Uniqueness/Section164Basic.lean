module

public import CFSG.GH74.Uniqueness.Section163

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

section Conf

variable (c : Conf16 Z M)

theorem t_mem_B0 : c.t ∈ c.B0 := subset_closure ⟨c.ht, c.ht_B⟩

theorem z_mem_B : c.z ∈ c.B := (mem_inf.mp c.z_mem_BM).1

theorem z_mem_B0 : c.z ∈ c.B0 := subset_closure ⟨c.hz, z_mem_B c⟩

theorem B0_le_B : c.B0 ≤ c.B := Cor713.zHull_le _

theorem gamma_subset_Bzero : Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) ⊆ (c.Bzero : Set X) :=
  fun _ hy => subset_closure (Or.inl (subset_closure hy))

theorem t_mem_Bzero : c.t ∈ c.Bzero := subset_closure (Or.inr rfl)

theorem z_mem_Bzero : c.z ∈ c.Bzero := gamma_subset_Bzero c ⟨c.hz, c.z_mem_BM⟩

theorem Bzero_le_B0 : c.Bzero ≤ c.B0 := by
  refine (closure_le _).mpr ?_
  rintro y (hy | rfl)
  · have hsub : Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) ⊆ Z ∩ (c.B : Set X) :=
      fun x hx => ⟨hx.1, (mem_inf.mp hx.2).1⟩
    exact closure_mono hsub hy
  · exact t_mem_B0 c

theorem Bzero_le_B : c.Bzero ≤ c.B := (Bzero_le_B0 c).trans (B0_le_B c)

theorem u_mem_centralizer_Bzero : c.u ∈ centralizer (c.Bzero : Set X) := by
  rw [mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.mp (Bzero_le_B c hh)

theorem commute_t_of_mem_centralizer_Bzero {g : X} (hg : g ∈ centralizer (c.Bzero : Set X)) :
    g * c.t = c.t * g :=
  ((mem_centralizer_iff.mp hg) c.t (t_mem_Bzero c)).symm

theorem commute_z_of_mem_centralizer_Bzero {g : X} (hg : g ∈ centralizer (c.Bzero : Set X)) :
    g * c.z = c.z * g :=
  ((mem_centralizer_iff.mp hg) c.z (z_mem_Bzero c)).symm

end Conf

theorem mem_D_of_commute (S : ZDSetup X Z M) (c : Ctx16 Z M) {g : X} (hgz : g * c.z = c.z * g)
    (hgt : g * c.t = c.t * g) : g ∈ M ⊓ conjugate M c.t := by
  have hgM : g ∈ M :=
    S.prodDisc.centralizer_le_of_mem c.hz c.hzM (mem_centralizer_singleton_iff.mpr hgz)
  refine mem_inf.mpr ⟨hgM, mem_conjugate_iff.mpr ?_⟩
  have e : c.t * g * c.t⁻¹ = g := by
    calc c.t * g * c.t⁻¹ = g * c.t * c.t⁻¹ := by rw [hgt]
      _ = g := by group
  rw [e]
  exact hgM

theorem centralizer_Bzero_le_D (S : ZDSetup X Z M) (c : Conf16 Z M) :
    centralizer (c.Bzero : Set X) ≤ c.D := fun _ hg =>
  mem_D_of_commute S c.toCtx16 (commute_z_of_mem_centralizer_Bzero c hg)
    (commute_t_of_mem_centralizer_Bzero c hg)

theorem commutator_zpowers_commutator_eq {A : Subgroup X} {t : X} (hA : Odd (Nat.card A))
    (ht : orderOf t = 2) (htA : t ∈ normalizer (A : Set X)) :
    ⁅zpowers t, ⁅zpowers t, A⁆⁆ = ⁅zpowers t, A⁆ := by
  have hTA : zpowers t ≤ normalizer (A : Set X) := zpowers_le.mpr htA
  let : MulDistribMulAction ↥(zpowers t) ↥A :=
    MulDistribMulAction.compHom ↥A (Subgroup.inclusion hTA)
  have hsmul : ∀ (a : ↥(zpowers t)) (y : ↥A), ((a • y : ↥A) : X) = a * y * (a : X)⁻¹ :=
    fun _ _ => rfl
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥(zpowers t)) := by
    rw [Nat.card_zpowers, ht]
    exact (Nat.coprime_two_left.mpr hA).symm
  have hidem := (CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization
    (A := ↥(zpowers t)) (H := ↥A) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hA) hcop).2.2.2
  have hmap := congrArg (Subgroup.map A.subtype) hidem
  simp only [map_actionCommutator_conj hsmul, map_subtype_top] at hmap
  exact hmap

omit [Finite X] in
theorem mem_normalizer_commutator {H₁ H₂ : Subgroup X} {g : X}
    (h₁ : g ∈ normalizer (H₁ : Set X)) (h₂ : g ∈ normalizer (H₂ : Set X)) :
    g ∈ normalizer ((⁅H₁, H₂⁆ : Subgroup X) : Set X) := by
  have key : ∀ k : X, k ∈ normalizer (H₁ : Set X) → k ∈ normalizer (H₂ : Set X) →
      ∀ x ∈ ⁅H₁, H₂⁆, k * x * k⁻¹ ∈ ⁅H₁, H₂⁆ := by
    intro k hk₁ hk₂ x hx
    have hle : ⁅H₁, H₂⁆ ≤ (⁅H₁, H₂⁆).comap (MulAut.conj k).toMonoidHom := by
      rw [commutator_le]
      intro a ha b hb
      rw [mem_comap]
      have e : (MulAut.conj k).toMonoidHom ⁅a, b⁆ = ⁅k * a * k⁻¹, k * b * k⁻¹⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact commutator_mem_commutator ((mem_normalizer_iff.mp hk₁ a).mp ha)
        ((mem_normalizer_iff.mp hk₂ b).mp hb)
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g h₁ h₂ x
  · intro hx
    have := key g⁻¹ (inv_mem h₁) (inv_mem h₂) _ hx
    simpa [mul_assoc] using this

theorem kGrp_le_D (hZ : IsInvariantInvolutionSet Z) {t : X} (ht : t ∈ Z) :
    kGrp M t ≤ M ⊓ conjugate M t := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hTO : zpowers t ≤ normalizer (pPrimeCoreIn (M ⊓ conjugate M t) : Set X) :=
    zpowers_le.mpr (mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate ht2))
  exact (Subgroup.le_normalizer_iff_commutator_le_right.mp hTO).trans (pPrimeCoreIn_le _)

omit [Finite X] in
theorem mem_centralizer_zpowers {t g : X} (hgt : g * t = t * g) :
    g ∈ centralizer ((zpowers t : Subgroup X) : Set X) := by
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact (Commute.zpow_left (show Commute t g from hgt.symm) k).eq

omit [Finite X] in
theorem mem_normalizer_kGrp {t g : X} (hgD : g ∈ M ⊓ conjugate M t) (hgt : g * t = t * g) :
    g ∈ normalizer (kGrp M t : Set X) :=
  mem_normalizer_commutator (centralizer_le_normalizer _ (mem_centralizer_zpowers hgt))
    (pPrimeCoreIn_normalizes _ hgD)

omit [Finite X] in
theorem commutator_le_inf_cenHull (hZ : IsInvariantInvolutionSet Z) {t w : X} (ht : t ∈ Z)
    (htw : t * w = w * t) {D A : Subgroup X} (htD : t ∈ normalizer (D : Set X)) (hAD : A ≤ D)
    (hAw : A ≤ centralizer ({w} : Set X)) :
    ⁅zpowers t, A⁆ ≤ D ⊓ cenHull Z w := by
  rw [commutator_le]
  intro g hg a ha
  have hgD : g ∈ normalizer (D : Set X) := (zpowers_le.mpr htD) hg
  have htC : t ∈ cenHull Z w := subset_closure ⟨ht, mem_centralizer_singleton_iff.mpr htw⟩
  have hgC : g ∈ cenHull Z w := (zpowers_le.mpr htC) hg
  have haN : a ∈ normalizer (cenHull Z w : Set X) := le_normalizer_zHull hZ _ (hAw ha)
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact D.mul_mem ((mem_normalizer_iff.mp hgD a).mp (hAD ha)) (D.inv_mem (hAD ha))
  · rw [commutatorElement_def]
    have h1 : a * g⁻¹ * a⁻¹ ∈ cenHull Z w := (mem_normalizer_iff.mp haN g⁻¹).mp (inv_mem hgC)
    have e : g * a * g⁻¹ * a⁻¹ = g * (a * g⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem hgC h1

theorem commutator_le_commutator_inf_cenHull (hZ : IsInvariantInvolutionSet Z) {t w : X}
    (ht : t ∈ Z) (htw : t * w = w * t) {D A : Subgroup X} (htD : t ∈ normalizer (D : Set X))
    (hAD : A ≤ D) (hAw : A ≤ centralizer ({w} : Set X)) (hA : Odd (Nat.card A))
    (htA : t ∈ normalizer (A : Set X)) :
    ⁅zpowers t, A⁆ ≤ ⁅zpowers t, D ⊓ cenHull Z w⁆ := by
  rw [← commutator_zpowers_commutator_eq hA (hZ.1 t ht) htA]
  exact commutator_mono le_rfl (commutator_le_inf_cenHull hZ ht htw htD hAD hAw)

theorem commutator_inf_le_fZero (h162 : Lemma162Stmt Z M) (c : Ctx16 Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hzF : c.z ∈ F) (htF : c.t ∈ F) (hne : ∃ y ∈ Z, y ∈ F ∧ y ∈ M ∧ y ≠ c.z)
    (hFF : zHull Z F = F) :
    ⁅zpowers c.t, (M ⊓ conjugate M c.t) ⊓ F⁆ ≤ fZero Z M F c.t := by
  obtain ⟨m, -, h | h⟩ := h162 c F hF hzF htF hne hFF
  · rw [h.1, commutator_le]
    intro g hg a ha
    have hgF : g ∈ F := (zpowers_le.mpr htF) hg
    have haF : a ∈ F := (mem_inf.mp ha).2
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hgF haF) (inv_mem hgF)) (inv_mem haF)
  · exact h.2.2.1

theorem cenHull_ne_top
    (S : ZDSetup X Z M) {w : X} (hw2 : orderOf w = 2) : cenHull Z w ≠ ⊤ := by
  intro h
  apply S.cor714_centralizer_ne_top hw2
  rw [eq_top_iff, ← h]
  exact Cor713.zHull_le _

theorem commutator_le_fZero
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Ctx16 Z M)
    {w : X} (hw2 : orderOf w = 2) (hzw : c.z * w = w * c.z) (htw : c.t * w = w * c.t)
    (hne : ∃ y ∈ Z, y ∈ cenHull Z w ∧ y ∈ M ∧ y ≠ c.z) {A : Subgroup X}
    (hAD : A ≤ M ⊓ conjugate M c.t) (hAw : A ≤ centralizer ({w} : Set X))
    (hA : Odd (Nat.card A)) (htA : c.t ∈ normalizer (A : Set X)) :
    ⁅zpowers c.t, A⁆ ≤ fZero Z M (cenHull Z w) c.t :=
  (commutator_le_commutator_inf_cenHull S.invariant c.ht htw
    (mem_normalizer_inf_conjugate (S.invariant.mul_self_eq_one c.ht)) hAD hAw hA htA).trans
    (commutator_inf_le_fZero h162 c (cenHull_ne_top S hw2)
      (subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr hzw⟩)
      (subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr htw⟩) hne (zHull_zHull _))

end Sec164

end CFSG.GH74.Uniqueness
