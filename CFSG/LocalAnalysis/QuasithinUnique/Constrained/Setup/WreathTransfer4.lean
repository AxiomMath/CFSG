module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer3

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

theorem elemThompsonIn_two_eq (S : Subgroup H) : elemThompsonIn 2 S = thompsonJ S :=
  CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ S

namespace WreathHyp

abbrev IsT0 (t : ∀ i, MulAut ↥(planesIn W I i)) : Prop :=
  @IsCoordProduct ↥W h.cg (Fin r) (planesIn W I) h.T0 Finset.univ t

@[expose] noncomputable def eElt (t : ∀ i, MulAut ↥(planesIn W I i)) (i : Fin r) : MulAut ↥W :=
  @coordElt ↥W h.cg (Fin r) _ _ (planesIn W I) h.planeFamily t i

include h

variable {t : ∀ i, MulAut ↥(planesIn W I i)}

theorem rho_J_le_T0 (ht : h.IsT0 t) : (thompsonJ R).map h.rho ≤ h.T0 := by
  let _ := h.cg
  unfold thompsonJ
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  obtain ⟨-, J, hC⟩ := h.maxElem_structure ht hA
  exact fun g hg => ⟨Subgroup.map_mono hA.1 hg, hC.le_baseGp hg⟩

omit [Finite H] in
theorem rho_J_ne_bot : (thompsonJ R).map h.rho ≠ ⊥ := by
  intro hbot
  have hJker : thompsonJ R ≤ h.rho.ker := by
    intro x hx
    have : h.rho x ∈ (thompsonJ R).map h.rho := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [h.ker_rho_eq_centralizer_V] at hJker
  exact h.J_not_le_centralizer hJker

omit [Finite H] in
theorem eElt_mem_T0 (ht : h.IsT0 t) (i : Fin r) : h.eElt t i ∈ h.T0 := by
  let _ := h.cg
  exact (ht.mem_iff _).mpr
    (CoordCond.mono (Finset.subset_univ _) (coordCond_coordElt h.planeFamily i))

omit [Finite H] in
theorem eElt_apply_self (i : Fin r) {y : ↥W} (hy : y ∈ planesIn W I i) :
    h.eElt t i y = ((t i ⟨y, hy⟩ : ↥(planesIn W I i)) : ↥W) := by
  let _ := h.cg
  exact coordElt_apply_self h.planeFamily t i hy

omit [Finite H] in
theorem eElt_apply_ne {i j : Fin r} (hj : j ≠ i) {y : ↥W} (hy : y ∈ planesIn W I j) :
    h.eElt t i y = y := by
  let _ := h.cg
  exact coordElt_apply_ne h.planeFamily t hj hy

omit [Finite H] in
theorem rho_conj_eElt (ht : h.IsT0 t) {x : H} (hx : x ∈ R) (i : Fin r) :
    h.rho x * h.eElt t i * (h.rho x)⁻¹ = h.eElt t (h.piH x i) := by
  let _ := h.cg
  have hF := h.planeFamily
  set σ := h.piH x with hσdef
  have hρσ : ∀ k, h.rho x • planesIn W I k = planesIn W I (σ k) := fun k =>
    permHom_spec hF ⟨h.rho x, wreathAut_le_permuting hF Pm (h.rho_mem_wreathAut x)⟩ k
  have hmem : ∀ k (y : ↥W), y ∈ planesIn W I k → h.rho x y ∈ planesIn W I (σ k) :=
    fun k y hy => ((smul_planes_iff (h.rho x) k (σ k)).mp (hρσ k) y).mpr hy
  have hmem' : ∀ k (y : ↥W), h.rho x y ∈ planesIn W I (σ k) → y ∈ planesIn W I k :=
    fun k y hy => ((smul_planes_iff (h.rho x) k (σ k)).mp (hρσ k) y).mp hy
  have heB : h.eElt t i ∈ baseGp (planesIn W I) := coordElt_mem_baseGp hF t i
  set g' := h.rho x * h.eElt t i * (h.rho x)⁻¹ with hg'
  have hg'B : g' ∈ baseGp (planesIn W I) := by
    intro j
    have h1 : (h.rho x)⁻¹ • planesIn W I j = planesIn W I (σ.symm j) := by
      rw [inv_smul_eq_iff, hρσ, σ.apply_symm_apply]
    show (h.rho x * h.eElt t i * (h.rho x)⁻¹) • planesIn W I j = planesIn W I j
    rw [mul_smul, mul_smul, h1, (mem_baseGp.mp heB) (σ.symm j), hρσ, σ.apply_symm_apply]
  have hg'T0 : g' ∈ h.T0 := by
    refine ⟨?_, hg'B⟩
    exact (R.map h.rho).mul_mem ((R.map h.rho).mul_mem ⟨x, hx, rfl⟩ (h.eElt_mem_T0 ht i).1)
      ((R.map h.rho).inv_mem ⟨x, hx, rfl⟩)
  have hout : ∀ k, k ≠ σ i → ∀ y ∈ planesIn W I k, g' y = y := by
    intro k hk y hy
    have hy' : (h.rho x)⁻¹ y ∈ planesIn W I (σ.symm k) := by
      refine hmem' (σ.symm k) _ ?_
      simpa using hy
    have hne : σ.symm k ≠ i := fun e => hk (by rw [← e, σ.apply_symm_apply])
    have he : h.eElt t i ((h.rho x)⁻¹ y) = (h.rho x)⁻¹ y := h.eElt_apply_ne hne hy'
    show h.rho x (h.eElt t i ((h.rho x)⁻¹ y)) = y
    rw [he]
    simp
  obtain ⟨z, hz, hz'⟩ : ∃ z : ↥W, z ∈ planesIn W I i ∧ h.eElt t i z ≠ z := by
    have h1 := (ht.invol i (Finset.mem_univ i)).1
    obtain ⟨y, hy⟩ : ∃ y : ↥(planesIn W I i), t i y ≠ y := by
      by_contra hcon
      push Not at hcon
      exact h1 (MulEquiv.ext hcon)
    refine ⟨y, y.2, ?_⟩
    rw [h.eElt_apply_self i y.2]
    intro hc
    exact hy (Subtype.ext hc)
  have hnt : g' (h.rho x z) ≠ h.rho x z := by
    show h.rho x (h.eElt t i ((h.rho x)⁻¹ (h.rho x z))) ≠ h.rho x z
    simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact fun hc => hz' ((h.rho x).injective hc)
  rcases (ht.mem_iff g').mp hg'T0 (σ i) with hid | ⟨-, hgt⟩
  · exact absurd (hid ⟨h.rho x z, hmem i z hz⟩) hnt
  · apply hF.autEq_of_forall_plane
    intro k y hy
    by_cases hk : k = σ i
    · subst hk
      rw [hgt ⟨y, hy⟩, h.eElt_apply_self (σ i) hy]
    · rw [hout k hk y hy, h.eElt_apply_ne hk hy]

omit [Finite H] in
theorem I_injective : Function.Injective I := by
  intro i j hij
  by_contra hne
  have hd : Disjoint (I i) (I j) := h.I_indep.pairwiseDisjoint hne
  rw [hij] at hd
  have := disjoint_self.mp hd
  have h4 := h.I_card j
  rw [this, Subgroup.card_bot] at h4
  omega

theorem rho_J_eq_T0 (ht : h.IsT0 t) : (thompsonJ R).map h.rho = h.T0 := by
  let _ := h.cg
  have hF := h.planeFamily
  set K := (thompsonJ R).map h.rho with hK
  apply le_antisymm (h.rho_J_le_T0 ht)
  have hAK : ∀ A, IsMaxElemAbelian R A → A.map h.rho ≤ K := fun A hA =>
    Subgroup.map_mono (maxElem_le_thompsonJ hA)
  have hex : ∃ i, h.eElt t i ∈ K := by
    by_contra hcon
    push Not at hcon
    apply h.rho_J_ne_bot
    unfold thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_eq_bot.mpr fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_eq_bot.mpr fun hA => ?_
    obtain ⟨-, J, hC⟩ := h.maxElem_structure ht hA
    have hJ : J = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      apply hcon i
      have hmem : h.eElt t i ∈ A.map h.rho :=
        (hC.mem_iff _).mpr (CoordCond.mono (Finset.singleton_subset_iff.mpr hi)
          (coordCond_coordElt hF i))
      exact hAK A hA hmem
    rw [eq_bot_iff]
    intro g hg
    have := eq_one_of_coordCond_empty hF (hJ ▸ (hC.mem_iff g).mp hg)
    rw [this]
    exact Subgroup.one_mem _
  have hall : ∀ j, h.eElt t j ∈ K := by
    obtain ⟨i, hi⟩ := hex
    intro j
    obtain ⟨x, hx, hxij⟩ := h.transitive_R i j
    have hσ : h.piH x i = j := by
      have := h.map_conj_plane x i
      rw [hxij] at this
      exact (h.I_injective this).symm
    rw [← hσ, ← h.rho_conj_eElt ht hx i]
    obtain ⟨k, hk, hkρ⟩ := hi
    rw [← hkρ]
    have hxn : x ∈ Subgroup.normalizer (thompsonJ R : Set H) :=
      normalizer_le_normalizer_thompsonJ R (Subgroup.le_normalizer hx)
    exact ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxn k).mp hk, by simp [map_mul]⟩
  intro g hg
  have hmem := coordCond_mem_iSup hF Finset.univ g ((ht.mem_iff g).mp hg)
  refine (iSup₂_le (fun i _ => (Subgroup.zpowers_le (G := MulAut ↥W)).mpr (hall i)) :
    (⨆ i ∈ (Finset.univ : Finset (Fin r)), Subgroup.zpowers (h.eElt t i)) ≤ K) hmem

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
