module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Outer
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley

theorem generation_transport {A B : Type*} [Group A] [Group B] (Ψ : A ≃* B) {Y S : Subgroup A}
    {g' : B} (hg : g' ∈ Subgroup.normalizer ((S.map Ψ.toMonoidHom : Subgroup B) : Set B))
    (hgen : Y.map Ψ.toMonoidHom ⊔ (Y.map Ψ.toMonoidHom).map (MulAut.conj g').toMonoidHom = ⊤) :
    Ψ.symm g' ∈ Subgroup.normalizer (S : Set A) ∧
      Y ⊔ Y.map (MulAut.conj (Ψ.symm g')).toMonoidHom = ⊤ := by
  constructor
  · rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    have e1 : h ∈ S ↔ Ψ h ∈ S.map Ψ.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simp
    have e2 : Ψ.symm g' * h * (Ψ.symm g')⁻¹ ∈ S ↔
        Ψ (Ψ.symm g' * h * (Ψ.symm g')⁻¹) ∈ S.map Ψ.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simp
    have e3 : Ψ (Ψ.symm g' * h * (Ψ.symm g')⁻¹) = g' * Ψ h * g'⁻¹ := by
      simp
    rw [e1, e2, e3]
    exact hg (Ψ h)
  · rw [eq_top_iff]
    intro z _
    have hz : Ψ z ∈ Y.map Ψ.toMonoidHom ⊔
        (Y.map Ψ.toMonoidHom).map (MulAut.conj g').toMonoidHom := by
      rw [hgen]
      exact Subgroup.mem_top _
    have hle : Y.map Ψ.toMonoidHom ⊔ (Y.map Ψ.toMonoidHom).map (MulAut.conj g').toMonoidHom ≤
        (Y ⊔ Y.map (MulAut.conj (Ψ.symm g')).toMonoidHom).map Ψ.toMonoidHom := by
      apply sup_le
      · exact Subgroup.map_mono le_sup_left
      · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨Ψ.symm g' * y * (Ψ.symm g')⁻¹, Subgroup.mem_sup_right ⟨y, hy, rfl⟩, ?_⟩
        simp [MulAut.conj_apply]
    obtain ⟨w, hw, hwz⟩ := hle hz
    have : w = z := Ψ.injective hwz
    rw [← this]
    exact hw

section Transport


theorem exists_equiv_g23 {Lb : Type} [Group Lb] (hm : ChevalleyExceptionalModel Lb .G2 3 1) :
    Nonempty (Lb ≃* G23) := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
  have : Fintype K := Fintype.ofFinite K
  have hFc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  let r : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hFc
  exact ⟨e.trans ((CFSG.TauCetiBridge.adjointQuotientCongr (τ := Tag.G2) r).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := Tag.G2) (K := ZMod 3))).trans QuotientGroup.quotientBot))⟩

theorem g23_generation_of_outer (hpin : G23Pinned phi)
    {Lb : Type} [Group Lb] (hm : ChevalleyExceptionalModel Lb .G2 3 1) {α : MulAut Lb}
    (hα : α * α = 1) (hout : α ∉ (MulAut.conj : Lb →* MulAut Lb).range) {Y : Subgroup Lb}
    (hYα : Y ≤ fixedGroup α) [hperf : Group.IsPerfect ↥Y] (hY : Nat.card Y = 504)
    {S : Subgroup Lb} (hSY : S ≤ Y) (hS : Nat.card S = 8) :
    ∃ g ∈ Subgroup.normalizer (S : Set Lb), Y ⊔ Y.map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨Ψ⟩ := exists_equiv_g23 hm
  set α' : MulAut G23 := MulAut.congr Ψ α with hα'def
  have hα'apply : ∀ z, α' (Ψ z) = Ψ (α z) := by
    intro z
    simp [hα'def, MulAut.congr_apply]
  have hα'2 : α' * α' = 1 := by
    rw [hα'def, ← map_mul, hα, map_one]
  have hout' : α' ∉ (MulAut.conj : G23 →* MulAut G23).range := by
    rintro ⟨c, hc⟩
    apply hout
    refine ⟨Ψ.symm c, MulEquiv.ext fun z => Ψ.injective ?_⟩
    have h1 : c * Ψ z * c⁻¹ = α' (Ψ z) := by
      have := congrArg (fun γ : MulAut G23 => γ (Ψ z)) hc
      simpa [MulAut.conj_apply] using this
    rw [hα'apply] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  obtain ⟨⟨ψ, hψ⟩, hcard⟩ := exists_conj_phi α' hα'2 hout'
  have hpin' : G23Pinned α' := G23Pinned.of_conj ψ hψ hpin
  have hinj : Function.Injective Ψ.toMonoidHom := Ψ.injective
  have hperf' : Group.IsPerfect ↥(Y.map Ψ.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := (Y.equivMapOfInjective Ψ.toMonoidHom hinj).toMonoidHom)
      (Y.equivMapOfInjective Ψ.toMonoidHom hinj).surjective
  have hY' : Nat.card ↥(Y.map Ψ.toMonoidHom) = 504 := by
    rw [← hY]
    exact (Nat.card_congr (Y.equivMapOfInjective Ψ.toMonoidHom hinj).toEquiv).symm
  have hS' : Nat.card ↥(S.map Ψ.toMonoidHom) = 8 := by
    rw [← hS]
    exact (Nat.card_congr (S.equivMapOfInjective Ψ.toMonoidHom hinj).toEquiv).symm
  have hYα' : Y.map Ψ.toMonoidHom ≤ fixedGroup α' := by
    rintro _ ⟨y, hy, rfl⟩
    show α' (Ψ y) = Ψ y
    have h1 : α y = y := hYα hy
    rw [hα'apply, h1]
  obtain ⟨g', hg', hgen'⟩ := generation_of_pinned hcard hpin' hYα' hY'
    (Subgroup.map_mono hSY) hS'
  obtain ⟨hg, hgen⟩ := generation_transport Ψ hg' hgen'
  exact ⟨Ψ.symm g', hg, hgen⟩

end Transport

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
