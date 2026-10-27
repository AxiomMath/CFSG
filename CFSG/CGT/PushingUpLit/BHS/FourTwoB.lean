module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.FourOneC
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

namespace Hyp42

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem dInter_eq_of_le (h : Hyp42 P D T M) {T₀ : Subgroup (MulAut V)} (hT₀P : T₀ ≤ P)
    (hT₀ : IsPGroup 2 T₀) (hE : ∀ A ∈ dInter D T, A ≤ T₀) : dInter D T₀ = dInter D T := by
  refine Set.Subset.antisymm (fun A hA => ?_) fun A hA => ⟨hA.1, hE A hA⟩
  obtain ⟨hAD, hAT₀⟩ := hA
  obtain ⟨T', hT', hT₀T'⟩ := Glauberman.exists_isSylowOf_ge (K := P) hT₀ hT₀P
  have hcomm : ∀ B ∈ dInter D T, ∀ b ∈ B, ∀ a ∈ A, a * b = b * a := fun B hB b hb a ha =>
    h.four_seven_pairs hT' A ⟨hAD, hAT₀.trans hT₀T'⟩ B ⟨hB.1, (hE B hB).trans hT₀T'⟩ a ha b hb
  have hAM : A ≤ M := fun a ha =>
    h.normSet_le (FourTwoTools.mem_setNormalizer_of_comm (h.le A hAD ha)
      fun B hB b hb => hcomm B hB b hb a ha)
  have hEle : (⨆ B ∈ dInter D T, B) ≤ T₀ := iSup₂_le hE
  have hEM : (⨆ B ∈ dInter D T, B) ≤ M := (iSup₂_le fun B hB => hB.2).trans h.le_M
  have hTM : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le
  obtain ⟨m, hmM, hm⟩ := FourTwoTools.exists_conjSub_ge hTM
    (hT₀.to_le (sup_le hEle hAT₀)) (sup_le hEM hAM)
  have hsub : dInter D T ⊆ dInter D (conjSub m T) := fun B hB =>
    ⟨hB.1, (le_iSup₂_of_le B hB le_rfl).trans (le_sup_left.trans hm)⟩
  rw [← h.dInter_conjSub_eq_of_subset (h.M_le hmM) hsub]
  exact ⟨hAD, le_sup_right.trans hm⟩

omit [Finite V] in
theorem le_M_of_dInter_eq (h : Hyp42 P D T M) {T₀ : Subgroup (MulAut V)} (hT₀P : T₀ ≤ P)
    (hd : dInter D T₀ = dInter D T) : T₀ ≤ M := fun g hg =>
  h.normSet_le (by
    have := h.toHyp41.mem_setNormalizer_dInter (hT₀P hg) hg
    rwa [hd] at this)

theorem cenIn_le_of_le_M (h : Hyp42 P D T M) {H T₀ : Subgroup (MulAut V)} (hHP : H ≤ P)
    (hT₀M : T₀ ≤ M) (hT₀ : IsPGroup 2 T₀) : cenIn H (fixV T₀) ≤ M := by
  have hTM : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le
  obtain ⟨g, hgM, hg⟩ := FourTwoTools.exists_conjSub_ge hTM hT₀ hT₀M
  intro x hx
  have hfix : ∀ v ∈ fixV T, x (g v) = g v := by
    intro v hv
    refine hx.2 (g v) ?_
    have h1 : (fixV T).map g.toMonoidHom ≤ fixV T₀ := by
      rw [← Glauberman.fixV_map_conj]
      exact fixV_anti hg
    exact h1 ⟨v, hv, rfl⟩
  have hmem : g⁻¹ * x * g ∈ cenIn P (fixV T) := by
    refine ⟨P.mul_mem (P.mul_mem (P.inv_mem (h.M_le hgM)) (hHP hx.1)) (h.M_le hgM), ?_⟩
    intro v hv
    simp [MulAut.mul_apply, hfix v hv]
  have := M.mul_mem (M.mul_mem hgM (h.cen_le hmem)) (M.inv_mem hgM)
  simpa [mul_assoc] using this

theorem restrict_dInter (h : Hyp42 P D T M) {H T₀ : Subgroup (MulAut V)} (hHP : H ≤ P)
    (hT₀ : IsSylowOf 2 T₀ H) (hd : dInter D T₀ = dInter D T)
    (hM : ¬ dInter D H ⊆ dInter D M) : Hyp42 H (dInter D H) T₀ (M ⊓ H) := by
  have hT₀M : T₀ ≤ M := h.le_M_of_dInter_eq (hT₀.1.trans hHP) hd
  exact
  { toHyp41 := h.toHyp41.dInter_restrict hHP
    syl := hT₀
    le_M := le_inf hT₀M hT₀.1
    M_le := inf_le_right
    ne_core := by
      intro heq
      obtain ⟨A, hAH, hAM⟩ := Set.not_subset.1 hM
      have hcore : A ∈ dCore H (dInter D H) (M ⊓ H) := heq ▸ hAH
      have h1 := hcore.2 1 H.one_mem
      rw [conjSub_one] at h1
      exact hAM ⟨hAH.1, h1.trans inf_le_left⟩
    normSet_le := by
      rw [FourTwoTools.dInter_dInter_of_le hT₀.1, hd]
      exact fun g hg => ⟨h.normSet_le ⟨hHP hg.1, hg.2⟩, hg.1⟩
    cen_le := fun x hx => ⟨h.cenIn_le_of_le_M hHP hT₀M hT₀.2.1 hx, hx.1⟩ }

end Hyp42

end CFSG.CGT.PushingUpLit.BHS
