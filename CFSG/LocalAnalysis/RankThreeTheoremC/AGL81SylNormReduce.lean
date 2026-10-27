module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenThreeInspection
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormW
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem exists_mulAut_of_sylAct {A : Type} [Group A] [Finite A] {P : Subgroup A} {b : A}
    {Q : Type} [Group Q] (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Q) (hb : SylAct P b)
    (hW : ¬ TrivOnW P b) :
    ∃ α : MulAut Q, orderOf α ∣ orderOf b ∧ (wSup Q).map α.toMonoidHom = wSup Q ∧
      (∃ S : Subgroup Q, S ≤ wSup Q ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex (wSup Q) ∧
        S.map α.toMonoidHom = S) ∧
      ∃ w ∈ wSup Q, α w ≠ w := by
  classical
  unfold SylAct at hb
  obtain ⟨hodd, hbP, T, hTP, hT2, hbT, hTW, hTi⟩ := hb
  unfold TrivOnW at hW
  push Not at hW
  obtain ⟨w, hw, hwW, hwc⟩ := hW
  let α₀ : MulAut ↥P := P.normalizerMonoidHom ⟨b, hbP⟩
  let αhat : MulAut (↥P ⧸ CFSG.pCore 2 ↥P) := CFSG.pCoreQuotMulAut ↥P α₀
  let α : MulAut Q := e.symm.trans (αhat.trans e)
  have hαdef : α = e.symm.trans (αhat.trans e) := rfl
  let Φ : MulAut (↥P ⧸ CFSG.pCore 2 ↥P) →* MulAut Q :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      map_one' := by ext x; simp
      map_mul' := by intro σ τ; ext x; simp }
  have hΦα : Φ αhat = α := rfl
  have horder : orderOf α ∣ orderOf b := by
    rw [← hΦα]
    refine (orderOf_map_dvd Φ αhat).trans ((orderOf_map_dvd (CFSG.pCoreQuotMulAut ↥P) α₀).trans ?_)
    have h := orderOf_map_dvd (P.normalizerMonoidHom)
      (⟨b, hbP⟩ : ↥(normalizer (P : Set A)))
    rwa [Subgroup.orderOf_mk] at h
  let That : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    (T.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hThatdef : That = (T.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) := rfl
  let S : Subgroup Q := That.map e.toMonoidHom
  have hSdef : S = That.map e.toMonoidHom := rfl
  haveI : Finite Q := Finite.of_surjective _ e.surjective
  have hSp : IsPGroup 2 S := by
    have h1 : IsPGroup 2 (T.subgroupOf P) :=
      IsPGroup.of_equiv hT2 (Subgroup.subgroupOfEquivOfLe hTP).symm
    have h2 : IsPGroup 2 That := h1.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    exact h2.map e.toMonoidHom
  have hSle : S ≤ wSup Q := by
    have h1 : S ≤ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).map e.toMonoidHom :=
      Subgroup.map_mono hTW
    rwa [map_wSup_eq e] at h1
  have hSrel : ¬ 2 ∣ S.relIndex (wSup Q) := by
    have h := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) That
      (wSup (↥P ⧸ CFSG.pCore 2 ↥P)) e.injective
    rw [map_wSup_eq e] at h
    rw [show S.relIndex (wSup Q) = That.relIndex (wSup (↥P ⧸ CFSG.pCore 2 ↥P)) from h]
    exact hTi
  have hKα₀ : (T.subgroupOf P).map α₀.toMonoidHom ≤ T.subgroupOf P := by
    rintro - ⟨t, ht, rfl⟩
    simp only [Subgroup.mem_subgroupOf] at ht ⊢
    change (((α₀ t : ↥P)) : A) ∈ T
    have hcoe : (((α₀ t : ↥P)) : A) = b * (t : A) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe P ⟨b, hbP⟩ t
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.1 hbT (t : A)).1 ht
  have hcomp_mk : αhat.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp α₀.toMonoidHom := by
    ext x
    exact CFSG.pCoreQuotMulAut_mk α₀ x
  have hThatmap : That.map αhat.toMonoidHom ≤ That := by
    rw [hThatdef, Subgroup.map_map, hcomp_mk, ← Subgroup.map_map]
    exact Subgroup.map_mono hKα₀
  have hαcomp : α.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp αhat.toMonoidHom := by
    ext x
    simp [hαdef, MulEquiv.trans_apply]
  have hSmap : S.map α.toMonoidHom = (That.map αhat.toMonoidHom).map e.toMonoidHom := by
    rw [hSdef, Subgroup.map_map, hαcomp, ← Subgroup.map_map]
  have hSfix : S.map α.toMonoidHom = S := by
    have hle : S.map α.toMonoidHom ≤ S := by
      rw [hSmap, hSdef]
      exact Subgroup.map_mono hThatmap
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective S α.toMonoidHom α.injective).toEquiv).le
  have hfix : α (e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩)) ≠
      e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩) := by
    intro heq
    have h3 : α (e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩)) =
        e (αhat (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩)) := by
      simp [hαdef, MulEquiv.trans_apply]
    have hfix' : αhat (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ :=
      e.injective (by rw [← h3]; exact heq)
    have hpc : (α₀ ⟨w, hw⟩) * (⟨w, hw⟩ : ↥P)⁻¹ ∈ CFSG.pCore 2 ↥P := by
      have h := Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 2) (G := ↥P))
        ((⟨w, hw⟩ : ↥P)⁻¹ * α₀ ⟨w, hw⟩) ?_ (α₀ ⟨w, hw⟩)
      · simpa [mul_assoc] using h
      · refine QuotientGroup.eq.1 ?_
        rw [← CFSG.pCoreQuotMulAut_mk α₀ ⟨w, hw⟩]
        exact hfix'.symm
    have hcoe : (((α₀ ⟨w, hw⟩) * (⟨w, hw⟩ : ↥P)⁻¹ : ↥P) : A) =
        b * w * b⁻¹ * w⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hmem : b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
      have h1 := (CFSG.mem_openPCoreOf_iff (p := 2)
        ((α₀ ⟨w, hw⟩) * (⟨w, hw⟩ : ↥P)⁻¹)).2 hpc
      rwa [hcoe] at h1
    exact hwc hmem
  refine ⟨α, horder, map_wSup_eq α, ⟨S, hSle, hSp, hSrel, hSfix⟩, ?_⟩
  refine ⟨e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩), ?_, hfix⟩
  have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩) ∈
      (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hwW
  rwa [map_wSup_eq e] at h1

theorem pCore_two_eq_bot_of_mulEquiv {A : Type} [Group A] [Finite A] {P : Subgroup A}
    {Q : Type} [Group Q] (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Q) : CFSG.pCore 2 Q = ⊥ := by
  rw [← CFSG.pCore_map_iso 2 e, pCore_quotient_pCore_eq_bot', Subgroup.map_bot]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
