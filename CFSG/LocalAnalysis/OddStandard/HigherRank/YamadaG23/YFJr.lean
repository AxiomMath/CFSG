module

public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ : Type} [Group Γ] [Finite Γ]

private def MaxRank (T U : Subgroup Γ) : Prop :=
  ∀ V : Subgroup Γ, V ≤ T → IsMulCommutative V → CFSG.pRank 2 V ≤ CFSG.pRank 2 U

private def IsMaxAb (T U : Subgroup Γ) : Prop :=
  U ≤ T ∧ IsMulCommutative U ∧ MaxRank T U

private lemma pRank_map_equiv {Γ' : Type} [Group Γ'] [Finite Γ']
    (e : Γ ≃* Γ') (H : Subgroup Γ) :
    CFSG.pRank 2 (H.map e.toMonoidHom) = CFSG.pRank 2 H :=
  (CFSG.pRank_congr_of_mulEquiv (H.equivMapOfInjective e.toMonoidHom e.injective) 2).symm

private lemma thompsonRank_eq_sSup (T : Subgroup Γ) :
    thompsonRank T = sSup {U : Subgroup Γ | IsMaxAb T U} := by
  rw [thompsonRank]
  apply le_antisymm
  · exact iSup_le fun U => iSup_le fun hU => iSup_le fun hc => iSup_le fun hm =>
      le_sSup ⟨hU, hc, hm⟩
  · exact sSup_le fun U hU => le_iSup_of_le U (le_iSup_of_le hU.1 (le_iSup_of_le hU.2.1
      (le_iSup_of_le hU.2.2 le_rfl)))

private lemma isMaxAb_map {Γ' : Type} [Group Γ'] [Finite Γ']
    (e : Γ ≃* Γ') {T U : Subgroup Γ} (h : IsMaxAb T U) :
    IsMaxAb (T.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · haveI : IsMulCommutative U := h.2.1
    exact inferInstance
  · intro V' hV'T hV'c
    have hV'eq : (V'.comap e.toMonoidHom).map e.toMonoidHom = V' :=
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective V'
    have hVle : V'.comap e.toMonoidHom ≤ T := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hV'T hx)
      rw [← e.injective hte]
      exact ht
    have hVc : IsMulCommutative (V'.comap e.toMonoidHom) := by
      haveI : IsMulCommutative V' := hV'c
      exact Subgroup.comap_injective_isMulCommutative V' e.injective
    calc CFSG.pRank 2 V' = CFSG.pRank 2 ((V'.comap e.toMonoidHom).map e.toMonoidHom) := by
          rw [hV'eq]
      _ = CFSG.pRank 2 (V'.comap e.toMonoidHom) := pRank_map_equiv e _
      _ ≤ CFSG.pRank 2 U := h.2.2 _ hVle hVc
      _ = CFSG.pRank 2 (U.map e.toMonoidHom) := (pRank_map_equiv e U).symm

private lemma isMaxAb_comap {Γ' : Type} [Group Γ'] [Finite Γ']
    (e : Γ ≃* Γ') {T : Subgroup Γ} {U' : Subgroup Γ'}
    (h : IsMaxAb (T.map e.toMonoidHom) U') :
    IsMaxAb T (U'.comap e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (h.1 hx)
    rw [← e.injective hte]
    exact ht
  · haveI : IsMulCommutative U' := h.2.1
    exact Subgroup.comap_injective_isMulCommutative U' e.injective
  · intro V hVT hVc
    have hU'eq : (U'.comap e.toMonoidHom).map e.toMonoidHom = U' :=
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective U'
    have hVc' : IsMulCommutative (V.map e.toMonoidHom) := by
      haveI : IsMulCommutative V := hVc
      exact inferInstance
    calc CFSG.pRank 2 V = CFSG.pRank 2 (V.map e.toMonoidHom) := (pRank_map_equiv e V).symm
      _ ≤ CFSG.pRank 2 U' := h.2.2 _ (Subgroup.map_mono hVT) hVc'
      _ = CFSG.pRank 2 ((U'.comap e.toMonoidHom).map e.toMonoidHom) := by rw [hU'eq]
      _ = CFSG.pRank 2 (U'.comap e.toMonoidHom) := pRank_map_equiv e _

private lemma thompsonRank_map_equiv {Γ' : Type} [Group Γ'] [Finite Γ']
    (e : Γ ≃* Γ') (T : Subgroup Γ) :
    (thompsonRank T).map e.toMonoidHom = thompsonRank (T.map e.toMonoidHom) := by
  apply le_antisymm
  · rw [thompsonRank_eq_sSup T, sSup_eq_iSup', Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [thompsonRank_eq_sSup (T.map e.toMonoidHom)]
    exact le_sSup (isMaxAb_map e U.2)
  · rw [thompsonRank_eq_sSup (T.map e.toMonoidHom), thompsonRank_eq_sSup T]
    refine sSup_le fun U' hU' => ?_
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective U']
    exact Subgroup.map_mono (le_sSup (isMaxAb_comap e hU'))

theorem thompsonRank_top_map_equiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (e : Y ≃* Y') :
    (thompsonRank (⊤ : Subgroup Y)).map e.toMonoidHom = thompsonRank (⊤ : Subgroup Y') := by
  simpa using thompsonRank_map_equiv e (⊤ : Subgroup Y)

theorem thompsonRank_top_pullback {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]
    (φ : P →* Q) (hφ : Function.Surjective φ) {N A : Subgroup Q} [N.Normal] (hNA : N ≤ A)
    {M : Subgroup P} [M.Normal] (hM : M = N.comap φ)
    (h : thompsonRank (⊤ : Subgroup (Q ⧸ N)) = A.map (QuotientGroup.mk' N)) :
    thompsonRank (⊤ : Subgroup (P ⧸ M)) = (A.comap φ).map (QuotientGroup.mk' M) := by
  let ψ : P ⧸ M →* Q ⧸ N := QuotientGroup.map M N φ (le_of_eq hM)
  have hψmk : ∀ p : P, ψ (QuotientGroup.mk' M p) = QuotientGroup.mk' N (φ p) := by
    intro p
    simp only [ψ, QuotientGroup.mk'_apply, QuotientGroup.map_mk]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨p, rfl⟩ := hφ q
    exact ⟨QuotientGroup.mk' M p, hψmk p⟩
  have hinj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective M x
    obtain ⟨p', rfl⟩ := QuotientGroup.mk'_surjective M y
    rw [hψmk p, hψmk p'] at hxy
    rw [QuotientGroup.mk'_eq_mk' N] at hxy
    obtain ⟨z, hz, hz'⟩ := hxy
    rw [QuotientGroup.mk'_eq_mk' M]
    refine ⟨p⁻¹ * p', ?_, by group⟩
    rw [hM, Subgroup.mem_comap, map_mul, map_inv, ← hz', inv_mul_cancel_left]
    exact hz
  let ψe : (P ⧸ M) ≃* (Q ⧸ N) := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hψemk : ∀ p : P, ψe (QuotientGroup.mk' M p) = QuotientGroup.mk' N (φ p) :=
    fun p => hψmk p
  have h1 : (thompsonRank (⊤ : Subgroup (P ⧸ M))).map ψe.toMonoidHom =
      thompsonRank (⊤ : Subgroup (Q ⧸ N)) := thompsonRank_top_map_equiv ψe
  rw [h] at h1
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNA]
  have hMle : M ≤ A.comap φ := by
    intro x hx
    rw [hM, Subgroup.mem_comap] at hx
    exact Subgroup.mem_comap.2 (hNA hx)
  have hAc : ((A.comap φ).map (QuotientGroup.mk' M)).comap (QuotientGroup.mk' M) =
      A.comap φ := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hMle]
  have h2 : thompsonRank (⊤ : Subgroup (P ⧸ M)) =
      (A.map (QuotientGroup.mk' N)).comap ψe.toMonoidHom := by
    rw [← h1, Subgroup.comap_map_eq_self_of_injective (f := ψe.toMonoidHom) ψe.injective]
  have h3 : (A.map (QuotientGroup.mk' N)).comap ψe.toMonoidHom =
      (A.comap φ).map (QuotientGroup.mk' M) := by
    ext x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective M x
    rw [Subgroup.mem_comap]
    change ψe (QuotientGroup.mk' M p) ∈ A.map (QuotientGroup.mk' N) ↔
      QuotientGroup.mk' M p ∈ (A.comap φ).map (QuotientGroup.mk' M)
    rw [hψemk p]
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, hae⟩ := hx
      obtain ⟨z, hz, hza⟩ := (QuotientGroup.mk'_eq_mk' N).1 hae
      rw [Subgroup.mem_map]
      refine ⟨p, ?_, rfl⟩
      rw [Subgroup.mem_comap, ← hza]
      exact A.mul_mem ha (hNA hz)
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨b, hb, hbe⟩ := hx
      rw [Subgroup.mem_comap] at hb
      obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' M).1 hbe
      have hbp : b⁻¹ * p ∈ M := by
        rw [← hz', inv_mul_cancel_left]
        exact hz
      rw [hM, Subgroup.mem_comap] at hbp
      have hbpn : (φ b)⁻¹ * φ p ∈ N := by simpa using hbp
      rw [Subgroup.mem_map]
      refine ⟨φ p, ?_, rfl⟩
      have h1 := A.mul_mem hb (hNA hbpn)
      rwa [mul_inv_cancel_left] at h1
  rw [h2, h3]

end CFSG.OddStandard.HigherRank.YamadaG23
