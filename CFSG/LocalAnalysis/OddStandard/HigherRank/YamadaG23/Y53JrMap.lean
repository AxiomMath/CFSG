module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

private def IsMaxAb {Γ : Type} [Group Γ] [Finite Γ] (T U : Subgroup Γ) : Prop :=
  U ≤ T ∧ IsMulCommutative U ∧
    ∀ V : Subgroup Γ, V ≤ T → IsMulCommutative V → CFSG.pRank 2 V ≤ CFSG.pRank 2 U

private lemma thompsonRank_eq_sSup {Γ : Type} [Group Γ] [Finite Γ] (T : Subgroup Γ) :
    thompsonRank T = sSup {U : Subgroup Γ | IsMaxAb T U} := by
  rw [thompsonRank]
  apply le_antisymm
  · exact iSup_le fun U => iSup_le fun hU => iSup_le fun hc => iSup_le fun hm =>
      le_sSup ⟨hU, hc, hm⟩
  · exact sSup_le fun U hU => le_iSup_of_le U (le_iSup_of_le hU.1 (le_iSup_of_le hU.2.1
      (le_iSup_of_le hU.2.2 le_rfl)))

private lemma pRank_map_inj {Y Γ : Type} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (f : Y →* Γ) (hf : Function.Injective f) (H : Subgroup Y) :
    CFSG.pRank 2 (H.map f) = CFSG.pRank 2 H :=
  (CFSG.pRank_congr_of_mulEquiv (H.equivMapOfInjective f hf) 2).symm

private lemma isMaxAb_map_inj {Y Γ : Type} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (f : Y →* Γ) (hf : Function.Injective f) {T U : Subgroup Y} (h : IsMaxAb T U) :
    IsMaxAb (T.map f) (U.map f) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · haveI : IsMulCommutative U := h.2.1
    exact inferInstance
  · intro V' hV'T hV'c
    have hVcomap_le : V'.comap f ≤ T := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hV'T hx)
      rwa [hf hte] at ht
    have hVrange : V' ≤ f.range := hV'T.trans (Subgroup.map_le_range (f := f) T)
    have hVeq : (V'.comap f).map f = V' := Subgroup.map_comap_eq_self hVrange
    have hVc : IsMulCommutative (V'.comap f) := by
      haveI : IsMulCommutative V' := hV'c
      exact Subgroup.comap_injective_isMulCommutative V' hf
    calc CFSG.pRank 2 V' = CFSG.pRank 2 ((V'.comap f).map f) := by rw [hVeq]
      _ = CFSG.pRank 2 (V'.comap f) := pRank_map_inj f hf _
      _ ≤ CFSG.pRank 2 U := h.2.2 _ hVcomap_le hVc
      _ = CFSG.pRank 2 (U.map f) := (pRank_map_inj f hf U).symm

private lemma isMaxAb_comap_inj {Y Γ : Type} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (f : Y →* Γ) (hf : Function.Injective f) {T : Subgroup Y} {U' : Subgroup Γ}
    (h : IsMaxAb (T.map f) U') :
    IsMaxAb T (U'.comap f) := by
  have hU'range : U' ≤ f.range := h.1.trans (Subgroup.map_le_range (f := f) T)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (h.1 hx)
    rwa [hf hte] at ht
  · haveI : IsMulCommutative U' := h.2.1
    exact Subgroup.comap_injective_isMulCommutative U' hf
  · intro V hVT hVc
    have hU'eq : (U'.comap f).map f = U' := Subgroup.map_comap_eq_self hU'range
    have hVc' : IsMulCommutative (V.map f) := by
      haveI : IsMulCommutative V := hVc
      exact inferInstance
    calc CFSG.pRank 2 V = CFSG.pRank 2 (V.map f) := (pRank_map_inj f hf V).symm
      _ ≤ CFSG.pRank 2 U' := h.2.2 _ (Subgroup.map_mono hVT) hVc'
      _ = CFSG.pRank 2 ((U'.comap f).map f) := by rw [hU'eq]
      _ = CFSG.pRank 2 (U'.comap f) := pRank_map_inj f hf _

private lemma thompsonRank_map_inj' {Y Γ : Type} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (f : Y →* Γ) (hf : Function.Injective f) (T : Subgroup Y) :
    (thompsonRank T).map f = thompsonRank (T.map f) := by
  apply le_antisymm
  · rw [thompsonRank_eq_sSup T, sSup_eq_iSup', Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [thompsonRank_eq_sSup (T.map f)]
    exact le_sSup (isMaxAb_map_inj f hf U.2)
  · rw [thompsonRank_eq_sSup (T.map f), thompsonRank_eq_sSup T]
    refine sSup_le fun U' hU' => ?_
    have hU'range : U' ≤ f.range := hU'.1.trans (Subgroup.map_le_range (f := f) T)
    rw [← Subgroup.map_comap_eq_self hU'range]
    exact Subgroup.map_mono (le_sSup (isMaxAb_comap_inj f hf hU'))

theorem y53_thompsonRank_map_inj {Y Γ : Type} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (f : Y →* Γ) (hf : Function.Injective f) :
    (thompsonRank (⊤ : Subgroup Y)).map f = thompsonRank f.range := by
  simpa only [Subgroup.map_top] using thompsonRank_map_inj' f hf (⊤ : Subgroup Y)

theorem y53_section_transport {Γ : Type} [Group Γ] [Finite Γ] {T₁ W Z A : Subgroup Γ}
    (hWT : W ≤ T₁) (hZW : Z ≤ W) (hAW : A ≤ W) (hZn : (Z.subgroupOf T₁).Normal)
    (h : SecProp W Z (fun Y _ _ π => thompsonRank (⊤ : Subgroup Y) = (A.subgroupOf W).map π)) :
    SecProp T₁ Z (fun Y _ _ π =>
      thompsonRank ((W.subgroupOf T₁).map π) = (A.subgroupOf T₁).map π) := by
  unfold SecProp at h ⊢
  obtain ⟨hZWn, hW⟩ := h
  refine ⟨hZn, ?_⟩
  let inc : ↥W →* ↥T₁ := Subgroup.inclusion hWT
  let ι : ↥W ⧸ Z.subgroupOf W →* ↥T₁ ⧸ Z.subgroupOf T₁ :=
    QuotientGroup.map (Z.subgroupOf W) (Z.subgroupOf T₁) inc
      (le_of_eq (Subgroup.comap_inclusion_subgroupOf hWT Z).symm)
  have hιmk : ∀ w : ↥W, ι (QuotientGroup.mk' (Z.subgroupOf W) w) =
      QuotientGroup.mk' (Z.subgroupOf T₁) (inc w) := by
    intro w
    simp only [ι, QuotientGroup.mk'_apply, QuotientGroup.map_mk]
  have hinj : Function.Injective ι := by
    intro x y hxy
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) x
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) y
    rw [hιmk w, hιmk w'] at hxy
    rw [QuotientGroup.mk'_eq_mk' (Z.subgroupOf T₁)] at hxy
    obtain ⟨z, hz, hz'⟩ := hxy
    rw [QuotientGroup.mk'_eq_mk' (Z.subgroupOf W)]
    refine ⟨⟨(z : Γ), hZW (Subgroup.mem_subgroupOf.1 hz)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.1 hz
    · apply Subtype.ext
      have hval := congrArg (fun t : ↥T₁ => (t : Γ)) hz'
      rw [Subgroup.coe_mul] at hval
      have hinc : ∀ u : ↥W, ((inc u : ↥T₁) : Γ) = (u : Γ) := fun _ => rfl
      rw [hinc w, hinc w'] at hval
      rw [Subgroup.coe_mul]
      simpa using hval
  have hrange : ι.range = (W.subgroupOf T₁).map (QuotientGroup.mk' (Z.subgroupOf T₁)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) x
      rw [hιmk w]
      exact Subgroup.mem_map.2 ⟨inc w, w.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t : Γ) ∈ W := ht
      refine ⟨QuotientGroup.mk' (Z.subgroupOf W) ⟨(t : Γ), ht'⟩, ?_⟩
      rw [hιmk]
      exact congrArg (QuotientGroup.mk' (Z.subgroupOf T₁)) (Subtype.ext rfl)
  have hcomp : ι.comp (QuotientGroup.mk' (Z.subgroupOf W)) =
      (QuotientGroup.mk' (Z.subgroupOf T₁)).comp inc :=
    MonoidHom.ext fun w => hιmk w
  have hsub : (A.subgroupOf W).map inc = A.subgroupOf T₁ := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨(x : Γ), hAW hx⟩, hx, Subtype.ext rfl⟩
  have hmap := y53_thompsonRank_map_inj ι hinj
  change thompsonRank (map (QuotientGroup.mk' (Z.subgroupOf T₁)) (W.subgroupOf T₁)) =
    map (QuotientGroup.mk' (Z.subgroupOf T₁)) (A.subgroupOf T₁)
  rw [hW, hrange] at hmap
  rw [← hmap, Subgroup.map_map, hcomp, ← Subgroup.map_map, hsub]

end CFSG.OddStandard.HigherRank.YamadaG23
