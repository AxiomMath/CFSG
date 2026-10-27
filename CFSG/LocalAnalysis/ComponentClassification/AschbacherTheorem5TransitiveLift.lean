module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveApply

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem bar_overlap_inf_centralizer (hC : Counterexample G D r Abar) {Q : Subgroup G}
    {j : Fin r} (hQj : Q ≤ centralizing D (Abar j)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G} (hTQ : T ≤ rightConjugate Q g)
    (hT2 : IsPGroup 2 T) (k : Fin r) :
    bar D T ⊓
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar k)) : Set (Bar D)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxT, hxC⟩
  obtain ⟨t, htT, rfl⟩ := (mem_bar_iff D T x).mp hxT
  rw [Subgroup.mem_bot]
  by_contra hne
  have ht1 : (t : G) ≠ 1 := by
    intro h
    apply hne
    rw [show t = 1 from Subtype.ext h, map_one]
  have htk : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar k)) (t : G) :=
    (centralizes_iff_mem_centralizer D _ (preimage_le D _) t).mpr hxC
  have hgt : g * t * g⁻¹ ∈ Q := (mem_rightConjugate_iff Q g t).mp (hTQ htT)
  obtain ⟨e, he⟩ := hT2 ⟨t, htT⟩
  apply hg
  refine mem_normalizer_of_fusion hC j k (t := g * t * g⁻¹) (g := g) ⟨e, ?_⟩ ?_
    (centralizes_of_mem_centralizing (hQj hgt)) ?_
  · rw [conj_pow, show ((t : G) ^ 2 ^ e) = 1 from congrArg Subtype.val he]
    group
  · intro h1
    apply ht1
    calc (t : G) = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rwa [show g⁻¹ * (g * (t : G) * g⁻¹) * g = t by group]

omit [Finite G] in
theorem mem_of_toBar_mem_bar {Y : Subgroup G} (hOY : aschbacherThm5Core D ≤ Y)
    {h : Subgroup.normalizer (D : Set G)} (hh : toBar D h ∈ bar D Y) : (h : G) ∈ Y := by
  obtain ⟨y, hy, hyh⟩ := (mem_bar_iff D Y _).mp hh
  have h1 : toBar D (y⁻¹ * h) = 1 := by rw [map_mul, map_inv, hyh, inv_mul_cancel]
  have hmem := (toBar_eq_one_iff D _).mp h1
  have := Y.mul_mem hy (hOY hmem)
  simpa using this

theorem exists_lift_isPGroup {Vbar : Subgroup (Bar D)} (hV : IsPGroup 2 Vbar) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTH : T ≤ Subgroup.normalizer (D : Set G)) (hTV : bar D T ≤ Vbar) :
    ∃ V : Subgroup G, T ≤ V ∧ V ≤ Subgroup.normalizer (D : Set G) ∧ IsPGroup 2 V ∧
      bar D V = Vbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (Vbar.comap (toBar D)).map (Subgroup.normalizer (D : Set G)).subtype with hWdef
  have hWH : W ≤ Subgroup.normalizer (D : Set G) := Subgroup.map_subtype_le _
  have hTW : T ≤ W := by
    intro t ht
    exact ⟨⟨t, hTH ht⟩, hTV (toBar_mem_bar D (h := ⟨t, hTH ht⟩) ht), rfl⟩
  have hWsub : W.subgroupOf (Subgroup.normalizer (D : Set G)) = Vbar.comap (toBar D) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.normalizer (D : Set G)).subtype_injective _
  have hWbar : bar D W = Vbar := by
    unfold bar
    rw [hWsub]
    exact Subgroup.map_comap_eq_self_of_surjective (toBar_surjective D) Vbar
  obtain ⟨V, hV', hTV'⟩ := AschbacherTheorem3.exists_isSylowOf_le hT2 hTW
  refine ⟨V, hTV', hV'.le.trans hWH, hV'.isPGroup, ?_⟩
  have hsyl := isSylowOf_bar (D := D) hV' hWH
  rw [hWbar] at hsyl
  exact (hsyl.eq_of_le hsyl.le le_rfl hV).symm

theorem exists_inter_conj_card (hC : Counterexample G D r Abar) {Q : Subgroup G} {k j : Fin r}
    (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q) (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G))) (hT1 : T ≠ ⊥) :
    ∃ R : Subgroup G, R ≤ Q ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g ∧
      IsPGroup 2 R ∧ Nat.card R = Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, htight⟩ := tightlyEmbedded_of_le_centralizing hC hkQ hQj hHQ
  obtain ⟨S, hS, hTS⟩ := AschbacherTheorem3.exists_isSylowOf_le hT.isPGroup
    (le_sup_right : T ≤ Q ⊔ T)
  have hg' : g ∉ Subgroup.normalizer (Q : Set G) := hN ▸ hg
  have hTQ' : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) := hN ▸ hT
  obtain ⟨-, hcard, -⟩ := part_one_of_isSylowOf Q htight g hg' hTQ' hS hTS hT1
  refine ⟨S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q, le_inf inf_le_right ?_,
    hS.isPGroup.to_le (inf_le_left.trans inf_le_left), hcard⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g := by
    have h := normalizer_two_subgroup_le (rightConjugate Q g) T
      (rightConjugate_tightlyEmbedded Q htight g) hT.isPGroup (hT.le.trans inf_le_left) hT1
    rwa [← AschbacherTheorem3.rightConjugate_normalizer, hN] at h
  exact inf_le_left.trans (inf_le_right.trans hNT)

theorem card_le_of_overlap (hC : Counterexample G D r Abar) {Q : Subgroup G} {k j : Fin r}
    (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q) (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G)))
    {R' : Subgroup G} (hR' : R' ≤ Q ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hR'2 : IsPGroup 2 R') : Nat.card R' ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G)
  have hR'' : rightConjugate R' g⁻¹ ≤ rightConjugate Q g⁻¹ ⊓ H := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹⁻¹).toMonoidHom) hR'
    change rightConjugate R' g⁻¹ ≤ rightConjugate (Q ⊓ rightConjugate H g) g⁻¹ at h1
    rwa [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one] at h1
  obtain ⟨T₂, hT₂, hRT₂⟩ := AschbacherTheorem3.exists_isSylowOf_le
    (AschbacherTheorem3.isPGroup_rightConjugate hR'2 g⁻¹) hR''
  rw [← rightConjugate_card R' g⁻¹]
  by_cases hT₂1 : T₂ = ⊥
  · rw [hT₂1, le_bot_iff] at hRT₂
    rw [hRT₂, Subgroup.card_bot]
    exact Nat.card_pos
  have hg' : g⁻¹ ∉ H := fun h => hg (by simpa using H.inv_mem h)
  obtain ⟨R, hR, hR2, hRcard⟩ := exists_inter_conj_card hC hkQ hQj hHQ hg' hT₂ hT₂1
  have hRg : rightConjugate R g ≤ rightConjugate Q g ⊓ H := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hR
    change rightConjugate R g ≤ rightConjugate (Q ⊓ rightConjugate H g⁻¹) g at h1
    rwa [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel,
      rightConjugate_one] at h1
  calc Nat.card (rightConjugate R' g⁻¹) ≤ Nat.card T₂ := Subgroup.card_le_of_le hRT₂
    _ = Nat.card R := hRcard.symm
    _ = Nat.card (rightConjugate R g) := (rightConjugate_card R g).symm
    _ ≤ Nat.card T := AschbacherTheorem3.card_le_of_isSylowOf hT
        (AschbacherTheorem3.isPGroup_rightConjugate hR2 g) hRg

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
