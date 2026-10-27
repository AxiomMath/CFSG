module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Closed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.GoldschmidtFour
open scoped commutatorElement

namespace Sec3Closed

theorem exists_card_commutator_le_of_centralizer {Y : Type*} [Group Y] [Finite Y]
    {S : Sylow 2 Y} {V : Subgroup Y} (hV : Hyp S V) {t : Y} (htS : t ∈ (S : Subgroup Y))
    (htV : ∃ k : Y, t ∈ rightConjugate V k) :
    ∃ U ≤ V, (∀ e ∈ V, e * t = t * e → e ∈ U) ∧ ∃ h : Y, rightConjugate U h ≤ S ∧
      Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) ≤ V.relIndex (rightConjugate U h) := by
  have : Nonempty {k : Y // t ∈ rightConjugate V k} := by
    obtain ⟨k, hk⟩ := htV
    exact ⟨⟨k, hk⟩⟩
  obtain ⟨⟨k, hk⟩, hmax⟩ := Finite.exists_max
    (fun k : {k : Y // t ∈ rightConjugate V k} =>
      Nat.card (V ⊓ rightConjugate V k.1 : Subgroup Y))
  set V' := rightConjugate V k with hV'def
  set V0 := V ⊓ V'
  set V1 := V0 ⊔ Subgroup.zpowers t
  have ht2 : t ^ 2 = 1 := by
    have h := hV.sq_eq_one ((mem_rightConjugate_iff _ _ _).1 hk)
    rw [conj_pow] at h
    have : t ^ 2 = k⁻¹ * (k * t ^ 2 * k⁻¹) * k := by group
    rw [this, h]
    group
  have htN : t ∈ Subgroup.normalizer (V : Set Y) := hV.le_normalizer htS
  have hV'comm : ∀ {a b : Y}, a ∈ V' → b ∈ V' → a * b = b * a := by
    intro a b ha hb
    rw [hV'def, mem_rightConjugate_iff] at ha hb
    have h := hV.comm ha hb
    have h' : k * (a * b) * k⁻¹ = k * (b * a) * k⁻¹ := by
      calc k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        _ = (k * b * k⁻¹) * (k * a * k⁻¹) := h
        _ = k * (b * a) * k⁻¹ := by group
    simpa using h'
  set ψ := commHom hV.elem.1 htN
  set V2 := (V0.comap ψ).map V.subtype
  have hV2V : V2 ≤ V := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hV2mem : ∀ {e : Y}, e ∈ V2 → ⁅e, t⁆ ∈ V0 := by
    rintro _ ⟨e, he, rfl⟩
    exact he
  have hV0V : V0 ≤ V := inf_le_left
  have hV0V' : V0 ≤ V' := inf_le_right
  have htV' : t ∈ V' := hk
  have hV1V' : V1 ≤ V' := sup_le hV0V' (Subgroup.zpowers_le.2 htV')
  have hV0V2 : V0 ≤ V2 := by
    intro e he
    refine ⟨⟨e, hV0V he⟩, ?_, rfl⟩
    show ⁅e, t⁆ ∈ V0
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hV'comm (hV0V' he) htV')]
    exact V0.one_mem
  have hV'N1 : V' ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro x hx
    apply GoldschmidtFour.mem_normalizer_of_conj_mem
    intro y hy
    rw [hV'comm hx (hV1V' hy), mul_inv_cancel_right]
    exact hy
  have hV2N1 : V2 ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro e he
    have heV := hV2V he
    apply GoldschmidtFour.mem_normalizer_of_conj_mem
    have hle : V1 ≤ V1.comap (MulAut.conj e).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        show e * z * e⁻¹ ∈ V1
        rw [hV.comm heV (hV0V hz), mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hz
      · rw [Subgroup.zpowers_le]
        show e * t * e⁻¹ ∈ V1
        have h : e * t * e⁻¹ = ⁅e, t⁆ * t := by rw [commutatorElement_def]; group
        rw [h]
        exact V1.mul_mem (Subgroup.mem_sup_left (hV2mem he))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    intro y hy
    exact hle hy
  have hV2p : IsPGroup 2 V2 := hV.isPGroup.to_le hV2V
  have hV'p : IsPGroup 2 V' := GoldschmidtFour.isPGroup_rightConjugate hV.isPGroup k
  obtain ⟨a, haN, R, hRp, hV'R, hV2R⟩ :=
    GoldschmidtFour.exists_conj_le_of_isPGroup hV2p hV'p hV2N1 hV'N1
  have hRN : R ≤ Subgroup.normalizer (V' : Set Y) := hV.le_normalizer_of_isPGroup hRp hV'R
  have hstep : rightConjugate (rightConjugate V2 a) k⁻¹ ≤ Subgroup.normalizer (V : Set Y) := by
    have h := GoldschmidtFour.rightConjugate_le_normalizer (hV2R.trans hRN) k⁻¹
    rwa [hV'def, GoldschmidtFour.rightConjugate_rightConjugate_inv] at h
  obtain ⟨n, hnN, R', hR'p, hSR', hnR'⟩ := GoldschmidtFour.exists_conj_le_of_isPGroup
    (GoldschmidtFour.isPGroup_rightConjugate (GoldschmidtFour.isPGroup_rightConjugate hV2p a) k⁻¹)
    S.isPGroup' hstep
    hV.le_normalizer
  have hR'S : R' = S := S.is_maximal' hR'p hSR'
  rw [hR'S, rightConjugate_mul, rightConjugate_mul, ← mul_assoc] at hnR'
  set h := a * k⁻¹ * n with hhdef
  have hV1h : rightConjugate V1 h ≤ V := by
    have h1 : rightConjugate V1 h = rightConjugate (rightConjugate V1 k⁻¹) n := by
      rw [hhdef, ← rightConjugate_mul, ← rightConjugate_mul,
        GoldschmidtFour.rightConjugate_of_mem_normalizer haN]
    rw [h1]
    calc rightConjugate (rightConjugate V1 k⁻¹) n
        ≤ rightConjugate (rightConjugate V' k⁻¹) n :=
          GoldschmidtFour.rightConjugate_mono (GoldschmidtFour.rightConjugate_mono hV1V' _) _
      _ = V := by
          rw [hV'def, GoldschmidtFour.rightConjugate_rightConjugate_inv,
            GoldschmidtFour.rightConjugate_of_mem_normalizer hnN]
  have hth : t ∈ rightConjugate V h⁻¹ := by
    rw [mem_rightConjugate_iff, inv_inv]
    exact hV1h (GoldschmidtFour.conj_mem_rightConjugate
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) h)
  have hle : Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) ≤ Nat.card V0 := hmax ⟨h⁻¹, hth⟩
  have hcardh : Nat.card (V ⊓ rightConjugate V h : Subgroup Y) =
      Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) := by
    rw [← rightConjugate_card (V ⊓ rightConjugate V h⁻¹) h, GoldschmidtFour.rightConjugate_inf,
      GoldschmidtFour.rightConjugate_inv_rightConjugate, inf_comm]
  have hV0h : rightConjugate V0 h = V ⊓ rightConjugate V h := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_inf ((GoldschmidtFour.rightConjugate_mono le_sup_left h).trans hV1h)
        (GoldschmidtFour.rightConjugate_mono hV0V h)
    · rw [rightConjugate_card, hcardh]
      exact hle
  have hinter : V ⊓ rightConjugate V2 h = rightConjugate V0 h := by
    apply le_antisymm
    · rw [hV0h]
      exact inf_le_inf_left _ (GoldschmidtFour.rightConjugate_mono hV2V h)
    · exact le_inf (hV0h ▸ inf_le_left) (GoldschmidtFour.rightConjugate_mono hV0V2 h)
  have hrel : V.relIndex (rightConjugate V2 h) * Nat.card V0 = Nat.card V2 := by
    have h' := Subgroup.relIndex_mul_card (H := V) (K := rightConjugate V2 h)
    rwa [hinter, rightConjugate_card, rightConjugate_card] at h'
  have hcount : Nat.card ψ.range * Nat.card V0 ≤ Nat.card V2 := by
    have hcomap : Nat.card V2 = Nat.card (V0.comap ψ) :=
      Subgroup.card_map_of_injective V.subtype_injective
    rw [hcomap]
    refine GoldschmidtFour.card_range_mul_card_le ψ (C := ψ.ker.map V.subtype) ?_ ?_ ?_
    · intro e he
      refine ⟨⟨e, hV0V he⟩, ?_, rfl⟩
      exact (GoldschmidtFour.mem_ker_commHom _ _ _).2 (hV'comm (hV0V' he) htV')
    · rintro _ ⟨x, rfl⟩
      refine ⟨⟨ψ x, GoldschmidtFour.commHom_mem _ _ x⟩, ?_, rfl⟩
      exact (GoldschmidtFour.mem_ker_commHom _ _ _).2
        (GoldschmidtFour.commHom_mul_comm _ _ hV.elem.2 ht2 x)
    · rw [Subgroup.card_map_of_injective V.subtype_injective]
  have hcomm : Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) ≤ Nat.card ψ.range :=
    Subgroup.card_le_of_le (GoldschmidtFour.commutator_zpowers_le_range hV.elem.1 htN ht2)
  refine ⟨V2, hV2V, fun e he het => ?_, h, hnR', ?_⟩
  · refine ⟨⟨e, he⟩, ?_, rfl⟩
    show ψ ⟨e, he⟩ ∈ V0
    rw [MonoidHom.mem_ker.1 ((GoldschmidtFour.mem_ker_commHom hV.elem.1 htN ⟨e, he⟩).2 het)]
    exact V0.one_mem
  have hpos : 0 < Nat.card V0 := Nat.card_pos
  have key : Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) * Nat.card V0 ≤
      V.relIndex (rightConjugate V2 h) * Nat.card V0 := by
    rw [hrel]
    exact (Nat.mul_le_mul_right _ hcomm).trans hcount
  exact Nat.le_of_mul_le_mul_right key hpos

variable {G : Type} [Group G] [Finite G]

structure ClosedHyp (S Z : Subgroup G) : Prop where
  ZS : Z ≤ S
  SC : S ≤ centralizer (Z : Set G)
  cardZ : Nat.card Z = 4
  cardS : Nat.card S = 2 ^ 14
  commZ : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z
  sqZ : ∀ x ∈ S, x * x ∈ Z
  modA : ∀ t ∈ centralizer (Z : Set G) ⊓ normalizer (S : Set G), t ∉ S → t * t ∈ S →
    2 ^ 6 ≤ Nat.card ↥(⁅S, zpowers t⁆ ⊔ Z) ∧
      Nat.card {s : ↥S // (s : G) * t * (s : G)⁻¹ * t⁻¹ ∈ Z} = 2 ^ 10
  modB : ∀ D : Subgroup G, D ≤ centralizer (Z : Set G) ⊓ normalizer (S : Set G) →
    (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) → (D ⊓ S).relIndex D ≤ 16
  modC : ∀ D : Subgroup G, D ≤ centralizer (Z : Set G) ⊓ normalizer (S : Set G) →
    (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) → (D ⊓ S).relIndex D = 16 →
    Nat.card {s : ↥S // ∀ d ∈ D, (s : G) * d * (s : G)⁻¹ * d⁻¹ ∈ Z} ≤ 16

omit [Finite G] in
theorem mem_of_conj_mem {Z : Subgroup G} {c u : G} (hc : c ∈ centralizer (Z : Set G))
    (hu : c * u * c⁻¹ ∈ Z) : u ∈ Z := by
  have h1 : c * u * c⁻¹ * c = c * (c * u * c⁻¹) := (mem_centralizer_iff.1 hc) _ hu
  have h2 : u = c * u * c⁻¹ := by
    have h3 : c * u = c * (c * u * c⁻¹) := by rw [← h1]; group
    exact mul_left_cancel h3
  rw [h2]
  exact hu

theorem card_inf_le_card_subtype {A B : Subgroup G} {P : ↥A → Prop}
    (hP : ∀ (x : G) (hx : x ∈ A ⊓ B), P ⟨x, hx.1⟩) :
    Nat.card ↥(A ⊓ B) ≤ Nat.card {s : ↥A // P s} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨⟨x, x.2.1⟩, hP x x.2⟩) fun x y hxy => ?_
  apply Subtype.ext
  have h := congrArg (fun s : {s : ↥A // P s} => ((s : ↥A) : G)) hxy
  simpa using h

theorem card_subtype_mem_eq {S Z : Subgroup G} [(Z.subgroupOf (centralizer (Z : Set G))).Normal]
    (hZS : Z ≤ S) (hSC : S ≤ centralizer (Z : Set G))
    (X : Subgroup (centralizer (Z : Set G) ⧸ Z.subgroupOf (centralizer (Z : Set G)))) :
    Nat.card {s : ↥S // QuotientGroup.mk' (Z.subgroupOf (centralizer (Z : Set G)))
        (Subgroup.inclusion hSC s) ∈ X} =
      Nat.card Z * Nat.card ↥(X ⊓ (S.subgroupOf (centralizer (Z : Set G))).map
        (QuotientGroup.mk' (Z.subgroupOf (centralizer (Z : Set G))))) := by
  set ρ : ↥S →* centralizer (Z : Set G) ⧸ Z.subgroupOf (centralizer (Z : Set G)) :=
    (QuotientGroup.mk' (Z.subgroupOf (centralizer (Z : Set G)))).comp (Subgroup.inclusion hSC)
    with hρ
  have hrange : ρ.range = (S.subgroupOf (centralizer (Z : Set G))).map
      (QuotientGroup.mk' (Z.subgroupOf (centralizer (Z : Set G)))) := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : Nat.card ρ.ker = Nat.card Z := by
    have hkeq : ρ.ker = Z.subgroupOf S := by
      ext s
      rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
      rfl
    rw [hkeq]
    exact Nat.card_congr (subgroupOfEquivOfLe hZS).toEquiv
  have h1 : Nat.card {s : ↥S // ρ s ∈ X} = Nat.card ↥(X.comap ρ) := rfl
  have h2 : Nat.card ↥(X.comap ρ) * X.relIndex ρ.range = Nat.card ↥S := by
    rw [← Subgroup.index_comap]
    exact Subgroup.card_mul_index _
  have h3 : Nat.card ρ.ker * Nat.card ρ.range = Nat.card ↥S := Subgroup.card_ker_mul_card_range ρ
  have h4 : X.relIndex ρ.range * Nat.card ↥(X ⊓ ρ.range) = Nat.card ρ.range :=
    Subgroup.relIndex_mul_card X ρ.range
  have hpos : 0 < X.relIndex ρ.range := Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
  have key : Nat.card ↥(X.comap ρ) * X.relIndex ρ.range =
      Nat.card ρ.ker * Nat.card ↥(X ⊓ ρ.range) * X.relIndex ρ.range := by
    rw [h2, ← h3, ← h4]
    ring
  have h5 := Nat.eq_of_mul_eq_mul_right hpos key
  show Nat.card {s : ↥S // ρ s ∈ X} = _
  rw [h1, h5, hker, hrange]

namespace ClosedHyp

variable {S Z : Subgroup G} (H : ClosedHyp S Z)
include H

omit [Finite G] in
theorem isPGroup : IsPGroup 2 S := IsPGroup.of_card H.cardS

theorem conj_mem_of_conj_mem {c : G} (hc : c ∈ centralizer (Z : Set G))
    (hle : ∀ s ∈ S, c⁻¹ * s * c ∈ centralizer (Z : Set G) ⊓ normalizer (S : Set G)) :
    ∀ s ∈ S, c⁻¹ * s * c ∈ S := by
  classical
  set D := rightConjugate S c with hD
  have hmemD : ∀ {x : G}, x ∈ D ↔ c * x * c⁻¹ ∈ S := fun {x} => mem_rightConjugate_iff S c x
  have hDN : D ≤ centralizer (Z : Set G) ⊓ normalizer (S : Set G) := fun x hx => by
    have h1 := hle _ (hmemD.1 hx)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rwa [e] at h1
  have hDZ : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Z := fun x hx y hy => by
    have h1 := H.commZ _ (hmemD.1 hx) _ (hmemD.1 hy)
    have e : c * x * c⁻¹ * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ =
        c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by group
    rw [e] at h1
    exact mem_of_conj_mem hc h1
  have hDsq : ∀ x ∈ D, x * x ∈ Z := fun x hx => by
    have h1 := H.sqZ _ (hmemD.1 hx)
    have e : c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
    rw [e] at h1
    exact mem_of_conj_mem hc h1
  have hDel : ∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S := fun a ha b hb =>
    ⟨H.ZS (hDsq a ha), H.ZS (hDZ a ha b hb)⟩
  have hrelD : (D ⊓ S).relIndex D = S.relIndex D := inf_relIndex_left D S
  have hk16 : S.relIndex D ≤ 16 := by
    rw [← hrelD]
    exact H.modB D hDN hDel
  have hkm : S.relIndex D * Nat.card ↥(S ⊓ D) = 16384 := by
    rw [Subgroup.relIndex_mul_card, hD, rightConjugate_card, H.cardS]
    norm_num
  by_cases hDS : D ≤ S
  · intro s hs
    exact hDS (GoldschmidtFour.conj_mem_rightConjugate hs c)
  · exfalso
    obtain ⟨w, hwD, hwS⟩ := IsConcreteLE.not_le_iff_exists.1 hDS
    have hk1 : S.relIndex D ≠ 1 := fun h => hDS (relIndex_eq_one.1 h)
    rcases Nat.lt_or_ge (S.relIndex D) 16 with hlt | hge
    · have hw := (H.modA w (hDN hwD) hwS (H.ZS (hDsq w hwD))).2
      have hm : Nat.card ↥(S ⊓ D) ≤ Nat.card {s : ↥S // (s : G) * w * (s : G)⁻¹ * w⁻¹ ∈ Z} :=
        card_inf_le_card_subtype fun x hx => hDZ x hx.2 w hwD
      rw [hw, show (2 : ℕ) ^ 10 = 1024 by norm_num] at hm
      have h1 : S.relIndex D * Nat.card ↥(S ⊓ D) ≤ 15 * 1024 := Nat.mul_le_mul (by omega) hm
      omega
    · have hk : S.relIndex D = 16 := le_antisymm hk16 hge
      have hw := H.modC D hDN hDel (hrelD.trans hk)
      have hm : Nat.card ↥(S ⊓ D) ≤
          Nat.card {s : ↥S // ∀ d ∈ D, (s : G) * d * (s : G)⁻¹ * d⁻¹ ∈ Z} :=
        card_inf_le_card_subtype fun x hx d hd => hDZ x hx.2 d hd
      have hm16 := hm.trans hw
      rw [hk] at hkm
      omega

theorem isSylowOf_centralizer {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (centralizer (Z : Set G) ⊓ normalizer (S : Set G))) :
    S ≤ T₁ ∧ IsSylowOf 2 T₁ (centralizer (Z : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₁ := centralizer (Z : Set G) ⊓ normalizer (S : Set G) with hN₁
  have hSN₁ : S ≤ N₁ := le_inf H.SC le_normalizer
  have hST₁ : S ≤ T₁ := by
    obtain ⟨Q, hQ⟩ := hT₁.exists_sylow_eq_subgroupOf
    have : (S.subgroupOf N₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hSN₁).2 inf_le_right
    have hp : IsPGroup 2 (S.subgroupOf N₁) := H.isPGroup.comap_subtype
    have hle := hp.le_sylow_of_normal Q
    intro s hs
    have h1 : (⟨s, hSN₁ hs⟩ : N₁) ∈ (Q : Subgroup N₁) := hle (mem_subgroupOf.2 hs)
    rw [hQ] at h1
    exact mem_subgroupOf.1 h1
  have hT₁C : T₁ ≤ centralizer (Z : Set G) := hT₁.le.trans inf_le_left
  obtain ⟨Q, hQ⟩ := (hT₁.isPGroup.comap_subtype (K := centralizer (Z : Set G))).exists_le_sylow
  set T := (Q : Subgroup (centralizer (Z : Set G))).map (centralizer (Z : Set G)).subtype
    with hTdef
  have hT : IsSylowOf 2 T (centralizer (Z : Set G)) := ⟨Q, rfl⟩
  have hT₁T : T₁ ≤ T := fun x hx =>
    ⟨⟨x, hT₁C hx⟩, hQ (show (⟨x, hT₁C hx⟩ : centralizer (Z : Set G)) ∈
      T₁.comap (centralizer (Z : Set G)).subtype from hx), rfl⟩
  have hTN : T ⊓ N₁ = T₁ :=
    hT₁.eq_of_le (le_inf hT₁T hT₁.le) inf_le_right (hT.isPGroup.to_le inf_le_left)
  have hTT : T₁ = T := by
    by_contra hne
    have hlt : T₁.subgroupOf T < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hT₁T fun x hx => ?_)
      have h1 : (⟨x, hx⟩ : T) ∈ T₁.subgroupOf T := htop ▸ mem_top _
      exact mem_subgroupOf.1 h1
    have : Group.IsNilpotent ↥T := hT.isPGroup.isNilpotent
    obtain ⟨x, hxN, hxT₁⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥T) _ hlt)
    have hxNorm : (x : G) ∈ normalizer (T₁ : Set G) := by
      have h1 : x ∈ (normalizer (T₁ : Set G)).subgroupOf T := by
        rw [subgroupOf_normalizer_eq hT₁T]
        exact hxN
      exact mem_subgroupOf.1 h1
    have hxC : (x : G) ∈ centralizer (Z : Set G) := hT.le x.2
    have hconj : ∀ s ∈ S, (x : G)⁻¹ * s * x ∈ N₁ := fun s hs => by
      have h1 := (mem_normalizer_iff.1 (inv_mem hxNorm) s).1 (hST₁ hs)
      rw [inv_inv] at h1
      exact hT₁.le h1
    have hxS := H.conj_mem_of_conj_mem hxC hconj
    have hxNS : (x : G) ∈ normalizer (S : Set G) := by
      have h1 := mem_normalizer_of_conj_mem (Q := S) (g := (x : G)⁻¹) fun s hs => by
        rw [inv_inv]
        exact hxS s hs
      simpa using inv_mem h1
    have hxTN : (x : G) ∈ T ⊓ N₁ := ⟨x.2, hxC, hxNS⟩
    rw [hTN] at hxTN
    exact hxT₁ (mem_subgroupOf.2 hxTN)
  refine ⟨hST₁, ?_⟩
  rw [hTT]
  exact hT

theorem conj_mem_of_mem {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (centralizer (Z : Set G) ⊓ normalizer (S : Set G))) {s c : G}
    (hs : s ∈ S) (hc : c ∈ centralizer (Z : Set G)) (hcs : c⁻¹ * s * c ∈ T₁) :
    c⁻¹ * s * c ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CZ := centralizer (Z : Set G) with hCZdef
  set N₁ := CZ ⊓ normalizer (S : Set G) with hN₁def
  obtain ⟨hST₁, hT₁C⟩ := H.isSylowOf_centralizer hT₁
  have : (Z.subgroupOf CZ).Normal := Sec2.subgroupOf_centralizer_normal Z
  set π : ↥CZ →* CZ ⧸ Z.subgroupOf CZ := QuotientGroup.mk' (Z.subgroupOf CZ) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z.subgroupOf CZ := QuotientGroup.ker_mk' _
  have hZS : Z ≤ S := H.ZS
  have hSCZ : S ≤ CZ := H.SC
  have hZCZ : Z ≤ CZ := hZS.trans hSCZ
  have hT₁N : T₁ ≤ N₁ := hT₁.le
  obtain ⟨Q₁, hQ₁⟩ := hT₁C.exists_sylow_eq_subgroupOf
  set PY : Sylow 2 (CZ ⧸ Z.subgroupOf CZ) := Q₁.mapSurjective hπs with hPYdef
  have hPY : (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) = (T₁.subgroupOf CZ).map π := by
    rw [hPYdef, Sylow.coe_mapSurjective, hQ₁]
  have hπeq : ∀ x y : ↥CZ, π x = π y → x⁻¹ * y ∈ Z.subgroupOf CZ := fun x y hxy => by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hπZ : ∀ x : ↥CZ, (x : G) ∈ Z → π x = 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
    exact hx
  have hπcomm : ∀ x y : ↥CZ,
      π x * π y = π y * π x ↔ (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ Z := by
    intro x y
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul, ← MonoidHom.mem_ker, hker, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  set V := (S.subgroupOf CZ).map π with hVdef
  have hmemS : ∀ x : ↥CZ, π x ∈ V → (x : G) ∈ S := by
    rintro x ⟨b, hb, hbe⟩
    have h1 : ((b⁻¹ * x : ↥CZ) : G) ∈ Z := mem_subgroupOf.mp (hπeq b x hbe)
    have hb : (b : G) ∈ S := mem_subgroupOf.mp hb
    have e : (x : G) = (b : G) * ((b⁻¹ * x : ↥CZ) : G) := by simp
    rw [e]
    exact S.mul_mem hb (hZS h1)
  have hmemT : ∀ x : ↥CZ, π x ∈ (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) → (x : G) ∈ T₁ := by
    intro x hx
    rw [hPY] at hx
    obtain ⟨t, ht, hte⟩ := hx
    have hz : ((t⁻¹ * x : ↥CZ) : G) ∈ Z := mem_subgroupOf.mp (hπeq t x hte)
    have ht : (t : G) ∈ T₁ := mem_subgroupOf.mp ht
    have e : (x : G) = (t : G) * ((t⁻¹ * x : ↥CZ) : G) := by simp
    rw [e]
    exact T₁.mul_mem ht (hST₁ (hZS hz))
  have hVP : V ≤ PY := by
    rw [hPY]
    exact map_mono fun a ha => hST₁ ha
  have hVel : IsElemAbelian 2 V := by
    refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact (hπcomm a b).2 (H.commZ _ (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hb))
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      refine hπZ _ ?_
      simpa [_root_.sq] using H.sqZ _ (mem_subgroupOf.mp ha)
  have hwc : ∀ h : CZ ⧸ Z.subgroupOf CZ, rightConjugate V h ≤ PY → rightConjugate V h = V := by
    intro h hhP
    obtain ⟨c', rfl⟩ := hπs h
    have hconj : ∀ s ∈ S, (c' : G)⁻¹ * s * c' ∈ N₁ := fun s hs => by
      have hsC := hSCZ hs
      have hsV : π ⟨s, hsC⟩ ∈ V := ⟨⟨s, hsC⟩, mem_subgroupOf.2 hs, rfl⟩
      have h1 : π (c'⁻¹ * ⟨s, hsC⟩ * c') ∈ (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := by
        rw [map_mul, map_mul, map_inv]
        exact hhP (GoldschmidtFour.conj_mem_rightConjugate hsV (π c'))
      exact hT₁N (hmemT _ h1)
    have hS' := H.conj_mem_of_conj_mem c'.2 hconj
    have hle : rightConjugate V (π c') ≤ V := by
      intro v hv
      rw [mem_rightConjugate_iff] at hv
      obtain ⟨b, hb, hbe⟩ := hv
      have e : v = π (c'⁻¹ * b * c') := by
        rw [map_mul, map_mul, map_inv, hbe]
        group
      rw [e]
      refine ⟨_, mem_subgroupOf.2 ?_, rfl⟩
      simpa using hS' b (mem_subgroupOf.1 hb)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  have hV : Hyp PY V := ⟨hVP, hVel, hwc⟩
  by_contra hcsS
  have hsC : s ∈ CZ := hSCZ hs
  set t₀ : ↥CZ := (⟨c, hc⟩ : ↥CZ)⁻¹ * ⟨s, hsC⟩ * ⟨c, hc⟩ with ht₀
  have ht₀G : (t₀ : G) = c⁻¹ * s * c := rfl
  have htP : π t₀ ∈ (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := by
    rw [hPY]
    exact ⟨t₀, mem_subgroupOf.2 hcs, rfl⟩
  have hsV : π ⟨s, hsC⟩ ∈ V := ⟨⟨s, hsC⟩, mem_subgroupOf.2 hs, rfl⟩
  have htV : ∃ k, π t₀ ∈ rightConjugate V k := ⟨π ⟨c, hc⟩, by
    rw [ht₀, map_mul, map_mul, map_inv]
    exact GoldschmidtFour.conj_mem_rightConjugate hsV _⟩
  obtain ⟨U, hUV, hCU, h, hUP, hcard⟩ := exists_card_commutator_le_of_centralizer hV htP htV
  set W := rightConjugate U h with hWdef
  have hWel : IsElemAbelian 2 W := Sec2.isElemAbelian_rightConjugate hVel hUV h
  set D := (W.comap π).map CZ.subtype with hDdef
  have hDN : D ≤ N₁ := by
    rintro _ ⟨a, ha, rfl⟩
    exact hT₁N (hmemT a (hUP ha))
  have hDel : ∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha2 : π a ^ 2 = 1 := hWel.2 _ ha
    have hab : π a * π b = π b * π a := GoldschmidtFour.comm_of_mem hWel.1 ha hb
    constructor
    · have h1 : a * a ∈ Z.subgroupOf CZ := by
        rw [← hker, MonoidHom.mem_ker, map_mul, ← _root_.sq]
        exact ha2
      exact hZS (mem_subgroupOf.mp h1)
    · exact hZS ((hπcomm a b).1 hab)
  have hDrel : (D ⊓ S).relIndex D = V.relIndex W := Sec2.relIndex_preimage_eq π hπs hker hZS hSCZ W
  have ht₀N : (t₀ : G) ∈ N₁ := hT₁N hcs
  have ht₀sq : (t₀ : G) * t₀ ∈ S := by
    rw [ht₀G]
    have hss := H.sqZ s hs
    have h2 : s * s * c = c * (s * s) := (mem_centralizer_iff.1 hc) _ hss
    have e : c⁻¹ * s * c * (c⁻¹ * s * c) = s * s := by
      calc c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s * c) := by group
        _ = c⁻¹ * (c * (s * s)) := by rw [h2]
        _ = s * s := by group
    rw [e]
    exact hZS hss
  obtain ⟨ha1, ha2⟩ := H.modA _ ht₀N hcsS ht₀sq
  have hcomm16 : 16 ≤ Nat.card (⁅V, zpowers (π t₀)⁆ : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := by
    have h1 : Nat.card (⁅S, zpowers (t₀ : G)⁆ ⊔ Z : Subgroup G) =
        Nat.card Z * Nat.card (⁅V, zpowers (π t₀)⁆ : Subgroup (CZ ⧸ Z.subgroupOf CZ)) :=
      Sec2.card_commutator_sup_eq hZCZ π hker hSCZ t₀.2
    rw [h1, H.cardZ, show (2 : ℕ) ^ 6 = 64 by norm_num] at ha1
    omega
  have hCV : Nat.card ↥(centralizer ({π t₀} : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V) = 256 := by
    have h1 : Nat.card {s : ↥S // π (Subgroup.inclusion hSCZ s) ∈
        centralizer ({π t₀} : Set (CZ ⧸ Z.subgroupOf CZ))} =
        Nat.card Z * Nat.card ↥(centralizer ({π t₀} : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V) :=
      card_subtype_mem_eq hZS hSCZ _
    have h2 : Nat.card {s : ↥S // π (Subgroup.inclusion hSCZ s) ∈
        centralizer ({π t₀} : Set (CZ ⧸ Z.subgroupOf CZ))} =
        Nat.card {s : ↥S // (s : G) * t₀ * (s : G)⁻¹ * (t₀ : G)⁻¹ ∈ Z} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [mem_centralizer_singleton_iff, hπcomm]
      rfl
    rw [h2, ha2, H.cardZ, show (2 : ℕ) ^ 10 = 1024 by norm_num] at h1
    omega
  have hrel16 : V.relIndex W = 16 := by
    refine le_antisymm ?_ (hcomm16.trans hcard)
    rw [← hDrel]
    exact H.modB D hDN hDel
  have hc16 := H.modC D hDN hDel (hDrel.trans hrel16)
  have hCW : Nat.card ↥(centralizer (W : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V) ≤ 4 := by
    have h1 : Nat.card {s : ↥S // π (Subgroup.inclusion hSCZ s) ∈
        centralizer (W : Set (CZ ⧸ Z.subgroupOf CZ))} =
        Nat.card Z * Nat.card ↥(centralizer (W : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V) :=
      card_subtype_mem_eq hZS hSCZ _
    have h2 : Nat.card {s : ↥S // π (Subgroup.inclusion hSCZ s) ∈
        centralizer (W : Set (CZ ⧸ Z.subgroupOf CZ))} =
        Nat.card {s : ↥S // ∀ d ∈ D, (s : G) * d * (s : G)⁻¹ * d⁻¹ ∈ Z} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [mem_centralizer_iff]
      constructor
      · rintro hx _ ⟨d, hd, rfl⟩
        have h3 := hx _ hd
        exact (hπcomm (Subgroup.inclusion hSCZ x) d).1 h3.symm
      · intro hx w hw
        obtain ⟨d, rfl⟩ := hπs w
        exact ((hπcomm (Subgroup.inclusion hSCZ x) d).2 (hx _ ⟨d, hw, rfl⟩)).symm
    rw [h2, H.cardZ] at h1
    omega
  have hWVle : V ⊓ W ≤ centralizer (W : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V := fun x hx =>
    ⟨mem_centralizer_iff.2 fun w hw => GoldschmidtFour.comm_of_mem hWel.1 hw hx.2, hx.1⟩
  have hWV : Nat.card ↥(V ⊓ W) ≤ 4 := (Subgroup.card_le_of_le hWVle).trans hCW
  have hWcard : Nat.card W ≤ 64 := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := W)
    rw [hrel16] at h1
    omega
  have hUcard : Nat.card ↥(centralizer ({π t₀} : Set (CZ ⧸ Z.subgroupOf CZ)) ⊓ V) ≤
      Nat.card U :=
    Subgroup.card_le_of_le fun e he => hCU e he.2 (mem_centralizer_singleton_iff.1 he.1)
  have hWU : Nat.card W = Nat.card U := rightConjugate_card U h
  omega

end ClosedHyp

theorem exists_sylow_strongly_closed {S Z : Subgroup G} (H : ClosedHyp S Z) :
    ∃ T : Subgroup G, IsSylowOf 2 T (centralizer (Z : Set G)) ∧ S ≤ T ∧
      ∀ x ∈ S, ∀ h ∈ centralizer (Z : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁⟩ := exists_isSylowOf 2 (centralizer (Z : Set G) ⊓ normalizer (S : Set G))
  obtain ⟨hST₁, hT₁C⟩ := H.isSylowOf_centralizer hT₁
  exact ⟨T₁, hT₁C, hST₁, fun x hx h hh hxT => H.conj_mem_of_mem hT₁ hx hh hxT⟩

end Sec3Closed

end CFSG.ComponentClassification.AS81
