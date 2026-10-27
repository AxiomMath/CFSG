module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightInduction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixTransport

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {X : Type} [Group X] [Finite X]

theorem exists_four_le {T : Subgroup X} (hm : 1 < pRank 2 T) :
    ∃ E : Subgroup X, E ≤ T ∧ (∀ e : E, e ^ 2 = 1) ∧ Nat.card E = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀T, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) T
  have hdvd : 2 ^ 2 ∣ Nat.card E₀ := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 hm
  obtain ⟨E, hEcard, -, hEE₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
  refine ⟨E, hEE₀.trans hE₀T, fun e => ?_, hEcard⟩
  exact Subtype.ext (by simpa using hE₀.2 e (hEE₀ e.2))

theorem oddCore_le_H {G₁ T Q H : Subgroup X} (hF : Frame G₁ T) (h43 : Hyp43 G₁ T Q H)
    (hm : 1 < pRank 2 T) : (CFSG.oddCore G₁).map G₁.subtype ≤ H := by
  set K := (CFSG.oddCore G₁).map G₁.subtype with hK
  obtain ⟨E, hET, hE2, hEcard⟩ := exists_four_le hm
  have hKodd : ¬ 2 ∣ Nat.card K := by
    rw [hK, Subgroup.card_map_of_injective G₁.subtype_injective]
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCore G₁)) ∘ even_iff_two_dvd.mpr
  have hEN : E ≤ Subgroup.normalizer (K : Set X) := by
    have : (CFSG.oddCore G₁).Characteristic := OddCore.characteristic G₁
    intro e he
    exact mem_normalizer_map_of_characteristic _ (hF.le_normalizer (hET he))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E K hE2 hEcard hKodd hEN
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he => ?_
  rintro x ⟨hxK, hxC⟩
  have hxG : x ∈ G₁ := (Subgroup.map_subtype_le _) hxK
  apply h43.mem_of_inf_ne_bot hxG
  intro hbot
  have he1 : (e : X) ≠ 1 := fun h1 => he (Subtype.ext h1)
  have hmem : (e : X) ∈ T ⊓ rightConjugate T x := by
    refine ⟨hET e.2, ?_⟩
    have hxe : x⁻¹ * e * x = e := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxC
      calc x⁻¹ * e * x = x⁻¹ * (e * x) := by group
        _ = x⁻¹ * (x * e) := by rw [this]
        _ = e := by group
    rw [← hxe]
    exact conj_mem_rightConjugate (hET e.2) x
  rw [hbot, Subgroup.mem_bot] at hmem
  exact he1 hmem

theorem SylowFrame.of_le {G T S G₁ : Subgroup X} (h : SylowFrame G T S) (hG₁ : G₁ ≤ G)
    (hTN : T ≤ Subgroup.normalizer (G₁ : Set X)) (hS : S ≤ G₁ ⊔ T) : SylowFrame G₁ T S := by
  have hF := h.toFrame
  have hinf : T ⊓ G₁ = ⊥ := by
    rw [eq_bot_iff, ← hF.inf_eq_bot]
    exact inf_le_inf_left T hG₁
  refine { toFrame := ⟨hTN, hinf, hF.isPGroup⟩, sylow := ?_, sylow_normalizer := ?_ }
  · exact h.sylow.of_le hS (sup_le_sup_right hG₁ T)
  · exact h.sylow_normalizer.of_le (inf_le_inf_right _ hS)
      (inf_le_inf_right _ (sup_le_sup_right hG₁ T))

theorem conclusion_mod_odd {N : ℕ} (IH : Theorem48Below N) {G₁ T S Q H : Subgroup X}
    (hcard : Nat.card (G₁ ⊔ T : Subgroup X) < N) (h : SylowFrame G₁ T S)
    (h43 : Hyp43 G₁ T Q H) (hidx : T.relIndex (S ⊓ H) ≤ Nat.card T) (hm : 1 < pRank 2 T) :
    G₁ ≤ Subgroup.normalizer ((relativeWeakClosure G₁ T S ⊔
      (CFSG.oddCore G₁).map G₁.subtype : Subgroup X) : Set X) ∨ IsMulCommutative S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := G₁ ⊔ T with hL
  have hGL : G₁ ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  have hSL : S ≤ L := h.sylow.le
  have hHL : H ≤ L := h43.le_sup
  set G' := G₁.subgroupOf L with hG'
  set T' := T.subgroupOf L with hT'def
  set S' := S.subgroupOf L with hS'def
  set Q' := Q.subgroupOf L with hQ'def
  set H' := H.subgroupOf L with hH'def
  have hS' : SylowFrame G' T' S' := h.subgroupOf
  have h43' : Hyp43 G' T' Q' H' := h43.subgroupOf
  have htop : G' ⊔ T' = ⊤ := sup_subgroupOf_eq_top G₁ T
  have hTm : T'.map L.subtype = T := by
    rw [hT'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hW'm : (relativeWeakClosure G' T' S').map L.subtype = relativeWeakClosure G₁ T S :=
    relativeWeakClosure_subgroupOf hGL hTL hSL
  set O' : Subgroup L := (CFSG.oddCore G').map G'.subtype with hO'
  have hO'G : O' ≤ G' := Subgroup.map_subtype_le _
  have hO'odd : Odd (Nat.card O') := by
    rw [hO', Subgroup.card_map_of_injective G'.subtype_injective]
    exact odd_card_oddCore _
  have hO'n : O'.Normal := by
    have : (CFSG.oddCore G').Characteristic := OddCore.characteristic _
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le (fun x hx => mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer hx))
      (fun x hx => mem_normalizer_map_of_characteristic _ (hS'.toFrame.le_normalizer hx))
  have hO'm : O'.map L.subtype = (CFSG.oddCore G₁).map G₁.subtype :=
    map_subtype_oddCore_subgroupOf hGL
  have hO'H : O' ≤ H' := by
    intro x hx
    rw [hH'def, Subgroup.mem_subgroupOf]
    apply oddCore_le_H h.toFrame h43 hm
    rw [← hO'm]
    exact Subgroup.mem_map_of_mem _ hx
  set π := QuotientGroup.mk' O' with hπ
  have hSb := hS'.map_odd htop O' hO'G hO'odd
  have h43b := Hyp43.map_odd hS'.toFrame h43' htop O' hO'G hO'odd
  have hinjT : ∀ z ∈ T', π z = 1 → z = 1 := fun z hz h1 =>
    mk_eq_one_of_odd hO'odd hS'.isPGroup hz h1
  have hinjS : ∀ z ∈ S', π z = 1 → z = 1 := fun z hz h1 =>
    mk_eq_one_of_odd hO'odd hS'.sylow.isPGroup hz h1
  have hOb : CFSG.oddCore (G'.map π) = ⊥ := Pre49.oddCore_quotient rfl
  have hmb : 1 < pRank 2 (T'.map π) := by
    rw [pRank_map_eq_of_ker π hinjT, ← pRank_map_eq L.subtype L.subtype_injective T', hTm]
    exact hm
  have hcardb : Nat.card (G'.map π ⊔ T'.map π : Subgroup (L ⧸ O')) < N := by
    calc Nat.card (G'.map π ⊔ T'.map π : Subgroup (L ⧸ O'))
        ≤ Nat.card (G' ⊔ T' : Subgroup L) := by
          rw [← Subgroup.map_sup]
          exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
      _ = Nat.card L := by rw [htop, Subgroup.card_top]
      _ < N := hcard
  have hidxb : (T'.map π).relIndex (S'.map π ⊓ H'.map π) ≤ Nat.card (T'.map π) := by
    have hle : S'.map π ⊓ H'.map π ≤ (S' ⊓ H').map π := by
      rintro _ ⟨⟨s, hs, rfl⟩, ⟨k, hk, hks⟩⟩
      refine ⟨s, ⟨hs, ?_⟩, rfl⟩
      have h1 : π (s * k⁻¹) = 1 := by rw [map_mul, map_inv, ← hks, mul_inv_cancel]
      have h2 : s * k⁻¹ ∈ O' := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have h3 := H'.mul_mem (hO'H h2) hk
      simpa using h3
    have hcardK : Nat.card (S'.map π ⊓ H'.map π : Subgroup (L ⧸ O')) ≤
        Nat.card (S ⊓ H : Subgroup X) := by
      calc Nat.card (S'.map π ⊓ H'.map π : Subgroup (L ⧸ O'))
          ≤ Nat.card ((S' ⊓ H').map π) := Subgroup.card_le_of_le hle
        _ ≤ Nat.card (S' ⊓ H' : Subgroup L) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
        _ = Nat.card (S ⊓ H : Subgroup X) := by
          have heq : S' ⊓ H' = (S ⊓ H).subgroupOf L := by
            ext z
            simp only [hS'def, hH'def, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
          rw [heq]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hSL)).toEquiv
    have hTK : T'.map π ≤ S'.map π ⊓ H'.map π :=
      le_inf (Subgroup.map_mono hS'.le) (Subgroup.map_mono (h43'.le_H))
    have hcT : Nat.card (T'.map π) = Nat.card T := by
      rw [card_map_eq_of_ker π hinjT, hT'def]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    have h1 := Subgroup.relIndex_mul_card (T'.map π) (S'.map π ⊓ H'.map π)
    rw [inf_eq_left.mpr hTK, hcT] at h1
    have h2 := Subgroup.relIndex_mul_card T (S ⊓ H)
    rw [inf_eq_left.mpr (le_inf h.le h43.le_H)] at h2
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [hcT]
    have h3 : (T'.map π).relIndex (S'.map π ⊓ H'.map π) * Nat.card T ≤
        Nat.card T * Nat.card T := by
      rw [h1]
      calc Nat.card (S'.map π ⊓ H'.map π : Subgroup (L ⧸ O')) ≤ Nat.card (S ⊓ H : Subgroup X) :=
            hcardK
        _ = T.relIndex (S ⊓ H) * Nat.card T := h2.symm
        _ ≤ Nat.card T * Nat.card T := Nat.mul_le_mul_right _ hidx
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hconcl := IH (L ⧸ O') (G'.map π) (T'.map π) (S'.map π) (Q'.map π) (H'.map π) hcardb hSb
    h43b hidxb hOb hmb
  have hkerπ : π.ker = O' := QuotientGroup.ker_mk' O'
  have hWmap := relativeWeakClosure_map_odd (G := G') (S := S') hS'.isPGroup
    hS'.sylow.isPGroup hO'G hO'odd
  rcases hconcl with hN | hpsl
  ·
    left
    intro x hx
    set x' : L := ⟨x, hGL hx⟩
    have h1 : π x' ∈ Subgroup.normalizer
        ((relativeWeakClosure G' T' S').map π : Set (L ⧸ O')) := by
      rw [← hWmap]
      exact hN (Subgroup.mem_map_of_mem π (hx : x' ∈ G'))
    have h2 : x' ∈ Subgroup.normalizer
        ((relativeWeakClosure G' T' S' ⊔ O' : Subgroup L) : Set L) := by
      have h3 : x' ∈ (Subgroup.normalizer
          ((relativeWeakClosure G' T' S').map π : Set (L ⧸ O'))).comap π := h1
      rwa [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O'),
        Subgroup.comap_map_eq, hkerπ] at h3
    have h4 := Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype h2)
    rwa [Subgroup.map_sup, hW'm, hO'm] at h4
  ·
    right
    have hab := isMulCommutative_of_psl_case hSb.toFrame hSb.sylow hpsl
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : (⟨a, hSL a.2⟩ : L) ∈ S' := a.2
    have hb : (⟨b, hSL b.2⟩ : L) ∈ S' := b.2
    have hc : π (⟨a, hSL a.2⟩ * ⟨b, hSL b.2⟩ * (⟨a, hSL a.2⟩ : L)⁻¹ *
        (⟨b, hSL b.2⟩ : L)⁻¹) = 1 := by
      have := hab.is_comm.comm ⟨π ⟨a, hSL a.2⟩, Subgroup.mem_map_of_mem π ha⟩
        ⟨π ⟨b, hSL b.2⟩, Subgroup.mem_map_of_mem π hb⟩
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h'
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h']
      group
    have hmem : (⟨a, hSL a.2⟩ * ⟨b, hSL b.2⟩ * (⟨a, hSL a.2⟩ : L)⁻¹ *
        (⟨b, hSL b.2⟩ : L)⁻¹ : L) ∈ S' :=
      S'.mul_mem (S'.mul_mem (S'.mul_mem ha hb) (S'.inv_mem ha)) (S'.inv_mem hb)
    have h1 := hinjS _ hmem hc
    have h2 : (a : X) * b * (a : X)⁻¹ * (b : X)⁻¹ = 1 := congrArg Subtype.val h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (a : X) * b = (a : X) * b * (a : X)⁻¹ * (b : X)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
