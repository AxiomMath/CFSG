module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Big
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Normal
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u w : J}

theorem BadLift.false_of_rank_two
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (IH : CanonicalBelow (Nat.card J))
    (hrank : CFSG.Open.pRank 2 (quasiNormalizer u) = 2) (hne : quasiImage B u ≠ ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, -, -, L, -, -, -, hP⟩ := hu.exists_partC_of_ne_top h hz IH hne
  have hT2 : CFSG.Open.pRank 2 (partCSylow T) = 2 := by
    rw [sylow_image_two_rank_eq]
    exact hrank
  have hcyc := hP.isCyclic_right_of_pRank_le_two hT2.le
  obtain ⟨S, hS⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.sylow_inheritance_of_normalizer_le
    2 (quasiNormalizer u) T (hP.normalizer_le_normalizer_zpowers_of_isCyclic hcyc)
  exact hP.false_of_isCyclic_of_isSylow hcyc S hS.symm h.perfect

theorem BadLift.false_of_twoRank_eq_two
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (h2 : twoRank J = 2)
    (hne : quasiImage B u ≠ ⊤) : False := by
  have h1 := hu.toEscapingLift.two_le_pRank_quasiNormalizer h hz
  have h3 := CFSG.SectionRank.pRank_mono (p := 2) (by decide) (le_top : quasiNormalizer u ≤ ⊤)
  have h4 : CFSG.Open.pRank 2 (⊤ : Subgroup J) = 2 := h2
  exact hu.false_of_rank_two h hz IH (by omega) hne

theorem EscapingLift.badLift_of_mem_hull (hw : EscapingLift B z w) (h : Setting J Q B)
    (hz : FourGen Q z) {y : J}
    (hy : (y : J ⧸ Subgroup.center J) ∈
      localInvolutionPointHull (z : J ⧸ Subgroup.center J) (w : J ⧸ Subgroup.center J))
    (hyy : y * y = centralElt J) : BadLift B z w := by
  refine ⟨hw, fun hse => ?_⟩
  set L := localInvolutionPointHull (z : J ⧸ Subgroup.center J) (w : J ⧸ Subgroup.center J)
  have hzL : (z : J ⧸ Subgroup.center J) ∈ L :=
    distinguished_mem_localInvolutionPointHull hw.commute
  have hyZ : y ∉ Subgroup.center J := fun h1 =>
    h.centralElt_ne_one (by rw [← hyy]; exact h.mul_self_of_mem_center h1)
  have h1 : orderOf (⟨_, hzL⟩ : L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz.orderOf_mk
  have h2 : orderOf (⟨_, hy⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hyy, QuotientGroup.eq_one_iff]
      exact h.centralElt_mem_center
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hyZ
  obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Timmesfeld.Bridge.isConj_of_orderOf_eq_two hse h1 h2)
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc'
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (c : J ⧸ Subgroup.center J)
  rw [← hg, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc'
  have hζ : (g * z * g⁻¹)⁻¹ * y ∈ Subgroup.center J := QuotientGroup.eq.mp hc'
  have hy' : y = g * z * g⁻¹ * ((g * z * g⁻¹)⁻¹ * y) := by group
  apply h.centralElt_ne_one
  rw [← hyy, hy']
  set ζ := (g * z * g⁻¹)⁻¹ * y
  have hcomm : ζ * (g * z * g⁻¹) = (g * z * g⁻¹) * ζ :=
    (Subgroup.mem_center_iff.mp hζ (g * z * g⁻¹)).symm
  calc g * z * g⁻¹ * ζ * (g * z * g⁻¹ * ζ) = g * z * g⁻¹ * (ζ * (g * z * g⁻¹)) * ζ := by group
    _ = g * (z * z) * g⁻¹ * (ζ * ζ) := by rw [hcomm]; group
    _ = 1 := by rw [hz.mul_self, h.mul_self_of_mem_center hζ]; group

theorem Setting.mem_of_conj_mem_of_centralizer_le (h : Setting J Q B) (hz : FourGen Q z)
    (hw : w * w = centralElt J)
    (hC : ∀ x : J, Commute (x : J ⧸ Subgroup.center J) (w : J ⧸ Subgroup.center J) → x ∈ B)
    {g : J} (hg : g * w * g⁻¹ ∈ B) : g ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hww : (g * w * g⁻¹) * (g * w * g⁻¹) = centralElt J := by
    have := h.conj_mul_self hw g⁻¹
    simpa using this
  have hD : IsPGroup 2 (Subgroup.zpowers (g * w * g⁻¹)) :=
    isPGroup_zpowers_of_orderOf_eq_four (h.orderOf_eq_four hww)
  obtain ⟨b, hbB, hb⟩ := exists_conj_mem_sylow_of_le Q h.sylow_le
    (Subgroup.zpowers_le.mpr hg) hD
  have hS := hb _ (Subgroup.mem_zpowers _)
  have hkw : (b * g) * w * (b * g)⁻¹ ∈ (Q : Subgroup J) := by
    rw [show (b * g) * w * (b * g)⁻¹ = b * (g * w * g⁻¹) * b⁻¹ by group]
    exact hS
  have hc1 := hz.comm_mem_center _ hkw
  have hc2 : w * ((b * g)⁻¹ * z * (b * g)) * w⁻¹ * ((b * g)⁻¹ * z * (b * g))⁻¹ ∈
      Subgroup.center J := by
    have := (inferInstance : (Subgroup.center J).Normal).conj_mem _ hc1 (b * g)⁻¹
    rw [show (b * g)⁻¹ * ((b * g) * w * (b * g)⁻¹ * z * ((b * g) * w * (b * g)⁻¹)⁻¹ * z⁻¹) *
      (b * g)⁻¹⁻¹ = w * ((b * g)⁻¹ * z * (b * g)) * w⁻¹ * ((b * g)⁻¹ * z * (b * g))⁻¹ by group]
      at this
    exact this
  have hcomm : Commute (((b * g)⁻¹ * z * (b * g) : J) : J ⧸ Subgroup.center J)
      (w : J ⧸ Subgroup.center J) := ((commute_mk_iff _ _).mpr hc2).symm
  have hk : (b * g)⁻¹ ∈ B :=
    h.mem_of_conj_mem (hz.mem_of_setting h) hz.order hz.not_mem_center (by simpa using hC _ hcomm)
  have hbg : b * g ∈ B := by simpa using B.inv_mem hk
  simpa using B.mul_mem (B.inv_mem hbB) hbg

theorem Setting.exists_conj_mem_ne (h : Setting J Q B) {w : J} (hwQ : w ∈ (Q : Subgroup J))
    (hww : w * w ∈ Subgroup.center J) (hwZ : w ∉ Subgroup.center J)
    (hcomm : ∀ q ∈ (Q : Subgroup J), q * w * q⁻¹ * w⁻¹ ∈ Subgroup.center J) :
    ∃ k : J, k⁻¹ * w * k ∈ (Q : Subgroup J) ∧ k⁻¹ * w * k * w⁻¹ ∉ Subgroup.center J := by
  have hsimple := h.simple
  set π := QuotientGroup.mk' (Subgroup.center J) with hπ
  let S : Sylow 2 (J ⧸ Subgroup.center J) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (J ⧸ Subgroup.center J)) = (Q : Subgroup J).map π :=
    Sylow.coe_mapSurjective _ _
  have hnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hZ : Subgroup.center J = ⊤ := by
      rw [eq_top_iff, ← h.perfect.commutator_eq_top, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, ← commute_mk_iff]
      exact hall _ _
    exact hwZ (hZ ▸ Subgroup.mem_top w)
  have hw1 : π w ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hwZ
  have hwc : IsCentralInvolution (S : Subgroup (J ⧸ Subgroup.center J)) (π w) := by
    refine ⟨hS ▸ Subgroup.mem_map_of_mem π hwQ, orderOf_eq_prime ?_ hw1, ?_⟩
    · rw [pow_two, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hww
    · intro s hs
      rw [hS] at hs
      obtain ⟨q, hq, rfl⟩ := hs
      exact ((commute_mk_iff q w).mpr (hcomm q hq)).eq
  obtain ⟨g, hgS, hgne⟩ := centralInvolution_exists_conj_mem_ne hsimple hnonab hwc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have hπt : π (k⁻¹ * w * k) = (k : J ⧸ Subgroup.center J)⁻¹ * π w * k := by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine ⟨k, ?_, fun hZ => hgne ?_⟩
  · rw [hS] at hgS
    obtain ⟨q, hq, hqt⟩ := hgS
    have hζ : q⁻¹ * (k⁻¹ * w * k) ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff]
      change π (q⁻¹ * (k⁻¹ * w * k)) = 1
      rw [map_mul, map_inv, hπt, ← hqt, inv_mul_cancel]
    have h1 := (Q : Subgroup J).mul_mem hq (h.center_le_sylow hζ)
    rwa [mul_inv_cancel_left] at h1
  · rw [← hπt]
    have h2 : π (k⁻¹ * w * k * w⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hZ
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
