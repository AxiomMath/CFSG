module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoverExcl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightExclCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitary
public import CFSG.Assembly.LowTwoRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicBender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem isCyclic_of_twoPoint (hL : OneComponent Y e v L) (hc : BaseConfig Y e) {c : L}
    (hcZ : c ∈ Subgroup.center L) (hce : (c : X) * c = e) (g : L) (hg : g ∉ Y.subgroupOf L)
    (P : Subgroup L) (hP : IsPGroup 2 P)
    (hPB : ∀ p ∈ P, p ∈ Y.subgroupOf L ∧ g⁻¹ * p * g ∈ Y.subgroupOf L) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := P ⊔ Subgroup.center L with hR
  have hR2 : IsPGroup 2 R := hP.to_sup_of_normal_right (hL.center_isPGroup hc)
  have hgY : (g : X)⁻¹ ∉ Y := fun h =>
    hg (Subgroup.mem_subgroupOf.mpr (by simpa using Y.inv_mem h))
  have hRT : R ≤ (Y ⊓ Y.conjBy ((g : X)⁻¹)⁻¹).subgroupOf L := by
    refine sup_le (fun p hp => Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩) fun c' hc' =>
      Subgroup.mem_subgroupOf.mpr (hL.center_mem_inf_conj hc _ hc')
    · exact Subgroup.mem_subgroupOf.mp (hPB p hp).1
    · refine Subgroup.mem_map.mpr ⟨((g⁻¹ * p * g : L) : X),
        Subgroup.mem_subgroupOf.mp (hPB p hp).2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
  have hinv : ∀ a ∈ R, ∀ b ∈ R, orderOf a = 2 → orderOf b = 2 → a = b := by
    intro a ha b hb ha2 hb2
    apply Subtype.ext
    rw [hc.eq_of_mem_inf_conj hgY (Subgroup.mem_subgroupOf.mp (hRT ha))
        (by rw [Subgroup.orderOf_coe]; exact ha2),
      hc.eq_of_mem_inf_conj hgY (Subgroup.mem_subgroupOf.mp (hRT hb))
        (by rw [Subgroup.orderOf_coe]; exact hb2)]
  have hc4 : orderOf c = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact hc.orderOf_eq_four hce
  have := isCyclic_of_forall_eq_of_central hR2 hinv (Subgroup.mem_sup_right hcZ)
    (fun r _ => Subgroup.mem_center_iff.mp hcZ r) hc4
  exact Subgroup.isCyclic_of_le (le_sup_left : P ≤ R)

theorem false_of_mem_center_sq
    (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (IH : CanonicalBelow (Nat.card X)) {c : L} (hcZ : c ∈ Subgroup.center L)
    (hce : (c : X) * c = e) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := hL.perfect
  have hsimple := hL.simple
  have hnonab := hL.nonabelian
  have hZ2 := hL.center_isPGroup hc
  have hne := hL.center_ne_bot hc
  have hZc := hL.center_isCyclic
  set π := QuotientGroup.mk' (Subgroup.center L) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Y.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact hL.center_le_subgroupOf hc
  have hker2 : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hZ2
  obtain ⟨S, hSB, hSc⟩ := hL.exists_sylow_le hc
  let Ss : Sylow 2 (L ⧸ Subgroup.center L) := S.mapSurjective hπ
  have hSsB : (Ss : Subgroup (L ⧸ Subgroup.center L)) ≤ (Y.subgroupOf L).map π := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSB
  have hΓ2 : properTwoGenCoreGamma (Ss : Subgroup (L ⧸ Subgroup.center L)) 2 ≠ ⊤ := fun h =>
    CyclicCase.map_ne_top_of_ker_le _ hker hL.subgroupOf_ne_top (top_le_iff.mp
      (h ▸ CyclicCase.gamma_two_le_map_of_cyclic _ hπ hker hker2
        (hL.isCyclic_of_twoPoint hc hcZ hce) Ss hSsB))
  have hc4 : orderOf c = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact hc.orderOf_eq_four hce
  have hcS : c ∈ (S : Subgroup L) := hZ2.le_sylow_of_normal S hcZ
  have h2 : 2 ≤ CFSG.Open.twoRank (L ⧸ Subgroup.center L) :=
    CFSG.Assembly.LowTwoRank.two_le_twoRank _ hnonab (hL.even_card_quotient hc)
  have hne2 : CFSG.Open.twoRank (L ⧸ Subgroup.center L) ≠ 2 := fun h => by
    have heq := rankTwoCoverStatement L hperf hZ2 hne hZc hsimple h
    exact hSc (isCyclic_of_forall_eq_of_central S.isPGroup' (fun a _ b _ ha hb => heq a b ha hb)
      hcS (fun r _ => Subgroup.mem_center_iff.mp hcZ r) hc4)
  have h3 : 3 ≤ CFSG.Open.pRank 2 (Ss : Subgroup (L ⧸ Subgroup.center L)) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq]
    omega
  have hcc : c * c ≠ 1 := fun h => by
    have h2e := hc.order
    rw [← hce, show (c : X) * c = 1 from congrArg Subtype.val h, orderOf_one] at h2e
    exact absurd h2e (by decide)
  have hcccc : c * c * (c * c) = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hce, hc.mul_self, Subgroup.coe_one])
  have hu : ∀ s ∈ Subgroup.center L, s * s = 1 → s = 1 ∨ s = c * c := by
    intro s hs hss
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      apply Subtype.ext
      rw [hL.eq_of_mem_center hc hs (orderOf_eq_prime (by rw [pow_two]; exact hss) hs1),
        Subgroup.coe_mul, hce]
  rcases IH _ (hL.card_quotient_lt hc) hsimple hnonab Ss h3 hΓ2 with hΓ1 | hJ
  · have hB := CyclicCase.isBenderGroup_of_gamma_one_ne_top Ss h2 hΓ1
    rcases CoverExcl.bender_cover_quotient_of_isCyclic hperf hZ2 hZc hne hnonab hB with hL2 | hS
    · exact hne2 (CFSG.GH74.twoRank_eq_of_mulEquiv_psl2Model (by norm_num) hL2.some)
    · exact false_of_szModel_of_mem_center hperf hZ2 hcZ hcc hcccc hu hS.some
  · exact hne (center_eq_bot_of_quotient_jOne hperf hJ.some)

theorem center_card_eq_two
    (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (IH : CanonicalBelow (Nat.card X)) : Nat.card (Subgroup.center L) = 2 := by
  have hZ2 := hL.center_isPGroup hc
  have he : (⟨e, hL.mem⟩ : L) ≠ 1 := fun h => by
    have h2 := hc.order
    rw [show e = 1 from congrArg Subtype.val h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hmem : ∀ s : Subgroup.center L, s = 1 ∨ s = ⟨⟨e, hL.mem⟩, hL.mem_center hc⟩ := by
    intro s
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hZ2 s
    obtain _ | _ | n := n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      exact Or.inl hn
    · rw [zero_add, pow_one] at hn
      right
      apply Subtype.ext
      apply Subtype.ext
      exact hL.eq_of_mem_center hc s.2 (by rw [Subgroup.orderOf_coe]; exact hn)
    · exfalso
      set w : Subgroup.center L := s ^ 2 ^ n with hw
      have hw4 : orderOf w = 4 := by
        rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact pow_dvd_pow 2 (by omega)),
          hn, show n + 1 + 1 = n + 2 by ring, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
        norm_num
      have hww : orderOf (w * w) = 2 := by
        rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hw4]; norm_num), hw4]
      have hwe := hL.eq_of_mem_center hc (w * w).2 (by rw [Subgroup.orderOf_coe]; exact hww)
      exact hL.false_of_mem_center_sq hc IH (c := (w : L)) w.2 hwe
  obtain ⟨y, -, hyu⟩ : ∃ y : Subgroup.center L, y ≠ 1 ∧ ∀ y', y' ≠ 1 → y' = y :=
    ⟨⟨⟨e, hL.mem⟩, hL.mem_center hc⟩, fun h => he (congrArg Subtype.val h), fun y' hy' =>
      (hmem y').resolve_left hy'⟩
  refine (Nat.card_eq_two_iff' (1 : Subgroup.center L)).mpr ⟨y, ?_, fun y' hy' => hyu y' hy'⟩
  rintro rfl
  exact he (congrArg Subtype.val (hyu ⟨⟨e, hL.mem⟩, hL.mem_center hc⟩ fun h =>
    he (congrArg Subtype.val h)))

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
