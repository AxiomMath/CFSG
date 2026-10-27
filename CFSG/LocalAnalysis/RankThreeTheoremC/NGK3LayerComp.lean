module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.ComponentClassification.Components
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X} {D : Subgroup X}

private theorem ngk_ne_one (h : NGKData X P z D) : z ≠ 1 := by
  intro h1
  have h3 := h.ord
  rw [h1, orderOf_one] at h3
  omega

private theorem ngk_pow_three (h : NGKData X P z D) : z ^ 3 = 1 := by
  rw [← h.ord]
  exact pow_orderOf_eq_one z

private theorem ngk_exists_sylow_inf (P : Sylow 3 X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    ∃ T : Sylow 3 K, (T : Subgroup K).map K.subtype = (P : Subgroup X) ⊓ K :=
  CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)

private theorem ngk_exists_inf_of_center_eq_bot (h : NGKData X P z D) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K = ⊥) :
    ∃ t ∈ (P : Subgroup X) ⊓ K, orderOf t = 3 := by
  have hdvd := CFSG.AGLEmbedding.prime_dvd_card_center_quotient_of_isComponentOf Nat.prime_three
    h.core hK
  have hK3 : 3 ∣ Nat.card K := by
    rw [hZ, ← Subgroup.index_eq_card, Subgroup.index_bot] at hdvd
    exact hdvd
  obtain ⟨T, hT⟩ := ngk_exists_sylow_inf P hK
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup K)) 3
    (T.dvd_card_of_dvd_card hK3)
  refine ⟨((t : K) : X), ?_, ?_⟩
  · rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype t.2
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]

omit [Finite X] in
private theorem ngk_center_map_conj_eq_bot (K : Subgroup X) (hZ : center K = ⊥) (g : X) :
    center (K.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨_, k, hk, rfl⟩ hc
  have hkc : (⟨k, hk⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k'
    have h1 := congrArg Subtype.val
      (mem_center_iff.1 hc ⟨_, mem_map_of_mem (MulAut.conj g).toMonoidHom k'.2⟩)
    have h2 : (MulAut.conj g).toMonoidHom ((k' : X) * k) =
        (MulAut.conj g).toMonoidHom (k * (k' : X)) := by
      rw [map_mul, map_mul]
      exact h1
    exact Subtype.ext ((MulAut.conj g).injective h2)
  rw [hZ, mem_bot] at hkc
  have hk1 : k = 1 := congrArg Subtype.val hkc
  subst hk1
  exact Subtype.ext (map_one _)

private theorem ngk_mem_layerCenter {K : Subgroup X} (hK : IsComponentOf K ⊤) {k : K}
    (hk : k ∈ center K) : (k : X) ∈ layerCenter X := by
  have hle : rankThreeLayer (⊤ : Subgroup X) ≤ centralizer ({(k : X)} : Set X) := by
    refine sSup_le fun L hL x hx => ?_
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    by_cases hLK : L = K
    · subst hLK
      exact (congrArg Subtype.val (mem_center_iff.1 hk ⟨x, hx⟩)).symm
    · exact commute_of_isComponentOf_ne hK hL (fun hKL => hLK hKL.symm) k k.2 x hx
  have hkE : (k : X) ∈ rankThreeLayer (⊤ : Subgroup X) :=
    le_sSup (show K ∈ {L : Subgroup X | IsComponentOf L ⊤} from hK) k.2
  refine ⟨⟨k, hkE⟩, mem_center_iff.2 fun g => ?_, rfl⟩
  apply Subtype.ext
  exact (mem_centralizer_iff.1 (hle g.2) k rfl).symm

theorem NGKData.no_centerless (h : NGKData X P z D) (hF : PlaneFacts (P : Subgroup X) D z) :
    ∀ K : Subgroup X, IsComponentOf K ⊤ → center K ≠ ⊥ := by
  intro K₀ hK₀ hZ₀
  have hfin : {K : Subgroup X | IsComponentOf K ⊤ ∧ center K = ⊥}.Finite := Set.toFinite _
  have hmem : ∀ {K : Subgroup X}, K ∈ hfin.toFinset ↔ IsComponentOf K ⊤ ∧ center K = ⊥ :=
    fun {K} => hfin.mem_toFinset
  set N₀ : Subgroup X := ⨆ K ∈ hfin.toFinset, K
  have hnorm : ∀ g : X, ∀ n ∈ N₀, g * n * g⁻¹ ∈ N₀ := by
    intro g
    have hle : N₀ ≤ N₀.comap (MulAut.conj g).toMonoidHom := by
      refine iSup₂_le fun K hK k hk => ?_
      obtain ⟨hKc, hKZ⟩ := hmem.1 hK
      have hKg : K.map (MulAut.conj g).toMonoidHom ∈ hfin.toFinset :=
        hmem.2 ⟨isComponentOf_map_conj hKc g, ngk_center_map_conj_eq_bot K hKZ g⟩
      exact le_iSup₂ (f := fun (K : Subgroup X) (_ : K ∈ hfin.toFinset) => K) _ hKg
        (mem_map_of_mem _ hk)
    exact fun n hn => hle hn
  have : N₀.Normal := ⟨fun n hn g => hnorm g n hn⟩
  have hPN : (P : Subgroup X) ≤ normalizer (((P : Subgroup X) ⊓ N₀ : Subgroup X) : Set X) :=
    (le_inf (le_normalizer (H := (P : Subgroup X)))
      (le_normalizer_of_normal (H := N₀) (K := (P : Subgroup X)))).trans
      inf_normalizer_le_normalizer_inf
  have hne : (P : Subgroup X) ⊓ N₀ ≠ ⊥ := by
    obtain ⟨t, htK, ht3⟩ := ngk_exists_inf_of_center_eq_bot h hK₀ hZ₀
    intro hbot
    have htN : t ∈ (P : Subgroup X) ⊓ N₀ :=
      ⟨htK.1, le_iSup₂ (f := fun (K : Subgroup X) (_ : K ∈ hfin.toFinset) => K) K₀
        (hmem.2 ⟨hK₀, hZ₀⟩) htK.2⟩
    rw [hbot, mem_bot] at htN
    rw [htN, orderOf_one] at ht3
    omega
  have hzN : z ∈ (P : Subgroup X) ⊓ N₀ := hF.z_mem _ inf_le_left hPN hne
  exact ngk_ne_one h (eq_one_of_mem_iSup_components hfin.toFinset
    (fun K hK => (hmem.1 hK).1) (fun K hK => (hmem.1 hK).2) z hzN.2
    fun K _ x _ => h.zc' x)

theorem NGKData.component_data (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) :
    z ∈ K ∧ (∀ k ∈ K, z * k = k * z) ∧
      (∀ k : K, k ∈ center K → (k : X) ∈ layerCenter X) ∧ IsCyclic (center K) := by
  have hp3 : IsPGroup 3 (center K) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf Nat.prime_three h.core hK
  have hnt : Nontrivial (center K) := (nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨n, hn, hcard⟩ := hp3.nontrivial_iff_card.1 hnt
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3
    (hcard ▸ dvd_pow_self 3 hn.ne')
  have hw₀K : ((w₀ : K) : X) ∈ K := (w₀ : K).2
  have hw₀3 : orderOf ((w₀ : K) : X) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw₀]
  have hw₀z : ((w₀ : K) : X) ∈ zpowers z :=
    hB _ (ngk_mem_layerCenter hK w₀.2) (by rw [← hw₀3]; exact pow_orderOf_eq_one _)
  have hzw : z ∈ zpowers ((w₀ : K) : X) := by
    have heq : zpowers ((w₀ : K) : X) = zpowers z :=
      eq_of_le_of_card_ge (zpowers_le.2 hw₀z) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, h.ord, hw₀3])
    rw [heq]
    exact mem_zpowers z
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hzw
  refine ⟨?_, ?_, fun k hk => ngk_mem_layerCenter hK hk, ?_⟩
  · rw [← hm]
    exact zpow_mem hw₀K m
  · intro k hk
    rw [← hm]
    exact (Commute.zpow_left (congrArg Subtype.val (mem_center_iff.1 w₀.2 ⟨k, hk⟩)).symm m).eq
  · by_contra hnc
    have h2 : 2 ≤ CFSG.Open.pRank 3 (center K) :=
      two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hp3 hnc
    obtain ⟨E, hEC, hE, hEcard⟩ := pRank_attained 3 (center K) (by omega)
    have h9 : 3 ^ 2 ≤ Nat.card E := hEcard ▸ Nat.pow_le_pow_right (by norm_num) h2
    have hEz : E.map K.subtype ≤ zpowers z := by
      rintro _ ⟨e, he, rfl⟩
      exact hB _ (ngk_mem_layerCenter hK (hEC he)) (by simpa using congrArg Subtype.val (hE.2 e he))
    have h3 : Nat.card (E.map K.subtype) ≤ 3 :=
      (card_le_of_le hEz).trans (by rw [Nat.card_zpowers, h.ord])
    rw [card_map_of_injective K.subtype_injective] at h3
    omega

theorem NGKData.not_isMulCommutative_inf (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) :
    ¬ IsMulCommutative ((P : Subgroup X) ⊓ K : Subgroup X) := by
  obtain ⟨hzK, hzc, -⟩ := h.component_data hB hK hZ
  obtain ⟨T, hT⟩ := ngk_exists_sylow_inf P hK
  have hperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hzcen : (⟨z, hzK⟩ : K) ∈ center K :=
    mem_center_iff.2 fun k => Subtype.ext (hzc k k.2).symm
  intro hcomm
  refine not_isMulCommutative_sylow_of_isPerfect hperf T hzcen
    (fun h1 => ngk_ne_one h (congrArg Subtype.val h1)) (Subtype.ext (ngk_pow_three h)) ?_
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  have ha : ((a : K) : X) ∈ (P : Subgroup X) ⊓ K := by
    rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype a.2
  have hb : ((b : K) : X) ∈ (P : Subgroup X) ⊓ K := by
    rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype b.2
  have hab := congrArg Subtype.val
    (mul_comm' (⟨_, ha⟩ : ↥((P : Subgroup X) ⊓ K)) ⟨_, hb⟩)
  exact Subtype.ext hab

theorem NGKData.exists_inf_order_three (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) :
    ∃ d ∈ (P : Subgroup X) ⊓ K, orderOf d = 3 ∧ d ∉ zpowers z := by
  obtain ⟨hzK, hzc, -⟩ := h.component_data hB hK hZ
  obtain ⟨T, hT⟩ := ngk_exists_sylow_inf P hK
  have hperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hzcen : (⟨z, hzK⟩ : K) ∈ center K :=
    mem_center_iff.2 fun k => Subtype.ext (hzc k k.2).symm
  have hnc : ¬ IsCyclic (T : Subgroup K) :=
    not_isCyclic_sylow_of_isPerfect hperf T hzcen
      (fun h1 => ngk_ne_one h (congrArg Subtype.val h1)) (Subtype.ext (ngk_pow_three h))
  have h2 : 2 ≤ CFSG.Open.pRank 3 (T : Subgroup K) :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) T.isPGroup' hnc
  obtain ⟨E, hET, hE, hEcard⟩ := pRank_attained 3 (T : Subgroup K) (by omega)
  have hbig : 3 < Nat.card E := by
    rw [hEcard]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (T : Subgroup K) := Nat.pow_le_pow_right (by norm_num) h2
  have hnle : ¬ E ≤ zpowers (⟨z, hzK⟩ : K) := fun hle =>
    absurd (Subgroup.card_le_of_le hle) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.ord]; omega)
  obtain ⟨d, hdE, hdz⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hd1 : d ≠ 1 := fun h1 => hdz (h1 ▸ one_mem _)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hE.2 d hdE) hd1
  refine ⟨(d : X), ?_, ?_, ?_⟩
  · rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype (hET hdE)
  · rw [Subgroup.orderOf_coe, hd3]
  · intro hd
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hd
    exact hdz (mem_zpowers_iff.2 ⟨m, Subtype.ext (by simpa using hm)⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
