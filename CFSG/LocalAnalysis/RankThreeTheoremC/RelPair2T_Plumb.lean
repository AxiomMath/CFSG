module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thg_isElemAbelian_subgroupOf {p : ℕ} {D H : Subgroup G} (hD : IsElemAbelian p D) :
    IsElemAbelian p (D.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hD H

theorem thg_card_le {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : CFSG.Open.pRank p H = 2)
    (E : Subgroup ↥H) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcardG : Nat.card (E.map H.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hk]
  have hk2 : k ≤ 2 := by
    have : k ≤ CFSG.Open.pRank p H := by
      refine le_csSup ⟨Nat.card G, ?_⟩
        ⟨E.map H.subtype, Subgroup.map_subtype_le E,
          CFSG.SectionRank.isElemAbelian_map hE H.subtype, hcardG⟩
      rintro r ⟨B, -, -, hB⟩
      calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card G := Subgroup.card_le_card_group B
    rwa [hH] at this
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

theorem thg_sylow {p : ℕ} (hp : p.Prime) {D H : Subgroup G} (hDH : D ≤ H)
    (hsyl : IsSylowOf p D (centralizer (D : Set G))) :
    IsSylowOf p (D.subgroupOf H) (centralizer ((D.subgroupOf H : Subgroup H) : Set H)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← isSylowOf_map_subtype_iff H]
  have hA : (D.subgroupOf H).map H.subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDH]
  have hB : (centralizer ((D.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      centralizer (D : Set G) ⊓ H := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, c.2⟩
      have hc' : c ∈ centralizer ((D.subgroupOf H : Subgroup H) : Set H) := hc
      show (c : G) ∈ centralizer (D : Set G)
      rw [mem_centralizer_iff] at hc' ⊢
      intro d hd
      exact congrArg Subtype.val (hc' ⟨d, hDH hd⟩ hd)
    · rintro ⟨hx, hxH⟩
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      have hx' : x ∈ centralizer (D : Set G) := hx
      show (⟨x, hxH⟩ : H) ∈ centralizer ((D.subgroupOf H : Subgroup H) : Set H)
      rw [mem_centralizer_iff]
      intro d hd
      exact Subtype.ext (mem_centralizer_iff.mp hx' d.1 hd)
  rw [hA, hB]
  exact hsyl.of_le (le_inf hsyl.le hDH) inf_le_left

omit [Finite G] in
theorem thg_join_le {D H : Subgroup G} :
    invariantTwoJoinIn D H ≤
      (invariantTwoJoinIn (D.subgroupOf H) (⊤ : Subgroup H)).map H.subtype := by
  refine invariantTwoJoinIn_le_of_forall fun X hXH hX2 hDX => ?_
  have hX' : X = (X.subgroupOf H).map H.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH]
  rw [hX']
  refine Subgroup.map_mono (le_invariantTwoJoinIn le_top hX2.comap_subtype ?_)
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  exact mem_normalizer_iff.mp (hDX hg) h.1

omit [Finite G] in
theorem thg_join {p : ℕ} {D H : Subgroup G} (hj : p ∣ Nat.card (invariantTwoJoinIn D H)) :
    p ∣ Nat.card (invariantTwoJoinIn (D.subgroupOf H) (⊤ : Subgroup H)) := by
  refine hj.trans ((Subgroup.card_dvd_of_le thg_join_le).trans ?_)
  rw [Subgroup.card_map_of_injective H.subtype_injective]

omit [Finite G] in
theorem thg_conj_centralizer {g d y : G} (hgd : g * d = d * g) (hy : y * d = d * y) :
    g * y * g⁻¹ * d = d * (g * y * g⁻¹) := by
  have h1 : g⁻¹ * d = d * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgd]
    group
  calc g * y * g⁻¹ * d = g * y * (g⁻¹ * d) := by group
    _ = g * y * (d * g⁻¹) := by rw [h1]
    _ = g * (y * d) * g⁻¹ := by group
    _ = g * (d * y) * g⁻¹ := by rw [hy]
    _ = (g * d) * y * g⁻¹ := by group
    _ = (d * g) * y * g⁻¹ := by rw [hgd]
    _ = d * (g * y * g⁻¹) := by group

omit [Finite G] in
theorem thg_mem_normalizer_map {H : Subgroup G} {W : Subgroup H} {g : H}
    (hg : g ∈ normalizer (W : Set H)) :
    (g : G) ∈ normalizer ((W.map H.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have hg' := mem_normalizer_iff.mp hg
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨g * w * g⁻¹, (hg' w).mp hw, by simp⟩
  · rintro ⟨w, hw, hwy⟩
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · exact (hg' (g⁻¹ * w * g)).mpr (by simpa [mul_assoc] using hw)
    · show ((g⁻¹ * w * g : H) : G) = y
      have h2 : (w : G) = (g : G) * y * (g : G)⁻¹ := hwy
      calc ((g⁻¹ * w * g : H) : G) = (g : G)⁻¹ * (w : G) * (g : G) := by simp
        _ = y := by rw [h2]; group

omit [Finite G] in
theorem thg_signalizer {p : ℕ} {D H : Subgroup G} (hDH : D ≤ H) {d : H} {K : Subgroup G}
    (hK2 : normalizer ((zpowers (d : G) : Subgroup G) : Set G) ≤ normalizer (K : Set G))
    (hK3 : p.Coprime (Nat.card K))
    (hK4 : ∀ Y : Subgroup G, Y ≤ normalizer ((zpowers (d : G) : Subgroup G) : Set G) →
      p.Coprime (Nat.card Y) → D ≤ normalizer (Y : Set G) → Y ≤ K) :
    ∃ O : Subgroup H, IsPSignalizer p (D.subgroupOf H) d O := by
  have hCN : centralizer ({(d : G)} : Set G) ≤
      normalizer ((zpowers (d : G) : Subgroup G) : Set G) :=
    centralizer_singleton_le_normalizer_zpowers _
  refine ⟨(K ⊓ centralizer ({(d : G)} : Set G)).subgroupOf H, ?_, ?_, ?_, ?_⟩
  · intro o ho
    have h1 : (o : G) ∈ centralizer ({(d : G)} : Set G) := ho.2
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp h1)
  · intro c hc
    have hcd : (c : G) * d = d * c :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    have hcG : (c : G) ∈ centralizer ({(d : G)} : Set G) := mem_centralizer_singleton_iff.mpr hcd
    have hKc := mem_normalizer_iff.mp (hK2 (hCN hcG))
    have hcd' : (c : G)⁻¹ * d = d * (c : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcd]
      group
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact ⟨(hKc (h : G)).mp hh.1,
        mem_centralizer_singleton_iff.mpr
          (thg_conj_centralizer hcd (mem_centralizer_singleton_iff.mp hh.2))⟩
    · intro hh
      refine ⟨(hKc (h : G)).mpr hh.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hy : ((c : G) * h * (c : G)⁻¹) * d = d * ((c : G) * h * (c : G)⁻¹) :=
        mem_centralizer_singleton_iff.mp hh.2
      have := thg_conj_centralizer hcd' hy
      have e : (c : G)⁻¹ * ((c : G) * h * (c : G)⁻¹) * (c : G) = h := by group
      simp only [inv_inv] at this
      rw [e] at this
      exact this
  · have hle : ((K ⊓ centralizer ({(d : G)} : Set G)).subgroupOf H).map H.subtype ≤ K := by
      rw [Subgroup.subgroupOf_map_subtype]
      intro x hx
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
    have := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at this
    exact Nat.Coprime.coprime_dvd_right this hK3
  · intro W hWC hWc hWN w hw
    have hW'C : W.map H.subtype ≤ centralizer ({(d : G)} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hWC hx))
    have hW'c : p.Coprime (Nat.card (W.map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hWc
    have hW'N : D ≤ normalizer ((W.map H.subtype : Subgroup G) : Set G) := fun g hg =>
      thg_mem_normalizer_map (hWN (show (⟨g, hDH hg⟩ : H) ∈ D.subgroupOf H from hg))
    have hW'K : W.map H.subtype ≤ K := hK4 _ (hW'C.trans hCN) hW'c hW'N
    exact ⟨hW'K ⟨w, hw, rfl⟩, hW'C ⟨w, hw, rfl⟩⟩

theorem IsOptimalRelPair.thompsonPreFrame {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : Setting G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hp : p ∈ rankThreeSigmaA G)
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) :
    ThompsonPreFrame p (primeComplementCore (G := H) p) (D.subgroupOf H) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  obtain ⟨hDab, z, hzD, hz1, hzc, -, hN₀M, -, -⟩ :=
    hd.ext.transitivity_data hS hD1 hp hd.not_le_normalizer hR h13
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  obtain ⟨hDe, hDc⟩ := hd.ext.isElemAbelian_of_isMulCommutative hprime hDab
  have hsylG := hd.ext.isSylowOf_centralizer hS hD1 hp hd.not_le_normalizer hDab hzD hz1 hzc hN₀M
  refine
    { prime := hprime
      odd := hodd
      coprime := primeComplementCore_coprime p
      max := fun N hN hc => normal_coprime_le_primeComplementCore p N hN hc
      elem := thg_isElemAbelian_subgroupOf hDe
      card := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv).trans hDc
      pCore_quot := by exact hfacts.pCore_quotient
      rank_le := thg_card_le hprime hfacts.pRank_eq
      sylow := thg_sylow hprime hDH hsylG
      signalizer := ?_
      join := thg_join hopt.pair.cand.not_coprime }
  intro d hdD hd1
  obtain ⟨K, -, hK2, hK3, hK4⟩ := hfacts.signalizer (d : G) hdD (fun h => hd1 (Subtype.ext h))
  exact thg_signalizer hDH hK2 hK3 hK4

end CFSG.LocalAnalysis.RankThreeTheoremC
