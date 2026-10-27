module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSection

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem conjQuotAction_coe_eq_one_iff {K : Subgroup G} [K.Normal]
    (hZ : center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥) (l : K) :
    conjQuotAction K (centralPreimage (pPrimeCore 2 K)) (l : G) = 1 ↔
      l ∈ centralPreimage (pPrimeCore 2 K) := by
  rw [conjQuotAction_coe]
  constructor
  · intro h
    have hc : (l : K ⧸ centralPreimage (pPrimeCore 2 K)) ∈
        center (K ⧸ centralPreimage (pPrimeCore 2 K)) := by
      rw [mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut (K ⧸ centralPreimage (pPrimeCore 2 K)) => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * (l : K ⧸ centralPreimage (pPrimeCore 2 K))
          = (l * g * (l : K ⧸ centralPreimage (pPrimeCore 2 K))⁻¹) * l := by rw [h1]
        _ = l * g := by group
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
    exact hc
  · intro h
    have h1 : (l : K ⧸ centralPreimage (pPrimeCore 2 K)) = 1 := (QuotientGroup.eq_one_iff l).mpr h
    rw [h1, map_one]

variable [Finite G]

theorem exists_mem_centralizer_conj {K : Subgroup G} [K.Normal]
    (hZ : center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥) {δ : G} (hδK : δ ∈ K)
    (hδ : δ ^ 2 = 1) {k : G} (hk : k ∈ K)
    (hkδ : conjQuotAction K (centralPreimage (pPrimeCore 2 K)) k *
        conjQuotAction K (centralPreimage (pPrimeCore 2 K)) δ =
      conjQuotAction K (centralPreimage (pPrimeCore 2 K)) δ *
        conjQuotAction K (centralPreimage (pPrimeCore 2 K)) k)
    {c : G} (hc : c ∈ K ⊓ centralizer ({δ} : Set G)) :
    ∃ c' ∈ K ⊓ centralizer ({δ} : Set G),
      conjQuotAction K (centralPreimage (pPrimeCore 2 K)) c' =
        conjQuotAction K (centralPreimage (pPrimeCore 2 K)) (k * c * k⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := conjQuotAction K (centralPreimage (pPrimeCore 2 K)) with hα
  obtain ⟨hcK, hcδ⟩ := mem_inf.mp hc
  set k' : K := ⟨k, hk⟩
  set δ' : K := ⟨δ, hδK⟩
  set c' : K := ⟨c, hcK⟩
  have hw : ⁅k', δ'⁆ ∈ centralPreimage (pPrimeCore 2 K) := by
    rw [← conjQuotAction_coe_eq_one_iff hZ]
    change α (k * δ * k⁻¹ * δ⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hkδ]
    group
  set q := QuotientGroup.mk' (pPrimeCore 2 K) with hq
  have hwc : q ⁅k', δ'⁆ ∈ center (K ⧸ pPrimeCore 2 K) := hw
  have hcδ' : c' * δ' = δ' * c' := Subtype.ext (mem_centralizer_singleton_iff.mp hcδ)
  have hx : q (k' * c' * k'⁻¹) ∈ centralizer ({q δ'} : Set (K ⧸ pPrimeCore 2 K)) := by
    rw [mem_centralizer_singleton_iff]
    obtain ⟨W, hWdef⟩ : ∃ W, W = q ⁅k', δ'⁆ := ⟨_, rfl⟩
    have hw' : ∀ g : K ⧸ pPrimeCore 2 K, g * W = W * g := by
      rw [hWdef]
      exact mem_center_iff.mp hwc
    have hWinv : ∀ g : K ⧸ pPrimeCore 2 K, g * W⁻¹ = W⁻¹ * g := by
      intro g
      calc g * W⁻¹ = W⁻¹ * (W * g) * W⁻¹ := by group
        _ = W⁻¹ * (g * W) * W⁻¹ := by rw [hw' g]
        _ = W⁻¹ * g := by group
    have hKD : q k' * q δ' = W * q δ' * q k' := by
      rw [hWdef]
      simp only [commutatorElement_def, map_mul, map_inv]
      group
    have hCD : q c' * q δ' = q δ' * q c' := by rw [← map_mul, ← map_mul, hcδ']
    have h3 : (q k')⁻¹ * q δ' = W⁻¹ * q δ' * (q k')⁻¹ := by
      have h4 : q δ' * (q k')⁻¹ = W * ((q k')⁻¹ * q δ') := by
        calc q δ' * (q k')⁻¹ = (q k')⁻¹ * (q k' * q δ') * (q k')⁻¹ := by group
          _ = (q k')⁻¹ * (W * q δ' * q k') * (q k')⁻¹ := by rw [hKD]
          _ = ((q k')⁻¹ * W) * q δ' := by group
          _ = (W * (q k')⁻¹) * q δ' := by rw [hw' (q k')⁻¹]
          _ = W * ((q k')⁻¹ * q δ') := by group
      calc (q k')⁻¹ * q δ' = W⁻¹ * (W * ((q k')⁻¹ * q δ')) := by group
        _ = W⁻¹ * (q δ' * (q k')⁻¹) := by rw [h4]
        _ = W⁻¹ * q δ' * (q k')⁻¹ := by group
    calc q (k' * c' * k'⁻¹) * q δ' = q k' * q c' * ((q k')⁻¹ * q δ') := by
          simp only [map_mul, map_inv]
          group
      _ = q k' * q c' * (W⁻¹ * q δ' * (q k')⁻¹) := by rw [h3]
      _ = q k' * (q c' * W⁻¹) * q δ' * (q k')⁻¹ := by group
      _ = q k' * (W⁻¹ * q c') * q δ' * (q k')⁻¹ := by rw [hWinv (q c')]
      _ = (q k' * W⁻¹) * q c' * q δ' * (q k')⁻¹ := by group
      _ = (W⁻¹ * q k') * q c' * q δ' * (q k')⁻¹ := by rw [hWinv (q k')]
      _ = W⁻¹ * q k' * (q c' * q δ') * (q k')⁻¹ := by group
      _ = W⁻¹ * q k' * (q δ' * q c') * (q k')⁻¹ := by rw [hCD]
      _ = W⁻¹ * (q k' * q δ') * q c' * (q k')⁻¹ := by group
      _ = W⁻¹ * (W * q δ' * q k') * q c' * (q k')⁻¹ := by rw [hKD]
      _ = q δ' * q (k' * c' * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
  have hodd : Odd (Nat.card (pPrimeCore 2 K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hδδ : δ' * δ' = 1 := Subtype.ext (by
    change δ * δ = 1
    rw [← pow_two, hδ])
  rw [← UnbalancedLayer.map_centralizer_eq hodd hδδ] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨(y : G), mem_inf.mpr ⟨y.2, ?_⟩, ?_⟩
  · exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
  · have hmem : y⁻¹ * (k' * c' * k'⁻¹) ∈ centralPreimage (pPrimeCore 2 K) := by
      apply le_centralPreimage
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      exact hyx
    have h1 := (conjQuotAction_coe_eq_one_iff hZ _).mpr hmem
    change α ((y : G)⁻¹ * (k * c * k⁻¹)) = 1 at h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

theorem isSubnormal_map_centralizer {K : Subgroup G} [K.Normal]
    (hZ : center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥) {δ : G} (hδK : δ ∈ K)
    (hδ : δ ^ 2 = 1) {N : Subgroup G} (hN : N ≤ K ⊓ centralizer ({δ} : Set G))
    (hNs : (N.subgroupOf (K ⊓ centralizer ({δ} : Set G))).IsSubnormal) :
    ((N.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict).subgroupOf
      (centralizer ({(conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict δ} :
        Set (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range))).IsSubnormal := by
  set α := conjQuotAction K (centralPreimage (pPrimeCore 2 K)) with hα
  set ρ := α.rangeRestrict with hρ
  set C := centralizer ({ρ δ} : Set α.range) with hC
  set D := (K ⊓ centralizer ({δ} : Set G)).map ρ with hD
  set I := K.map ρ with hI
  have hND : N.map ρ ≤ D := map_mono hN
  have hDI : D ≤ I ⊓ C := by
    rintro _ ⟨c, hc, rfl⟩
    refine mem_inf.mpr ⟨mem_map_of_mem ρ (mem_inf.mp hc).1, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2]
  have hIC : I ⊓ C ≤ C := inf_le_right
  have h1 : ((N.map ρ).subgroupOf D).IsSubnormal := by
    let g : ↥(K ⊓ centralizer ({δ} : Set G)) →* D := ρ.subgroupMap _
    have hg : Function.Surjective g := ρ.subgroupMap_surjective _
    have heq : (N.subgroupOf (K ⊓ centralizer ({δ} : Set G))).map g =
        (N.map ρ).subgroupOf D := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨⟨x, hN hx⟩, hx, Subtype.ext hxy⟩
    rw [← heq]
    exact hNs.map hg
  have h2 : (D.subgroupOf (I ⊓ C)).Normal := by
    rw [normal_subgroupOf_iff hDI]
    intro d b hd hb
    obtain ⟨c, hc, rfl⟩ := hd
    obtain ⟨hbI, hbC⟩ := mem_inf.mp hb
    obtain ⟨k, hk, rfl⟩ := hbI
    have hkδ : α k * α δ = α δ * α k :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hbC)
    obtain ⟨c', hc', hc'eq⟩ := exists_mem_centralizer_conj hZ hδK hδ hk hkδ hc
    refine ⟨c', hc', ?_⟩
    apply Subtype.ext
    change α c' = α k * α c * (α k)⁻¹
    rw [hc'eq, map_mul, map_mul, map_inv]
  have hIn : I.Normal := (inferInstance : K.Normal).map ρ α.rangeRestrict_surjective
  have h3 : ((I ⊓ C).subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff hIC]
    intro x c hx hc
    exact mem_inf.mpr ⟨hIn.conj_mem x (mem_inf.mp hx).1 c,
      mul_mem (mul_mem hc (mem_inf.mp hx).2) (inv_mem hc)⟩
  have hDC : (D.subgroupOf C).IsSubnormal :=
    (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hDI hIC h3.isSubnormal).mpr h2.isSubnormal
  exact (CatalogueBPrimeJoin.subgroupOf_isSubnormal_iff hND (hDI.trans hIC) hDC).mpr h1

end CFSG.ComponentClassification.TBLit
