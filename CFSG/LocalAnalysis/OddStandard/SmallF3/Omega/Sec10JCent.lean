module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem inv_eq_of_orderOf_eq_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  haveI : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient (α := A) (d := 2) hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

private theorem exists_sq_eq_of_isCyclic_two [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    (hK2 : IsPGroup 2 K) {t : G} (htK : t ∈ K) (ht : orderOf t = 2)
    (hne : K ≠ zpowers t) : ∃ u ∈ K, u * u = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic K := hK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  have hle : zpowers t ≤ K := zpowers_le.2 htK
  have hn2 : 2 ≤ n := by
    by_contra hc
    push Not at hc
    have h2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
    have hd : Nat.card (zpowers t) ∣ Nat.card K := Subgroup.card_dvd_of_le hle
    rw [h2, hn] at hd
    interval_cases n
    · exact absurd hd (by norm_num)
    · exact hne (eq_of_le_of_card_ge hle (by rw [hn, h2]; norm_num)).symm
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  rw [hn] at hg₀
  refine ⟨((g₀ ^ 2 ^ (n - 2) : K) : G), (g₀ ^ 2 ^ (n - 2)).2, ?_⟩
  rw [← pow_two]
  have hval : (((g₀ ^ 2 ^ (n - 2) : K)) : G) ^ 2 = (((g₀ ^ 2 ^ (n - 1) : K)) : G) := by
    rw [← SubgroupClass.coe_pow, show (g₀ ^ 2 ^ (n - 2)) ^ 2 = g₀ ^ 2 ^ (n - 1) by
      rw [← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega]]
  rw [hval]
  have hord : orderOf (g₀ ^ 2 ^ (n - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hg₀]; exact Nat.pow_dvd_pow 2 (by omega)),
      hg₀, Nat.pow_div (by omega) (by norm_num), show n - (n - 1) = 1 by omega, pow_one]
  have huniq := inv_eq_of_orderOf_eq_two (A := K) (x := g₀ ^ 2 ^ (n - 1))
    (y := ⟨t, htK⟩) hord (by rw [Subgroup.orderOf_mk, ht])
  exact congrArg Subtype.val huniq

private theorem exists_mul_of_mem_sup_of_normalizes {V W : Subgroup G}
    (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ ∈ W) {x : G} (hx : x ∈ V ⊔ W) :
    ∃ v ∈ V, ∃ w ∈ W, x = v * w := by
  let D : Subgroup G :=
    { carrier := {x | ∃ v ∈ V, ∃ w ∈ W, x = v * w}
      one_mem' := ⟨1, V.one_mem, 1, W.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨v1, hv1, w1, hw1, rfl⟩ ⟨v2, hv2, w2, hw2, rfl⟩
        refine ⟨v1 * v2, V.mul_mem hv1 hv2, (v2⁻¹ * w1 * v2) * w2,
          W.mul_mem (by simpa using hVW v2⁻¹ (V.inv_mem hv2) w1 hw1) hw2, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨v, hv, w, hw, rfl⟩
        refine ⟨v⁻¹, V.inv_mem hv, v * w⁻¹ * v⁻¹, hVW v hv w⁻¹ (W.inv_mem hw), ?_⟩
        group }
  have hle : V ⊔ W ≤ D :=
    sup_le (fun v hv => ⟨v, hv, 1, W.one_mem, by simp⟩)
      (fun w hw => ⟨1, V.one_mem, w, hw, by simp⟩)
  exact hle hx

private theorem isCyclic_of_isPGroup_le_centralizer [Finite G] (h102 : Asc82Lemma102)
    {t : G} {L : Subgroup G} (hset : Sec10Setting G t L) {X : Subgroup G}
    (hX : X ≤ centralizer (L : Set G)) (hX2 : IsPGroup 2 X) : IsCyclic ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX'2 : IsPGroup 2 (X.subgroupOf (centralizer (L : Set G))) :=
    hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm
  obtain ⟨Q, hQle⟩ := hX'2.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup (centralizer (L : Set G))) := h102 G t L hset Q
  haveI : IsCyclic ↥(Q : Subgroup (centralizer (L : Set G))) := hQcyc
  have hX'cyc : IsCyclic ↥(X.subgroupOf (centralizer (L : Set G))) :=
    Subgroup.isCyclic_of_le hQle
  haveI : IsCyclic ↥(X.subgroupOf (centralizer (L : Set G))) := hX'cyc
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX)
    (Subgroup.subgroupOfEquivOfLe hX).surjective

theorem sec10J_cent_eq [Finite G] (h102 : Asc82Lemma102) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {V : Subgroup G} (hVS : V ≤ S)
    (hzV : z ∈ V) (hV : IsElemAbelianMod z V) :
    centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) = zpowers t := by
  obtain ⟨hpsp, htC, htnotL, htS, hN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  have hWleS : secW t K1 K2 ≤ S := sec10J_W_le hP5 hb hctx
  have hUS : V ⊔ secW t K1 K2 ≤ S := sup_le hVS hWleS
  have hU2 : IsPGroup 2 (V ⊔ secW t K1 K2 : Subgroup G) := hctx.sylow.2.1.to_le hUS
  have htW : t ∈ secW t K1 K2 := by
    rw [secW]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htU : t ∈ V ⊔ secW t K1 K2 := Subgroup.mem_sup_right htW
  have htC' : t ∈ centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) := ⟨htC, htU⟩
  refine le_antisymm ?_ (zpowers_le.2 htC')
  by_contra hle
  have hCne : centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) ≠ zpowers t :=
    fun h => hle (le_of_eq h)
  have hC2 : IsPGroup 2 (centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) : Subgroup G) :=
    hU2.to_le inf_le_right
  have hccyc : IsCyclic (centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) : Subgroup G) :=
    isCyclic_of_isPGroup_le_centralizer h102 hctx.toSec10Z.toSec10Setting inf_le_left hC2
  obtain ⟨u, huC, hu2⟩ :=
    exists_sq_eq_of_isCyclic_two hccyc hC2 htC' hctx.involution hCne
  have huU : u ∈ V ⊔ secW t K1 K2 := huC.2
  obtain ⟨v, hvV, w, hwW, huvw⟩ :=
    exists_mul_of_mem_sup_of_normalizes
      (fun v hv w hw => sec10J_W_normal hP5 hb hctx v (hVS hv) w hw) huU
  obtain ⟨q, hqQ, hwq⟩ := sec10J_mem_W hP5 hb hctx w hwW
  have hvS : v ∈ S := hVS hvV
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (hctx.sylow.1 hvS)
  have hqS : q ∈ S := (sec10J_Q_le hP5 hb hctx hqQ).1
  have hqt : q * t = t * q := mem_centralizer_singleton_iff.mp (hctx.sylow.1 hqS)
  have htt : t * t = 1 := by rw [← sq, ← hctx.involution, pow_orderOf_eq_one]
  have h1 : t = (v * w) * (v * w) := by rw [← hu2, huvw]
  have hmain : (v * w) * (v * w) = (v * v) * ((v⁻¹ * q * v) * q) := by
    rcases hwq with hwq | hwq
    · rw [hwq]; group
    · rw [hwq]
      have hkey : (v⁻¹ * (q * t) * v) * (q * t) = (v⁻¹ * q * v) * q := by
        calc (v⁻¹ * (q * t) * v) * (q * t)
            = v⁻¹ * q * (t * v) * q * t := by group
          _ = v⁻¹ * q * (v * t) * q * t := by rw [← hvt]
          _ = v⁻¹ * q * v * (t * q) * t := by group
          _ = v⁻¹ * q * v * (q * t) * t := by rw [← hqt]
          _ = v⁻¹ * q * v * q * (t * t) := by group
          _ = v⁻¹ * q * v * q := by rw [htt, mul_one]
      calc (v * (q * t)) * (v * (q * t))
          = (v * v) * ((v⁻¹ * (q * t) * v) * (q * t)) := by group
        _ = (v * v) * ((v⁻¹ * q * v) * q) := by rw [hkey]
  have htform : t = (v * v) * ((v⁻¹ * q * v) * q) := h1.trans hmain
  have hzQ : z ∈ secQ K1 K2 := (sec10KS_Q_elem hP5 hC5 hpsp hctx).1
  have hzQle : zpowers z ≤ secQ K1 K2 := zpowers_le.2 hzQ
  have hvvQ : v * v ∈ secQ K1 K2 := hzQle (hV v hvV v hvV).2
  have hcQ : v⁻¹ * q * v ∈ secQ K1 K2 := by
    have := sec10J_Q_normal hP5 hb hctx v⁻¹ (S.inv_mem hvS) q hqQ
    simpa using this
  have htQ : t ∈ secQ K1 K2 := by
    rw [htform]
    exact (secQ K1 K2).mul_mem hvvQ ((secQ K1 K2).mul_mem hcQ hqQ)
  exact (sec10J_t_notin_Q hP5 hb hctx) htQ

end CFSG.OddStandard.SmallF3.Omega
