module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

theorem sq_mem_of_four {u v r : G} (hu2 : u * u = 1) (hv2 : v * v = 1) (hvu : v * u = u * v)
    (c1 : r * (u * r * u⁻¹) = u * r * u⁻¹ * r)
    (c2 : r * (u * v * r * (u * v)⁻¹) = u * v * r * (u * v)⁻¹ * r)
    (c3 : r * (v * r * v⁻¹) = v * r * v⁻¹ * r) {K : Subgroup G}
    (hu : centralizer ({u} : Set G) ≤ K) (hv : centralizer ({v} : Set G) ≤ K)
    (huv : centralizer ({u * v} : Set G) ≤ K) : r ^ 2 ∈ K := by
  set ru := u * r * u⁻¹ with hru
  set rv := v * r * v⁻¹ with hrv
  set ruv := (u * v) * r * (u * v)⁻¹ with hruv
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hvu]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have c3' : ru * ruv = ruv * ru := by
    have e1 : ru * ruv = u * (r * rv) * u⁻¹ := by rw [hru, hruv, hrv]; group
    have e2 : ruv * ru = u * (rv * r) * u⁻¹ := by rw [hru, hruv, hrv]; group
    rw [e1, e2, c3]
  have hcomm_of : ∀ w x : G, w * x * w⁻¹ = x → x ∈ centralizer ({w} : Set G) := fun w x h => by
    rw [mem_centralizer_singleton_iff]
    calc x * w = w * x * w⁻¹ * w := by rw [h]
      _ = w * x := by group
  have h1 : r * ru ∈ K := by
    refine hu (hcomm_of u _ ?_)
    calc u * (r * ru) * u⁻¹ = ru * ((u * u) * r * (u * u)⁻¹) := by rw [hru]; group
      _ = r * ru := by rw [hu2, one_mul, inv_one, mul_one, c1]
  have h2 : ru⁻¹ * ruv⁻¹ ∈ K := by
    refine hv (hcomm_of v _ ?_)
    have ev1 : v * ru * v⁻¹ = ruv := by
      rw [hru, hruv]
      calc v * (u * r * u⁻¹) * v⁻¹ = (v * u) * r * (v * u)⁻¹ := by group
        _ = (u * v) * r * (u * v)⁻¹ := by rw [hvu]
    have ev2 : v * ruv * v⁻¹ = ru := by
      rw [hru, hruv]
      calc v * ((u * v) * r * (u * v)⁻¹) * v⁻¹ = (v * u * v) * r * (v * u * v)⁻¹ := by group
        _ = (u * v * v) * r * (u * v * v)⁻¹ := by rw [hvu]
        _ = u * r * u⁻¹ := by rw [mul_assoc u v v, hv2, mul_one]
    calc v * (ru⁻¹ * ruv⁻¹) * v⁻¹ = (v * ru * v⁻¹)⁻¹ * (v * ruv * v⁻¹)⁻¹ := by group
      _ = ruv⁻¹ * ru⁻¹ := by rw [ev1, ev2]
      _ = ru⁻¹ * ruv⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, c3']
  have h3 : r * ruv ∈ K := by
    refine huv (hcomm_of (u * v) _ ?_)
    calc (u * v) * (r * ruv) * (u * v)⁻¹ =
        ruv * (((u * v) * (u * v)) * r * ((u * v) * (u * v))⁻¹) := by rw [hruv]; group
      _ = r * ruv := by rw [huv2, one_mul, inv_one, mul_one, c2]
  have hprod : r ^ 2 = (r * ru) * (ru⁻¹ * ruv⁻¹) * (r * ruv) := by
    have hc : ruv⁻¹ * r = r * ruv⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← c2, mul_inv_cancel_right]
    calc r ^ 2 = r * (r * ruv⁻¹) * ruv := by rw [sq]; group
      _ = r * (ruv⁻¹ * r) * ruv := by rw [hc]
      _ = (r * ru) * (ru⁻¹ * ruv⁻¹) * (r * ruv) := by group
  rw [hprod]
  exact K.mul_mem (K.mul_mem h1 h2) h3

theorem exists_two_ne_one {T : Subgroup G} (hT : 3 ≤ Nat.card T) :
    ∃ u ∈ T, ∃ v ∈ T, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype T := Fintype.ofFinite T
  have h3 : 1 < (Finset.univ.erase (1 : T)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h3
  rw [Finset.mem_erase] at ha hb
  exact ⟨a, a.2, b, b.2, fun h => ha.1 (Subtype.ext h), fun h => hb.1 (Subtype.ext h),
    fun h => hab (Subtype.ext h)⟩

theorem inf_center_ne_bot_of_le [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := mem_inf.1 hy
  refine ne_bot_iff_exists_ne_one.mpr ⟨⟨y, mem_inf.2 ⟨mem_subgroupOf.1 hyU,
    mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun t ht => ?_⟩⟩⟩, fun h => hy1 ?_⟩
  · exact congrArg Subtype.val (mem_center_iff.1 hyZ ⟨t, ht⟩)
  · have h' : (y : G) = 1 := congrArg Subtype.val h
    have h'' : y = 1 := Subtype.ext h'
    exact Subtype.ext h''

theorem mem_normalizer_inf_centralizer {Q : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((Q ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxQ, hxC⟩
    refine ⟨(mem_normalizer_iff.1 hg x).1 hxQ, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    have := mem_centralizer_iff.1 hxC _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  · rintro ⟨hxQ, hxC⟩
    refine ⟨(mem_normalizer_iff.1 hg x).2 hxQ, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g * y * g⁻¹ ∈ Q := (mem_normalizer_iff.1 hg y).1 hy
    have := mem_centralizer_iff.1 hxC _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = x * y := by group

theorem exists_center_commute [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    {w : G} (hw : IsPGroup 2 (zpowers w)) (hwQ : w ∈ normalizer (Q : Set G)) :
    ∃ z ∈ Q, z ≠ 1 ∧ z ∈ centralizer (Q : Set G) ∧ z * w = w * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := Q ⊓ centralizer (Q : Set G) with hZ
  set P : Subgroup G := zpowers w ⊔ Q with hP
  have hPp : IsPGroup 2 P := hw.to_sup_of_normal_right' hQ (zpowers_le.mpr hwQ)
  have hZne : Z ≠ ⊥ := by
    have h := inf_center_ne_bot_of_le hQ le_rfl le_normalizer hQ1
    rwa [inf_eq_right.mpr inf_le_left] at h
  have hZP : Z ≤ P := inf_le_left.trans le_sup_right
  have hPN : P ≤ normalizer (Z : Set G) :=
    sup_le (zpowers_le.mpr (mem_normalizer_inf_centralizer hwQ))
      (fun q hq => mem_normalizer_inf_centralizer (le_normalizer hq))
  obtain ⟨⟨z, hz⟩, hz1⟩ := ne_bot_iff_exists_ne_one.mp (inf_center_ne_bot_of_le hPp hZP hPN hZne)
  obtain ⟨⟨hzQ, hzC⟩, -, hzP⟩ := mem_inf.mp hz
  refine ⟨z, hzQ, fun h => hz1 (Subtype.ext h), hzC, ?_⟩
  exact (mem_centralizer_iff.mp hzP w (mem_sup_left (mem_zpowers w))).symm

theorem exists_ne_one_mem_of_centralizers_le [Finite G] {Q W : Subgroup G} (hQ : IsPGroup 2 Q)
    {r : G} (hr : r ∈ Q) (hr2 : r ^ 2 ≠ 1) (hW4 : Nat.card W = 4) (hWe : IsElemAbelian 2 W)
    (hcomm : ∀ w ∈ W, w ∉ normalizer (Q : Set G) →
      ∀ a ∈ Q, ∀ b ∈ rightConjugate Q w, a * b = b * a)
    {K : Subgroup G} (hK : ∀ w ∈ W, w ≠ 1 → centralizer ({w} : Set G) ≤ K) :
    ∃ z ∈ Q, z ≠ 1 ∧ z ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw => by rw [← sq]; exact hWe.2 w hw
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => by
    have := hWe.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : W) ⟨y, hy⟩)
  have hWp : ∀ w ∈ W, w ≠ 1 → IsPGroup 2 (zpowers w) := fun w hw hw1 =>
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact hW2 w hw) hw1)
  by_cases hN : ∃ w ∈ W, w ≠ 1 ∧ w ∈ normalizer (Q : Set G)
  · obtain ⟨w, hwW, hw1, hwN⟩ := hN
    have hQ1 : Q ≠ ⊥ := fun h => hr2 (by
      have : r ∈ (⊥ : Subgroup G) := h ▸ hr
      rw [mem_bot] at this
      rw [this, one_pow])
    obtain ⟨z, hzQ, hz1, -, hzw⟩ := exists_center_commute hQ hQ1 (hWp w hwW hw1) hwN
    exact ⟨z, hzQ, hz1, hK w hwW hw1 (mem_centralizer_singleton_iff.mpr hzw)⟩
  · push Not at hN
    obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_ne_one (T := W) (by omega)
    have huvW : u * v ∈ W := W.mul_mem hu hv
    have huv1 : u * v ≠ 1 := fun h => huv (by
      rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left (hW2 v hv)])
    have hc : ∀ w ∈ W, w ≠ 1 → r * (w * r * w⁻¹) = w * r * w⁻¹ * r := by
      intro w hw hw1
      have hwN : w⁻¹ ∉ normalizer (Q : Set G) := fun h => hN w hw hw1 (by simpa using inv_mem h)
      apply hcomm w⁻¹ (W.inv_mem hw) hwN r hr
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hr
    exact ⟨r ^ 2, Q.pow_mem hr 2, hr2, sq_mem_of_four (hW2 u hu) (hW2 v hv) (hWc v hv u hu)
      (hc u hu hu1) (hc _ huvW huv1) (hc v hv hv1) (hK u hu hu1) (hK v hv hv1)
      (hK _ huvW huv1)⟩

end CFSG.ComponentClassification.Asc76.L26
