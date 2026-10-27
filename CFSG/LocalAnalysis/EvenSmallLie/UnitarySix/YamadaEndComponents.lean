module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set M := A ⊔ B with hM
  have hBM : B ≤ M := le_sup_right
  have hAM : A ≤ M := le_sup_left
  have hMN : M ≤ normalizer (B : Set G) := sup_le hAB le_normalizer
  have : (B.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hBM).mpr hMN
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf M) (B.subgroupOf M)
  have htop : A.subgroupOf M ⊔ B.subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup hAM hBM]
    exact subgroupOf_self M
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hAM] at h1
  have h2 : Nat.card M = Nat.card B * (B.subgroupOf M).index := by
    rw [← Subgroup.card_mul_index (B.subgroupOf M)]
    congr 1
    exact Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv
  have h3 := Subgroup.relIndex_mul_card B A
  rw [inf_comm] at h3
  rw [h2, h1, ← h3]
  ring

theorem card_sup_le [Finite G] {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf hAB
  have hpos : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
  calc Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card (A ⊔ B : Subgroup G) *
        Nat.card (A ⊓ B : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card A * Nat.card B := h

theorem card_sup_of_inf_eq_bot [Finite G] {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf hAB
  rwa [hinf, card_bot, mul_one] at h

theorem eq_one_of_pow_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) {x : G} (hx : x ∈ A)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (⟨x, hx⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card A) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hA)
  have h3 : orderOf x ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
  rw [Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

section CentralProduct

variable [Finite G] {M M' : Subgroup G}

omit [Finite G] in
theorem eq_of_mul_eq_mul (hc : ⁅M, M'⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G)))
    {y y' z z' : G} (hy : y ∈ M) (hy' : y' ∈ M) (hz : z ∈ M') (hz' : z' ∈ M')
    (h : y * z = y' * z') {k k' : ℕ} (hk : y ^ 2 ^ k = 1) (hk' : y' ^ 2 ^ k' = 1) :
    y = y' ∧ z = z' := by
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  set c := y⁻¹ * y' with hcdef
  have hc' : c = z * z'⁻¹ := by
    rw [hcdef]
    calc y⁻¹ * y' = y⁻¹ * (y' * z') * z'⁻¹ := by group
      _ = y⁻¹ * (y * z) * z'⁻¹ := by rw [h]
      _ = z * z'⁻¹ := by group
  have hcM : c ∈ M ⊓ M' := ⟨M.mul_mem (M.inv_mem hy) hy', hc' ▸ M'.mul_mem hz (M'.inv_mem hz')⟩
  have hyc : y * c = c * y := (mem_centralizer_iff.mp (hMC hy) c hcM.2).symm
  have hy'eq : y' = y * c := by rw [hcdef]; group
  have hcpow : c ^ 2 ^ (k + k') = 1 := by
    have h1 : y ^ 2 ^ (k + k') = 1 := by
      rw [pow_add, pow_mul, hk, one_pow]
    have h2 : y' ^ 2 ^ (k + k') = 1 := by
      rw [pow_add, mul_comm (2 ^ k), pow_mul, hk', one_pow]
    rw [hy'eq, (show Commute y c from hyc).mul_pow, h1, one_mul] at h2
    exact h2
  have hc1 := eq_one_of_pow_of_odd hodd hcM hcpow
  have hyy : y = y' := by rw [hy'eq, hc1, mul_one]
  refine ⟨hyy, ?_⟩
  rw [hyy] at h
  exact mul_left_cancel h

theorem inf_eq_bot_of_isPGroup (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G))) {A B : Subgroup G}
    (hA : A ≤ M) (hB : B ≤ M') (hA2 : IsPGroup 2 A) : A ⊓ B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (A ⊓ B : Subgroup G) := hA2.to_le inf_le_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hcop : Nat.Coprime (Nat.card (A ⊓ B : Subgroup G)) (Nat.card (M ⊓ M' : Subgroup G)) := by
    rw [hn]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  rwa [inf_of_le_left (le_inf (inf_le_left.trans hA) (inf_le_right.trans hB))] at this


omit [Finite G] in
theorem coe_sup_eq_mul (hc : ⁅M, M'⁆ = ⊥) {A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M') :
    (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) := by
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  refine coe_mul_of_left_le_normalizer_right A B ?_
  intro a ha
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro b hb
  exact (mem_centralizer_iff.mp (hMC (hA ha)) b (hB hb))

omit [Finite G] in
theorem sup_inf_sup (hc : ⁅M, M'⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G)))
    {A A' B B' : Subgroup G} (hA : A ≤ M) (hA' : A' ≤ M) (hB : B ≤ M') (hB' : B' ≤ M')
    (hA2 : IsPGroup 2 A) (hA'2 : IsPGroup 2 A') :
    (A ⊔ B) ⊓ (A' ⊔ B') = (A ⊓ A') ⊔ (B ⊓ B') := by
  refine le_antisymm ?_ (le_inf (sup_le_sup inf_le_left inf_le_left)
    (sup_le_sup inf_le_right inf_le_right))
  rintro x ⟨hx, hx'⟩
  have h1 : x ∈ (A : Set G) * (B : Set G) := coe_sup_eq_mul hc hA hB ▸ hx
  have h2 : x ∈ (A' : Set G) * (B' : Set G) := coe_sup_eq_mul hc hA' hB' ▸ hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  obtain ⟨a', ha', b', hb', hab⟩ := h2
  obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
  obtain ⟨k', hk'⟩ := hA'2 ⟨a', ha'⟩
  have e := eq_of_mul_eq_mul hc hodd (hA ha) (hA' ha') (hB hb) (hB' hb') hab.symm
    (k := k) (k' := k') (congrArg Subtype.val hk) (congrArg Subtype.val hk')
  refine mul_mem (mem_sup_left ⟨ha, e.1 ▸ ha'⟩) (mem_sup_right ⟨hb, e.2 ▸ hb'⟩)


theorem card_sup_of_le (hc : ⁅M, M'⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G)))
    {A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M') (hA2 : IsPGroup 2 A) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  refine card_sup_of_inf_eq_bot ?_ (inf_eq_bot_of_isPGroup hodd hA hB hA2)
  intro a ha
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro b hb
  exact mem_centralizer_iff.mp (hMC (hA ha)) b (hB hb)

theorem sylow_eq_sup (hc : ⁅M, M'⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G)))
    {Q : Subgroup G} (hQ : IsSylowOf 2 Q (M ⊔ M'))
    (hMn : M ⊔ M' ≤ normalizer (M : Set G)) (hM'n : M ⊔ M' ≤ normalizer (M' : Set G)) :
    Q = (Q ⊓ M) ⊔ (Q ⊓ M') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₁ : IsSylowOf 2 (Q ⊓ M) M := hQ.inf_of_le_normalizer le_sup_left hMn
  have h₂ : IsSylowOf 2 (Q ⊓ M') M' := hQ.inf_of_le_normalizer le_sup_right hM'n
  have hcard := card_sup_of_le hc hodd (inf_le_right : Q ⊓ M ≤ M) (inf_le_right : Q ⊓ M' ≤ M')
    h₁.isPGroup
  have hprod := card_sup_mul_card_inf (A := M) (B := M') (le_sup_left.trans hM'n)
  have hne : ∀ X : Subgroup G, Nat.card X ≠ 0 := fun X => Nat.card_pos.ne'
  have hv : (Nat.card (M ⊔ M' : Subgroup G)).factorization 2 =
      (Nat.card M).factorization 2 + (Nat.card M').factorization 2 := by
    have h : (Nat.card (M ⊔ M' : Subgroup G) * Nat.card (M ⊓ M' : Subgroup G)).factorization 2 =
        (Nat.card M * Nat.card M').factorization 2 := by rw [hprod]
    rw [Nat.factorization_mul (hne _) (hne _), Nat.factorization_mul (hne _) (hne _)] at h
    simp only [Finsupp.coe_add, Pi.add_apply] at h
    have h0 : (Nat.card (M ⊓ M' : Subgroup G)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => by
        rcases hodd with ⟨k, hk⟩
        omega)
    omega
  refine (eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
  rw [hcard, h₁.card_eq, h₂.card_eq, hQ.card_eq, ← pow_add, hv]

theorem card_inf_centralizer_eq (hc : ⁅M, M'⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G)))
    {t : G} (ht : t * t = 1) (hM' : M' = conjR M t) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (htT : t ∈ normalizer (T : Set G)) (hTeq : T = (T ⊓ M) ⊔ (T ⊓ M')) :
    Nat.card (T ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card (T ⊓ M : Subgroup G) ∧
      Nat.card T = Nat.card (T ⊓ M : Subgroup G) ^ 2 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hconjM : ∀ y ∈ M, t * y * t⁻¹ ∈ M' := fun y hy => by
    rw [hM', mem_conjR, hti]
    have : t * (t * y * t) * t = y := by
      rw [show t * (t * y * t) * t = (t * t) * y * (t * t) by group, ht, one_mul, mul_one]
    rw [this]
    exact hy
  have hconjM' : ∀ z ∈ M', t * z * t⁻¹ ∈ M := fun z hz => by
    rw [hM', mem_conjR] at hz
    exact hz
  have hconjT : ∀ x ∈ T, t * x * t⁻¹ ∈ T := fun x hx => (mem_normalizer_iff.mp htT x).mp hx
  have hcard' : Nat.card (T ⊓ M' : Subgroup G) = Nat.card (T ⊓ M : Subgroup G) := by
    have : T ⊓ M' = conjR (T ⊓ M) t := by
      rw [conjR_inf, conjR_eq_self (show t ∈ normalizer (T : Set G) from htT), hM']
    rw [this, card_conjR]
  have hTcard : Nat.card T = Nat.card (T ⊓ M : Subgroup G) * Nat.card (T ⊓ M' : Subgroup G) := by
    conv_lhs => rw [hTeq]
    exact card_sup_of_le hc hodd inf_le_right inf_le_right (hT2.to_le inf_le_left)
  have h2 : ∀ y ∈ T, ∃ k : ℕ, y ^ 2 ^ k = 1 := fun y hy => by
    obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hfix : ∀ y ∈ M, y * (t * y * t⁻¹) * t = t * (y * (t * y * t⁻¹)) := by
    intro y hy
    have hcomm : t * y * t⁻¹ * y = y * (t * y * t⁻¹) :=
      mem_centralizer_iff.mp (hMC hy) _ (hconjM _ hy)
    calc y * (t * y * t⁻¹) * t = (t * y * t⁻¹ * y) * t := by rw [hcomm]
      _ = t * (y * (t * y * t⁻¹)) := by rw [hti]; group
  have hmem : ∀ y : (T ⊓ M : Subgroup G),
      (y : G) * (t * y * t⁻¹) ∈ (T ⊓ centralizer ({t} : Set G) : Subgroup G) := fun y =>
    ⟨mul_mem y.2.1 (hconjT _ y.2.1), mem_centralizer_singleton_iff.mpr (hfix _ y.2.2)⟩
  set φ : (T ⊓ M : Subgroup G) → (T ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    fun y => ⟨(y : G) * (t * y * t⁻¹), hmem y⟩ with hφ
  have hinj : Function.Injective φ := by
    intro y y' hyy
    have h := congrArg Subtype.val hyy
    simp only [hφ] at h
    obtain ⟨k, hk⟩ := h2 _ y.2.1
    obtain ⟨k', hk'⟩ := h2 _ y'.2.1
    exact Subtype.ext (eq_of_mul_eq_mul hc hodd y.2.2 y'.2.2 (hconjM _ y.2.2) (hconjM _ y'.2.2) h
      hk hk').1
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hxT, hxC⟩
    have hx : x ∈ (↑(T ⊓ M ⊔ T ⊓ M') : Set G) := by rw [← hTeq]; exact hxT
    rw [coe_sup_eq_mul hc inf_le_right inf_le_right] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    have hfixx : t * (y * z) * t⁻¹ = y * z := by
      have := mem_centralizer_singleton_iff.mp hxC
      calc t * (y * z) * t⁻¹ = (y * z) * t * t⁻¹ := by rw [this]
        _ = y * z := by group
    have hyz : y * z = (t * z * t⁻¹) * (t * y * t⁻¹) := by
      rw [← hfixx]
      have hcomm := mem_centralizer_iff.mp (hMC (hconjM' z hz.2)) _ (hconjM y hy.2)
      calc t * (y * z) * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by group
        _ = (t * z * t⁻¹) * (t * y * t⁻¹) := hcomm
    obtain ⟨k, hk⟩ := h2 _ hy.1
    obtain ⟨k', hk'⟩ := h2 _ (hconjT _ hz.1)
    obtain ⟨-, hz'⟩ := eq_of_mul_eq_mul hc hodd hy.2 (hconjM' z hz.2) hz.2 (hconjM y hy.2) hyz hk
      hk'
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [hφ]
    rw [hz']
  have hbij : Nat.card (T ⊓ M : Subgroup G) =
      Nat.card (T ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  refine ⟨hbij.symm, ?_⟩
  rw [hTcard, hcard', sq]

end CentralProduct

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
