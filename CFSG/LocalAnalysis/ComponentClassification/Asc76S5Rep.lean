module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_pow_mem {H : Subgroup G} {x : G} {m n : ℕ} (hm : x ^ m ∈ H)
    (hn : x ^ n ∈ H) (hmn : Nat.Coprime m n) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at h
  have hx : x = (x ^ m) ^ (m.gcdA n) * (x ^ n) ^ (m.gcdB n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hx]
  exact H.mul_mem (H.zpow_mem hm _) (H.zpow_mem hn _)

theorem commute_of_mem_centralizer {A : Subgroup G} {a k : G} (ha : a ∈ A)
    (hk : k ∈ centralizer (A : Set G)) : Commute a k :=
  mem_centralizer_iff.mp hk a ha

theorem mem_normalizer_inf {X Y : Subgroup G} {a : G} (hX : a ∈ normalizer (X : Set G))
    (hY : a ∈ normalizer (Y : Set G)) : a ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_normalizer_iff.mp hX x).mp h1, (mem_normalizer_iff.mp hY x).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_normalizer_iff.mp hX x).mpr h1, (mem_normalizer_iff.mp hY x).mpr h2⟩

variable [Finite G]

theorem exists_mul_of_mem_sup_centralizer {A R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {t : G}
    (ht : t ∈ A ⊔ centralizer (A : Set G)) (htR : t ∈ normalizer (R : Set G)) {m : ℕ}
    (htm : t ^ 2 ^ m = 1) : ∃ a ∈ A, ∃ r ∈ R, t = a * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hKA : K ≤ normalizer (A : Set G) := centralizer_le_normalizer A
  have hmem : t ∈ ((A : Set G) * (K : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left A K hKA]
    exact ht
  obtain ⟨a, ha, k, hk, hak⟩ := hmem
  have hak' : a * k = t := hak
  have hcomm : Commute a k := commute_of_mem_centralizer ha hk
  have hRK : R ≤ K := hR.le
  have hkR : k ∈ normalizer (R : Set G) := by
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxK : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk (hRK hx)) (K.inv_mem hk)
    have h1 := (mem_normalizer_iff.mp htR x).mp hx
    have h2 : t * x * t⁻¹ = k * x * k⁻¹ := by
      rw [← hak']
      have hc : Commute a (k * x * k⁻¹) := commute_of_mem_centralizer ha hxK
      calc a * k * x * (a * k)⁻¹ = a * (k * x * k⁻¹) * a⁻¹ := by group
        _ = k * x * k⁻¹ := by rw [hc.eq]; group
    change k * x * k⁻¹ ∈ R
    rw [← h2]
    exact h1
  set Z := A ⊓ K with hZ
  have hkpow : k ^ 2 ^ m ∈ Z ⊔ R := by
    refine mem_sup_left ⟨?_, K.pow_mem hk _⟩
    have h := htm
    rw [← hak', hcomm.mul_pow] at h
    have : k ^ 2 ^ m = (a ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact A.inv_mem (A.pow_mem ha _)
  set H := zpowers k ⊔ R with hH
  have hHK : H ≤ K := sup_le ((zpowers_le).mpr hk) hRK
  have hHR : H ≤ normalizer (R : Set G) := sup_le ((zpowers_le).mpr hkR) le_normalizer
  have hRH : R ≤ H := le_sup_right
  have hn : (R.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hRH).mpr hHR
  have hRsyl : IsSylowOf 2 R H := hR.of_le hRH hHK
  have hodd : ¬ 2 ∣ R.relIndex H := (isSylowOf_iff.mp hRsyl).2.2
  have hkH : k ∈ H := mem_sup_left (mem_zpowers k)
  have hkd : k ^ R.relIndex H ∈ Z ⊔ R := by
    have h := Subgroup.pow_index_mem (R.subgroupOf H) (⟨k, hkH⟩ : H)
    have h' : k ^ (R.subgroupOf H).index ∈ R := by simpa using mem_subgroupOf.mp h
    exact mem_sup_right h'
  have hcop : Nat.Coprime (2 ^ m) (R.relIndex H) :=
    Nat.Coprime.pow_left m
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  have hkZR : k ∈ Z ⊔ R := mem_of_pow_mem_of_pow_mem hkpow hkd hcop
  have hRZ : R ≤ normalizer (Z : Set G) := fun r hr =>
    mem_normalizer_inf (hKA (hRK hr)) (le_normalizer (hRK hr))
  have hmem2 : k ∈ ((Z : Set G) * (R : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left Z R hRZ]
    exact hkZR
  obtain ⟨z, hz, r, hr, hzr⟩ := hmem2
  have hzr' : z * r = k := hzr
  refine ⟨a * z, A.mul_mem ha hz.1, r, hr, ?_⟩
  rw [← hak', ← hzr', mul_assoc]

omit [Finite G] in
theorem commutator_rightConjugate_ne_bot {A : Subgroup G} (hA : standardComponentIsStandard A)
    (g : G) : ⁅A, rightConjugate A g⁆ ≠ ⊥ :=
  hA.2.2.2.2 g⁻¹

theorem not_le_normalizer_rightConjugate {A T : Subgroup G} (hA : standardComponentIsStandard A)
    {g : G} (hg : g ∉ normalizer (A : Set G)) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) :
    ¬ A ≤ normalizer (rightConjugate A g : Set G) := by
  intro hAN
  have hq : Open.IsQuasisimple A := hA.1
  set K := centralizer (A : Set G) with hKdef
  set P := rightConjugate K g ⊓ normalizer (A : Set G) with hP
  have hKg : rightConjugate K g = centralizer (rightConjugate A g : Set G) :=
    AschbacherTheorem3.rightConjugate_centralizer A g
  have hAP : A ≤ normalizer (P : Set G) := by
    intro a ha
    have h1 : a ∈ normalizer (rightConjugate K g : Set G) := by
      rw [hKg]
      exact AschbacherTheorem3.normalizer_le_normalizer_centralizer _ (hAN ha)
    have h2 : a ∈ normalizer (normalizer (A : Set G) : Set G) :=
      le_normalizer (le_normalizer ha)
    exact mem_normalizer_inf h1 h2
  have hPA : P ≤ normalizer (A : Set G) := inf_le_right
  have hAPA : A ≤ normalizer ((P ⊓ A : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_inf (hAP ha) (le_normalizer ha)
  rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_right hAPA with hZ | hEq
  · have hc : ⁅P, A⁆ = ⊥ :=
      commutator_eq_bot_of_inf_le_centerOf hq hPA hAP (hZ.trans inf_le_right)
    have hPK : P ≤ K := (commutator_eq_bot_iff_le_centralizer).mp hc
    have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
    have hgK : g ∉ normalizer (K : Set G) := by rwa [normalizer_centralizer_eq hA]
    have hTKK : T ≤ K ⊓ rightConjugate K g := le_inf (hTK.trans hPK) (hTK.trans inf_le_left)
    exact hT1 (two_subgroup_of_odd_eq_bot T _ hT (hK.2 g hgK) hTKK)
  · have hAK : A ≤ centralizer (rightConjugate A g : Set G) := by
      rw [← hKg, ← hEq]
      exact inf_le_left.trans inf_le_left
    exact commutator_rightConjugate_ne_bot hA g ((commutator_eq_bot_iff_le_centralizer).mpr hAK)

theorem even_card_of_isPGroup {V : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    Even (Nat.card V) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV
  rcases n with _ | n
  · exact absurd (card_eq_one.mp (by simpa using hn)) hV1
  · rw [hn, pow_succ]
    exact even_two.mul_left _

theorem not_le_gammaOneOn {A U : Subgroup G} (hA : standardComponentIsStandard A) (g : G)
    (hU : U ≤ rightConjugate (centralizer (A : Set G)) g) (hUp : IsPGroup 2 U)
    (hnot : ¬ A ≤ normalizer (rightConjugate A g : Set G)) : ¬ A ≤ gammaOneOn U A := by
  intro hle
  apply hnot
  refine hle.trans (iSup_le fun V => iSup_le fun hVU => iSup_le fun hV1 => ?_)
  refine inf_le_right.trans ?_
  have hKg : TightlyEmbedded (rightConjugate (centralizer (A : Set G)) g) :=
    tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA) g
  have h1 := normalizer_le_normalizer_of_tightlyEmbedded hKg (hVU.trans hU)
    (even_card_of_isPGroup (hUp.to_le hVU) hV1)
  rw [← AschbacherTheorem3.rightConjugate_normalizer, normalizer_centralizer_eq hA,
    AschbacherTheorem3.rightConjugate_normalizer] at h1
  exact h1

theorem isSylowOf_of_le_centralizer {K R T : Subgroup G} (hK : TightlyEmbedded K) {g : G}
    (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (K : Set G)))
    (hR : IsSylowOf 2 R K) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (htR : R ≤ centralizer ({t} : Set G)) : IsSylowOf 2 T (rightConjugate K g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 : T ≠ ⊥ := fun h => ht1 (by rw [h] at ht; exact (mem_bot.mp ht))
  have htK : t ∈ rightConjugate K g := (hT.le ht).1
  have hzK : zpowers t ≤ rightConjugate K g := (zpowers_le).mpr htK
  have hzeven : Even (Nat.card (zpowers t)) := by
    refine even_card_of_isPGroup (hT.isPGroup.to_le ((zpowers_le).mpr ht)) ?_
    intro h
    exact ht1 ((zpowers_eq_bot).mp h)
  have htC : t ∈ centralizer (R : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.mp (htR hr)
  have hRz : R ≤ centralizer (zpowers t : Set G) :=
    le_centralizer_iff.mp ((zpowers_le).mpr htC)
  have hRN : R ≤ normalizer (rightConjugate K g : Set G) :=
    (hRz.trans (centralizer_le_normalizer _)).trans (normalizer_le_normalizer_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate hK g) hzK hzeven)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K ⊓ normalizer (rightConjugate K g : Set G))
  have hcard := card_eq_card_of_overlap hK hg hT hT1 hP
  have hRP : Nat.card R ≤ Nat.card P :=
    card_le_of_isSylowOf hP (le_inf hR.le hRN) hR.isPGroup
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (rightConjugate K g)
  have hTS : Nat.card T ≤ Nat.card S := card_le_of_isSylowOf hS (hT.le.trans inf_le_left)
    hT.isPGroup
  have hSR : Nat.card S = Nat.card R := by rw [hS.card_eq, hR.card_eq, rightConjugate_card]
  refine isSylowOf_of_card (hT.le.trans inf_le_left) ?_
  rw [← hS.card_eq]
  omega
