module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Subgroup CFSG CFSG.ABGLocalTools

theorem klein_conj_conj_eq_self {D : Type*} [Group D] (Q : Subgroup D) [IsElementaryAbelian 2 Q]
    (hQcard : Nat.card Q = 4) {x : D} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    {n : D} (hn : n ∈ normalizer (Q : Set D)) (hxn : n * x * n⁻¹ = x) :
    ∀ q ∈ Q, n * (n * q * n⁻¹) * n⁻¹ = q := by
  have hsq : ∀ q ∈ Q, q ^ 2 = 1 := fun q hq => elemPow_eq_one_of_isElementaryAbelian q hq
  have hθQ : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hn q).mp hq
  have hxsq : x ^ 2 = 1 := hsq x hxQ
  have hAQ : zpowers x ≤ Q := zpowers_le.2 hxQ
  have hA2 : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hxsq hx1
  have hrel : (zpowers x).relIndex Q = 2 := by
    have := Subgroup.relIndex_mul_card (zpowers x) Q
    rw [inf_eq_left.mpr hAQ, hA2, hQcard] at this
    omega
  have hfix : ∀ a ∈ zpowers x, n * a * n⁻¹ = a := by
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← conj_zpow, hxn]
  have hinj : ∀ u w : D, n * u * n⁻¹ = n * w * n⁻¹ → u = w := by
    intro u w h
    simpa using h
  intro q hq
  by_cases hqA : q ∈ zpowers x
  · rw [hfix q hqA, hfix q hqA]
  · set r := n * q * n⁻¹ with hr
    have hrQ : r ∈ Q := hθQ q hq
    have hrA : r ∉ zpowers x := by
      intro hrA
      apply hqA
      have := hfix r hrA
      have hqr : q = r := hinj q r (by rw [← hr]; exact this.symm)
      rw [hqr]; exact hrA
    have hidx : ((zpowers x).subgroupOf Q).index = 2 := hrel
    have hmem : (⟨q, hq⟩ : Q)⁻¹ * ⟨r, hrQ⟩ ∈ (zpowers x).subgroupOf Q := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp [Subgroup.mem_subgroupOf, hqA, hrA]
    have hmem' : q⁻¹ * r ∈ zpowers x := by
      simpa [Subgroup.mem_subgroupOf] using hmem
    set a := q⁻¹ * r with ha
    have haQ : a ∈ Q := hAQ hmem'
    have ha2 : a ^ 2 = 1 := hsq a haQ
    have hra : r = q * a := by rw [ha]; group
    calc n * r * n⁻¹ = n * (q * a) * n⁻¹ := by rw [← hra]
      _ = (n * q * n⁻¹) * (n * a * n⁻¹) := by group
      _ = r * a := by rw [hfix a hmem']
      _ = q := by rw [hra, mul_assoc, ← sq, ha2, mul_one]

theorem eq_top_of_klein_sylow_central {D : Type*} [Group D] [Finite D] (Q : Subgroup D)
    [IsElementaryAbelian 2 Q] (hQp : IsPGroup 2 Q) (hQidx : ¬ 2 ∣ Q.index) (hQcard : Nat.card Q = 4)
    {x : D} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxc : x ∈ Subgroup.center D)
    (hO : pPrimeCore 2 D = ⊥) : Q = ⊤ := by
  let P : Sylow 2 D := hQp.toSylow hQidx
  have hNC : normalizer (P : Set D) ≤ centralizer (P : Set D) := by
    intro n hn
    have hn' : n ∈ normalizer (Q : Set D) := hn
    have hxn : n * x * n⁻¹ = x := by
      have := Subgroup.mem_center_iff.mp hxc n
      rw [mul_inv_eq_iff_eq_mul]; exact this
    have h2 : ∀ q ∈ Q, q * n ^ 2 = n ^ 2 * q := by
      intro q hq
      have h := klein_conj_conj_eq_self Q hQcard hxQ hx1 hn' hxn q hq
      calc q * n ^ 2 = n * (n * q * n⁻¹) * n⁻¹ * n ^ 2 := by rw [h]
        _ = n ^ 2 * q := by rw [sq]; group
    have hdvd : Q.relIndex (normalizer (Q : Set D)) ∣ Q.index :=
      Subgroup.relIndex_dvd_index_of_le le_normalizer
    have hodd : ¬ 2 ∣ Q.relIndex (normalizer (Q : Set D)) := fun h => hQidx (h.trans hdvd)
    have hpow : n ^ Q.relIndex (normalizer (Q : Set D)) ∈ Q := by
      have := Subgroup.pow_index_mem (Q.subgroupOf (normalizer (Q : Set D))) ⟨n, hn'⟩
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨j, hj⟩ : ∃ j, Q.relIndex (normalizer (Q : Set D)) = 2 * j + 1 :=
      ⟨Q.relIndex (normalizer (Q : Set D)) / 2, by omega⟩
    rw [hj] at hpow
    have hc : n ^ 2 ∈ centralizer (Q : Set D) := by
      rw [mem_centralizer_iff]; intro q hq; exact h2 q hq
    have hd : n ^ (2 * j + 1) ∈ centralizer (Q : Set D) := by
      rw [mem_centralizer_iff]; intro q hq; exact setLike_mul_comm hq hpow
    have hn_eq : n = ((n ^ 2) ^ j)⁻¹ * n ^ (2 * j + 1) := by
      rw [← pow_mul, pow_succ, inv_mul_cancel_left]
    have hn_mem : n ∈ centralizer (Q : Set D) := by
      rw [hn_eq]; exact mul_mem (inv_mem (pow_mem hc j)) hd
    exact hn_mem
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hK1 : (MonoidHom.transferSylow P hNC).ker = ⊥ := by
    refine pPrimeCore_eq_bot_iff.mp hO _ inferInstance ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hNC)
  have hcard := hcompl.card_mul_card
  rw [hK1, Subgroup.card_bot, one_mul] at hcard
  exact Subgroup.eq_top_of_card_eq Q hcard

theorem card_le_sq_card_fixed {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    [IsElementaryAbelian 2 V] {a : G} (ha : ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (ha2 : ∀ v ∈ V, a ^ 2 * v = v * a ^ 2) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hinv : ∀ v ∈ V, v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq v hv)
  let ψ : V →* V := MonoidHom.mk'
    (fun v => ⟨(v : G)⁻¹ * (a * v * a⁻¹), mul_mem (inv_mem v.2) (ha v v.2)⟩)
    (by
      intro v w
      apply Subtype.ext
      have hc : (w : G)⁻¹ * ((v : G)⁻¹ * (a * v * a⁻¹)) =
          ((v : G)⁻¹ * (a * v * a⁻¹)) * (w : G)⁻¹ :=
        setLike_mul_comm (inv_mem w.2) (mul_mem (inv_mem v.2) (ha v v.2))
      calc (((v * w : V) : G))⁻¹ * (a * ((v * w : V) : G) * a⁻¹)
          = (w : G)⁻¹ * ((v : G)⁻¹ * (a * v * a⁻¹)) * (a * w * a⁻¹) := by
            simp only [Subgroup.coe_mul]; group
        _ = ((v : G)⁻¹ * (a * v * a⁻¹)) * ((w : G)⁻¹ * (a * w * a⁻¹)) := by
            rw [hc]; group)
  have hψ : ∀ v : V, (ψ v : G) = (v : G)⁻¹ * (a * v * a⁻¹) := fun v => rfl
  have hker : ψ.ker = (V ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (v : G)⁻¹ * (a * v * a⁻¹) = 1 := by rw [← hψ, h]; rfl
      refine ⟨v.2, ?_⟩
      have : a * v * a⁻¹ = v := by
        rw [inv_mul_eq_one] at h'
        exact h'.symm
      calc (v : G) * a = a * v * a⁻¹ * a := by rw [this]
        _ = a * v := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hψ]
      have : a * v * a⁻¹ = v := by
        calc a * v * a⁻¹ = (v : G) * a * a⁻¹ := by rw [← h]
          _ = v := by group
      rw [this]
      simp
  have hrange : ψ.range ≤ (V ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(ψ v).2, ?_⟩
    have hu := hinv _ (ψ v).2
    rw [hψ] at hu ⊢
    have hθ : a * (a * (v : G) * a⁻¹) * a⁻¹ = v := by
      have h := ha2 v v.2
      rw [sq] at h
      calc a * (a * (v : G) * a⁻¹) * a⁻¹ = (a * a * v) * (a⁻¹ * a⁻¹) := by group
        _ = v * (a * a) * (a⁻¹ * a⁻¹) := by rw [h]
        _ = v := by group
    have h1 : a * ((v : G)⁻¹ * (a * v * a⁻¹)) * a⁻¹ = ((v : G)⁻¹ * (a * v * a⁻¹))⁻¹ := by
      calc a * ((v : G)⁻¹ * (a * v * a⁻¹)) * a⁻¹
          = (a * v * a⁻¹)⁻¹ * (a * (a * v * a⁻¹) * a⁻¹) := by group
        _ = (a * v * a⁻¹)⁻¹ * v := by rw [hθ]
        _ = _ := by group
    have h2 : a * ((v : G)⁻¹ * (a * v * a⁻¹)) * a⁻¹ = (v : G)⁻¹ * (a * v * a⁻¹) := by
      rw [h1, hu]
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = Nat.card V := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have h1 : Nat.card ψ.ker = Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 : Nat.card ψ.range ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) :=
    calc Nat.card ψ.range ≤ Nat.card ((V ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf V) :=
          Subgroup.card_le_of_le hrange
      _ = _ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcard, h1, sq]
  exact Nat.mul_le_mul_left _ h2

theorem card_mul_card_le_inf_mul_of_comm {G : Type*} [Group G] [Finite G] (A B V : Subgroup G)
    (hA : A ≤ V) (hB : B ≤ V) (_hV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card V := by
  have h1 := Subgroup.relIndex_mul_card A B
  have h2 := Subgroup.relIndex_mul_card A V
  rw [inf_eq_left.mpr hA] at h2
  have hV0 : 0 < Nat.card V := Nat.card_pos
  have h3 : A.relIndex B ≤ A.relIndex V :=
    Subgroup.relIndex_le_of_le_right hB (fun h0 => by rw [h0, zero_mul] at h2; omega)
  calc Nat.card A * Nat.card B = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by rw [h1]
    _ ≤ Nat.card A * (A.relIndex V * Nat.card ↥(A ⊓ B)) := by gcongr
    _ = (A.relIndex V * Nat.card A) * Nat.card ↥(A ⊓ B) := by ring
    _ = Nat.card ↥(A ⊓ B) * Nat.card V := by rw [h2, mul_comm]

theorem mem_of_isSylowOf_of_central_involution {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowOf 2 T ⊤) {x : X} (hx2 : x ^ 2 = 1) (hxc : x ∈ Subgroup.center X) : x ∈ T := by
  obtain ⟨-, hTp, hTidx⟩ := isSylowOf_iff.mp hT
  rw [Subgroup.relIndex_top_right] at hTidx
  have : (zpowers x).Normal := Subgroup.normal_of_le_center (zpowers_le.2 hxc)
  have : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  exact (IsElementaryAbelian.isPGroup 2 (zpowers x)).le_sylow_of_normal (hTp.toSylow hTidx)
    (mem_zpowers x)

theorem exists_mem_normalizer_not_mem_of_lt {G : Type*} [Group G] [Finite G] {P R : Subgroup G}
    (hR : IsPGroup 2 R) (hPR : P < R) : ∃ r ∈ R, r ∉ P ∧ r ∈ normalizer (P : Set G) := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent
  have hlt : P.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    have hRP : R ≤ P := fun r hr => by
      have : (⟨r, hr⟩ : R) ∈ P.subgroupOf R := by rw [h]; trivial
      exact this
    exact absurd hPR (not_lt_of_ge hRP)
  obtain ⟨⟨r, hrR⟩, hrN, hrP⟩ := Set.exists_of_ssubset (hnc _ hlt)
  refine ⟨r, hrR, hrP, ?_⟩
  have h2 : (⟨r, hrR⟩ : R) ∈ normalizer (P.subgroupOf R) := hrN
  rw [← Subgroup.subgroupOf_normalizer_eq hPR.le] at h2
  exact h2

theorem card_elemAb_le_pow_pRank {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 2 ^ CFSG.pRank 2 G := by
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 A)
  have hle : r ≤ CFSG.pRank 2 G := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, inferInstance, hr⟩
    rintro s ⟨B, -, hB⟩
    calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  rw [hr]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem pPrimeCore_map_le_of_normal {X : Type*} [Group X] [Finite X] (D : Subgroup X) [D.Normal] :
    (CFSG.pPrimeCore 2 D).map D.subtype ≤ CFSG.pPrimeCore 2 X := by
  have hMn : ((CFSG.pPrimeCore 2 D).map D.subtype).Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hm
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g d, ?_, ?_⟩
    · have h := Subgroup.characteristic_iff_comap_eq.mp
        (inferInstance : (CFSG.pPrimeCore 2 D).Characteristic) (MulAut.conjNormal g)
      have hd' : d ∈ (CFSG.pPrimeCore 2 D).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [h]; exact hd
      exact hd'
    · exact MulAut.conjNormal_apply g d
  have hMcop : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 D).map D.subtype)) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact pPrimeCore_coprime_card
  exact le_sSup ⟨hMn, hMcop⟩

theorem isElementaryAbelian_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [IsElementaryAbelian 2 A] : IsElementaryAbelian 2 B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

theorem isElementaryAbelian_subgroupOf {G : Type*} [Group G] {Q D : Subgroup G} (hQD : Q ≤ D)
    [IsElementaryAbelian 2 Q] : IsElementaryAbelian 2 (Q.subgroupOf D) :=
  isElementaryAbelian_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQD).symm

end CFSG.GH74.GLS.C3.Layer2
