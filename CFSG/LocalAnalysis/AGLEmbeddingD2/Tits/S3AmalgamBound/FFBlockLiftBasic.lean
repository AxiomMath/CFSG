module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LieType.BorelTits.Basic

public section

set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G]

theorem not_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup 2 P) : ¬ p ∣ Nat.card P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
  exact hp2 this

theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : y ∈ Subgroup.normalizer (H₂ : Set G)) :
    y ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  have key : ∀ z : G, z ∈ Subgroup.normalizer (H₁ : Set G) → z ∈ Subgroup.normalizer (H₂ : Set G) →
      ∀ x ∈ ⁅H₁, H₂⁆, z * x * z⁻¹ ∈ ⁅H₁, H₂⁆ := by
    intro z hz₁ hz₂ x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have e : z * ⁅a, b⁆ * z⁻¹ = ⁅z * a * z⁻¹, z * b * z⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp hz₁ a).mp ha) ((Subgroup.mem_normalizer_iff.mp hz₂ b).mp hb)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
      rw [e]; exact (⁅H₁, H₂⁆).mul_mem hx hy
    | inv x _ hx =>
      have e : z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
      rw [e]; exact (⁅H₁, H₂⁆).inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key y h₁ h₂ x
  · intro hx
    have h₁' : y⁻¹ ∈ Subgroup.normalizer (H₁ : Set G) := inv_mem h₁
    have h₂' : y⁻¹ ∈ Subgroup.normalizer (H₂ : Set G) := inv_mem h₂
    have := key y⁻¹ h₁' h₂' _ hx
    simpa [mul_assoc] using this

theorem mem_normalizer_sup {S T : Subgroup G} {y : G}
    (hS : y ∈ Subgroup.normalizer (S : Set G)) (hT : y ∈ Subgroup.normalizer (T : Set G)) :
    y ∈ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) := by
  have key : ∀ z : G, z ∈ Subgroup.normalizer (S : Set G) → z ∈ Subgroup.normalizer (T : Set G) →
      ∀ x ∈ S ⊔ T, z * x * z⁻¹ ∈ S ⊔ T := by
    intro z hz₁ hz₂
    have h : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj z).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hz₁ a).mp ha)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hz₂ a).mp ha)
    intro x hx
    simpa [MulAut.conj_apply] using h hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key y hS hT x
  · intro hx
    have := key y⁻¹ (inv_mem hS) (inv_mem hT) _ hx
    simpa [mul_assoc] using this

section Coprime

variable [Finite G]

theorem commutator_le_blockU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y P A : Subgroup G}
    (hAY : A ≤ Y) (hA : IsPGroup p A) (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hYP : Y ≤ Subgroup.normalizer (P : Set G)) :
    ⁅P, A⁆ ≤ blockU Y := by
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hAY.trans hYP
  have h1 : ⁅P, A⁆ ≤ pCoreOf 2 Y := by
    have hle : ⁅P, A⁆ ≤ Y ⊓ P := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      refine ⟨?_, ?_⟩
      · have hxa : x * a * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hPY hx) a).mp (hAY ha)
        have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [e]; exact Y.mul_mem hxa (Y.inv_mem (hAY ha))
      · have h2 : a * x⁻¹ * a⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hAP ha) x⁻¹).mp (P.inv_mem hx)
        have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]; exact P.mul_mem hx h2
    refine hle.trans ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hP.to_le inf_le_right)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hYP hg⟩
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A P hA
    (not_dvd_card_of_isPGroup_two hp hp2 hP) hAP
  calc ⁅P, A⁆ = ⁅⁅P, A⁆, A⁆ := hidem.symm
    _ ≤ ⁅pCoreOf 2 Y, Y⁆ := Subgroup.commutator_mono h1 hAY

end Coprime

section Structure

variable [Finite G]

omit [Finite G] in
theorem pCoreOf_two_eq' (Y : Subgroup G) :
    pCoreOf 2 Y = (CFSG.pCore 2 Y).map Y.subtype := by
  rfl

theorem card_alternatingGroup_fin_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup (α := Fin 3)]
  simp [Nat.factorial]

theorem exists_decomp_of_altType {Y : Subgroup G} (h : IsAltType Y 3) {y : G} (hy : y ∈ Y)
    (hyQ : y ∉ pCoreOf 2 Y) : ∀ g ∈ Y, ∃ o ∈ pCoreOf 2 Y, ∃ k : ℤ, g = o * y ^ k := by
  obtain ⟨α, hsurj, hker, -⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y' : ↥Y := ⟨y, hy⟩ with hy'
  have hα1 : α y' ≠ 1 := by
    intro h1
    apply hyQ
    have : y' ∈ α.ker := h1
    rw [hker] at this
    rw [pCoreOf_two_eq']
    exact ⟨y', this, rfl⟩
  have hz : Subgroup.zpowers (α y') = ⊤ :=
    zpowers_eq_top_of_prime_card (p := 3) card_alternatingGroup_fin_three hα1
  intro g hg
  have hmem : α ⟨g, hg⟩ ∈ Subgroup.zpowers (α y') := by rw [hz]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hker' : (⟨g, hg⟩ : ↥Y) * y' ^ (-k) ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, hk]; simp
  rw [hker] at hker'
  refine ⟨g * y ^ (-k), ?_, k, by group⟩
  rw [pCoreOf_two_eq']
  exact ⟨_, hker', by simp [hy']⟩

theorem orderOf_eq_three_of_odd {Y : Subgroup G} (h : IsAltType Y 3) {x : G} (hx : x ∈ Y)
    (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) : orderOf x = 3 ∧ x ∉ pCoreOf 2 Y := by
  have hcore2 : IsPGroup 2 (pCoreOf 2 Y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hxQ : x ∉ pCoreOf 2 Y := by
    intro hxQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hcore2 ⟨x, hxQ⟩
    have h1 : orderOf x = 2 ^ n := by rw [← Subgroup.orderOf_mk x hxQ]; exact hn
    have : orderOf x = 1 := by
      have h2 : Odd (2 ^ n) := h1 ▸ hodd
      have : n = 0 := by
        by_contra hn0
        exact (Nat.not_even_iff_odd.mpr h2) (by
          exact (Nat.even_pow.mpr ⟨even_two, hn0⟩))
      rw [h1, this]; simp
    exact hx1 (orderOf_eq_one_iff.mp this)
  refine ⟨?_, hxQ⟩
  obtain ⟨α, hsurj, hker, -⟩ := h
  set x' : ↥Y := ⟨x, hx⟩ with hx'
  have hα3 : α x' ^ 3 = 1 := by
    have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := card_alternatingGroup_fin_three
    have := pow_card_eq_one' (G := alternatingGroup (Fin 3)) (x := α x')
    rwa [h3] at this
  have hx3 : x' ^ 3 ∈ α.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hα3
  rw [hker] at hx3
  have hx3Q : x ^ 3 ∈ pCoreOf 2 Y := by
    rw [pCoreOf_two_eq']; exact ⟨_, hx3, rfl⟩
  have hodd3 : Odd (orderOf (x ^ 3)) := by
    have hdvd : orderOf (x ^ 3) ∣ orderOf x := orderOf_pow_dvd 3
    exact Odd.of_dvd_nat hodd hdvd
  have hx31 : x ^ 3 = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hcore2 ⟨x ^ 3, hx3Q⟩
    have h1 : orderOf (x ^ 3) = 2 ^ n := by rw [← Subgroup.orderOf_mk _ hx3Q]; exact hn
    have : n = 0 := by
      by_contra hn0
      have h2 : Odd (2 ^ n) := h1 ▸ hodd3
      exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    rw [this] at h1
    simpa using h1
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx31
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h3

theorem le_closure_odd_of_isShort2 {Y : Subgroup G} (h : IsShort2 Y) :
    Y ≤ Subgroup.closure {x : G | x ∈ Y ∧ Odd (orderOf x)} := by
  obtain ⟨h1, -⟩ := h
  set S : Set ↥Y := {x | Odd (orderOf x)} with hS
  set N : Subgroup ↥Y := Subgroup.closure S with hN
  have hnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * x * g⁻¹))
      have : orderOf (g * x * g⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simpa [MulAut.conj_apply] using this
      rw [this]; exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]; exact N.mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]; exact N.inv_mem hx
  have h2 : IsPGroup 2 (↥Y ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    set a := (orderOf g).factorization 2 with ha
    refine ⟨a, ?_⟩
    set m := orderOf g / 2 ^ a with hm
    have hmodd : Odd m := by
      have : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos g).ne'
      exact Nat.odd_iff.mpr (by omega)
    have hgm : g ^ (2 ^ a) ∈ N := by
      apply Subgroup.subset_closure
      show Odd (orderOf (g ^ (2 ^ a)))
      have : orderOf (g ^ (2 ^ a)) = m := by
        rw [orderOf_pow' _ (by positivity)]
        have hg : Nat.gcd (orderOf g) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Nat.ordProj_dvd _ _)
        rw [hg]
      rw [this]; exact hmodd
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hgm
  have htop : N = ⊤ := h1 N h2
  intro x hx
  have hxN : (⟨x, hx⟩ : ↥Y) ∈ N := by rw [htop]; trivial
  have himg := Subgroup.mem_map_of_mem Y.subtype hxN
  rw [hN, MonoidHom.map_closure] at himg
  refine Subgroup.closure_mono ?_ himg
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z.2, by simpa [hS, Subgroup.orderOf_coe] using hz⟩

end Structure

section Odd

variable [Finite G]

theorem exists_orderOf_two_pow {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  exact ⟨n, by rw [← Subgroup.orderOf_mk x hx]; exact hn⟩

theorem mem_of_odd_eq_two_mul {N : Subgroup G} {x o c : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) (ho : o ∈ Subgroup.normalizer (N : Set G))
    (hc : c ∈ N) (hxo : x = o * c) (hodd : Odd (orderOf x)) (ho2 : ∃ k : ℕ, orderOf o = 2 ^ k) :
    x ∈ N := by
  let φ := QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G)))
  set x' : ↥(Subgroup.normalizer (N : Set G)) := ⟨x, hx⟩
  set o' : ↥(Subgroup.normalizer (N : Set G)) := ⟨o, ho⟩
  set c' : ↥(Subgroup.normalizer (N : Set G)) := ⟨c, Subgroup.le_normalizer hc⟩
  have hx'o' : x' = o' * c' := Subtype.ext hxo
  have hc'1 : φ c' = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc
  have hφ : φ x' = φ o' := by rw [hx'o', map_mul, hc'1, mul_one]
  have h1 : orderOf (φ x') ∣ orderOf x := by
    have := orderOf_map_dvd φ x'
    simpa [x', Subgroup.orderOf_mk] using this
  obtain ⟨k, hk⟩ := ho2
  have h2 : orderOf (φ x') ∣ 2 ^ k := by
    have h2' : orderOf (φ o') ∣ orderOf o := by
      have := orderOf_map_dvd φ o'
      simpa [o', Subgroup.orderOf_mk] using this
    rw [hφ]; rwa [hk] at h2'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have h3 : orderOf (φ x') = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : φ x' = 1 := orderOf_eq_one_iff.mp h3
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact h4

end Odd

section PowMem

variable [Finite G]

theorem pow_mem_of_eq_two_mul {N : Subgroup G} {x o c : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) (ho : o ∈ Subgroup.normalizer (N : Set G))
    (hc : c ∈ N) (hxo : x = o * c) {m : ℕ} (hm : orderOf o = 2 ^ m) : x ^ 2 ^ m ∈ N := by
  let φ := QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G)))
  set x' : ↥(Subgroup.normalizer (N : Set G)) := ⟨x, hx⟩
  set o' : ↥(Subgroup.normalizer (N : Set G)) := ⟨o, ho⟩
  set c' : ↥(Subgroup.normalizer (N : Set G)) := ⟨c, Subgroup.le_normalizer hc⟩
  have hx'o' : x' = o' * c' := Subtype.ext hxo
  have hc'1 : φ c' = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc
  have hφ : φ x' = φ o' := by rw [hx'o', map_mul, hc'1, mul_one]
  have ho'm : o' ^ 2 ^ m = 1 := by
    apply Subtype.ext
    show o ^ 2 ^ m = 1
    rw [← hm]; exact pow_orderOf_eq_one o
  have : φ (x' ^ 2 ^ m) = 1 := by rw [map_pow, hφ, ← map_pow, ho'm, map_one]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

end PowMem

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
