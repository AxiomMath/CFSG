module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Inner

variable {G : Type} [Group G]

theorem mul_mem_of_index_le_two {A : Type*} [Group A] [Finite A] {R : Subgroup A}
    (hR : R.index ≤ 2) {a b : A} (ha : a ∉ R) (hb : b ∉ R) : a⁻¹ * b ∈ R := by
  by_contra hab
  have hmk : ∀ x y : A, (QuotientGroup.mk x : A ⧸ R) = QuotientGroup.mk y → x⁻¹ * y ∈ R :=
    fun x y h => QuotientGroup.eq.mp h
  have hinj : Function.Injective
      (fun i : Fin 3 => (QuotientGroup.mk (![1, a, b] i) : A ⧸ R)) := by
    intro i j hij
    simp only at hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      have := hmk _ _ hij
      simp at this
      exact ha this
    · exfalso
      have := hmk _ _ hij
      simp at this
      exact hb this
    · exfalso
      have := hmk _ _ hij.symm
      simp at this
      exact ha this
    · rfl
    · exfalso
      have := hmk _ _ hij
      exact hab (by simpa using this)
    · exfalso
      have := hmk _ _ hij.symm
      simp at this
      exact hb this
    · exfalso
      exact hab (by simpa using hmk _ _ hij.symm)
    · rfl
  have h3 : 3 ≤ R.index := by
    rw [Subgroup.index]
    simpa using Nat.card_le_card_of_injective _ hinj
  omega

theorem inducesInner_mul' {K : Subgroup G} {a b : G} (ha : Ch1.InducesInner a K)
    (hb : Ch1.InducesInner b K) : Ch1.InducesInner (a * b) K := by
  obtain ⟨l₁, hl₁, h₁⟩ := ha
  obtain ⟨l₂, hl₂, h₂⟩ := hb
  refine ⟨l₁ * l₂, K.mul_mem hl₁ hl₂, fun x hx => ?_⟩
  have hx' : l₁⁻¹ * x * l₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hl₁) hx) hl₁
  calc (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
    _ = b⁻¹ * (l₁⁻¹ * x * l₁) * b := by rw [h₁ x hx]
    _ = l₂⁻¹ * (l₁⁻¹ * x * l₁) * l₂ := h₂ _ hx'
    _ = (l₁ * l₂)⁻¹ * x * (l₁ * l₂) := by group

theorem inducesInner_inv_mul_of_not [Finite G] {K : Subgroup G}
    (hK : Nat.card (MulAut ↥K) ≤ 2 * Nat.card ↥K)
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) {g₁ g₂ : G}
    (h₁ : g₁ ∈ Subgroup.normalizer (K : Set G)) (h₂ : g₂ ∈ Subgroup.normalizer (K : Set G))
    (o₁ : ¬ Ch1.InducesInner g₁ K) (o₂ : ¬ Ch1.InducesInner g₂ K) :
    Ch1.InducesInner (g₁⁻¹ * g₂) K := by
  classical
  let R₀ : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hc : ∀ y ∈ K, (k : G) * y = y * (k : G) := by
      intro y hy
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : G)) hk
      simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
      calc (k : G) * y = ((k : G) * y * (k : G)⁻¹) * k := by group
        _ = y * k := by rw [this]
    exact Subtype.ext (hZ k k.2 hc)
  have hcard : Nat.card R₀ = Nat.card ↥K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : R₀.index ≤ 2 := by
    have h1 := R₀.index_mul_card
    rw [hcard] at h1
    have : R₀.index * Nat.card ↥K ≤ 2 * Nat.card ↥K := by rw [h1]; exact hK
    exact Nat.le_of_mul_le_mul_right this Nat.card_pos
  let ψ : Subgroup.normalizer (K : Set G) →* MulAut ↥K := conjAct K
  have hψ : ∀ n : Subgroup.normalizer (K : Set G),
      Ch1.InducesInner (n : G) K ↔ ψ n⁻¹ ∈ R₀ := by
    intro n
    constructor
    · rintro ⟨l, hl, hact⟩
      refine ⟨⟨l⁻¹, K.inv_mem hl⟩, ?_⟩
      ext x
      show ((l⁻¹ * (x : G) * (l⁻¹)⁻¹ : G)) = ((n : G)⁻¹ * (x : G) * ((n : G)⁻¹)⁻¹)
      rw [inv_inv, inv_inv, ← hact x x.2]
    · rintro ⟨a, ha⟩
      refine ⟨(a : G)⁻¹, K.inv_mem a.2, fun x hx => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) ha
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : ((ψ n⁻¹ ⟨x, hx⟩ : ↥K) : G) = (n : G)⁻¹ * x * ((n : G)⁻¹)⁻¹ := rfl
      rw [h2] at h1
      have h3 : (n : G)⁻¹ * x * (n : G) = (a : G) * x * (a : G)⁻¹ := by
        simpa using h1.symm
      calc (n : G)⁻¹ * x * (n : G) = (a : G) * x * (a : G)⁻¹ := h3
        _ = ((a : G)⁻¹)⁻¹ * x * (a : G)⁻¹ := by group
  let n₁ : Subgroup.normalizer (K : Set G) := ⟨g₁, h₁⟩
  let n₂ : Subgroup.normalizer (K : Set G) := ⟨g₂, h₂⟩
  have hn₁ : ψ n₁⁻¹ ∉ R₀ := fun h => o₁ ((hψ n₁).mpr h)
  have hn₂ : ψ n₂⁻¹ ∉ R₀ := fun h => o₂ ((hψ n₂).mpr h)
  have ha : (ψ n₂⁻¹)⁻¹ ∉ R₀ := fun h => hn₂ (by simpa using R₀.inv_mem h)
  have hb : (ψ n₁⁻¹)⁻¹ ∉ R₀ := fun h => hn₁ (by simpa using R₀.inv_mem h)
  have hmem := mul_mem_of_index_le_two hidx ha hb
  have hprod : (ψ n₂⁻¹)⁻¹⁻¹ * (ψ n₁⁻¹)⁻¹ = ψ (n₁⁻¹ * n₂)⁻¹ := by
    rw [inv_inv, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    show (g₂⁻¹ * g₁⁻¹⁻¹ : G) = (g₁⁻¹ * g₂)⁻¹
    group
  rw [hprod] at hmem
  exact (hψ (n₁⁻¹ * n₂)).mpr hmem

end Inner

section OddCore

variable {G : Type*} [Group G]

theorem map_conj_normalizer_self {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : S.map (MulAut.conj g).toMonoidHom = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)

theorem le_oddCoreIn' {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

variable [Finite G]

theorem exists_odd_normalized_of_two {X S C : Subgroup G} {t : G}
    (hS : IsSylowTwoOf S X) (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (ht : t ∈ C) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hSC : S ⊓ C = Subgroup.zpowers t) :
    ∃ O : Subgroup G, O ≤ C ∧ X ≤ Subgroup.normalizer (O : Set G) ∧ Odd (Nat.card O) ∧
      Nat.card C = 2 * Nat.card O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hzc : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  have hPc : Nat.card P = 2 := by
    apply le_antisymm
    · set P' : Subgroup G := (P : Subgroup ↥C).map C.subtype with hP'
      have hP'C : P' ≤ C := Subgroup.map_subtype_le _
      have hP'p : IsPGroup 2 ↥P' := P.isPGroup'.map C.subtype
      obtain ⟨S', hP'S', hS'⟩ := exists_isSylowTwoOf_of_le (hP'C.trans hCX) hP'p
      obtain ⟨h, hhX, hconj⟩ := hS.exists_conj hS'
      have hSC' : S' ⊓ C = (S ⊓ C).map (MulAut.conj h).toMonoidHom := by
        rw [hconj, map_equiv_inf, map_conj_normalizer_self (hXC hhX)]
      have h1 : Nat.card P' ≤ Nat.card ↥(S' ⊓ C) := Subgroup.card_le_of_le (le_inf hP'S' hP'C)
      have h2 : Nat.card ↥(S' ⊓ C) = 2 := by
        rw [hSC', card_map_equiv, hSC, hzc]
      have h3 : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective C.subtype_injective
      omega
    · have hzp : IsPGroup 2 ↥((Subgroup.zpowers t).subgroupOf C) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr ht)).toEquiv,
          hzc]
        norm_num
      obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
      have h1 : Nat.card ↥((Subgroup.zpowers t).subgroupOf C) ≤ Nat.card Q :=
        Subgroup.card_le_of_le hQ
      have h2 : Nat.card ↥((Subgroup.zpowers t).subgroupOf C) = 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr ht)).toEquiv,
          hzc]
      have h3 : Nat.card Q = Nat.card P := by
        rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]
      omega
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  obtain ⟨-, -, -, ⟨-, hodd, hidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement P hPcyc
  refine ⟨(CFSG.pPrimeCore 2 ↥C).map C.subtype, Subgroup.map_subtype_le _,
    CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized X C hXC _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hodd
  · have h1 := (CFSG.pPrimeCore 2 ↥C).index_mul_card
    rw [hidx, hPc] at h1
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    omega

end OddCore

end CFSG.QuasithinUnique.Unc25K1
