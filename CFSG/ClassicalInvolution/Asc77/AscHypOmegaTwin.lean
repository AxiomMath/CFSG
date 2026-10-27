module

public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaBasic
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2DatumTwin
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77.AscHypOmega

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem four_le_natCard_galoisField (hq : 5 ≤ p ^ f) : 4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  omega

theorem natCard_conjSub (n : G) (K : Subgroup G) : Nat.card (conjSub n K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem mem_normalizer_of_conjSub_eq {K : Subgroup G} {n : G} (h : conjSub n K = K) :
    n ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conj_mem_conjSub (n := n) hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_conjSub_iff] at hx
    simpa [mul_assoc] using hx

theorem isPGroup_zpowers_conj [Finite G] {v : G} (hv : IsPGroup 2 (Subgroup.zpowers v)) (a : G) :
    IsPGroup 2 (Subgroup.zpowers (a * v * a⁻¹)) := by
  obtain ⟨n, hn⟩ := hv.exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  have hord : orderOf (a * v * a⁻¹) = orderOf v := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective v
  rw [Nat.card_zpowers, hord, ← Nat.card_zpowers, hn]

theorem conjSub_mem_omegaAt (K₀ : Subgroup G) (z₀ g : G) :
    conjSub g K₀ ∈ omegaAt K₀ z₀ (g * z₀ * g⁻¹) :=
  ⟨g⁻¹, by simp [conjSub], by simp⟩

section Members

variable [Finite G] {K₀ : Subgroup G} {z₀ : G}

omit [Finite G] in
theorem isQuasisimple_oddQuot (hq : 5 ≤ p ^ f) (h : IsClassicalMember p f K₀ z₀) :
    CFSG.Open.IsQuasisimple (K₀ ⧸ classicalInvolutionOddCore K₀) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (isQuasisimple_specialLinearGroup_two (four_le_natCard_galoisField hq))

theorem twins_of_conjSub (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀) {a b : G}
    (hab : a * z₀ * a⁻¹ = b * z₀ * b⁻¹) (hne : conjSub a K₀ ≠ conjSub b K₀) :
    conjSub b K₀ ≤ Subgroup.normalizer (conjSub a K₀ : Set G) ∧
      conjSub a K₀ ≤ Subgroup.normalizer (conjSub b K₀ : Set G) ∧
      ⁅conjSub a K₀, conjSub b K₀⁆ ≤ oddCoreOf (conjSub a K₀) ⊓ oddCoreOf (conjSub b K₀) := by
  have hA := conjSub_mem_omegaAt K₀ z₀ a
  have hB : conjSub b K₀ ∈ omegaAt K₀ z₀ (a * z₀ * a⁻¹) := hab ▸ conjSub_mem_omegaAt K₀ z₀ b
  obtain ⟨h1, h2, h3, -⟩ := twins_of_perfect h₀.subnormal h₀.perfect.commutator_eq_top
    (isQuasisimple_oddQuot hq h₀) hA hB hne
  exact ⟨h1, h2, h3⟩

theorem omega4_of_classical (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {K J : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hne : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ K hK
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K₀ J hJ
  have hKa := h₀.conj a
  have hJb := h₀.conj b
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hKa
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hJb
  by_cases h2 : 2 ∣ Nat.card ↥(conjSub a K₀ ⊓ conjSub b K₀)
  ·
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu1 : (u : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu'
      omega
    have huu : (u : G) * u = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
    have ha := (hUa.unique u (Subgroup.mem_inf.mp u.2).1 huu).resolve_left hu1
    have hb := (hUb.unique u (Subgroup.mem_inf.mp u.2).2 huu).resolve_left hu1
    obtain ⟨-, hKJ, hcomm⟩ := twins_of_conjSub hq h₀ (ha.symm.trans hb) hne
    refine ⟨?_, fun _ => hcomm⟩
    obtain ⟨e⟩ := hKa.nonempty_equiv
    have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
    exact padicValNat_card_inf_le_one hKa.perfect hKJ hne
      (by rw [natCard_conjSub, natCard_conjSub]) hodd (four_le_natCard_galoisField hq) e
  · rw [padicValNat.eq_zero_of_not_dvd h2]
    exact ⟨Nat.zero_le _, fun h => absurd h (by norm_num)⟩

theorem normalizer_of_twins (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {K J : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀)
    {z : G} (hKz : IsUniqueInvolution K z) (hJz : IsUniqueInvolution J z) :
    J ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ K hK
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K₀ J hJ
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj a)
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj b)
  by_cases hne : conjSub a K₀ = conjSub b K₀
  · rw [hne]
    exact Subgroup.le_normalizer
  · exact (twins_of_conjSub hq h₀ ((hUa.eq hKz).trans (hUb.eq hJz).symm) hne).1

theorem eq_of_mem_of_mem (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {K J : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀)
    {k : G} (hkK : k ∈ K) (hkJ : k ∈ J) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hk4 : 4 ≤ orderOf k) : K = J := by
  by_contra hne
  have h1 := (omega4_of_classical hp2 hq h₀ hK hJ hne).1
  obtain ⟨n, hn⟩ := hk2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 4 ∣ Nat.card ↥(K ⊓ J) := by
    have h4 : 4 ∣ orderOf k := by
      rw [hn]
      exact (pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)
    exact h4.trans (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hkK, hkJ⟩))
  have hpos : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have := (padicValNat_dvd_iff_le (p := 2) (n := 2) hpos).mp (by simpa using hdvd)
  omega

theorem centralizer_le_normalizer_of_mem (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h₀ : IsClassicalMember p f K₀ z₀) {K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀)
    {k : G} (hkK : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k)) (hk4 : 4 ≤ orderOf k) :
    Subgroup.centralizer ({k} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  apply mem_normalizer_of_conjSub_eq
  have hcK : conjSub c K ∈ CoreAssembly.conjClass K₀ := by
    obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ K hK
    exact ⟨c * a, conjSub_mul c a K₀⟩
  have hkc : k ∈ conjSub c K := by
    have := conj_mem_conjSub (n := c) hkK
    have hck : c * k * c⁻¹ = k := by rw [mul_inv_eq_iff_eq_mul]; exact hc
    rwa [hck] at this
  exact (eq_of_mem_of_mem hp2 hq h₀ hK hcK hkK hkc hk2 hk4).symm

end Members

@[expose] def HasTwin (K : Subgroup G) (z : G) : Prop :=
  ∃ K₁ ∈ CoreAssembly.conjClass K, K₁ ≠ K ∧ IsUniqueInvolution K₁ z

theorem centralizer_le_normalizer_of_not_hasTwin {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (h : ¬ HasTwin K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  apply mem_normalizer_of_conjSub_eq
  by_contra hne
  apply h
  refine ⟨conjSub c K, ⟨c, rfl⟩, hne, ?_⟩
  have hcz : c * z * c⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hc
  have := hz.conj c
  rwa [hcz] at this

@[expose] def Omega5At (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) : Prop :=
  ∀ J ∈ Ω, K ≠ J → ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) →
    v * z = z * v → v ∈ Subgroup.normalizer (K : Set G)

section Transport

variable [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem omega5_of_omega5At (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    (h5 : Omega5At (CoreAssembly.conjClass K₀) K₀ z₀) :
    ∀ K ∈ CoreAssembly.conjClass K₀, ∀ J ∈ CoreAssembly.conjClass K₀, K ≠ J → ∀ z : G,
      IsUniqueInvolution K z → ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) →
        IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
          v ∈ Subgroup.normalizer (K : Set G) := by
  intro K hK J hJ hKJ z hz v hvJ hvnc hv2 hvz
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ K hK
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj a)
  have hza : a * z₀ * a⁻¹ = z := hUa.eq hz
  have hJ' : conjSub a⁻¹ J ∈ CoreAssembly.conjClass K₀ := by
    obtain ⟨b, rfl⟩ := CoreAssembly.single_class K₀ J hJ
    exact ⟨a⁻¹ * b, conjSub_mul a⁻¹ b K₀⟩
  have hne' : K₀ ≠ conjSub a⁻¹ J := by
    intro h
    apply hKJ
    have := congrArg (conjSub a) h
    rwa [conjSub_conjSub_inv] at this
  have hv' : a⁻¹ * v * a ∈ conjSub a⁻¹ J := by
    simpa using conj_mem_conjSub (n := a⁻¹) hvJ
  have hnc' : ¬ ∀ w ∈ conjSub a⁻¹ J, (a⁻¹ * v * a) * w = w * (a⁻¹ * v * a) := by
    intro h
    apply hvnc
    intro w hw
    have hw' : a⁻¹ * w * a ∈ conjSub a⁻¹ J := by simpa using conj_mem_conjSub (n := a⁻¹) hw
    have := h _ hw'
    calc v * w = a * ((a⁻¹ * v * a) * (a⁻¹ * w * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * w * a) * (a⁻¹ * v * a)) * a⁻¹ := by rw [this]
      _ = w * v := by group
  have hv2' : IsPGroup 2 (Subgroup.zpowers (a⁻¹ * v * a)) := by
    have := isPGroup_zpowers_conj hv2 a⁻¹
    rwa [inv_inv] at this
  have hz₀ : z₀ = a⁻¹ * z * a := by rw [← hza]; group
  have hvz' : (a⁻¹ * v * a) * z₀ = z₀ * (a⁻¹ * v * a) := by
    rw [hz₀]
    calc a⁻¹ * v * a * (a⁻¹ * z * a) = a⁻¹ * (v * z) * a := by group
      _ = a⁻¹ * (z * v) * a := by rw [hvz]
      _ = a⁻¹ * z * a * (a⁻¹ * v * a) := by group
  have hn := h5 _ hJ' hne' _ hv' hnc' hv2' hvz'
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have hx := hn (a⁻¹ * x * a)
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have e : a⁻¹ * (v * x * v⁻¹) * a = (a⁻¹ * v * a) * (a⁻¹ * x * a) * (a⁻¹ * v * a)⁻¹ := by group
  rw [e]
  exact hx

end Transport

end CFSG.ClassicalInvolution.Asc77.AscHypOmega
