module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type}  [Group G]

structure IsA4Block (L U : Subgroup G) : Prop where
  card_U : Nat.card U = 4
  sq_U : ∀ u ∈ U, u ^ 2 = 1
  comm_U : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u
  card_L : Nat.card L = 12
  center_L : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g = 1
  exists_c : ∃ c ∈ L, orderOf c = 3 ∧ c ∈ normalizer (U : Set G) ∧
    (∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u) ∧ L = U ⊔ zpowers c

theorem IsA4Block.of_alt3 [Finite G] {L : Subgroup G} (hs : IsShort2 L) (ha : IsAltType L 3) :
    IsA4Block L (blockU L) := by
  obtain ⟨-, hU4, hU2, hUab, hL12, hZ, hc⟩ := hs.alt3_structure ha
  exact ⟨hU4, hU2, hUab, hL12, hZ, hc⟩

theorem IsA4Block.le {L U : Subgroup G} (h : IsA4Block L U) : U ≤ L := by
  obtain ⟨c, -, -, -, -, hLc⟩ := h.exists_c
  rw [hLc]; exact le_sup_left

theorem IsA4Block.map {L U : Subgroup G} (h : IsA4Block L U) (φ : G ≃* G) :
    IsA4Block (L.map φ.toMonoidHom) (U.map φ.toMonoidHom) := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  refine ⟨?_, ?_, ?_, ?_, ?_, φ c, ⟨c, hcL, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h.card_U
  · rintro _ ⟨u, hu, rfl⟩
    show (φ u) ^ 2 = 1
    rw [← map_pow, h.sq_U u hu, map_one]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    show φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul, h.comm_U u hu v hv]
  · rw [Subgroup.card_map_of_injective φ.injective]; exact h.card_L
  · rintro _ ⟨g, hg, rfl⟩ hcomm
    have hg1 : g = 1 := h.center_L g hg (fun l hl => φ.injective (by
      have := hcomm (φ l) ⟨l, hl, rfl⟩
      simpa [map_mul] using this))
    simp [hg1]
  · rw [← hc3]
    exact orderOf_injective φ.toMonoidHom φ.injective c
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have e : φ.symm (φ c * x * (φ c)⁻¹) = c * φ.symm x * c⁻¹ := by simp
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hcN (φ.symm x)
  · rintro _ ⟨u, hu, rfl⟩ hu1 heq
    refine hcfp u hu (fun h1 => hu1 (by simp [h1])) (φ.injective ?_)
    simpa [map_mul, map_inv] using heq
  · conv_lhs => rw [hLc]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

theorem IsA4Block.conj {L U : Subgroup G} (h : IsA4Block L U) (g : G) :
    IsA4Block (conjR L g) (conjR U g) :=
  h.map (MulAut.conj g⁻¹)

theorem IsA4Block.le_of_mem [Finite G] {L U N : Subgroup G} (h : IsA4Block L U)
    (hLN : L ≤ normalizer (N : Set G)) {v : G} (hvN : v ∈ N) (hvU : v ∈ U) (hv1 : v ≠ 1) :
    U ≤ N := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]; exact one_mem _
  · obtain ⟨n, hn⟩ := klein_conj_transitive h.card_U hc3' hcN hcfp hvU hu hv1 hu1
    rw [hn]
    have hcn : (c ^ n)⁻¹ ∈ L := inv_mem (pow_mem hcL n)
    have := (Subgroup.mem_normalizer_iff.mp (hLN hcn) v).mp hvN
    simpa using this

theorem IsA4Block.commutator_eq [Finite G] {L U A : Subgroup G} (h : IsA4Block L U)
    (hA2 : IsPGroup 2 A) (hAL : A ≤ normalizer (L : Set G)) (hAU : A ≤ normalizer (U : Set G))
    (hnt : ¬ A ≤ centralizer (U : Set G)) : ⁅L, A⁆ = L := by
  classical
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hUL : U ≤ L := h.le
  have hB2 : IsPGroup 2 ↥(A ⊔ U) := by
    obtain ⟨n, hn⟩ := hA2.exists_card_eq
    have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hAU
    have hdvd : Nat.card ↥(A ⊔ U) ∣ 2 ^ (n + 2) := by
      have h1 : Nat.card ↥(A ⊔ U) ∣ Nat.card ↥A * Nat.card ↥U := Dvd.intro _ hmul
      have h2 : Nat.card ↥A * Nat.card ↥U = 2 ^ (n + 2) := by rw [hn, h.card_U]; ring
      rwa [h2] at h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card hm
  have hBN : A ⊔ U ≤ normalizer (U : Set G) := sup_le hAU Subgroup.le_normalizer
  have hntB : ¬ A ⊔ U ≤ centralizer (U : Set G) := fun hB => hnt (le_sup_left.trans hB)
  obtain ⟨z, hzU, hz1, -, -, -, hcenty⟩ :=
    klein_structure h.card_U h.sq_U (le_sup_right : U ≤ A ⊔ U) hBN hB2 hntB
  have hz2 : z ^ 2 = 1 := h.sq_U z hzU
  obtain ⟨a, haA, han⟩ : ∃ a ∈ A, a ∉ centralizer (U : Set G) := by
    by_contra hcon
    apply hnt
    intro a ha
    by_contra h'
    exact hcon ⟨a, ha, h'⟩
  have haB : a ∈ A ⊔ U := Subgroup.mem_sup_left haA
  have haUn : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hAU haA) u).mp hu
  have hNL : ⁅L, A⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl a' ha'
    have h1 : a' * l⁻¹ * a'⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL ha') l⁻¹).mp (inv_mem hl)
    have : ⁅l, a'⁆ = l * (a' * l⁻¹ * a'⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hl h1
  have hLN : L ≤ normalizer ((⁅L, A⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left L A
  obtain ⟨u₀, hu₀U, hu₀z⟩ : ∃ u₀ ∈ U, u₀ ∉ zpowers z := by
    by_contra hcon
    have hle : U ≤ zpowers z := fun u hu => by
      by_contra h'; exact hcon ⟨u, hu, h'⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
    rw [h.card_U, h2] at h1
    omega
  have hu₀a : ¬ u₀ * a = a * u₀ := fun hc => hu₀z ((hcenty a haB han u₀ hu₀U).mpr hc)
  have hvN : ⁅u₀, a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator (hUL hu₀U) haA
  have hvU : ⁅u₀, a⁆ ∈ U := by
    have : ⁅u₀, a⁆ = u₀ * (a * u₀⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hu₀U (by simpa using haUn u₀⁻¹ (inv_mem hu₀U))
  have hv1 : ⁅u₀, a⁆ ≠ 1 := by
    intro hv
    apply hu₀a
    rw [commutatorElement_def] at hv
    calc u₀ * a = (u₀ * a * u₀⁻¹ * a⁻¹) * a * u₀ := by group
      _ = a * u₀ := by rw [hv]; group
  have hUN : U ≤ ⁅L, A⁆ := h.le_of_mem hLN hvN hvU hv1
  have hnN : ⁅c, a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator hcL haA
  have hnL : ⁅c, a⁆ ∈ L := hNL hnN
  have hnU : ⁅c, a⁆ ∉ U := by
    intro hnU
    have hza : z * a = a * z := (hcenty a haB han z hzU).mp (Subgroup.mem_zpowers z)
    have hz''U : c * z * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hcN z).mp hzU
    have hz''1 : c * z * c⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have hz''z : c * z * c⁻¹ ≠ z := hcfp z hzU hz1
    have e1 : (c * a * c⁻¹) * (c * z * c⁻¹) * (c * a * c⁻¹)⁻¹ = c * z * c⁻¹ := by
      have : a * z * a⁻¹ = z := by
        calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [← hza]
          _ = z := by group
      calc (c * a * c⁻¹) * (c * z * c⁻¹) * (c * a * c⁻¹)⁻¹ = c * (a * z * a⁻¹) * c⁻¹ := by group
        _ = c * z * c⁻¹ := by rw [this]
    have e2 : c * a * c⁻¹ = ⁅c, a⁆ * a := by
      rw [commutatorElement_def]; group
    have hwU : a * (c * z * c⁻¹) * a⁻¹ ∈ U := haUn _ hz''U
    have e3 : a * (c * z * c⁻¹) * a⁻¹ = c * z * c⁻¹ := by
      have e4 : ⁅c, a⁆ * (a * (c * z * c⁻¹) * a⁻¹) * ⁅c, a⁆⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by
        have := h.comm_U _ hnU _ hwU
        rw [this]; group
      calc a * (c * z * c⁻¹) * a⁻¹ = ⁅c, a⁆ * (a * (c * z * c⁻¹) * a⁻¹) * ⁅c, a⁆⁻¹ := e4.symm
        _ = (⁅c, a⁆ * a) * (c * z * c⁻¹) * (⁅c, a⁆ * a)⁻¹ := by group
        _ = (c * a * c⁻¹) * (c * z * c⁻¹) * (c * a * c⁻¹)⁻¹ := by rw [← e2]
        _ = c * z * c⁻¹ := e1
    have hcomm : (c * z * c⁻¹) * a = a * (c * z * c⁻¹) := by
      calc (c * z * c⁻¹) * a = (a * (c * z * c⁻¹) * a⁻¹) * a := by rw [e3]
        _ = a * (c * z * c⁻¹) := by group
    have hmem := (hcenty a haB han _ hz''U).mpr hcomm
    rcases (mem_zpowers_iff_of_sq_eq_one hz2).mp hmem with h1 | h1
    · exact hz''1 h1
    · exact hz''z h1
  have hcN' : c ∈ ⁅L, A⁆ := by
    have hLc' : L = zpowers c ⊔ U := by rw [hLc, sup_comm]
    have hnmem : ⁅c, a⁆ ∈ ((zpowers c ⊔ U : Subgroup G) : Set G) := by rw [← hLc']; exact hnL
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (zpowers c) U (zpowers_le.mpr hcN)] at hnmem
    obtain ⟨y, hy, u', hu', hyu0⟩ := hnmem
    have hyu : y * u' = ⁅c, a⁆ := hyu0
    have hyN : y ∈ ⁅L, A⁆ := by
      have : y = ⁅c, a⁆ * u'⁻¹ := by rw [← hyu]; group
      rw [this]
      exact mul_mem hnN (inv_mem (hUN hu'))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : c ^ k = c ^ (k % 3) := by
      have := zpow_mod_orderOf c k
      rw [hc3] at this
      simpa using this.symm
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h0 | h0
    · exfalso
      apply hnU
      rw [← hyu, hk, h0, zpow_zero, one_mul]
      exact hu'
    · rw [hk, h0, zpow_one] at hyN
      exact hyN
    · rw [hk, h0] at hyN
      have hc4 : c = (c ^ (2 : ℤ)) * (c ^ (2 : ℤ)) := by
        calc c = c * c ^ (3 : ℤ) := by
              have : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3'
              rw [this, mul_one]
          _ = (c ^ (2 : ℤ)) * (c ^ (2 : ℤ)) := by group
      rw [hc4]
      exact mul_mem hyN hyN
  refine le_antisymm hNL ?_
  calc L = U ⊔ zpowers c := hLc
    _ ≤ ⁅L, A⁆ := sup_le hUN ((Subgroup.zpowers_le).mpr hcN')

end CFSG.QuasithinUnique.DoubleA3
