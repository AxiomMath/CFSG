module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModelConj

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup
open CFSG.ComponentClassification.GSThmB

variable {K : Type} {G : Type*} [Group K] [Group G] (M : AutModel K G)

theorem conj_inv_mem_of_conj_mem {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ q ∈ H, g * q * g⁻¹ ∈ H) : ∀ q ∈ H, g⁻¹ * q * g ∈ H := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective])
  intro q hq
  rw [← heq] at hq
  obtain ⟨r, hr, hrq⟩ := hq
  have : r = g⁻¹ * q * g := by
    rw [← hrq]
    show r = g⁻¹ * (g * r * g⁻¹) * g
    group
  rw [← this]
  exact hr

variable (hPA : M.P ≤ M.A) (hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1)
include hPA hcent

theorem f2_of_model [Finite K] (θ : MulAut K) (Q₀ : Subgroup G)
    (hQ₀ : Q₀ ≤ M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G))
    (hcard : Nat.card ↥(M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G)) = 2 ^ 5 * 45)
    (hcardQ₀ : Nat.card Q₀ = 2 ^ 5) (g₀ : G) (hg₀P : g₀ ∈ M.P)
    (hg₀N : ∀ q ∈ Q₀, g₀ * q * g₀⁻¹ ∈ Q₀) (hg₀Q : g₀ ∉ Q₀) (hg₀2 : g₀ * g₀ ∈ Q₀)
    (hg₀σ : (M.Φ θ : G) * (g₀⁻¹ * (M.Φ θ : G) * g₀) ∈ M.P)
    (Q : Subgroup (MulAut K)) (hQC : Q ≤ centralizer ({θ} : Set (MulAut K)))
    (hQS : ∃ T : Sylow 2 ↥(centralizer ({θ} : Set (MulAut K))),
      (T : Subgroup _) = Q.subgroupOf (centralizer ({θ} : Set (MulAut K)))) :
    ∃ g : MulAut K, g ∈ Cat8.Inn K ∧ g ∈ normalizer (Q : Set (MulAut K)) ∧ g ∉ Q ∧
      g * g ∈ Q ∧ θ * (g⁻¹ * θ * g) ∈ Cat8.Inn K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : G := (M.Φ θ : G) with hσdef
  set CA : Subgroup G := M.A ⊓ centralizer ({σ} : Set G) with hCA
  have : Finite (MulAut K) :=
    Finite.of_injective (fun φ : MulAut K => (φ : K → K)) DFunLike.coe_injective
  have : Finite M.A := Finite.of_equiv _ M.Φ.toEquiv
  have : Finite CA := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have : Finite Q₀ := Finite.of_injective (inclusion (hQ₀.trans inf_le_left))
    (inclusion_injective _)
  have hmapC := map_centralizer_singleton M θ
  let e : ↥(centralizer ({θ} : Set (MulAut K))) ≃* CA :=
    ((centralizer ({θ} : Set (MulAut K))).equivMapOfInjective M.ι M.ι_injective).trans
      (MulEquiv.subgroupCongr hmapC)
  have he : ∀ x, ((e x : CA) : G) = M.ι x := fun x => rfl
  obtain ⟨T, hT⟩ := hQS
  let T' : Sylow 2 CA := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ₀2 : IsPGroup 2 (Q₀.subgroupOf CA) := by
    refine IsPGroup.of_card (n := 5) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀).toEquiv, hcardQ₀]
  have hQ₀i : ¬ 2 ∣ (Q₀.subgroupOf CA).index := by
    have h := index_mul_card (Q₀.subgroupOf CA)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀).toEquiv, hcardQ₀, hcard] at h
    have : (Q₀.subgroupOf CA).index = 45 := by omega
    rw [this]
    decide
  let S₀ : Sylow 2 CA := hQ₀2.toSylow hQ₀i
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq CA S₀ T'
  have hcA : (c : G) ∈ M.A := c.2.1
  have hcσ : (c : G) * σ = σ * c := mem_centralizer_singleton_iff.1 c.2.2
  have hmemQ : ∀ η : MulAut K, η ∈ Q ↔ (c : G)⁻¹ * M.ι η * c ∈ Q₀ := by
    intro η
    have hT'mem : ∀ y : CA, y ∈ (T' : Subgroup CA) ↔ c⁻¹ * y * c ∈ Q₀.subgroupOf CA := by
      intro y
      rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply, IsPGroup.toSylow_coe]
    constructor
    · intro hη
      have hηC : η ∈ centralizer ({θ} : Set (MulAut K)) := hQC hη
      have h1 : e ⟨η, hηC⟩ ∈ (T' : Subgroup CA) := by
        show e ⟨η, hηC⟩ ∈ T.map e.toMonoidHom
        refine ⟨⟨η, hηC⟩, ?_, rfl⟩
        rw [hT, SetLike.mem_coe, mem_subgroupOf]
        exact hη
      have h2 := (hT'mem _).1 h1
      rw [mem_subgroupOf] at h2
      simpa [he] using h2
    · intro hη
      have hηA : M.ι η ∈ CA := by
        have : (c : G)⁻¹ * M.ι η * c ∈ CA := hQ₀ hη
        have h3 := CA.mul_mem (CA.mul_mem c.2 this) (CA.inv_mem c.2)
        simpa [mul_assoc] using h3
      obtain ⟨η', hη'⟩ := e.surjective ⟨M.ι η, hηA⟩
      have hηη : (η' : MulAut K) = η := by
        apply M.ι_injective
        rw [← he, hη']
      have h1 : e η' ∈ (T' : Subgroup CA) := by
        rw [hT'mem, mem_subgroupOf, hη']
        simpa using hη
      obtain ⟨t, ht, hte⟩ := h1
      have htη : t = η' := e.injective hte
      rw [hT, SetLike.mem_coe, mem_subgroupOf, htη, hηη] at ht
      exact ht
  have hg'A : (c : G) * g₀ * (c : G)⁻¹ ∈ M.A :=
    M.A.mul_mem (M.A.mul_mem hcA (hPA hg₀P)) (M.A.inv_mem hcA)
  let g : MulAut K := M.Φ.symm ⟨(c : G) * g₀ * (c : G)⁻¹, hg'A⟩
  have hgι : M.ι g = (c : G) * g₀ * (c : G)⁻¹ := by
    show (M.Φ (M.Φ.symm ⟨_, hg'A⟩) : G) = _
    rw [MulEquiv.apply_symm_apply]
  have hg₀N' := conj_inv_mem_of_conj_mem hg₀N
  have hcg : ∀ y : G, (c : G)⁻¹ * ((c : G) * g₀ * (c : G)⁻¹ * y *
      ((c : G) * g₀ * (c : G)⁻¹)⁻¹) * c = g₀ * ((c : G)⁻¹ * y * c) * g₀⁻¹ := fun y => by group
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_range_conj_iff M hPA hcent]
    show M.ι g ∈ M.P
    rw [hgι]
    exact conj_mem_P_of_mem_A M hcA hg₀P
  · rw [mem_normalizer_iff]
    intro η
    rw [hmemQ, hmemQ, map_mul, map_mul, map_inv, hgι, hcg]
    constructor
    · exact hg₀N _
    · intro h
      have := hg₀N' _ h
      simpa [mul_assoc] using this
  · rw [hmemQ, hgι]
    simpa [mul_assoc] using hg₀Q
  · rw [hmemQ, map_mul, hgι]
    have : (c : G)⁻¹ * ((c : G) * g₀ * (c : G)⁻¹ * ((c : G) * g₀ * (c : G)⁻¹)) * c =
        g₀ * g₀ := by group
    rw [this]
    exact hg₀2
  · rw [mem_range_conj_iff M hPA hcent]
    show M.ι (θ * (g⁻¹ * θ * g)) ∈ M.P
    rw [map_mul, map_mul, map_mul, map_inv, hgι]
    have h1 : σ * (((c : G) * g₀ * (c : G)⁻¹)⁻¹ * σ * ((c : G) * g₀ * (c : G)⁻¹)) =
        (c : G) * (σ * (g₀⁻¹ * σ * g₀)) * (c : G)⁻¹ := by
      have hcσ' : (c : G)⁻¹ * σ = σ * (c : G)⁻¹ := by
        calc (c : G)⁻¹ * σ = (c : G)⁻¹ * (σ * c) * (c : G)⁻¹ := by group
          _ = (c : G)⁻¹ * ((c : G) * σ) * (c : G)⁻¹ := by rw [hcσ]
          _ = σ * (c : G)⁻¹ := by group
      calc σ * (((c : G) * g₀ * (c : G)⁻¹)⁻¹ * σ * ((c : G) * g₀ * (c : G)⁻¹))
          = σ * (c : G) * g₀⁻¹ * ((c : G)⁻¹ * σ) * (c : G) * g₀ * (c : G)⁻¹ := by group
        _ = σ * (c : G) * g₀⁻¹ * (σ * (c : G)⁻¹) * (c : G) * g₀ * (c : G)⁻¹ := by rw [hcσ']
        _ = (σ * (c : G)) * (g₀⁻¹ * σ * g₀) * (c : G)⁻¹ := by group
        _ = ((c : G) * σ) * (g₀⁻¹ * σ * g₀) * (c : G)⁻¹ := by rw [hcσ]
        _ = (c : G) * (σ * (g₀⁻¹ * σ * g₀)) * (c : G)⁻¹ := by group
    have : M.ι θ = σ := rfl
    rw [this, h1]
    exact conj_mem_P_of_mem_A M hcA hg₀σ

end CFSG.ComponentClassification.CatFactsSmall
