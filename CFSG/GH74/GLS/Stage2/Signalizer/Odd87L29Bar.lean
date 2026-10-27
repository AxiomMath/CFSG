module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Cls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

section Bar

variable {G : Type} [Group G] [Finite G]

theorem lemma29Alt_of_z_mem_bar {z : G} {k : Kind} {S : Subgroup G}
    (hbar : ∀ u ∈ S, ∀ hu : u ∈ Cen z, u * u = 1 → u ∉ zpowers z →
      TwoNilp ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z))))
    {U : Subgroup G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) {u : G} (huU : u ∈ U)
    (huS : u ∈ S) (hu1 : u ∉ zpowers z) : Lemma29Alt z k U := by
  have hu : u ∈ Cen z := by
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU huU hzU
  have hu2 : u * u = 1 := four_sq_eq_one hU huU
  exact Or.inl ((hasNormal2Compl_iff_twoNilp _).mpr
    (twoNilp_centralizer_of_bar hzU huU hu (hbar u huS hu hu2 hu1)))

theorem lemma29FirstAt_of_bar {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hnoconj : ∀ U : Subgroup G, IVK.IsFourSubgroup U → (∀ u ∈ U, ¬ IsConj z u) →
      Lemma29Alt z k U)
    (hbar : ∀ u ∈ S, ∀ hu : u ∈ Cen z, u * u = 1 → u ∉ zpowers z →
      TwoNilp ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)))) :
    Lemma29FirstAt z k := by
  intro U hU
  by_cases hno : ∀ u ∈ U, ¬ IsConj z u
  · exact hnoconj U hU hno
  push Not at hno
  obtain ⟨u₀, hu₀U, hu₀z⟩ := hno
  obtain ⟨c, hc⟩ := isConj_iff.mp hu₀z
  apply lemma29Alt_of_map_conj_inv U c
  set U₁ : Subgroup G := U.map (MulAut.conj c⁻¹).toMonoidHom with hU₁def
  have hU₁ : IVK.IsFourSubgroup U₁ := four_map_of_injective _ (MulAut.conj c⁻¹).injective hU
  have hzU₁ : z ∈ U₁ := by
    refine ⟨u₀, hu₀U, ?_⟩
    show c⁻¹ * u₀ * c⁻¹⁻¹ = z
    rw [← hc]
    group
  obtain ⟨u, huU₁, hu1⟩ := exists_mem_not_zpowers hU₁ hzU₁
  have hu : u ∈ Cen z := by
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU₁ huU₁ hzU₁
  have hu2 : u * u = 1 := four_sq_eq_one hU₁ huU₁
  have hW : IsPGroup 2 ↥(zpowers u) := by
    have hord : orderOf u ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers]; exact hi)
  have hWC : zpowers u ≤ Cen z := (zpowers_le).mpr hu
  obtain ⟨m, hm, hle⟩ := exists_conj_le_of_isSylowOf ctx.sylow hWC hW
  obtain ⟨s, hsS, hsu⟩ := hle (mem_zpowers u)
  have hsu' : m * s * m⁻¹ = u := hsu
  apply lemma29Alt_of_map_conj_inv U₁ m
  set U₂ : Subgroup G := U₁.map (MulAut.conj m⁻¹).toMonoidHom with hU₂def
  have hU₂ : IVK.IsFourSubgroup U₂ := four_map_of_injective _ (MulAut.conj m⁻¹).injective hU₁
  have hmz : m * z = z * m := by
    have := hm
    rw [show m ∈ Cen z ↔ _ from Iff.rfl, Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hzU₂ : z ∈ U₂ := by
    refine ⟨z, hzU₁, ?_⟩
    show m⁻¹ * z * m⁻¹⁻¹ = z
    rw [inv_inv]
    calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
      _ = m⁻¹ * (m * z) := by rw [hmz]
      _ = z := by group
  have hsU₂ : s ∈ U₂ := by
    refine ⟨u, huU₁, ?_⟩
    show m⁻¹ * u * m⁻¹⁻¹ = s
    rw [inv_inv, ← hsu']
    group
  have hs1 : s ∉ zpowers z := by
    rintro ⟨n, hn⟩
    apply hu1
    refine ⟨n, ?_⟩
    have hn' : z ^ n = s := hn
    rw [← hsu', ← hn']
    have : m * z ^ n * m⁻¹ = (m * z * m⁻¹) ^ n := by rw [conj_zpow]
    rw [this]
    have : m * z * m⁻¹ = z := by
      calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [hmz]
        _ = z := by group
    rw [this]
  exact lemma29Alt_of_z_mem_bar hbar hU₂ hzU₂ hsU₂ hsS hs1

end Bar

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
