module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Swap
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Conj
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonSwap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_zpowers {z : G} {U : Subgroup G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) :
    ∃ u ∈ U, u ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have hle : U ≤ zpowers z := hcon
  have hz2 : z ^ 2 = 1 := by
    have := four_sq_eq_one hU hzU
    rwa [← pow_two] at this
  have h1 : Nat.card ↥U ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
  have h2 : Nat.card ↥(zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz2)
  have := hU.2
  omega

omit [Finite G] in
theorem comm_of_mem_four {U : Subgroup G} (hU : IVK.IsFourSubgroup U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a := by
  have := hU.1.toIsMulCommutative
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)

omit [Finite G] in
theorem map_conj_map_conj_inv (U : Subgroup G) (c : G) :
    (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hy
    exact ⟨c * y * c⁻¹, ⟨y, hy, rfl⟩, by simp [mul_assoc]⟩

theorem lemma29Alt_of_map_conj_inv {z : G} {k : Kind} (U : Subgroup G) (c : G)
    (h : Lemma29Alt z k (U.map (MulAut.conj c⁻¹).toMonoidHom)) : Lemma29Alt z k U := by
  have := lemma29Alt_map_conj (z := z) (k := k) _ c h
  have e := map_conj_map_conj_inv U c⁻¹
  rw [inv_inv] at e
  rwa [e] at this

theorem twoNilp_centralizer_of_nonswap {z : G} {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hp : PairShape z q₁ q₂ L₁ L₂)
    (hnt : ∀ u ∈ S, ∀ hu : u ∈ Cen z, u * u = 1 → u ∉ zpowers z →
      ∀ (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
        (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))),
        Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
          Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1)
    {U : Subgroup G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) {u : G} (huU : u ∈ U)
    (huS : u ∈ S) (hu1 : u ∉ zpowers z) (hu : u ∈ Cen z)
    (hnsw : ¬ Swaps z u L₁ L₂) : TwoNilp ↥(centralizer (U : Set G)) := by
  have hu2 : u * u = 1 := four_sq_eq_one hU huU
  rcases swaps_or_normalizes hp.ne hp.comps hu with hsw | ⟨hc₁, hc₂⟩
  · exact absurd hsw hnsw
  · have hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) := by
      have := mem_normalizer_of_map_conj_eq (K := L₁) (c := (toBar z ⟨u, hu⟩)⁻¹) hc₁
      simpa using (normalizer (L₁ : Set (CentralizerBar z))).inv_mem this
    have hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) := by
      have := mem_normalizer_of_map_conj_eq (K := L₂) (c := (toBar z ⟨u, hu⟩)⁻¹) hc₂
      simpa using (normalizer (L₂ : Set (CentralizerBar z))).inv_mem this
    obtain ⟨ht₁, ht₂⟩ := hnt u huS hu hu2 hu1 hn₁ hn₂
    exact twoNilp_centralizer_of_bar hzU huU hu
      (twoNilp_centralizer_bar_of_nonswap ctx hp huS hu hu2 hn₁ hn₂ ht₁ ht₂)

theorem lemma29Alt_of_z_mem {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (hp : PairShape z q₁ q₂ L₁ L₂)
    (hswap : ∀ u ∈ S, u ∈ Cen z → u * u = 1 → u ∉ zpowers z → Swaps z u L₁ L₂ →
      ∀ U : Subgroup G, IVK.IsFourSubgroup U → z ∈ U → u ∈ U → Lemma29Alt z k U)
    (hnt : ∀ u ∈ S, ∀ hu : u ∈ Cen z, u * u = 1 → u ∉ zpowers z →
      ∀ (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
        (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))),
        Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
          Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1)
    {U : Subgroup G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) {u : G} (huU : u ∈ U)
    (huS : u ∈ S) (hu1 : u ∉ zpowers z) : Lemma29Alt z k U := by
  have hu : u ∈ Cen z := by
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU huU hzU
  have hu2 : u * u = 1 := four_sq_eq_one hU huU
  by_cases hsw : Swaps z u L₁ L₂
  · exact hswap u huS hu hu2 hu1 hsw U hU hzU huU
  · exact Or.inl ((hasNormal2Compl_iff_twoNilp _).mpr
      (twoNilp_centralizer_of_nonswap ctx hp hnt hU hzU huU huS hu1 hu hsw))

theorem lemma29FirstAt_of_pair {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (hp : PairShape z q₁ q₂ L₁ L₂)
    (hnoconj : ∀ U : Subgroup G, IVK.IsFourSubgroup U → (∀ u ∈ U, ¬ IsConj z u) →
      Lemma29Alt z k U)
    (hswap : ∀ u ∈ S, u ∈ Cen z → u * u = 1 → u ∉ zpowers z → Swaps z u L₁ L₂ →
      ∀ U : Subgroup G, IVK.IsFourSubgroup U → z ∈ U → u ∈ U → Lemma29Alt z k U)
    (hnt : ∀ u ∈ S, ∀ hu : u ∈ Cen z, u * u = 1 → u ∉ zpowers z →
      ∀ (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
        (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z))),
        Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1 ∧
          Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1) :
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
  exact lemma29Alt_of_z_mem ctx hp hswap hnt hU₂ hzU₂ hsU₂ hsS hs1

end Reduction

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
