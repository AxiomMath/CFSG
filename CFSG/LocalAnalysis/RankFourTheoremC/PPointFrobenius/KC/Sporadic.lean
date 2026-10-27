module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Setup
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Inputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

theorem kcSporOrd_primeFactors_lt (s : TauCeti.SporadicName) :
    ∀ p ∈ (kcSporOrd s).primeFactors, p < 80 := by
  cases s <;> simp only [kcSporOrd] <;> norm_num [Nat.primeFactors]

theorem kc_spor_table : ∀ s : TauCeti.SporadicName, ∀ p ∈ Finset.range 80, p.Prime → 5 ≤ p →
    ∀ n ∈ Finset.Icc 3 10, p ^ n ∣ kcSporOrd s → ¬ p ^ (n + 1) ∣ kcSporOrd s →
      p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ kcSporOrd s → s = .Th ∧ p = 5 ∧ n = 3 := by
  decide +kernel

theorem kc_spor_table11 : ∀ s : TauCeti.SporadicName, ∀ p ∈ Finset.range 80, p.Prime → 5 ≤ p →
    ¬ p ^ 11 ∣ kcSporOrd s := by
  decide +kernel

theorem kc_spor_arith (s : TauCeti.SporadicName) (p n : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 3 ≤ n) (h1 : p ^ n ∣ kcSporOrd s) (h2 : ¬ p ^ (n + 1) ∣ kcSporOrd s)
    (h3 : p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ kcSporOrd s) : s = .Th ∧ p = 5 ∧ n = 3 := by
  have hN : kcSporOrd s ≠ 0 := by cases s <;> simp [kcSporOrd]
  have hpN : p ∈ (kcSporOrd s).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by omega)).trans h1, hN⟩
  have hp80 : p ∈ Finset.range 80 := Finset.mem_range.2 (kcSporOrd_primeFactors_lt s p hpN)
  have hn10 : n ≤ 10 := by
    by_contra h
    exact kc_spor_table11 s p hp80 hp hp5 ((pow_dvd_pow p (by omega)).trans h1)
  exact kc_spor_table s p hp80 hp hp5 n (Finset.mem_Icc.2 ⟨hn, hn10⟩) h1 h2 h3

theorem kc_noncomm_of_abelian_sylow {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (S : Sylow p K) (hS : IsMulCommutative (S : Subgroup K)) {x y : K}
    (hxy : IsPGroup p (Subgroup.closure ({x, y} : Set K))) : x * y = y * x := by
  obtain ⟨P, hHP⟩ := hxy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P S
  have hxP : x ∈ (P : Subgroup K) := hHP (Subgroup.subset_closure (by simp))
  have hyP : y ∈ (P : Subgroup K) := hHP (Subgroup.subset_closure (by simp))
  have hxS : (MulAut.conj g) x ∈ (S : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hxP
  have hyS : (MulAut.conj g) y ∈ (S : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hyP
  have key : (MulAut.conj g) x * (MulAut.conj g) y = (MulAut.conj g) y * (MulAut.conj g) x :=
    congrArg Subtype.val (hS.is_comm.comm ⟨_, hxS⟩ ⟨_, hyS⟩)
  rw [← map_mul, ← map_mul] at key
  exact (MulAut.conj g).injective key

theorem kc_sporadic (hOrd : KCSporadicOrders) (hTh : KCThFive) {K : Type} [Group K] [Finite K]
    {p n : ℕ} [Fact p.Prime] {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L)
    (s : TauCeti.SporadicName) (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  have hcard : Nat.card K = kcSporOrd s := (Nat.card_congr e.toEquiv).trans (hOrd s)
  have h1 : p ^ n ∣ kcSporOrd s := hcard ▸ h.dvd
  have h2 : ¬ p ^ (n + 1) ∣ kcSporOrd s := hcard ▸ h.not_dvd
  have h3 : p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ kcSporOrd s := by
    have := h.card_L ▸ h.card_L_dvd
    exact hcard ▸ this
  obtain ⟨rfl, rfl, rfl⟩ := kc_spor_arith s p n h.prime h.p5 h.n3 h1 h2 h3
  obtain ⟨x, y, -, -, hxy, hP⟩ := hTh
  have hP' : IsPGroup 5 (Subgroup.closure ({e.symm x, e.symm y} : Set K)) := by
    have := hP.map e.symm.toMonoidHom
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  exact hxy (by
    have := kc_noncomm_of_abelian_sylow S h.elem_S.1 hP'
    simpa using congrArg e this)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
