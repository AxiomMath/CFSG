module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AltCent

open CFSG Subgroup Equiv Equiv.Perm

theorem not_dvd_of_three_le {n k : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) (hk : 3 ≤ k)
    (hkm : 2 * k ≤ n + 4) :
    ¬ n.factorial / 2 ∣ (n + 4 - 2 * k).factorial * 2 ^ k * k.factorial := by
  rcases hn with rfl | rfl | rfl
  · have hk4 : k ≤ 4 := by omega
    interval_cases k <;> decide
  · have hk5 : k ≤ 5 := by omega
    interval_cases k <;> decide
  · have hk5 : k ≤ 5 := by omega
    interval_cases k <;> decide

theorem card_cycleType_le_two {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) {π : Perm (Fin (n + 4))}
    (hπ2 : π * π = 1) (hπ1 : π ≠ 1)
    (hdvd : n.factorial / 2 ∣ Nat.card (centralizer ({π} : Set (Perm (Fin (n + 4)))))) :
    Multiset.card π.cycleType = 1 ∨ Multiset.card π.cycleType = 2 := by
  rw [Idx.card_centralizer_inv hπ2 hπ1] at hdvd
  have hct := Idx.cycleType_eq_replicate hπ2
  have hk0 : Multiset.card π.cycleType ≠ 0 := by
    intro h0
    apply hπ1
    rw [← cycleType_eq_zero, hct, h0, Multiset.replicate_zero]
  have hkm : 2 * Multiset.card π.cycleType ≤ n + 4 := by
    have h1 := sum_cycleType_le π
    rw [hct, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at h1
    omega
  by_contra hk12
  exact not_dvd_of_three_le hn (by omega) hkm hdvd

theorem exists_dt {m : ℕ} {π : Perm (Fin m)} (hπ2 : π * π = 1)
    (hk : Multiset.card π.cycleType = 2) :
    ∃ i j k l : Fin m, [i, j, k, l].Nodup ∧ π = swap i j * swap k l ∧
      π.support = {i, j, k, l} := by
  classical
  have hct := Idx.cycleType_eq_replicate hπ2
  have hsupp : π.support.card = 4 := by
    rw [← sum_cycleType, hct, hk]
    simp
  have hπ2' : ∀ a, π (π a) = a := fun a => by
    rw [← Perm.mul_apply, hπ2, Perm.one_apply]
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < π.support.card)
  set j := π i with hj
  have hij : i ≠ j := fun h => (mem_support.mp hi) h.symm
  have hjs : j ∈ π.support := mem_support.mpr (by rw [hj, hπ2']; exact hij)
  have hrest : 0 < ((π.support.erase i).erase j).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hjs⟩),
      Finset.card_erase_of_mem hi]
    omega
  obtain ⟨k, hk'⟩ := Finset.card_pos.mp hrest
  simp only [Finset.mem_erase] at hk'
  obtain ⟨hkj, hki, hks⟩ := hk'
  set l := π k with hl
  have hkl : k ≠ l := fun h => (mem_support.mp hks) h.symm
  have hli : l ≠ i := by
    intro h
    apply hkj
    rw [hj, ← h, hl, hπ2']
  have hlj : l ≠ j := by
    intro h
    apply hki
    have := congrArg π h
    rw [hl, hπ2', hj, hπ2'] at this
    exact this
  have hn : [i, j, k, l].Nodup := by
    simp [hij, Ne.symm hki, Ne.symm hli, Ne.symm hkj, Ne.symm hlj, hkl]
  have hls : l ∈ π.support := mem_support.mpr (by rw [hl, hπ2']; exact hkl)
  have hseq : π.support = {i, j, k, l} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [hsupp, Finset.card_insert_of_notMem (by simp [hij, Ne.symm hki, Ne.symm hli]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hkj, Ne.symm hlj]),
        Finset.card_pair hkl]
  refine ⟨i, j, k, l, hn, ?_, hseq⟩
  obtain ⟨hdi, hdj, hdk, hdl, hdF⟩ := dt_apply (π := swap i j * swap k l) rfl hn
  ext a
  by_cases ha : a ∈ π.support
  · rw [hseq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · rw [hdi]
    · rw [hdj, hj, hπ2']
    · rw [hdk]
    · rw [hdl, hl, hπ2']
  · have hfix : π a = a := by
      by_contra h
      exact ha (mem_support.mpr h)
    rw [hfix]
    rw [hseq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    rw [hdF a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2]

theorem exists_conj_le {G : Type} [Group G] [Finite G] {M R Q₀ : Subgroup G} {α : G}
    (hRM : R ≤ M) (hRα : R ≤ centralizer ({α} : Set G))
    (hRS : ∃ R' : Sylow 2 ↥M, (R' : Subgroup _) = R.subgroupOf M)
    (hQM : Q₀ ≤ M ⊓ centralizer ({α} : Set G)) (hQ2 : IsPGroup 2 Q₀) :
    ∃ c ∈ M ⊓ centralizer ({α} : Set G), ∀ g ∈ Q₀, c * g * c⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R', hR'⟩ := hRS
  set M₁ := M ⊓ centralizer ({α} : Set G) with hM₁
  have hRM₁ : R ≤ M₁ := le_inf hRM hRα
  have hM₁M : M₁ ≤ M := inf_le_left
  have hR2 : IsPGroup 2 ↥(R.subgroupOf M₁) := by
    rintro ⟨x, hx⟩
    rw [mem_subgroupOf] at hx
    have hxR' : (⟨x, hM₁M x.2⟩ : ↥M) ∈ (R' : Subgroup ↥M) := by
      rw [hR', mem_subgroupOf]
      exact hx
    obtain ⟨k, hk⟩ := R'.isPGroup' ⟨_, hxR'⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ↥(R' : Subgroup ↥M) => ((y : ↥M) : G)) hk
    simpa using this
  have hidx : ¬ 2 ∣ (R.subgroupOf M₁).index := by
    intro h2
    apply R'.not_dvd_index
    rw [hR']
    have h3 := Subgroup.relIndex_mul_relIndex R M₁ M hRM₁ hM₁M
    change 2 ∣ R.relIndex M
    rw [← h3]
    exact dvd_mul_of_dvd_left h2 _
  set R₁ : Sylow 2 ↥M₁ := hR2.toSylow hidx with hR₁
  have hQ₁ : IsPGroup 2 ↥(Q₀.subgroupOf M₁) := hQ2.comap_subtype
  obtain ⟨Q, hQ⟩ := hQ₁.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥M₁ Q R₁
  refine ⟨c, c.2, fun g hg => ?_⟩
  set g₁ : ↥M₁ := ⟨g, hQM hg⟩ with hg₁
  have hmem : c * g₁ * c⁻¹ ∈ (R₁ : Subgroup ↥M₁) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    have : g₁ ∈ (Q : Subgroup ↥M₁) := hQ (by rw [mem_subgroupOf]; exact hg)
    exact Subgroup.smul_mem_pointwise_smul g₁ (MulAut.conj c) _ this
  rw [hR₁, IsPGroup.toSylow_coe, mem_subgroupOf] at hmem
  simpa using hmem

end AltCent

end CFSG.ComponentClassification.CatFactsL4U4
