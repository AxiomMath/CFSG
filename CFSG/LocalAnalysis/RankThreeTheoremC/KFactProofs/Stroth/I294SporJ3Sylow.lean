module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

theorem sylowCentral_card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (a : A) :
    Nat.card (Subgroup.centralizer ({e a} : Set B)) =
      Nat.card (Subgroup.centralizer ({a} : Set A)) := by
  have hmap : (Subgroup.centralizer ({a} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set B) := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      have hac : a * c = c * a := hc a (Set.mem_singleton a)
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hac]
    · intro hb
      rw [Subgroup.mem_centralizer_iff] at hb
      refine ⟨e.symm b, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      apply e.injective
      have hab : e a * b = b * e a := hb (e a) (Set.mem_singleton _)
      simpa [map_mul] using hab
  rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem pow_three_dvd_card_centralizer_of_mem {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {P Z : Subgroup G} (hPp : ∃ k, Nat.card P = p ^ k)
    (hP3 : p ^ 3 ∣ Nat.card P) (hZP : Z ≤ P) (hZc : ∀ z ∈ Z, ∀ g ∈ P, Commute z g)
    (hZ : Nat.card Z = p ^ 2) {y : G} (hy : y ∈ P) :
    p ^ 3 ∣ Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  by_cases hyZ : y ∈ Z
  · have hPC : P ≤ Subgroup.centralizer ({y} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.2 (hZc y hyZ g hg).symm
    exact hP3.trans (Subgroup.card_dvd_of_le hPC)
  · set H : Subgroup G := Subgroup.closure (↑Z ∪ {y} : Set G) with hH
    have hHP : H ≤ P := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (hz | rfl)
      · exact hZP hz
      · exact hy
    have hHC : H ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (hz | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hZc _ hz y hy)
      · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hZH : Z ≤ H := fun z hz => Subgroup.subset_closure (Or.inl hz)
    have hyH : y ∈ H := Subgroup.subset_closure (Or.inr rfl)
    obtain ⟨k, hk⟩ := hPp
    have hHdvd : Nat.card H ∣ p ^ k := hk ▸ Subgroup.card_dvd_of_le hHP
    obtain ⟨m, -, hHm⟩ := (Nat.dvd_prime_pow hp.out).1 hHdvd
    have hm : 2 < m := by
      by_contra hle
      have hle1 : Nat.card Z ≤ Nat.card H := Subgroup.card_le_of_le hZH
      rw [hZ, hHm] at hle1
      have h2 : 2 ≤ m := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle1
      have hm2 : m = 2 := by omega
      have hHZ : Z = H := Subgroup.eq_of_le_of_card_ge hZH (by rw [hZ, hHm, hm2])
      exact hyZ (hHZ ▸ hyH)
    exact (pow_dvd_pow p hm).trans (hHm ▸ Subgroup.card_dvd_of_le hHC)

theorem pow_three_dvd_card_centralizer_of_sylow_central {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] {P Z : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) (hP3 : p ^ 3 ∣ Nat.card P)
    (hZP : Z ≤ P) (hZc : ∀ z ∈ Z, ∀ g ∈ P, Commute z g) (hZ : Nat.card Z = p ^ 2) {x : G}
    (hx : orderOf x = p) : p ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  let S : Sylow p G := Sylow.ofCard P hP
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hxQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hxg : x ∈ (g • S : Sylow p G) := by
    rw [hg]
    exact hxQ (Subgroup.mem_zpowers x)
  have hy : g⁻¹ * x * g ∈ P := by
    have h : x ∈ (MulAut.conj g • (S : Subgroup G)) := hxg
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    have h' : g⁻¹ * x * g ∈ (S : Subgroup G) := by simpa [MulAut.conj_inv_apply] using h
    exact h'
  have hcard := sylowCentral_card_centralizer_mulEquiv (MulAut.conj g⁻¹) x
  have hconj : (MulAut.conj g⁻¹) x = g⁻¹ * x * g := by simp [MulAut.conj_apply]
  rw [hconj] at hcard
  rw [← hcard]
  exact pow_three_dvd_card_centralizer_of_mem ⟨_, hP⟩ hP3 hZP hZc hZ hy

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
