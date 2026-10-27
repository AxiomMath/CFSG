module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Inv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem sec5b517_kfam0 : Kfam5 K₁ K₂ h 0 = K₁ := by
  simp [Kfam5]

private theorem sec5b517_kfam1 : Kfam5 K₁ K₂ h 1 = K₂ := by
  simp [Kfam5]

private theorem sec5b517_kfam2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by
  simp [Kfam5]

private theorem sec5b517_kfam3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by
  simp [Kfam5]

theorem sec5b517_quad (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Sec5B517Quad (Kfam5 K₁ K₂ h) z := by
  have h14 := h514 G t L S z r B A K₁ K₂ h c
  refine ⟨?_, ?_, ?_, c.z_mul_self, c.z_ne_one⟩
  · intro i j hij a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅Kfam5 K₁ K₂ h i, Kfam5 K₁ K₂ h j⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [h14.2.1 i j hij, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · intro i
    exact h14.2.2 i
  · intro i
    fin_cases i <;>
      simp only [Kfam5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]
    · exact c.z_mem_K₁
    · exact c.z_mem_K₂
    · exact c.z_mem_K₃
    · exact c.z_mem_K₄

theorem sec5b517_gamma_eq : Gamma5 K₁ K₂ h = Set.range (Kfam5 K₁ K₂ h) := by
  ext P
  constructor
  · intro hP
    simp only [Gamma5, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact ⟨0, sec5b517_kfam0⟩
    · exact ⟨1, sec5b517_kfam1⟩
    · exact ⟨2, sec5b517_kfam2⟩
    · exact ⟨3, sec5b517_kfam3⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;>
      simp [Gamma5, Kfam5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]

theorem sec5b517_all_eq : Sec5B517All (Kfam5 K₁ K₂ h) =
    K₁ ⊔ K₂ ⊔ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := rfl

theorem sec5b517_Qsub_eq :
    Qsub K₁ K₂ h = twoCoreIn (Sec5B517All (Kfam5 K₁ K₂ h)) := rfl

theorem sec5b517_normalizer_le (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    normalizer (Qsub K₁ K₂ h : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have hq := sec5b517_quad h514 c
  have hzQ : z ∈ Qsub K₁ K₂ h := by
    have hz8 : z ∈ Sec5B517Q8 hq := hq.core_eq ▸ hq.z_mem_core
    rwa [sec5b517_Qsub_eq, hq.core_eq]
  have hwQ : n * z * n⁻¹ ∈ Qsub K₁ K₂ h :=
    (Subgroup.mem_normalizer_iff.mp hn z).mp hzQ
  have hwQ' : n * z * n⁻¹ ∈ twoCoreIn (Sec5B517All (Kfam5 K₁ K₂ h)) := by
    rwa [sec5b517_Qsub_eq] at hwQ
  have hcent : ∀ x ∈ twoCoreIn (Sec5B517All (Kfam5 K₁ K₂ h)),
      (n * z * n⁻¹) * x = x * (n * z * n⁻¹) := by
    intro x hx
    have hxQ : x ∈ Qsub K₁ K₂ h := by rwa [sec5b517_Qsub_eq]
    have hx' : n⁻¹ * x * n ∈ Qsub K₁ K₂ h := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hn) x).mp hxQ
    have hx8 : n⁻¹ * x * n ∈ Sec5B517Q8 hq := by
      rwa [sec5b517_Qsub_eq, hq.core_eq] at hx'
    have hxK : n⁻¹ * x * n ∈ Sec5B517All (Kfam5 K₁ K₂ h) := Sec5B517Q8.le_all hq hx8
    have hcomm : z * (n⁻¹ * x * n) = (n⁻¹ * x * n) * z := hq.z_comm_all hxK
    calc (n * z * n⁻¹) * x = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by rw [hcomm]
      _ = x * (n * z * n⁻¹) := by group
  have hw1 : n * z * n⁻¹ ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      have h2 := congrArg (fun y => n⁻¹ * y * n) h1
      simpa [mul_assoc] using h2
    exact c.z_ne_one hz1
  rcases hq.central_core hwQ' hcent with h1 | hz
  · exact absurd h1 hw1
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg (fun y => y * n) hz
    simpa [mul_assoc] using h2

theorem sec5b517_delta_mem_Q (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {d : G} (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h)) : d ∈ Qsub K₁ K₂ h := by
  obtain ⟨hd2, hdz, P, hP, P', hP', hPP', hdP⟩ := hd
  rw [sec5b517_gamma_eq] at hP hP'
  obtain ⟨i, rfl⟩ := hP
  obtain ⟨j, rfl⟩ := hP'
  have hij : i ≠ j := by
    intro hij
    exact hPP' (by rw [hij])
  have hd_sq : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
  have hd_ne1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd2
    omega
  have hq := sec5b517_quad h514 c
  have hmem := hq.pair_mem_Q8 hij hdP hd_sq hd_ne1 hdz
  rwa [sec5b517_Qsub_eq, hq.core_eq]

theorem sec5b517_delta_not_conj (h37 : Asc82Lemma37) (h515c : Asc82Lemma515c)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h)) :
    ∀ g : G, g⁻¹ * z * g ≠ d := by
  obtain ⟨S', r', B', A', P₁, P₂, h', c', -⟩ :=
    h515c G t L S z r B A K₁ K₂ h c d hd
  intro g
  exact sec5_t_not_conj_z h37 c'.toSec5Ctx g

theorem sec5b517_mem_delta (h514 : Asc82Lemma514) (fuse : Asc82Fact517Fuse)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hdQ : d ∈ Qsub K₁ K₂ h)
    (hd2 : orderOf d = 2) (hnc : ∀ g : G, g⁻¹ * z * g ≠ d) :
    d ∈ Delta5 z (Gamma5 K₁ K₂ h) := by
  have hq := sec5b517_quad h514 c
  have hdz : d ≠ z := by
    intro h1
    exact hnc 1 (by simpa using h1.symm)
  have hdQ8 : d ∈ Sec5B517Q8 hq := by
    rwa [sec5b517_Qsub_eq, hq.core_eq] at hdQ
  have hd_sq : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
  have hd_ne1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd2
    omega
  obtain ⟨m, hm, hd₀mem, hd₀ne⟩ := fuse G t L S z r B A K₁ K₂ h c
  set d₀ : G := m⁻¹ * z * m with hd₀def
  have hd₀_props : orderOf d₀ = 2 ∧ d₀ ∈ Qsub K₁ K₂ h ∧
      ∀ P ∈ Gamma5 K₁ K₂ h, ¬ P ≤ centralizer ({d₀} : Set G) := by
    rcases hd₀mem with h1 | h1
    · exact absurd h1 hd₀ne
    · exact h1
  have hd₀Q8 : d₀ ∈ Sec5B517Q8 hq := by
    rw [← hq.core_eq, ← sec5b517_Qsub_eq]
    exact hd₀_props.2.1
  have hd₀_sq : d₀ * d₀ = 1 := by rw [← pow_two, ← hd₀_props.1, pow_orderOf_eq_one]
  have hd₀_ne1 : d₀ ≠ 1 := by
    intro h1
    have h2 : orderOf (1 : G) = 2 := h1 ▸ hd₀_props.1
    rw [orderOf_one] at h2
    omega
  have hd₀_nc : ∀ i : Fin 4, ¬ Kfam5 K₁ K₂ h i ≤ centralizer ({d₀} : Set G) := by
    intro i hi
    exact hd₀_props.2.2 (Kfam5 K₁ K₂ h i)
      (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩) hi
  obtain ⟨k₀, hk₀, hd₀k⟩ := hq.type4_of_noncentral hd₀Q8 hd₀_sq hd₀_ne1 hd₀ne hd₀_nc
  rcases hq.invol_cases hdQ8 hd_sq hd_ne1 hdz with ⟨k, hk, hdk⟩ | ⟨i, j, hij, hdij⟩
  · obtain ⟨y, hy⟩ := hq.type4_conj hk₀ hk
    have hz_eq : z = m * d₀ * m⁻¹ := by rw [hd₀def]; group
    have hconj : (m * y)⁻¹ * z * (m * y) = d := by
      have h1 : (m * y)⁻¹ * z * (m * y) = y⁻¹ * d₀ * y := by
        rw [hz_eq]; group
      rw [h1, hd₀k, hy, ← hdk]
    exact absurd hconj (hnc (m * y))
  · refine ⟨hd2, hdz, Kfam5 K₁ K₂ h i, ?_, Kfam5 K₁ K₂ h j, ?_, hq.ne hij, hdij⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range_self i
    · rw [sec5b517_gamma_eq]; exact Set.mem_range_self j

theorem sec5b517_delta_conj (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h515c : Asc82Lemma515c) (fuse : Asc82Fact517Fuse)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {n : G}
    (hn : n ∈ normalizer (Qsub K₁ K₂ h : Set G)) {d : G}
    (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h)) : n⁻¹ * d * n ∈ Delta5 z (Gamma5 K₁ K₂ h) := by
  have hdQ : d ∈ Qsub K₁ K₂ h := sec5b517_delta_mem_Q h514 c hd
  have hdQ' : n⁻¹ * d * n ∈ Qsub K₁ K₂ h := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hn) d).mp hdQ
  have hd2 : orderOf (n⁻¹ * d * n) = 2 := by
    rw [← hd.1]
    exact (SemiconjBy.orderOf_eq n⁻¹ (by
      show n⁻¹ * d = (n⁻¹ * d * n) * n⁻¹
      group)).symm
  have hnc' : ∀ g : G, g⁻¹ * z * g ≠ n⁻¹ * d * n := by
    intro g hg
    have hconj : (g * n⁻¹)⁻¹ * z * (g * n⁻¹) = d := by
      have h1 : (g * n⁻¹)⁻¹ * z * (g * n⁻¹) = n * (g⁻¹ * z * g) * n⁻¹ := by group
      rw [h1, hg]; group
    exact (sec5b517_delta_not_conj h37 h515c c hd (g * n⁻¹)) hconj
  exact sec5b517_mem_delta h514 fuse c hdQ' hd2 hnc'

end CFSG.OddStandard.SmallF3.Omega
