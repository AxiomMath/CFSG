module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Pair
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma sec5_fin4_cover {i j l m n : Fin 4} (hij : i ≠ j) (hlm : l ≠ m) (hli : l ≠ i)
    (hlj : l ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) : n = i ∨ n = j ∨ n = l ∨ n = m := by
  revert i j l m n
  decide

private lemma sec5_fin4_two_compl {i j l m u v : Fin 4} (hij : i ≠ j) (hlm : l ≠ m)
    (hli : l ≠ i) (hlj : l ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) (huv : u ≠ v)
    (hui : u ≠ i) (huj : u ≠ j) (hvi : v ≠ i) (hvj : v ≠ j) :
    (u = l ∧ v = m) ∨ (u = m ∧ v = l) := by
  revert i j l m u v
  decide

private lemma sec5_sq_of_orderOf_two {d : G} (hd2 : orderOf d = 2) : d * d = 1 := by
  rw [← pow_two, ← hd2, pow_orderOf_eq_one]

private lemma sec5_ne_one_of_orderOf_two {d : G} (hd2 : orderOf d = 2) : d ≠ 1 := by
  intro h1
  rw [h1, orderOf_one] at hd2
  omega

private lemma sec5_pair_of_quad_direct {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) : Sec5Pair (K i) (K j) z :=
  ⟨hq.comm i j hij, hq.iso i, hq.iso j, hq.z_mem i, hq.z_mem j, hq.z_sq, hq.z_ne⟩

private lemma sec5_pair_decomp_sq {K : Fin 4 → Subgroup G} {z : G} (hq : Sec5B517Quad K z)
    {i j : Fin 4} (hij : i ≠ j) {d : G} (hd : d ∈ K i ⊔ K j) (hd_sq : d * d = 1)
    (hd1 : d ≠ 1) (hdz : d ≠ z) :
    ∃ a ∈ K i, ∃ b ∈ K j, d = a * b ∧ a * a = z ∧ b * b = z := by
  obtain ⟨a, ha, b, hb, hd_eq⟩ := sec5b_mem_sup_of_comm (hq.comm i j hij) hd
  have hab_eq : a * b = b * a := hq.comm i j hij a ha b hb
  have hab : Commute a b := hab_eq
  have hsq : a * a * (b * b) = 1 := by
    have h1 : (a * b) * (a * b) = 1 := by rw [← hd_eq]; exact hd_sq
    rwa [← pow_two (a * b), hab.mul_pow 2, pow_two a, pow_two b] at h1
  have huKj : a * a ∈ K j := by
    have hu_eq : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [hu_eq]
    exact (K j).inv_mem ((K j).mul_mem hb hb)
  have hcent : ∀ v ∈ K i, (a * a) * v = v * (a * a) := fun v hv =>
    hq.comm j i hij.symm (a * a) huKj v hv
  rcases hq.eq_of_central ((K i).mul_mem ha ha) hcent with h1 | hz
  · have hb1 : b * b = 1 := by
      rw [h1, one_mul] at hsq
      exact hsq
    have hd_or : d = 1 ∨ d = z := by
      rcases hq.eq_of_sq ha h1 with ha1 | haz <;>
        rcases hq.eq_of_sq hb hb1 with hb1' | hbz
      · left; rw [hd_eq, ha1, hb1', mul_one]
      · right; rw [hd_eq, ha1, hbz, one_mul]
      · right; rw [hd_eq, haz, hb1', mul_one]
      · left; rw [hd_eq, haz, hbz, hq.z_sq]
    rcases hd_or with hd_or | hd_or
    · exact absurd hd_or hd1
    · exact absurd hd_or hdz
  · have hb2 : b * b = z := by
      have h2 : z * (b * b) = z * z := by rw [← hz, hsq, hz, hq.z_sq]
      exact mul_left_cancel h2
    exact ⟨a, ha, b, hb, hd_eq, hz, hb2⟩

private lemma sec5_ki_not_le_centralizer {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a b d : G} (ha : a ∈ K i)
    (hb : b ∈ K j) (hd : d = a * b) (ha2 : a * a = z) :
    ¬ K i ≤ centralizer ({d} : Set G) := by
  intro hle
  have hcent : ∀ v ∈ K i, a * v = v * a := by
    intro v hv
    have hvd : v * d = d * v := by
      have h1 := hle hv
      rwa [Subgroup.mem_centralizer_singleton_iff] at h1
    have hvb : v * b = b * v := hq.comm i j hij v hv b hb
    have key : v * a * b = a * v * b := by
      calc v * a * b = v * (a * b) := by group
        _ = v * d := by rw [hd]
        _ = d * v := hvd
        _ = (a * b) * v := by rw [hd]
        _ = a * (b * v) := by group
        _ = a * (v * b) := by rw [hvb]
        _ = a * v * b := by group
    exact mul_right_cancel key.symm
  rcases hq.eq_of_central ha hcent with h1 | hz
  · rw [h1, one_mul] at ha2
    exact hq.z_ne ha2.symm
  · rw [hz, hq.z_sq] at ha2
    exact hq.z_ne ha2.symm

theorem sec5_pair_of_gamma (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {P P' : Subgroup G} (hP : P ∈ Gamma5 K₁ K₂ h) (hP' : P' ∈ Gamma5 K₁ K₂ h) (hne : P ≠ P') :
    Sec5Pair P P' z := by
  rw [sec5b517_gamma_eq] at hP hP'
  obtain ⟨i, rfl⟩ := hP
  obtain ⟨j, rfl⟩ := hP'
  have hij : i ≠ j := fun hij => hne (by rw [hij])
  exact sec5_pair_of_quad_direct (sec5b517_quad h514 c) hij

theorem sec5_delta_support (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G}
    (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h)) :
    ∃ i j : Fin 4, i ≠ j ∧ d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j := by
  obtain ⟨hd2, hdz, P, hP, P', hP', hPP', hdP⟩ := hd
  rw [sec5b517_gamma_eq] at hP hP'
  obtain ⟨i, rfl⟩ := hP
  obtain ⟨j, rfl⟩ := hP'
  exact ⟨i, j, fun hij => hPP' (by rw [hij]), hdP⟩

theorem sec5_mem_delta_of_pair (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {i j : Fin 4} (hij : i ≠ j) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) : d ∈ Delta5 z (Gamma5 K₁ K₂ h) := by
  have hq := sec5b517_quad h514 c
  exact ⟨hd2, hdz, Kfam5 K₁ K₂ h i,
    by rw [sec5b517_gamma_eq]; exact Set.mem_range_self i,
    Kfam5 K₁ K₂ h j,
    by rw [sec5b517_gamma_eq]; exact Set.mem_range_self j,
    hq.ne hij, hd⟩

theorem sec5_kOf_iff (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {i j l m : Fin 4} (hij : i ≠ j) (hlm : l ≠ m) (hli : l ≠ i) (hlj : l ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) (P : Subgroup G) :
    IsKOf (Gamma5 K₁ K₂ h) d P ↔ P = Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m := by
  have hq := sec5b517_quad h514 c
  have hd_sq : d * d = 1 := sec5_sq_of_orderOf_two hd2
  have hd1 : d ≠ 1 := sec5_ne_one_of_orderOf_two hd2
  obtain ⟨a, ha, b, hb, hd_eq, ha2, hb2⟩ := sec5_pair_decomp_sq hq hij hd hd_sq hd1 hdz
  have hab : a * b = b * a := hq.comm i j hij a ha b hb
  have hkj : ¬ Kfam5 K₁ K₂ h j ≤ centralizer ({d} : Set G) :=
    sec5_ki_not_le_centralizer hq hij.symm hb ha (by rw [hd_eq, hab]) hb2
  constructor
  · rintro ⟨P₁, hP₁, P₂, hP₂, hP₁P₂, hP_eq, hP_le⟩
    rw [sec5b517_gamma_eq] at hP₁ hP₂
    obtain ⟨u, rfl⟩ := hP₁
    obtain ⟨v, rfl⟩ := hP₂
    have huv : u ≠ v := fun huv => hP₁P₂ (by rw [huv])
    have hP_le' : Kfam5 K₁ K₂ h u ⊔ Kfam5 K₁ K₂ h v ≤ centralizer ({d} : Set G) := by
      rw [← hP_eq]; exact hP_le
    have hu_le : Kfam5 K₁ K₂ h u ≤ centralizer ({d} : Set G) :=
      le_trans le_sup_left hP_le'
    have hv_le : Kfam5 K₁ K₂ h v ≤ centralizer ({d} : Set G) :=
      le_trans le_sup_right hP_le'
    have hui : u ≠ i := fun hui =>
      sec5_ki_not_le_centralizer hq hij ha hb hd_eq ha2 (hui ▸ hu_le)
    have hvi : v ≠ i := fun hvi =>
      sec5_ki_not_le_centralizer hq hij ha hb hd_eq ha2 (hvi ▸ hv_le)
    have huj : u ≠ j := fun huj => hkj (huj ▸ hu_le)
    have hvj : v ≠ j := fun hvj => hkj (hvj ▸ hv_le)
    rcases sec5_fin4_two_compl hij hlm hli hlj hmi hmj huv hui huj hvi hvj with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP_eq
    · exact hP_eq.trans (sup_comm _ _)
  · intro hP
    rw [hP]
    refine ⟨Kfam5 K₁ K₂ h l, ?_, Kfam5 K₁ K₂ h m, ?_, hq.ne hlm, rfl, ?_⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range_self l
    · rw [sec5b517_gamma_eq]; exact Set.mem_range_self m
    · exact sup_le (Sec5B517Quad.le_centralizer_of_mem_pair hq hli hlj hd)
        (Sec5B517Quad.le_centralizer_of_mem_pair hq hmi hmj hd)

theorem sec5_exists_compl (i j : Fin 4) (hij : i ≠ j) :
    ∃ l m : Fin 4, l ≠ m ∧ l ≠ i ∧ l ≠ j ∧ m ≠ i ∧ m ≠ j := by
  revert i j
  decide

theorem sec5_gamma_eq_quad {i j l m : Fin 4} (hij : i ≠ j) (hlm : l ≠ m) (hli : l ≠ i)
    (hlj : l ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) : Gamma5 K₁ K₂ h =
      {Kfam5 K₁ K₂ h i, Kfam5 K₁ K₂ h j, Kfam5 K₁ K₂ h l, Kfam5 K₁ K₂ h m} := by
  rw [sec5b517_gamma_eq]
  ext P
  constructor
  · rintro ⟨n, rfl⟩
    have hn : n = i ∨ n = j ∨ n = l ∨ n = m :=
      sec5_fin4_cover hij hlm hli hlj hmi hmj
    rcases hn with rfl | rfl | rfl | rfl <;> simp
  · intro hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact Set.mem_range_self i
    · exact Set.mem_range_self j
    · exact Set.mem_range_self l
    · exact Set.mem_range_self m

end CFSG.OddStandard.SmallF3.Omega
