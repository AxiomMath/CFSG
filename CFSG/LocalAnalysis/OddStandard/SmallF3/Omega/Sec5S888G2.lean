module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Inv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888_sup_comm {A B C : Subgroup G}
    (hA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hB : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    ∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c = c * x := by
  intro x hx c hc
  have hle : A ⊔ B ≤ centralizer ({c} : Set G) := by
    apply sup_le
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hA a ha c hc
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hB b hb c hc
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

private lemma s888_comm_sup_right {A C D : Subgroup G}
    (hC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) {a : G} (ha : a ∈ A) {y : G}
    (hy : y ∈ C ⊔ D) : a * y = y * a := by
  have hle : C ⊔ D ≤ centralizer ({a} : Set G) := by
    apply sup_le
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hC a ha c hc).symm
    · intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hD a ha d hd).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

private lemma s888_cancel_right {a b v : G} (hbv : b * v = v * b)
    (h : (a * b) * v = v * (a * b)) : a * v = v * a := by
  have h1 : (a * b) * v = (a * v) * b := by
    calc (a * b) * v = a * (b * v) := mul_assoc a b v
      _ = a * (v * b) := by rw [hbv]
      _ = (a * v) * b := (mul_assoc a v b).symm
  have h2 : v * (a * b) = (v * a) * b := (mul_assoc v a b).symm
  exact mul_right_cancel (by rw [← h1, h, h2])

private lemma s888_cancel_left {a b v : G} (hav : a * v = v * a)
    (h : (a * b) * v = v * (a * b)) : b * v = v * b := by
  have h1 : (a * b) * v = a * (b * v) := mul_assoc a b v
  have h2 : v * (a * b) = a * (v * b) := by
    calc v * (a * b) = v * a * b := (mul_assoc v a b).symm
      _ = a * v * b := by rw [← hav]
      _ = a * (v * b) := mul_assoc a v b
  exact mul_left_cancel (by rw [← h1, h, h2])

private lemma s888_le_centralizer_of_le_mul_right {i : Fin 4} {a b : G}
    (hbi : K i ≤ centralizer ({b} : Set G))
    (habi : K i ≤ centralizer ({a * b} : Set G)) :
    K i ≤ centralizer ({a} : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (s888_cancel_right (Subgroup.mem_centralizer_singleton_iff.mp (hbi hv)).symm
    (Subgroup.mem_centralizer_singleton_iff.mp (habi hv)).symm).symm

private lemma s888_le_centralizer_of_le_mul_left {i : Fin 4} {a b : G}
    (hai : K i ≤ centralizer ({a} : Set G))
    (habi : K i ≤ centralizer ({a * b} : Set G)) :
    K i ≤ centralizer ({b} : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (s888_cancel_left (Subgroup.mem_centralizer_singleton_iff.mp (hai hv)).symm
    (Subgroup.mem_centralizer_singleton_iff.mp (habi hv)).symm).symm

private lemma s888_not_le_centralizer_left (hq : Sec5B517Quad K z) {i j : Fin 4}
    (hij : i ≠ j) {d : G} (hd : d ∈ K i ⊔ K j) (hd2 : d * d = 1) (hd1 : d ≠ 1)
    (hdz : d ≠ z) : ¬ K i ≤ centralizer ({d} : Set G) := by
  intro hle
  obtain ⟨a, ha, b, hb, hd_eq⟩ := sec5b_mem_sup_of_comm (hq.comm i j hij) hd
  have hacent : ∀ v ∈ K i, a * v = v * a := by
    intro v hv
    have hdv : (a * b) * v = v * (a * b) := by
      have h' := hle hv
      rw [Subgroup.mem_centralizer_singleton_iff] at h'
      rw [hd_eq] at h'
      exact h'.symm
    exact s888_cancel_right (hq.comm j i hij.symm b hb v hv) hdv
  rcases hq.eq_of_central ha hacent with ha1 | haz
  · subst ha1
    have hdj : d ∈ K j := by rw [hd_eq, one_mul]; exact hb
    rcases hq.eq_of_sq hdj hd2 with h | h
    · exact hd1 h
    · exact hdz h
  · subst haz
    have hdj : d ∈ K j := by rw [hd_eq]; exact (K j).mul_mem (hq.z_mem j) hb
    rcases hq.eq_of_sq hdj hd2 with h | h
    · exact hd1 h
    · exact hdz h

theorem Sec5B517Quad.not_le_centralizer_of_mem_pair (hq : Sec5B517Quad K z) {i j : Fin 4}
    (hij : i ≠ j) {d : G} (hd : d ∈ K i ⊔ K j) (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z) :
    ¬ K i ≤ centralizer ({d} : Set G) ∧ ¬ K j ≤ centralizer ({d} : Set G) :=
  ⟨s888_not_le_centralizer_left hq hij hd hd2 hd1 hdz,
    s888_not_le_centralizer_left hq hij.symm (by rwa [sup_comm]) hd2 hd1 hdz⟩

theorem Sec5B517Quad.mul_pair_props (hq : Sec5B517Quad K z) {a b : G}
    (ha : a ∈ K 0 ⊔ K 1) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hb : b ∈ K 2 ⊔ K 3) (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbz : b ≠ z) :
    (a * b) * (a * b) = 1 ∧ a * b ≠ 1 ∧ a * b ≠ z ∧ a * b ∈ Sec5B517Q8 hq ∧
      ∀ i : Fin 4, ¬ K i ≤ centralizer ({a * b} : Set G) := by
  have h01_2 : ∀ x ∈ K 0 ⊔ K 1, ∀ y ∈ K 2, x * y = y * x :=
    s888_sup_comm (hq.comm 0 2 (by decide)) (hq.comm 1 2 (by decide))
  have h01_3 : ∀ x ∈ K 0 ⊔ K 1, ∀ y ∈ K 3, x * y = y * x :=
    s888_sup_comm (hq.comm 0 3 (by decide)) (hq.comm 1 3 (by decide))
  have hcomm : Commute a b := s888_comm_sup_right h01_2 h01_3 ha hb
  have haQ : a ∈ Sec5B517Q8 hq :=
    Sec5B517Quad.pair_mem_Q8 hq (by decide : (0 : Fin 4) ≠ 1) ha ha2 ha1 haz
  have hbQ : b ∈ Sec5B517Q8 hq :=
    Sec5B517Quad.pair_mem_Q8 hq (by decide : (2 : Fin 4) ≠ 3) hb hb2 hb1 hbz
  have hmem : a * b ∈ Sec5B517Q8 hq := (Sec5B517Q8 hq).mul_mem haQ hbQ
  have hsq : (a * b) * (a * b) = 1 := by
    rw [← pow_two (a * b), hcomm.mul_pow 2, pow_two a, pow_two b, ha2, hb2, mul_one]
  have hnota : ¬ K 0 ≤ centralizer ({a} : Set G) ∧ ¬ K 1 ≤ centralizer ({a} : Set G) :=
    Sec5B517Quad.not_le_centralizer_of_mem_pair hq (i := 0) (j := 1) (by decide) ha ha2 ha1 haz
  have hnotb : ¬ K 2 ≤ centralizer ({b} : Set G) ∧ ¬ K 3 ≤ centralizer ({b} : Set G) :=
    Sec5B517Quad.not_le_centralizer_of_mem_pair hq (i := 2) (j := 3) (by decide) hb hb2 hb1 hbz
  have h0b : K 0 ≤ centralizer ({b} : Set G) :=
    Sec5B517Quad.le_centralizer_of_mem_pair hq (l := 0) (i := 2) (j := 3)
      (by decide) (by decide) hb
  have h1b : K 1 ≤ centralizer ({b} : Set G) :=
    Sec5B517Quad.le_centralizer_of_mem_pair hq (l := 1) (i := 2) (j := 3)
      (by decide) (by decide) hb
  have h2a : K 2 ≤ centralizer ({a} : Set G) :=
    Sec5B517Quad.le_centralizer_of_mem_pair hq (l := 2) (i := 0) (j := 1)
      (by decide) (by decide) ha
  have h3a : K 3 ≤ centralizer ({a} : Set G) :=
    Sec5B517Quad.le_centralizer_of_mem_pair hq (l := 3) (i := 0) (j := 1)
      (by decide) (by decide) ha
  have hnc : ∀ i : Fin 4, ¬ K i ≤ centralizer ({a * b} : Set G) := by
    intro i
    fin_cases i
    · intro hle
      exact hnota.1 (s888_le_centralizer_of_le_mul_right h0b hle)
    · intro hle
      exact hnota.2 (s888_le_centralizer_of_le_mul_right h1b hle)
    · intro hle
      exact hnotb.1 (s888_le_centralizer_of_le_mul_left h2a hle)
    · intro hle
      exact hnotb.2 (s888_le_centralizer_of_le_mul_left h3a hle)
  have hne1 : a * b ≠ 1 := by
    intro h
    exact hnc 0 (by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff, h, mul_one, one_mul])
  have hnez : a * b ≠ z := by
    intro h
    exact hnc 0 (by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff, h]
      exact (hq.z_comm hv).symm)
  exact ⟨hsq, hne1, hnez, hmem, hnc⟩

end CFSG.OddStandard.SmallF3.Omega
