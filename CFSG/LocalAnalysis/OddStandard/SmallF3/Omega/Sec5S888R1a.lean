module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

@[expose] def Sec5B517Q8.pair (hq : Sec5B517Quad K z) (i j : Fin 4) : Subgroup G :=
  Sec5B517Q8 hq ⊓ (K i ⊔ K j)

private theorem s888r1a_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem s888r1a_isPGroup_twoCoreIn (X : Subgroup G) : IsPGroup 2 (twoCoreIn X) := by
  unfold twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype

private theorem s888r1a_le_twoCoreIn_of_normal {X P : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hn : (P.subgroupOf X).Normal) : P ≤ twoCoreIn X := by
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hn, hP2'⟩
  calc
    P = (P.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hPX).symm
    _ ≤ (CFSG.pCore 2 ↥X).map X.subtype := Subgroup.map_mono hle
    _ = twoCoreIn X := rfl

private theorem s888r1a_mem_all_of_mem {i : Fin 4} {x : G} (hx : x ∈ K i) :
    x ∈ Sec5B517All K := by
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  · exact Subgroup.mem_sup_right hx

private theorem s888r1a_sup_le_all (i j : Fin 4) : K i ⊔ K j ≤ Sec5B517All K :=
  sup_le (fun _ hx => s888r1a_mem_all_of_mem (i := i) hx)
    (fun _ hx => s888r1a_mem_all_of_mem (i := j) hx)

private lemma s888r1a_iso_z_eq_neg_one (hq : Sec5B517Quad K z) {i : Fin 4}
    (e : ↥(K i) ≃* SL23) : e ⟨z, hq.z_mem i⟩ = -1 := by
  have hsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul]
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) * ⟨z, hq.z_mem i⟩ = 1 :=
      Subtype.ext (by simpa using hq.z_sq)
    rw [hsub, map_one]
  rcases sl23_unique_involution _ hsq with h1 | hneg
  · exfalso
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h1, map_one])
    exact hq.z_ne (congrArg Subtype.val hsub)
  · exact hneg

private lemma s888r1a_comm_mem_zpowers (hq : Sec5B517Quad K z) {i : Fin 4} {u v : G}
    (hu : u ∈ K i) (hu4 : u ^ 4 = 1) (hv : v ∈ K i) (hv4 : v ^ 4 = 1) :
    u * v * u⁻¹ * v⁻¹ ∈ zpowers z := by
  obtain ⟨e⟩ := hq.iso i
  have hzu : e ⟨z, hq.z_mem i⟩ = -1 := s888r1a_iso_z_eq_neg_one hq e
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := by
    have hsub : (⟨u, hu⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hu4)
    rw [← map_pow, hsub, map_one]
  have hv4' : (e ⟨v, hv⟩) ^ 4 = 1 := by
    have hsub : (⟨v, hv⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hv4)
    rw [← map_pow, hsub, map_one]
  have hmap : e (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) =
      e ⟨u, hu⟩ * e ⟨v, hv⟩ * (e ⟨u, hu⟩)⁻¹ * (e ⟨v, hv⟩)⁻¹ := by
    simp only [map_mul, map_inv]
  rcases (sl23_q8_comm_sq (e ⟨u, hu⟩) (e ⟨v, hv⟩) hu4' hv4').1 with hc | hc
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = 1 := by
      apply e.injective
      rw [hmap, hc]
      exact (map_one e).symm
    have hG : u * v * u⁻¹ * v⁻¹ = 1 := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact (zpowers z).one_mem
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := by
      apply e.injective
      rw [hmap, hc]
      exact hzu.symm
    have hG : u * v * u⁻¹ * v⁻¹ = z := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact Subgroup.mem_zpowers z

private lemma s888r1a_prod_commutator (hq : Sec5B517Quad K z) {k l : Fin 4 → G}
    (hk : ∀ i, k i ∈ K i) (hl : ∀ i, l i ∈ K i) :
    Sec5B517Prod k * Sec5B517Prod l * (Sec5B517Prod k)⁻¹ * (Sec5B517Prod l)⁻¹ =
      Sec5B517Prod (fun i => k i * l i * (k i)⁻¹ * (l i)⁻¹) := by
  simp only [sec5b517_prod_inv hq hk, sec5b517_prod_inv hq hl,
    sec5b517_prod_mul hq hk hl,
    sec5b517_prod_mul hq (fun i => (K i).mul_mem (hk i) (hl i))
      (fun i => (K i).inv_mem (hk i)),
    sec5b517_prod_mul hq
      (fun i => (K i).mul_mem ((K i).mul_mem (hk i) (hl i)) ((K i).inv_mem (hk i)))
      (fun i => (K i).inv_mem (hl i))]

theorem Sec5B517Q8.mem_pair_iff (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {x : G} :
    x ∈ Sec5B517Q8.pair hq i j ↔
      ∃ a ∈ K i, ∃ b ∈ K j, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ x = a * b := by
  constructor
  · rintro ⟨hxQ, hxX⟩
    obtain ⟨a, ha, b, hb, hx_eq⟩ := sec5b_mem_sup_of_comm (hq.comm i j hij) hxX
    have hx4 : x ^ 4 = 1 := Sec5B517Q8.pow_four hq hxQ
    have hab : Commute a b := hq.comm i j hij a ha b hb
    have hxab4 : (a * b) ^ 4 = 1 := by rw [← hx_eq]; exact hx4
    have hprod : a ^ 4 * b ^ 4 = 1 := by
      rw [← hab.mul_pow 4]
      exact hxab4
    have ha4Kj : a ^ 4 ∈ K j := by
      have h : a ^ 4 = (b ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      rw [h]
      exact (K j).inv_mem ((K j).pow_mem hb 4)
    have ha4_cent : ∀ v ∈ K i, a ^ 4 * v = v * a ^ 4 :=
      fun v hv => hq.comm j i hij.symm (a ^ 4) ha4Kj v hv
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hq.z_sq
    have ha8 : a ^ (2 ^ 3) = 1 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
      rcases hq.eq_of_central ((K i).pow_mem ha 4) ha4_cent with h1 | hz
      · rw [h1, one_pow]
      · rw [hz, hz2]
    have ha4 : a ^ 4 = 1 := hq.pow4_of_pow ha ha8
    have hb4 : b ^ 4 = 1 := by
      have h := hprod
      rw [ha4, one_mul] at h
      exact h
    exact ⟨a, ha, b, hb, ha4, hb4, hx_eq⟩
  · rintro ⟨a, ha, b, hb, ha4, hb4, rfl⟩
    exact ⟨(Sec5B517Q8 hq).mul_mem (Sec5B517Q8.mem_of_mem hq ha ha4)
      (Sec5B517Q8.mem_of_mem hq hb hb4), Subgroup.mul_mem_sup ha hb⟩

theorem Sec5B517Q8.mem_pair_of_sq (hq : Sec5B517Quad K z) {i j : Fin 4} {x : G}
    (hx : x ∈ K i ⊔ K j) (hx2 : x * x = 1) : x ∈ Sec5B517Q8.pair hq i j := by
  refine ⟨Sec5B517Q8.mem_of_pow hq (s888r1a_sup_le_all i j hx) (m := 1) ?_, hx⟩
  rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
  exact hx2

theorem Sec5B517Q8.sq_mem_zpowers (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {x : G}
    (hx : x ∈ Sec5B517Q8.pair hq i j) : x * x ∈ zpowers z := by
  obtain ⟨a, ha, b, hb, ha4, hb4, hx_eq⟩ := (Sec5B517Q8.mem_pair_iff hq hij).mp hx
  have hab : Commute a b := hq.comm i j hij a ha b hb
  have hxx : x * x = (a * a) * (b * b) := by
    rw [hx_eq, ← pow_two (a * b), hab.mul_pow 2, pow_two a, pow_two b]
  rw [hxx]
  rcases hq.sq_of_pow4 ha ha4 with haa | haa <;> rcases hq.sq_of_pow4 hb hb4 with hbb | hbb
  · rw [haa, hbb, one_mul]; exact (zpowers z).one_mem
  · rw [haa, hbb, one_mul]; exact Subgroup.mem_zpowers z
  · rw [haa, hbb, mul_one]; exact Subgroup.mem_zpowers z
  · rw [haa, hbb, hq.z_sq]; exact (zpowers z).one_mem

theorem Sec5B517Q8.commutator_mem_zpowers (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {x y : G} (hx : x ∈ Sec5B517Q8.pair hq i j) (hy : y ∈ Sec5B517Q8.pair hq i j) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hx.1
  obtain ⟨l, hl, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hy.1
  rw [s888r1a_prod_commutator hq (fun m => (hk m).1) (fun m => (hl m).1)]
  simp only [Sec5B517Prod]
  exact (zpowers z).mul_mem ((zpowers z).mul_mem ((zpowers z).mul_mem
    (s888r1a_comm_mem_zpowers hq (hk 0).1 (hk 0).2 (hl 0).1 (hl 0).2)
    (s888r1a_comm_mem_zpowers hq (hk 1).1 (hk 1).2 (hl 1).1 (hl 1).2))
    (s888r1a_comm_mem_zpowers hq (hk 2).1 (hk 2).2 (hl 2).1 (hl 2).2))
    (s888r1a_comm_mem_zpowers hq (hk 3).1 (hk 3).2 (hl 3).1 (hl 3).2)

theorem Sec5B517Q8.twoCoreIn_sup_eq_pair (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) :
    twoCoreIn (K i ⊔ K j) = Sec5B517Q8.pair hq i j := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxX : x ∈ K i ⊔ K j := s888r1a_twoCoreIn_le_self _ hx
    have hxAll : x ∈ Sec5B517All K := s888r1a_sup_le_all i j hxX
    obtain ⟨m, hm⟩ := (s888r1a_isPGroup_twoCoreIn (K i ⊔ K j)).exists_pow_pow_eq_one ⟨x, hx⟩
    have hxm : x ^ (2 ^ m) = 1 := by
      simpa using congrArg (fun y : ↥(twoCoreIn (K i ⊔ K j)) => (y : G)) hm
    exact ⟨Sec5B517Q8.mem_of_pow hq hxAll hxm, hxX⟩
  · intro x hx
    refine s888r1a_le_twoCoreIn_of_normal inf_le_right ?_ ?_ hx
    · intro y
      refine ⟨2, Subtype.ext ?_⟩
      have hy4 : (y : G) ^ 4 = 1 := Sec5B517Q8.pow_four hq y.2.1
      simpa using hy4
    · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      exact ⟨Sec5B517Q8.conj_mem hq (s888r1a_sup_le_all i j hk) hh.1,
        (K i ⊔ K j).mul_mem ((K i ⊔ K j).mul_mem hk hh.2) ((K i ⊔ K j).inv_mem hk)⟩

end CFSG.OddStandard.SmallF3.Omega
