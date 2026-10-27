module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5op_odd_comm_trick {G : Type*} [Group G] {z y h : G} {N : Subgroup G}
    (hz : z * z = 1) (hyz : y * z = z * y) (hNz : ∀ n ∈ N, n * z = z * n)
    (hNy : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hN : Odd (Nat.card N)) (hy : Odd (orderOf y))
    (hc : ∃ (e : ℕ) (n : G), n ∈ N ∧ y * h * y⁻¹ * h⁻¹ = z ^ e * n) :
    y * h * y⁻¹ * h⁻¹ ∈ N := by
  obtain ⟨e, n, hnN, he⟩ := hc
  have hyc : Commute y z := hyz
  have hyze : ∀ k : ℕ, y * z ^ k = z ^ k * y := fun k => (hyc.pow_right k).eq
  have key : ∀ j : ℕ, ∃ p ∈ N, y ^ j * h * (y ^ j)⁻¹ = z ^ (j * e) * p * h := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨p, hpN, hp⟩ := ih
      have hAe : (y * p * y⁻¹) * z ^ e = z ^ e * (y * p * y⁻¹) :=
        (Commute.pow_right (hNz (y * p * y⁻¹) (hNy p hpN)) e).eq
      have hmain : y * (z ^ (j * e) * p * h) * y⁻¹
          = z ^ ((j + 1) * e) * ((y * p * y⁻¹) * n) * h := by
        calc
          y * (z ^ (j * e) * p * h) * y⁻¹
              = (y * z ^ (j * e) * y⁻¹) * (y * p * y⁻¹) * (y * h * y⁻¹) := by
                group
          _ = z ^ (j * e) * (y * p * y⁻¹) * (y * h * y⁻¹) := by
                rw [hyze (j * e)]; group
          _ = z ^ (j * e) * (y * p * y⁻¹) * (z ^ e * n * h) := by
                rw [show y * h * y⁻¹ = z ^ e * n * h from by rw [← he]; group]
          _ = z ^ (j * e) * ((y * p * y⁻¹) * z ^ e) * n * h := by group
          _ = z ^ (j * e) * (z ^ e * (y * p * y⁻¹)) * n * h := by rw [hAe]
          _ = z ^ (j * e) * z ^ e * ((y * p * y⁻¹) * n) * h := by group
          _ = z ^ ((j + 1) * e) * ((y * p * y⁻¹) * n) * h := by
                rw [← pow_add, show j * e + e = (j + 1) * e by ring]
      refine ⟨(y * p * y⁻¹) * n, N.mul_mem (hNy p hpN) hnN, ?_⟩
      calc
        y ^ (j + 1) * h * (y ^ (j + 1))⁻¹
            = y * (y ^ j * h * (y ^ j)⁻¹) * y⁻¹ := by rw [pow_succ']; group
        _ = y * (z ^ (j * e) * p * h) * y⁻¹ := by rw [hp]
        _ = z ^ ((j + 1) * e) * ((y * p * y⁻¹) * n) * h := hmain
  obtain ⟨p, hpN, hp⟩ := key (orderOf y)
  have hyo : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hp' : h = z ^ (orderOf y * e) * p * h := by simpa [hyo] using hp
  have hze : z ^ (orderOf y * e) * p = 1 := by
    have h2 := congrArg (fun x => x * h⁻¹) hp'
    rw [mul_inv_cancel] at h2
    rw [mul_assoc, mul_inv_cancel, mul_one] at h2
    exact h2.symm
  have hzmp : z ^ (orderOf y * e) = p⁻¹ := by
    rw [← inv_eq_of_mul_eq_one_right hze, inv_inv]
  obtain ⟨k, hk⟩ := hy
  have hzm : z ^ orderOf y = z := by
    rw [hk, pow_succ, pow_mul, show z ^ 2 = 1 by rw [pow_two, hz], one_pow, one_mul]
  have hzeN : z ^ e ∈ N := by
    have hzme : z ^ e = z ^ (orderOf y * e) := by rw [pow_mul, hzm]
    rw [hzme, hzmp]
    exact N.inv_mem hpN
  rw [he]
  exact N.mul_mem hzeN hnN

theorem sec5op_eq_top_of_odd_sylow {C : Type*} [Group C] [Finite C] (F P : Subgroup C)
    (hP : IsPGroup 2 P) (hidx : Odd P.index) (hPF : P ≤ F)
    (hodd : ∀ c : C, Odd (orderOf c) → c ∈ F) : F = ⊤ := by
  let S : Set C := {c | Odd (orderOf c)}
  let K : Subgroup C := Subgroup.normalClosure S
  have hconj : Group.conjugatesOfSet S ⊆ S := by
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hc⟩ := hy
    rw [isConj_iff] at hc
    obtain ⟨c, rfl⟩ := hc
    have hord : orderOf (c * x * c⁻¹) = orderOf x := by
      simpa using MulEquiv.orderOf_eq (MulAut.conj c) x
    change Odd (orderOf (c * x * c⁻¹))
    rw [hord]
    exact hx
  have hKF : K ≤ F := by
    calc K = Subgroup.closure (Group.conjugatesOfSet S) := rfl
      _ ≤ Subgroup.closure S := Subgroup.closure_mono hconj
      _ ≤ F := (Subgroup.closure_le F).mpr fun x hx => hodd x hx
  have hSK : S ⊆ K := Subgroup.subset_normalClosure
  have hquot : IsPGroup 2 (C ⧸ K) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K g
    obtain ⟨a, b, hbodd, ho⟩ :=
      Nat.exists_eq_two_pow_mul_odd (n := orderOf x) (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    change (x : C ⧸ K) ^ (2 ^ a) = 1
    rw [← QuotientGroup.mk_pow]
    rw [QuotientGroup.eq_one_iff]
    apply hSK
    apply Odd.of_dvd_nat hbodd
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← ho]
    exact pow_orderOf_eq_one x
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := C ⧸ K)).mp hquot
  have hFodd : Odd F.index := Odd.of_dvd_nat hidx (Subgroup.index_dvd_of_le hPF)
  have hdiv : F.index ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_of_le hKF
  have hcop : Nat.Coprime F.index (2 ^ n) := (Odd.coprime_two_right hFodd).pow_right n
  exact Subgroup.index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdiv)

theorem sec5op_fix_centralizer {M : Type*} [Group M] [Finite M] (α : MulAut M) (P : Subgroup M)
    (hP : IsPGroup 2 P) (hidx : Odd P.index) {u : M} (hPc : ∀ x ∈ P, x * u = u * x)
    (hPfix : ∀ x ∈ P, α x = x)
    (hodd : ∀ c ∈ centralizer ({u} : Set M), Odd (orderOf c) → α c = c) :
    ∀ x ∈ centralizer ({u} : Set M), α x = x := by
  let C : Subgroup M := centralizer ({u} : Set M)
  have hPC : P ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    rw [hm]
    exact (hPc x hx).symm
  let F : Subgroup C :=
    { carrier := {c : C | α (c : M) = (c : M)}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change α ((a : M) * (b : M)) = (a : M) * (b : M)
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change α ((a : M)⁻¹) = (a : M)⁻¹
        rw [map_inv, ha] }
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.comap_subtype
  have hidx' : Odd (P.subgroupOf C).index := by
    refine Odd.of_dvd_nat hidx ?_
    exact ⟨C.index, (Subgroup.relIndex_mul_index hPC).symm⟩
  have hP'F : P.subgroupOf C ≤ F := by
    intro x hx
    change α (x : M) = (x : M)
    exact hPfix (x : M) hx
  have hodd' : ∀ c : C, Odd (orderOf c) → c ∈ F := by
    intro c hc
    change α (c : M) = (c : M)
    exact hodd (c : M) c.2 (by rw [Subgroup.orderOf_coe]; exact hc)
  have htop : F = ⊤ := sec5op_eq_top_of_odd_sylow F (P.subgroupOf C) hP' hidx' hP'F hodd'
  intro x hx
  have hxC : x ∈ C := hx
  have hmem : (⟨x, hxC⟩ : C) ∈ F := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

end CFSG.OddStandard.SmallF3.Omega
