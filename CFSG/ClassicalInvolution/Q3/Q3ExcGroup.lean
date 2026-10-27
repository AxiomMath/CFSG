module

public import CFSG.ClassicalInvolution.Q3.OddCentralizerFree
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution

section CentralProduct

variable {G : Type} [Group G]

theorem exc3_commute_iSup_finset {ι : Type*} (H : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) {j : ι} (s : Finset ι)
    (hj : j ∉ s) : ∀ a ∈ H j, ∀ b ∈ (⨆ i ∈ s, H i), a * b = b * a := by
  intro a ha b hb
  have hle : (⨆ i ∈ s, H i) ≤ Subgroup.centralizer (H j : Set G) := by
    refine iSup₂_le fun i hi => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hc j i (fun h => hj (h ▸ hi)) y hy x hx
  exact Subgroup.mem_centralizer_iff.mp (hle hb) a ha

theorem exc3_mem_iSup_center_finset {ι : Type*} [DecidableEq ι] (H : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) (s : Finset ι) :
    ∀ x ∈ (⨆ i ∈ s, H i), (∀ y ∈ (⨆ i ∈ s, H i), x * y = y * x) →
      x ∈ ⨆ i ∈ s, (H i ⊓ Subgroup.centralizer (H i : Set G)) := by
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    have h0 : (⨆ i ∈ (∅ : Finset ι), H i) = ⊥ := by simp
    rw [h0, Subgroup.mem_bot] at hx
    rw [hx]
    exact one_mem _
  | insert j s hj ih =>
    intro x hx hxc
    rw [Finset.iSup_insert] at hx hxc ⊢
    have hcomm : ∀ a ∈ H j, ∀ b ∈ (⨆ i ∈ s, H i), a * b = b * a :=
      exc3_commute_iSup_finset H hc s hj
    obtain ⟨a, ha, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have haZ : a ∈ Subgroup.centralizer (H j : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have e1 := hxc h (Subgroup.mem_sup_left hh)
      have e2 : h * p = p * h := hcomm h hh p hp
      have e3 : (h * a) * p = (a * h) * p := by
        calc (h * a) * p = h * (a * p) := by group
          _ = a * p * h := e1.symm
          _ = a * (p * h) := by group
          _ = a * (h * p) := by rw [e2]
          _ = (a * h) * p := by group
      exact mul_right_cancel e3
    have hpc : ∀ q ∈ (⨆ i ∈ s, H i), p * q = q * p := by
      intro q hq
      have e1 := hxc q (Subgroup.mem_sup_right hq)
      have e2 : a * q = q * a := hcomm a ha q hq
      have e3 : a * (p * q) = a * (q * p) := by
        calc a * (p * q) = a * p * q := by group
          _ = q * (a * p) := e1
          _ = (q * a) * p := by group
          _ = (a * q) * p := by rw [e2]
          _ = a * (q * p) := by group
      exact mul_left_cancel e3
    exact mul_mem (Subgroup.mem_sup_left ⟨ha, haZ⟩)
      (Subgroup.mem_sup_right (ih p hp hpc))

theorem exc3_center_le_iSup {ι : Type*} [Finite ι] (H : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) {x : G} (hx : x ∈ ⨆ i, H i)
    (hxc : ∀ y ∈ ⨆ i, H i, x * y = y * x) :
    x ∈ ⨆ i, (H i ⊓ Subgroup.centralizer (H i : Set G)) := by
  classical
  have := Fintype.ofFinite ι
  have h := exc3_mem_iSup_center_finset H hc Finset.univ
  simp only [Finset.mem_univ, iSup_pos] at h
  exact h x hx hxc

end CentralProduct

section Lift

variable {K C : Type*} [Group K] [Group C]

theorem exc3_eq_one_of_sq_eq_one_of_odd {M : Type*} [Group M] {x : M} (hx : x ^ 2 = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem exc3_mem_zpowers_pow_three {M : Type*} [Group M] {n : M} {k : ℕ}
    (hk : orderOf n = 2 ^ k) : n ∈ Subgroup.zpowers (n ^ 3) := by
  rw [mem_zpowers_pow_iff, hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem exc3_le_of_map_le {ψ : K →* C} (hker : ψ.ker ≤ Subgroup.center K)
    (h2 : IsPGroup 2 ψ.ker) {L R : Subgroup K}
    (hR : Subgroup.closure {y : R | y ^ 3 = 1} = ⊤) (h : R.map ψ ≤ L.map ψ) : R ≤ L := by
  have key : ∀ y : K, y ∈ R → y ^ 3 = 1 → y ∈ L := by
    intro y hyR hy3
    obtain ⟨l, hlL, hl⟩ := h (Subgroup.mem_map_of_mem ψ hyR)
    set n : K := l⁻¹ * y with hn
    have hnk : n ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hn, map_mul, map_inv, hl, inv_mul_cancel]
    have hyn : y = l * n := by rw [hn]; group
    have hcomm : Commute l n := Subgroup.mem_center_iff.mp (hker hnk) l
    have hn3 : n ^ 3 = (l ^ 3)⁻¹ := by
      have : (l * n) ^ 3 = l ^ 3 * n ^ 3 := hcomm.mul_pow 3
      rw [← hyn, hy3] at this
      exact eq_inv_of_mul_eq_one_right this.symm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨n, hnk⟩
    have hk' : orderOf n = 2 ^ k := by
      rw [← Subgroup.orderOf_mk n hnk]
      exact hk
    have hnz := exc3_mem_zpowers_pow_three hk'
    have hnL : n ∈ L := by
      refine (Subgroup.zpowers_le.mpr ?_) hnz
      rw [hn3]
      exact L.inv_mem (L.pow_mem hlL 3)
    rw [hyn]
    exact L.mul_mem hlL hnL
  intro x hx
  have hle : Subgroup.closure {y : R | y ^ 3 = 1} ≤ L.subgroupOf R :=
    (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
      (key y.1 y.2 (by
        have := congrArg Subtype.val hy
        simpa using this))
  exact Subgroup.mem_subgroupOf.1 (hle (hR ▸ Subgroup.mem_top (⟨x, hx⟩ : R)))

theorem exc3_eq_of_map_eq {ψ : K →* C} (hker : ψ.ker ≤ Subgroup.center K)
    (h2 : IsPGroup 2 ψ.ker) {L R : Subgroup K}
    (hL : Subgroup.closure {y : L | y ^ 3 = 1} = ⊤)
    (hR : Subgroup.closure {y : R | y ^ 3 = 1} = ⊤) (h : L.map ψ = R.map ψ) : L = R :=
  le_antisymm (exc3_le_of_map_le hker h2 hL h.le) (exc3_le_of_map_le hker h2 hR h.ge)

end Lift

end CFSG.ClassicalInvolution.Q3
