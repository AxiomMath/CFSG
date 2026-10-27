module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXClass

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

namespace S11sCtx

variable {G : Type} [Group G] [Finite G] {t z : G} {K1 K2 T R : Subgroup G}
  {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G} (c : S11sCtx t z K1 K2 T R ρ a x)

private theorem s11s_zpowers_involution_eq {u y : G} (hu : u * u = 1)
    (hy : y ∈ Subgroup.zpowers u) : y = 1 ∨ y = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left; rw [hm, zpow_mul, hu2, one_zpow]
  · right; rw [hm, zpow_add_one, zpow_mul, hu2, one_zpow, one_mul]

include c

theorem z_K1 : z ∈ K1 := by
  exact twoCoreIn_le_self K1 c.q8.z_mem1

theorem z_K2 : z ∈ K2 := by
  exact twoCoreIn_le_self K2 c.q8.z_mem2

theorem Q1_le_Q : twoCoreIn K1 ≤ secQ K1 K2 := by
  rw [c.Q_eq]; exact le_sup_left

theorem Q2_le_Q : twoCoreIn K2 ≤ secQ K1 K2 := by
  rw [c.Q_eq]; exact le_sup_right

theorem D_comm_Q {d q : G} (hd : d ∈ secD K1 K2 R) (hq : q ∈ secQ K1 K2) : d * q = q * d := by
  exact (Subgroup.mem_centralizer_iff.mp hd.1 q hq).symm

theorem z_comm_D {d : G} (hd : d ∈ secD K1 K2 R) : z * d = d * z := by
  exact (c.D_comm_Q hd (c.Q1_le_Q c.q8.z_mem1)).symm

theorem T_N0 {g : G} (hg : g ∈ T) {n : G} (hn : n ∈ oddCoreIn (secK0 t z)) :
    g * n * g⁻¹ ∈ oddCoreIn (secK0 t z) := by
  exact sec11_conj_mem_oddCoreIn (c.T_N hg) hn

theorem rho_Q (y : ↥R) (κ : ↥(K1 ⊔ K2)) (hκ : (κ : G) ∈ secQ K1 K2) :
    ((ρ y κ : ↥(K1 ⊔ K2)) : G) = (y : G) * κ * (y : G)⁻¹ := by
  have hκK : (κ : G) ∈ K1 ⊔ K2 := c.set.split.Q_le hκ
  obtain ⟨n', hn', h⟩ :=
    c.rho.act y (κ : G) 1 κ (c.QKD hκ) (oddCoreIn (secK0 t z)).one_mem (by simp)
  have hyq : (y : G) * (κ : G) * (y : G)⁻¹ ∈ secQ K1 K2 :=
    (Subgroup.mem_normalizer_iff.mp (c.RQ y.2) (κ : G)).mp hκ
  have h' : (1 : G) * ((y : G) * (κ : G) * (y : G)⁻¹) =
      n' * ((ρ y κ : ↥(K1 ⊔ K2)) : G) := by
    rw [one_mul]; exact h
  exact (c.set.split.split.unique (oddCoreIn (secK0 t z)).one_mem hn' (c.set.split.Q_le hyq)
    (ρ y κ).2 h').2.symm

theorem rho_D (y : ↥R) (hy : (y : G) ∈ secD K1 K2 R) : ρ y = 1 := by
  exact c.rho.ker_of_mem c.set.split hy

theorem mem_D (y : ↥R) (hy : ρ y = 1) : (y : G) ∈ secD K1 K2 R := by
  exact c.rho.mem_of_ker c.set.split c.QKD c.RQ hy

theorem rho_K (y : ↥R) (hyK : (y : G) ∈ K1 ⊔ K2) :
    ρ y = MulAut.conj (⟨(y : G), hyK⟩ : ↥(K1 ⊔ K2)) := by
  exact c.rho.conj_of_mem c.set.split hyK

theorem rho_keep {Ki : Subgroup G} (hKi : Ki ≤ K1 ⊔ K2) (y : ↥R)
    (hy : (y : G) ∈ normalizer ((Ki ⊔ oddCoreIn (secK0 t z) : Subgroup G) : Set G)) :
    ∀ κ ∈ Ki.subgroupOf (K1 ⊔ K2), ρ y κ ∈ Ki.subgroupOf (K1 ⊔ K2) := by
  intro κ hκ
  obtain ⟨k, hk, n, hn, hkn⟩ := c.rho.lift κ
  obtain ⟨n', hn', hact⟩ := c.rho.act y k n κ hk hn hkn
  have hkKiN : k ∈ Ki ⊔ oddCoreIn (secK0 t z) := by
    rw [hkn]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left hκ)
  have hyk : (y : G) * k * (y : G)⁻¹ ∈ Ki ⊔ oddCoreIn (secK0 t z) :=
    (Subgroup.mem_normalizer_iff.mp hy k).mp hkKiN
  have hrho : ((ρ y κ : ↥(K1 ⊔ K2)) : G) = n'⁻¹ * ((y : G) * k * (y : G)⁻¹) := by
    rw [hact]; group
  have hmem : ((ρ y κ : ↥(K1 ⊔ K2)) : G) ∈ Ki ⊔ oddCoreIn (secK0 t z) := by
    rw [hrho]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((oddCoreIn (secK0 t z)).inv_mem hn')) hyk
  obtain ⟨a', ha', n'', hn'', haen⟩ := exists_mul_of_mem_sup_of_commute
    (H := Ki) (K := oddCoreIn (secK0 t z))
    (fun a ha b hb => c.set.split.comm' hb (hKi ha)) hmem
  have hnK : n'' ∈ K1 ⊔ K2 := by
    have h1 : n'' = a'⁻¹ * ((ρ y κ : ↥(K1 ⊔ K2)) : G) := by rw [haen]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKi ha')) (ρ y κ).2
  have hn1 : n'' = 1 := c.set.split.split.disj n'' hn'' hnK
  show ((ρ y κ : ↥(K1 ⊔ K2)) : G) ∈ Ki
  rw [haen, hn1, mul_one]
  exact ha'

theorem rho_outer {Ki : Subgroup G} (hKi : Ki ≤ K1 ⊔ K2) (y : ↥R)
    (hyN : ∀ n ∈ oddCoreIn (secK0 t z), (y : G) * n * (y : G)⁻¹ ∈ oddCoreIn (secK0 t z))
    (hy : IsOuterOn (y : G) (Ki ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))) :
    ¬ ∃ k ∈ Ki.subgroupOf (K1 ⊔ K2), ∀ w ∈ Ki.subgroupOf (K1 ⊔ K2), ρ y w = k * w * k⁻¹ := by
  rintro ⟨k0, hk0, hinner⟩
  apply hy.2
  have hk0Ki : (k0 : G) ∈ Ki := hk0
  refine ⟨(k0 : G), Subgroup.mem_sup_left hk0Ki, fun g hg => ?_⟩
  obtain ⟨κ0, hκ0, n, hn, hge⟩ := exists_mul_of_mem_sup_of_commute
    (H := Ki) (K := oddCoreIn (secK0 t z))
    (fun a ha b hb => c.set.split.comm' hb (hKi ha)) hg
  let κ : ↥(K1 ⊔ K2) := ⟨κ0, hKi hκ0⟩
  obtain ⟨k1, hk1, n0, hn0, hk1e⟩ := c.rho.lift κ
  obtain ⟨n', hn', hact⟩ := c.rho.act y k1 n0 κ hk1 hn0 hk1e
  have hinnerG : ((ρ y κ : ↥(K1 ⊔ K2)) : G) = (k0 : G) * κ0 * (k0 : G)⁻¹ := by
    simpa [κ] using congrArg Subtype.val (hinner κ (show (κ : G) ∈ Ki from hκ0))
  have hCKi : (k0 : G) * κ0 * (k0 : G)⁻¹ ∈ Ki :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk0Ki hκ0) (Subgroup.inv_mem _ hk0Ki)
  have hD : (y : G) * n * (y : G)⁻¹ ∈ oddCoreIn (secK0 t z) := hyN n hn
  have hE : n⁻¹ ∈ oddCoreIn (secK0 t z) := (oddCoreIn (secK0 t z)).inv_mem hn
  have hA : (y : G) * n0⁻¹ * (y : G)⁻¹ ∈ oddCoreIn (secK0 t z) :=
    hyN n0⁻¹ ((oddCoreIn (secK0 t z)).inv_mem hn0)
  have hCDE : ((k0 : G) * κ0 * (k0 : G)⁻¹) *
      (((y : G) * n * (y : G)⁻¹) * n⁻¹) =
      (((y : G) * n * (y : G)⁻¹) * n⁻¹) * ((k0 : G) * κ0 * (k0 : G)⁻¹) :=
    c.set.split.comm' (Subgroup.mul_mem _ hD hE) (hKi hCKi)
  have hgy : (y : G) * g * (y : G)⁻¹ =
      ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * ((k0 : G) * κ0 * (k0 : G)⁻¹) *
        ((y : G) * n * (y : G)⁻¹) := by
    have hg' : g = n0⁻¹ * k1 * n := by
      rw [hge, hk1e, show (κ : G) = κ0 from rfl]; group
    rw [hg']
    rw [show (y : G) * (n0⁻¹ * k1 * n) * (y : G)⁻¹ =
        ((y : G) * n0⁻¹ * (y : G)⁻¹) * ((y : G) * k1 * (y : G)⁻¹) *
          ((y : G) * n * (y : G)⁻¹) by group]
    rw [hact, hinnerG]
    group
  have hgyk : (k0 : G) * g * (k0 : G)⁻¹ = ((k0 : G) * κ0 * (k0 : G)⁻¹) * n := by
    have hc : (k0 : G) * n = n * (k0 : G) := c.set.split.comm' hn (hKi hk0Ki)
    calc (k0 : G) * g * (k0 : G)⁻¹ = (k0 : G) * (κ0 * n) * (k0 : G)⁻¹ := by rw [hge]
      _ = ((k0 : G) * κ0 * (k0 : G)⁻¹) * ((k0 : G) * n * (k0 : G)⁻¹) := by group
      _ = ((k0 : G) * κ0 * (k0 : G)⁻¹) * n := by
            rw [show (k0 : G) * n * (k0 : G)⁻¹ = n by rw [hc]; group]
  have hprod : (y : G) * g * (y : G)⁻¹ * ((k0 : G) * g * (k0 : G)⁻¹)⁻¹ =
      ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * ((y : G) * n * (y : G)⁻¹) * n⁻¹ := by
    rw [hgy, hgyk, mul_inv_rev]
    have hmain : ((k0 : G) * κ0 * (k0 : G)⁻¹) *
        (((y : G) * n * (y : G)⁻¹) * n⁻¹) * ((k0 : G) * κ0 * (k0 : G)⁻¹)⁻¹ =
        ((y : G) * n * (y : G)⁻¹) * n⁻¹ := by
      rw [hCDE]; group
    calc ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * ((k0 : G) * κ0 * (k0 : G)⁻¹) *
          ((y : G) * n * (y : G)⁻¹) * (n⁻¹ * ((k0 : G) * κ0 * (k0 : G)⁻¹)⁻¹)
        = ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * (((k0 : G) * κ0 * (k0 : G)⁻¹) *
            (((y : G) * n * (y : G)⁻¹) * n⁻¹) *
            ((k0 : G) * κ0 * (k0 : G)⁻¹)⁻¹) := by group
      _ = ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * (((y : G) * n * (y : G)⁻¹) * n⁻¹) := by
            rw [hmain]
      _ = ((y : G) * n0⁻¹ * (y : G)⁻¹) * n' * ((y : G) * n * (y : G)⁻¹) * n⁻¹ := by
            group
  rw [hprod]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hn') hD) hE

theorem rho_a12 (ha : a ∈ R) :
    ∀ κ ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨a, ha⟩ κ ∈ K2.subgroupOf (K1 ⊔ K2) := by
  intro κ hκ
  have hκK : a * (κ : G) * a⁻¹ ∈ K1 ⊔ K2 := Subgroup.mem_sup_right (c.a_swap (κ : G) hκ)
  have h := c.rho.apply_conj c.set.split (y := ⟨a, ha⟩)
    (fun n hn => by simpa using c.T_N0 c.a_T hn) hκK
  show ((ρ ⟨a, ha⟩ κ : ↥(K1 ⊔ K2)) : G) ∈ K2
  rw [h]
  exact c.a_swap (κ : G) hκ

theorem rho_a21 (ha : a ∈ R) :
    ∀ κ ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨a, ha⟩ κ ∈ K1.subgroupOf (K1 ⊔ K2) := by
  intro κ hκ
  have hκK : a * (κ : G) * a⁻¹ ∈ K1 ⊔ K2 := Subgroup.mem_sup_left (c.a_swap' (κ : G) hκ)
  have h := c.rho.apply_conj c.set.split (y := ⟨a, ha⟩)
    (fun n hn => by simpa using c.T_N0 c.a_T hn) hκK
  show ((ρ ⟨a, ha⟩ κ : ↥(K1 ⊔ K2)) : G) ∈ K1
  rw [h]
  exact c.a_swap' (κ : G) hκ

theorem rho_a_sq (ha : a ∈ R) : ρ ⟨a, ha⟩ * ρ ⟨a, ha⟩ = 1 := by
  rw [← map_mul]
  have h : (⟨a, ha⟩ : ↥R) * ⟨a, ha⟩ = 1 := by
    apply Subtype.ext
    simpa using c.a_sq
  rw [h, map_one]

theorem embA_mem_Q1 {q : SL23} (hq : q ^ 4 = 1) :
    ((c.pair.embA q : ↥(K1 ⊔ K2)) : G) ∈ twoCoreIn K1 := by
  refine c.Q1_pow _ (c.pair.embA_mem q) ?_
  have h4 : (c.pair.embA q : ↥(K1 ⊔ K2)) ^ 4 = 1 := by
    rw [← map_pow, hq, map_one]
  simpa using congrArg Subtype.val h4

theorem embB_mem_Q2 {q : SL23} (hq : q ^ 4 = 1) :
    ((c.pair.embB q : ↥(K1 ⊔ K2)) : G) ∈ twoCoreIn K2 := by
  refine c.Q2_pow _ (c.pair.embB_mem q) ?_
  have h4 : (c.pair.embB q : ↥(K1 ⊔ K2)) ^ 4 = 1 := by
    rw [← map_pow, hq, map_one]
  simpa using congrArg Subtype.val h4

theorem embB_neg_one : ((c.pair.embB (-1) : ↥(K1 ⊔ K2)) : G) = z := by
  have hw2 : (⟨z, c.set.split.z_mem⟩ : ↥(K1 ⊔ K2)) * ⟨z, c.set.split.z_mem⟩ = 1 := by
    apply Subtype.ext
    simpa using c.q8.z_sq
  have hw1 : (⟨z, c.set.split.z_mem⟩ : ↥(K1 ⊔ K2)) ≠ 1 := by
    intro hw
    exact c.q8.z_ne (by simpa using congrArg Subtype.val hw)
  have h := c.pair.s11s_embB_neg_one (w := ⟨z, c.set.split.z_mem⟩) c.z_K2 hw2 hw1
  simpa using congrArg Subtype.val h

theorem sq_eq_z1 {g : G} (hg : g ∈ twoCoreIn K1) (hgz : g ∉ zpowers z) : g * g = z := by
  have hmem : g * g ∈ zpowers z := (c.q8.elem1 g hg g hg).2
  rcases s11s_zpowers_involution_eq c.q8.z_sq hmem with h | h
  · exact absurd (c.q8.invol1 g hg h) hgz
  · exact h

end S11sCtx

end CFSG.OddStandard.SmallF3.Omega
