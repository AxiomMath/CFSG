module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public section

namespace CFSG.KC.O8

open Subgroup CFSG.EvenSmallLie.OmegaEight

theorem isPGroup_zpowers_of_pow_four {G : Type*} [Group G] {x : G} (h : x ^ 4 = 1) :
    IsPGroup 2 (zpowers x) := fun g => ⟨2, by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hn, OneMemClass.coe_one, show (2 : ℕ) ^ 2 = 4 by norm_num,
    ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]⟩

theorem zpowers_le_normalizer_of_inv {G : Type*} [Group G] {x b : G} (h : x * b * x⁻¹ = b⁻¹) :
    zpowers x ≤ normalizer (zpowers b : Set G) := by
  have e : b = x⁻¹ * b⁻¹ * x := by rw [← h]; group
  have h' : x⁻¹ * b * x⁻¹⁻¹ = b⁻¹ := by
    calc x⁻¹ * b * x⁻¹⁻¹ = (x⁻¹ * b⁻¹ * x)⁻¹ := by group
      _ = b⁻¹ := by rw [← e]
  rw [zpowers_le, mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
    exact mem_zpowers_iff.2 ⟨-n, by rw [← inv_zpow', ← h, conj_zpow]⟩
  · intro hg
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hg
    refine mem_zpowers_iff.2 ⟨-n, ?_⟩
    rw [← inv_zpow', ← h', conj_zpow, hn]
    group

theorem conj_pow' {G : Type*} [Group G] (a g : G) : ∀ n : ℕ, (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹
  | 0 => by simp
  | n + 1 => by rw [pow_succ, conj_pow' a g n, pow_succ]; group


theorem exists_conj_sylowT {K : Subgroup (Equiv.Perm (Fin 360))} (hSK : sylowT ≤ K)
    {Q : Subgroup (Equiv.Perm (Fin 360))} (hQ : Q ≤ K ⊓ autT) (hp : IsPGroup 2 Q) :
    ∃ a ∈ K ⊓ autT, ∀ y ∈ Q, a * y * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup autT := K.subgroupOf autT
  have hle : (sylowA : Subgroup autT) ≤ H := by
    intro x hx
    rw [coe_sylowA, mem_subgroupOf] at hx
    exact mem_subgroupOf.2 (hSK hx)
  set P : Sylow 2 H := sylowA.subtype hle
  set Qh : Subgroup H := (Q.subgroupOf autT).subgroupOf H
  have hQh : IsPGroup 2 Qh := fun x => by
    have hx : ((x : H) : autT).1 ∈ Q := by
      have := x.2
      rw [mem_subgroupOf, mem_subgroupOf] at this
      exact this
    obtain ⟨k, hk⟩ := hp ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨R, hR⟩ := hQh.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P R
  have key : ∀ y ∈ Q, ((((g⁻¹ : H) : autT) : Equiv.Perm (Fin 360)) * y *
      (((g⁻¹ : H) : autT) : Equiv.Perm (Fin 360))⁻¹) ∈ sylowT := by
    intro y hy
    have hyA : y ∈ autT := (hQ hy).2
    have hyK : y ∈ K := (hQ hy).1
    set yh : H := ⟨⟨y, hyA⟩, mem_subgroupOf.2 hyK⟩
    have h1 : yh ∈ (R : Subgroup H) := hR (by
      rw [mem_subgroupOf, mem_subgroupOf]
      exact hy)
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.inv_def, MulAut.conj_symm_apply, Sylow.coe_subtype, mem_subgroupOf, coe_sylowA,
      mem_subgroupOf] at h1
    simpa using h1
  refine ⟨(((g⁻¹ : H) : autT) : Equiv.Perm (Fin 360)), ⟨?_, ((g⁻¹ : H) : autT).2⟩, key⟩
  exact mem_subgroupOf.1 (g⁻¹).2

private theorem conj_root {a j x : Equiv.Perm (Fin 360)} (ha : a ∈ autT) (hjO : j ∉ omegaT)
    (hjj : j * j = x) :
    a * j * a⁻¹ ∉ omegaT ∧ a * j * a⁻¹ * (a * j * a⁻¹) = a * x * a⁻¹ := by
  refine ⟨fun h => hjO ((conj_mem_omegaT ha).2 h), ?_⟩
  rw [← hjj]
  group

theorem outer_root_of
    (hcent : ∀ s ∈ sylowT, s * mainPerm 0 = mainPerm 0 * s)
    (h0 : ∀ j ∈ sylowT, j ∉ omegaT → j * j = mainPerm 0 →
      ∃ c ∈ omegaT, c * mainPerm 0 = mainPerm 0 * c ∧ ∃ k : ℕ,
        (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1)
    (h1 : ∀ k < 38, repTypes.getD k 0 = 1 → ∀ j ∈ sylowT, j ∉ omegaT → j * j = repPerm k →
      ∀ u ∈ sylowT, u ∈ omegaT → u * u = repPerm k → j * u * j⁻¹ ≠ u⁻¹)
    (h2 : ∀ k < 38, repTypes.getD k 0 = 2 → ∀ j ∈ sylowT, j ∉ omegaT → j * j ≠ repPerm k)
    (hty : ∀ t < 5, ∀ i < 3, ∀ g : Equiv.Perm (Fin 360), g * mainPerm i * g⁻¹ = mainPerm t →
      t = i)
    (hord : ∀ i < 3, mainPerm i * mainPerm i = 1 ∧ mainPerm i ≠ 1)
    {i : ℕ} (hi : i < 3) {j : Equiv.Perm (Fin 360)} (hjA : j ∈ autT) (hjO : j ∉ omegaT)
    (hjj : j * j = mainPerm i) :
    (∃ c ∈ omegaT, c * mainPerm i = mainPerm i * c ∧ ∃ k : ℕ,
        (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1) ∨
      ∀ u ∈ omegaT, u * u = mainPerm i → j * u * j⁻¹ ≠ u⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hx2, hx1⟩ := hord i hi
  have hj4 : j ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, hjj, hx2]
  have hjx : j * mainPerm i = mainPerm i * j := by rw [← hjj, mul_assoc]
  have toRep : ∀ {a : Equiv.Perm (Fin 360)}, a ∈ autT → a * j * a⁻¹ ∈ sylowT →
      ∃ k < 38, ∃ b ∈ autT, repTypes.getD k 0 = i ∧ b * j * b⁻¹ ∈ sylowT ∧
        b * j * b⁻¹ ∉ omegaT ∧ b * j * b⁻¹ * (b * j * b⁻¹) = repPerm k ∧
        ∀ v ∈ sylowT, b * a⁻¹ * v * (b * a⁻¹)⁻¹ ∈ sylowT := by
    intro a ha hjS
    obtain ⟨hO', hsq'⟩ := conj_root ha hjO hjj
    have hyS : a * mainPerm i * a⁻¹ ∈ sylowT := by
      rw [← hsq']
      exact sylowT.mul_mem hjS hjS
    have hyo : orderOf (a * mainPerm i * a⁻¹) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc a * mainPerm i * a⁻¹ * (a * mainPerm i * a⁻¹) = a * (mainPerm i * mainPerm i) * a⁻¹ :=
              by group
          _ = 1 := by rw [hx2]; group
      · intro h
        apply hx1
        calc mainPerm i = a⁻¹ * (a * mainPerm i * a⁻¹) * a := by group
          _ = 1 := by rw [h]; group
    obtain ⟨k, hk, c, hc, hce⟩ := exists_rep_of_involution hyS hyo
    have hcA : c ∈ autT := sylowT_le_autT hc
    have hb : c⁻¹ * a ∈ autT := autT.mul_mem (autT.inv_mem hcA) ha
    have hbj : c⁻¹ * a * j * (c⁻¹ * a)⁻¹ = c⁻¹ * (a * j * a⁻¹) * c := by group
    obtain ⟨hO'', hsq''⟩ := conj_root hb hjO hjj
    have hsqk : c⁻¹ * a * j * (c⁻¹ * a)⁻¹ * (c⁻¹ * a * j * (c⁻¹ * a)⁻¹) = repPerm k := by
      rw [hsq'']
      calc c⁻¹ * a * mainPerm i * (c⁻¹ * a)⁻¹ = c⁻¹ * (a * mainPerm i * a⁻¹) * c := by group
        _ = repPerm k := by rw [hce]; group
    have hty' : repTypes.getD k 0 = i := by
      refine hty _ (repTypes_lt hk) i hi ((conjPerm k)⁻¹ * (c⁻¹ * a)) ?_
      have e := conj_mainPerm hk
      calc (conjPerm k)⁻¹ * (c⁻¹ * a) * mainPerm i * ((conjPerm k)⁻¹ * (c⁻¹ * a))⁻¹ =
            (conjPerm k)⁻¹ * (c⁻¹ * (a * mainPerm i * a⁻¹) * c) * conjPerm k := by group
        _ = (conjPerm k)⁻¹ * repPerm k * conjPerm k := by rw [hce]; group
        _ = mainPerm (repTypes.getD k 0) := by rw [← e]; group
    refine ⟨k, hk, c⁻¹ * a, hb, hty', ?_, hO'', hsqk, fun v hv => ?_⟩
    · rw [hbj]
      exact sylowT.mul_mem (sylowT.mul_mem (sylowT.inv_mem hc) hjS) hc
    · have e : c⁻¹ * a * a⁻¹ * v * (c⁻¹ * a * a⁻¹)⁻¹ = c⁻¹ * v * c := by group
      rw [e]
      exact sylowT.mul_mem (sylowT.mul_mem (sylowT.inv_mem hc) hv) hc
  interval_cases i
  ·
    left
    set K := centralizer ({mainPerm 0} : Set (Equiv.Perm (Fin 360)))
    have hSK : sylowT ≤ K := fun s hs => mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (hcent s hs).symm
    have hjK : j ∈ K := mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hjx.symm
    obtain ⟨a, ⟨haK, haA⟩, hconj⟩ := exists_conj_sylowT hSK
      (Q := zpowers j) (zpowers_le.2 ⟨hjK, hjA⟩) (isPGroup_zpowers_of_pow_four hj4)
    have hax : a * mainPerm 0 = mainPerm 0 * a :=
      (mem_centralizer_iff.1 haK (mainPerm 0) rfl).symm
    obtain ⟨hO', hsq'⟩ := conj_root haA hjO hjj
    have hsq0 : a * j * a⁻¹ * (a * j * a⁻¹) = mainPerm 0 := by
      rw [hsq', hax]
      group
    obtain ⟨c, hc, hcx, k, hk1, hk3⟩ := h0 _ (hconj j (mem_zpowers j)) hO' hsq0
    have haiA : a⁻¹ ∈ autT := autT.inv_mem haA
    refine ⟨a⁻¹ * c * a⁻¹⁻¹, (conj_mem_omegaT haiA).1 hc, ?_, k, ?_⟩
    · calc a⁻¹ * c * a⁻¹⁻¹ * mainPerm 0 = a⁻¹ * c * (a * mainPerm 0) := by group
        _ = a⁻¹ * (c * mainPerm 0) * a := by rw [hax]; group
        _ = a⁻¹ * (mainPerm 0 * c) * a := by rw [hcx]
        _ = a⁻¹ * mainPerm 0 * a * (a⁻¹ * c * a) := by group
        _ = mainPerm 0 * (a⁻¹ * c * a⁻¹⁻¹) := by
          rw [show a⁻¹ * mainPerm 0 * a = mainPerm 0 by
            calc a⁻¹ * mainPerm 0 * a = a⁻¹ * (a * mainPerm 0) := by rw [hax]; group
              _ = mainPerm 0 := by group]
          group
    · have e : j⁻¹ * (a⁻¹ * c * a⁻¹⁻¹) * j * (a⁻¹ * c * a⁻¹⁻¹)⁻¹ =
          a⁻¹ * ((a * j * a⁻¹)⁻¹ * c * (a * j * a⁻¹) * c⁻¹) * a⁻¹⁻¹ := by group
      rw [e, conj_pow', conj_pow']
      refine ⟨fun h => hk1 ?_, ?_⟩
      · calc ((a * j * a⁻¹)⁻¹ * c * (a * j * a⁻¹) * c⁻¹) ^ k =
            a * (a⁻¹ * ((a * j * a⁻¹)⁻¹ * c * (a * j * a⁻¹) * c⁻¹) ^ k * a⁻¹⁻¹) * a⁻¹ := by
              group
          _ = 1 := by rw [h]; group
      · rw [hk3]
        group
  ·
    right
    intro u hu huu he
    have huA : u ∈ autT := omegaT_le_autT hu
    obtain ⟨a, ⟨-, haA⟩, hconj⟩ := exists_conj_sylowT (K := ⊤) le_top
      (Q := zpowers j ⊔ zpowers u)
      (sup_le (zpowers_le.2 ⟨mem_top j, hjA⟩) (zpowers_le.2 ⟨mem_top u, huA⟩))
      ((isPGroup_zpowers_of_pow_four hj4).to_sup_of_normal_right'
        (isPGroup_zpowers_of_pow_four (by
          rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, huu, hx2]))
        (zpowers_le_normalizer_of_inv he))
    obtain ⟨k, hk, b, hbA, hty', hjS, hjO', hjk, hbS⟩ :=
      toRep haA (hconj j (mem_sup_left (mem_zpowers j)))
    have huS : b * u * b⁻¹ ∈ sylowT := by
      have := hbS _ (hconj u (mem_sup_right (mem_zpowers u)))
      have e : b * a⁻¹ * (a * u * a⁻¹) * (b * a⁻¹)⁻¹ = b * u * b⁻¹ := by group
      rwa [e] at this
    have huk : b * u * b⁻¹ * (b * u * b⁻¹) = repPerm k := by
      rw [← hjk]
      calc b * u * b⁻¹ * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
        _ = b * (j * j) * b⁻¹ := by rw [huu, hjj]
        _ = b * j * b⁻¹ * (b * j * b⁻¹) := by group
    refine h1 k hk hty' _ hjS hjO' hjk _ huS ((conj_mem_omegaT hbA).1 hu) huk ?_
    calc b * j * b⁻¹ * (b * u * b⁻¹) * (b * j * b⁻¹)⁻¹ = b * (j * u * j⁻¹) * b⁻¹ := by group
      _ = (b * u * b⁻¹)⁻¹ := by rw [he]; group
  ·
    exfalso
    obtain ⟨a, ⟨-, haA⟩, hconj⟩ := exists_conj_sylowT (K := ⊤) le_top
      (Q := zpowers j) (zpowers_le.2 ⟨mem_top j, hjA⟩) (isPGroup_zpowers_of_pow_four hj4)
    obtain ⟨k, hk, b, -, hty', hjS, hjO', hjk, -⟩ := toRep haA (hconj j (mem_zpowers j))
    exact h2 k hk hty' _ hjS hjO' hjk

end CFSG.KC.O8

end
