module

public import CFSG.GH74.Uniqueness.Section164A
public import CFSG.GH74.Uniqueness.Section164Dict
public import CFSG.GH74.Uniqueness.Section12Center

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

theorem lemma162_B0
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) :
    ∃ m : ℕ, 2 ≤ m ∧
      ((fZero Z M c.B0 c.t = c.B0 ∧
          (Bender.BenderType ↥c.B0 m 1 1 ∨ Bender.BenderType ↥c.B0 m 2 1)) ∨
        (Bender.BenderType ↥(fZero Z M c.B0 c.t) m 1 1 ∧ (∃ e, BenderSub Z M c.B0 m 3 e) ∧
          ⁅zpowers c.t, (M ⊓ conjugate M c.t) ⊓ c.B0⁆ ≤ fZero Z M c.B0 c.t ∧
          ∀ v : MulAut ↥c.B0, v * v = 1 → (∀ x : ↥c.B0, (x : X) = c.z ∨ (x : X) = c.t → v x = x) →
            ∀ x : ↥c.B0, (x : X) ∈ fZero Z M c.B0 c.t → v x = x)) := by
  obtain ⟨y, hy, hyz⟩ := exists_mem_gamma_ne S c
  exact h162 c.toCtx16 c.B0 (cenHull_ne_top S c.hu2) (z_mem_B0 c) (t_mem_B0 c)
    ⟨y, hy.1, subset_closure ⟨hy.1, (mem_inf.mp hy.2).1⟩, (mem_inf.mp hy.2).2, hyz⟩
    (zHull_zHull _)

theorem fZero_B0 (c : Conf16 Z M) : fZero Z M c.B0 c.t = c.Bzero := fZero_eq_Bzero c rfl

theorem exists_benderType_Bzero
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    ∃ i' e' : ℕ, Bender.BenderType ↥c.Bzero n i' e' := by
  obtain ⟨m, -, ⟨hF, hBT⟩ | ⟨hBT, ⟨e', hB'⟩, -⟩⟩ := lemma162_B0 S h162 c
  · rw [fZero_B0] at hF
    have hmn : ∀ {i' e'}, Bender.BenderType ↥c.B0 m i' e' → m = n := by
      intro i' e' h'
      have hc := h'.center_eq_bot
      exact (h'.unique (benderType_of_center_eq_bot hB.bender hc)).1
    rcases hBT with h' | h'
    · rw [← hmn h']
      exact ⟨1, 1, h'.of_mulEquiv (MulEquiv.subgroupCongr hF.symm)⟩
    · rw [← hmn h']
      exact ⟨2, 1, h'.of_mulEquiv (MulEquiv.subgroupCongr hF.symm)⟩
  · have hmn : n = m := (hB.bender.unique hB'.bender).1
    rw [fZero_B0] at hBT
    rw [hmn]
    exact ⟨1, 1, hBT⟩

theorem invol_Bzero {n i e : ℕ} (c : Conf16 Z M) (hB : BenderSub Z M c.B0 n i e) :
    ∀ y ∈ c.Bzero, orderOf y = 2 → y ∈ Z := fun y hy hy2 =>
  hB.invol y (Bzero_le_B0 c hy) hy2

theorem Bzero_not_le (c : Conf16 Z M) : ¬ c.Bzero ≤ M := fun h => c.htM (h (t_mem_Bzero c))

theorem inter_Bzero_eq (c : Conf16 Z M) :
    Z ∩ ((M ⊓ c.Bzero : Subgroup X) : Set X) = Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := by
  ext y
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_inf]
  constructor
  · rintro ⟨hyZ, hyM, hyB⟩
    exact ⟨hyZ, Bzero_le_B c hyB, hyM⟩
  · rintro ⟨hyZ, hyB, hyM⟩
    exact ⟨hyZ, hyM, gamma_subset_Bzero c ⟨hyZ, mem_inf.mpr ⟨hyB, hyM⟩⟩⟩

theorem exists_sylow_Bzero
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i' e' : ℕ}
    (hBz : Bender.BenderType ↥c.Bzero n i' e') {n₀ i e : ℕ} (hB : BenderSub Z M c.B0 n₀ i e) :
    ∃ Q₀ : Sylow 2 ↥c.Bzero,
      (⟨c.z, z_mem_Bzero c⟩ : ↥c.Bzero) ∈ Bender.rootCenter (Q₀ : Subgroup ↥c.Bzero) ∧
      M.comap c.Bzero.subtype = Bender.borel (Q₀ : Subgroup ↥c.Bzero) ∧
      zHull Z (c.B ⊓ M) = (Bender.rootCenter (Q₀ : Subgroup ↥c.Bzero)).map c.Bzero.subtype ∧
      Nat.card ↥(zHull Z (c.B ⊓ M)) = 2 ^ n := by
  obtain ⟨Q₀, hzR, hQ₀⟩ := exists_sylow_borel_eq S hBz c.hz c.hzM (z_mem_Bzero c)
    (Bzero_not_le c)
  have hzh : zHull Z (c.B ⊓ M) = zHull Z (M ⊓ c.Bzero) :=
    congrArg Subgroup.closure (inter_Bzero_eq c).symm
  refine ⟨Q₀, hzR, hQ₀, ?_, ?_⟩
  · rw [hzh]
    exact zHull_inter_eq_map_rootCenter hBz hQ₀ (invol_Bzero c hB) S.invariant
  · rw [hzh]
    exact card_zHull_inter hBz hQ₀ (invol_Bzero c hB) S.invariant

theorem zHull_le_P (S : ZDSetup X Z M) (c : Conf16 Z M) {n : ℕ}
    (hcard : Nat.card ↥(zHull Z (c.B ⊓ M)) = 2 ^ n) : zHull Z (c.B ⊓ M) ≤ c.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := c.B0 ⊓ M with hK
  have hQK : zHull Z (c.B ⊓ M) ≤ K := by
    refine (closure_le _).mpr ?_
    rintro y ⟨hyZ, hyBM⟩
    exact mem_inf.mpr ⟨subset_closure ⟨hyZ, (mem_inf.mp hyBM).1⟩, (mem_inf.mp hyBM).2⟩
  have hnorm : K ≤ normalizer (zHull Z (c.B ⊓ M) : Set X) := by
    refine le_trans ?_ (le_normalizer_zHull S.invariant (c.B ⊓ M))
    exact le_inf (inf_le_left.trans (B0_le_B c)) inf_le_right
  have hN : ((zHull Z (c.B ⊓ M)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hnorm
  have hp : IsPGroup 2 ((zHull Z (c.B ⊓ M)).subgroupOf K) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  obtain ⟨Sy, hSy⟩ := c.hP
  have hle := hp.le_sylow_of_normal Sy
  intro x hx
  rw [← hSy]
  exact ⟨⟨x, hQK hx⟩, hle hx, rfl⟩

theorem Q_eq_zHull
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) :
    c.Q = zHull Z (c.B ⊓ M) ∧ Nat.card ↥c.Q = 2 ^ n ∧
      ∀ x ∈ c.Q, x ≠ 1 → x ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := by
  obtain ⟨i', e', hBz⟩ := exists_benderType_Bzero S h162 c hB
  obtain ⟨Q₀, -, hQ₀, hzh, hcard⟩ := exists_sylow_Bzero S c hBz hB
  have hle := zHull_le_P S c hcard
  have hPM : c.P ≤ c.B0 ⊓ M := c.hP.le
  have heq : c.Q = zHull Z (c.B ⊓ M) := by
    apply le_antisymm
    · refine (closure_le _).mpr ?_
      rintro x ⟨hxP, hx2⟩
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
        have hxB0 := (mem_inf.mp (hPM hxP)).1
        exact subset_closure ⟨hB.invol x hxB0 hxo,
          mem_inf.mpr ⟨B0_le_B c hxB0, (mem_inf.mp (hPM hxP)).2⟩⟩
    · refine (closure_le _).mpr ?_
      rintro x hx
      refine subset_closure ⟨hle (subset_closure hx), S.invariant.mul_self_eq_one hx.1⟩
  refine ⟨heq, heq ▸ hcard, fun x hx hx1 => ?_⟩
  rw [heq, hzh] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h]; rfl)
  obtain ⟨hyM, hyo⟩ := mem_inter_of_mem_rootCenter hBz hQ₀ hy hy1
  exact ⟨invol_Bzero c hB _ y.2 hyo, mem_inf.mpr ⟨Bzero_le_B c y.2, hyM⟩⟩

theorem exists_conj_gamma
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) {x : X}
    (hx : x ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X)) :
    ∃ d ∈ c.B ⊓ M, x = d⁻¹ * c.z * d := by
  obtain ⟨i', e', hBz⟩ := exists_benderType_Bzero S h162 c hB
  obtain ⟨Q₀, hzR, hQ₀, -, -⟩ := exists_sylow_Bzero S c hBz hB
  have hxB : x ∈ c.Bzero := gamma_subset_Bzero c hx
  have hxR : (⟨x, hxB⟩ : ↥c.Bzero) ∈ Bender.rootCenter (Q₀ : Subgroup ↥c.Bzero) :=
    mem_rootCenter_of_mem hBz hQ₀ hxB (mem_inf.mp hx.2).2 (S.invariant.1 x hx.1)
  have hne1 : ∀ {y : X} (hy : y ∈ c.Bzero), y ∈ Z → (⟨y, hy⟩ : ↥c.Bzero) ≠ 1 := by
    intro y hy hyZ h
    have h1 : y = 1 := congrArg Subtype.val h
    have := S.invariant.1 y hyZ
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨hc, -⟩ := cartan_eq_comap hBz hQ₀ (t_mem_Bzero c) c.htM
    (S.invariant.mul_self_eq_one c.ht)
  obtain ⟨d, hd, hdx⟩ := hc.exists_cartan_conj hzR (hne1 (z_mem_Bzero c) c.hz) hxR
    (hne1 hxB hx.1)
  have hdM : (d : X) ∈ M := by
    have : d ∈ Bender.borel (Q₀ : Subgroup ↥c.Bzero) := Bender.cartan_le_borel _ _ hd
    rw [← hQ₀] at this
    exact this
  refine ⟨d, mem_inf.mpr ⟨Bzero_le_B c d.2, hdM⟩, ?_⟩
  have := congrArg Subtype.val hdx
  simpa using this

end Sec164

end CFSG.GH74.Uniqueness
