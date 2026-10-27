module

public import CFSG.ClassicalInvolution.Q3.Q3ExcGroup
public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.LieType.HighestRoot
open scoped MatrixGroups

@[expose] def Exc3Big {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  CFSG.IsQuasisimple A ∧
    ∀ z ∈ A, (∀ g ∈ A, g * z = z * g) → ∃ m : ℕ, z ^ (2 ^ m) = 1

@[expose] def Exc3Small {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  Nonempty (SL(2, ZMod 3) ≃* A)

theorem exc3Small_natCard {G : Type*} [Group G] {A : Subgroup G} (h : Exc3Small A) :
    Nat.card A = 24 := by
  obtain ⟨e⟩ := h
  rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]

section Join

variable {G : Type*} [Group G] {ι : Type*}

theorem exc3_iSup_comm (H : ι → Subgroup G) (hc : ∀ i j, ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) :
    ∀ a ∈ ⨆ i, H i, ∀ b ∈ ⨆ i, H i, a * b = b * a := by
  have step : ∀ i, ∀ a ∈ H i, ∀ b ∈ ⨆ j, H j, a * b = b * a := by
    intro i a ha b hb
    have hle : (⨆ j, H j) ≤ Subgroup.centralizer ({a} : Set G) := by
      refine iSup_le fun j y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc i j a ha y hy).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm
  intro a ha b hb
  induction ha using Subgroup.iSup_induction' with
  | hp i x hx => exact step i x hx b hb
  | h1 => simp
  | hmul x y _ _ hx hy =>
    calc x * y * b = x * (y * b) := by group
      _ = x * (b * y) := by rw [hy]
      _ = (x * b) * y := by group
      _ = (b * x) * y := by rw [hx]
      _ = b * (x * y) := by group

theorem exc3_iSup_pow_eq_one (H : ι → Subgroup G)
    (hc : ∀ i j, ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a)
    (h2 : ∀ i, ∀ x ∈ H i, ∃ m : ℕ, x ^ (2 ^ m) = 1) :
    ∀ x ∈ ⨆ i, H i, ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  intro x hx
  induction hx using Subgroup.iSup_induction' with
  | hp i y hy => exact h2 i y hy
  | h1 => exact ⟨0, by simp⟩
  | hmul a b ha hb hma hmb =>
    obtain ⟨m, hm⟩ := hma
    obtain ⟨n, hn⟩ := hmb
    have hab : Commute a b := exc3_iSup_comm H hc a
      (by simpa using ha) b (by simpa using hb)
    refine ⟨m + n, ?_⟩
    rw [hab.mul_pow, pow_add, pow_mul, hm, one_pow, one_mul, mul_comm (2 ^ m), pow_mul, hn,
      one_pow]

theorem exc3_mem_zpowers_pow_two_pow {M : Type*} [Group M] {n : M} (hodd : Odd (orderOf n))
    (m : ℕ) : n ∈ Subgroup.zpowers (n ^ (2 ^ m)) := by
  rw [mem_zpowers_pow_iff]
  exact (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)).symm

theorem exc3_eq_one_of_pow_two_pow {M : Type*} [Group M] {n : M} (hodd : Odd (orderOf n))
    {m : ℕ} (h : n ^ (2 ^ m) = 1) : n = 1 := by
  have h1 : orderOf n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : Nat.Coprime (orderOf n) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

end Join

section OddNormal

variable {G : Type*} [Group G] [Finite G]

theorem exc3_inf_eq_bot_of_comp {A : Subgroup G} (hA : Exc3Big A ∨ Exc3Small A)
    {M : Subgroup G} (hodd : Odd (Nat.card M))
    (hMn : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M) : M ⊓ A = ⊥ := by
  have hN : ((M ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnM, hnA⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa using hMn g g.2 n hnM
    · simpa using mul_mem (mul_mem g.2 hnA) (inv_mem g.2)
  have hodd' : ∀ y ∈ M, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard M hy)
  rcases hA with ⟨hq, h2⟩ | hs
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
    · exfalso
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_isQuasisimple (ModelFacts.open_isQuasisimple hq)
      have hxM : (x : G) ∈ M := by
        have : x ∈ (M ⊓ A).subgroupOf A := htop ▸ Subgroup.mem_top x
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
      have h := hodd' _ hxM
      rw [Subgroup.orderOf_coe, hx] at h
      exact absurd h (by decide)
    · refine eq_bot_iff.mpr fun y hy => ?_
      rw [Subgroup.mem_bot]
      have hyc : (⟨y, hy.2⟩ : A) ∈ Subgroup.center A := hcen (Subgroup.mem_subgroupOf.2 hy)
      obtain ⟨k, hk⟩ := h2 y hy.2 (fun g hg => by
        have := Subgroup.mem_center_iff.mp hyc ⟨g, hg⟩
        exact (congrArg Subtype.val this))
      exact exc3_eq_one_of_pow_two_pow (hodd' y hy.1) hk
  · obtain ⟨e⟩ := hs
    refine eq_bot_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot]
    by_contra hy1
    have hcard : Nat.card A = 24 := by
      rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]
    have hord : orderOf y ∣ 24 := by
      have := Subgroup.orderOf_dvd_natCard A hy.2
      rwa [hcard] at this
    have hy3 : y ^ 3 = 1 := by
      have h3 : orderOf y ∣ 3 := by
        have hc : Nat.Coprime (orderOf y) 8 := by
          have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr (hodd' y hy.1))
          simpa using this
        have h24 : orderOf y ∣ 3 * 8 := by simpa using hord
        exact (Nat.Coprime.dvd_of_dvd_mul_right hc h24)
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    have htop := eq_top_of_normal_of_pow_three (B := A) e
      (N := (M ⊓ A).subgroupOf A) (fun x hx g => hN.conj_mem x hx g) (x := ⟨y, hy.2⟩)
      (Subgroup.mem_subgroupOf.2 hy) (Subtype.ext hy3 : (⟨y, hy.2⟩ : A) ^ 3 = 1)
      (fun h => hy1 (congrArg Subtype.val h))
    have h1 : (e (-1) : G) ∈ M := by
      have : (e (-1)) ∈ (M ⊓ A).subgroupOf A := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
    have h2 := orderOf_injective e.toMonoidHom e.injective (-1)
    simp only [MulEquiv.coe_toMonoidHom] at h2
    have h3 := hodd' _ h1
    rw [Subgroup.orderOf_coe, h2, orderOf_neg_one_SL23] at h3
    exact absurd h3 (by decide)

omit [Finite G] in
theorem exc3_center_pow_eq_one {A : Subgroup G} (hA : Exc3Big A ∨ Exc3Small A) :
    ∀ x ∈ A ⊓ Subgroup.centralizer (A : Set G), ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  intro x hx
  have hxc : (⟨x, hx.1⟩ : A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
  rcases hA with ⟨-, h2⟩ | hs
  · exact h2 x hx.1 (fun g hg => (Subgroup.mem_centralizer_iff.mp hx.2 g hg))
  · obtain ⟨e⟩ := hs
    have key : ∀ g : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y * g = g * y) →
        g = 1 ∨ g = -1 := by decide +kernel
    have hc' : ∀ y : SL(2, ZMod 3), y * e.symm ⟨x, hx.1⟩ = e.symm ⟨x, hx.1⟩ * y := by
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (e y) (e y).2)
    have hsq : (e.symm ⟨x, hx.1⟩) ^ 2 = 1 := by
      rcases key _ hc' with h | h
      · rw [h]; simp
      · rw [h]; decide +kernel
    refine ⟨1, ?_⟩
    have h2 : (⟨x, hx.1⟩ : A) ^ 2 = 1 := by
      apply e.symm.injective
      rw [map_pow, hsq, map_one]
    simpa using congrArg Subtype.val h2

end OddNormal

section Layer

variable {G : Type} [Group G] [Finite G] {ι : Type*} [Finite ι]

theorem exc3_oddNormal_eq_bot_of_comp (C : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, a * b = b * a)
    (hC : ∀ i, Exc3Big (C i) ∨ Exc3Small (C i))
    (hexp : ∀ g : G, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i)
    {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  classical
  set P : Subgroup G := ⨆ i, C i with hP
  have hodd' : ∀ y ∈ N, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hy)
  have hNP : ∀ n ∈ N, n ∈ P := by
    intro n hn
    obtain ⟨m, hm⟩ := hexp n
    exact (Subgroup.zpowers_le.mpr hm) (exc3_mem_zpowers_pow_two_pow (hodd' n hn) m)
  have hnorm : ∀ i, ∀ g ∈ P, ∀ c ∈ C i, g * c * g⁻¹ ∈ C i := by
    intro i g hg
    induction hg using Subgroup.iSup_induction' with
    | hp j a ha =>
      intro c hc
      by_cases hij : j = i
      · subst hij
        exact mul_mem (mul_mem ha hc) (inv_mem ha)
      · have h1 : a * c = c * a := hcomm j i hij a ha c hc
        have : a * c * a⁻¹ = c := by rw [h1]; group
        rw [this]
        exact hc
    | h1 =>
      intro c hc
      simpa using hc
    | hmul a b _ _ iha ihb =>
      intro c hc
      have e : a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact iha _ (ihb c hc)
  have hNC : ∀ n ∈ N, ∀ i, ∀ c ∈ C i, n * c = c * n := by
    intro n hn i c hc
    have hbot := exc3_inf_eq_bot_of_comp (hC i) hodd
      (fun a _ m hm => ‹N.Normal›.conj_mem m hm a)
    have hmem : n * c * n⁻¹ * c⁻¹ ∈ N ⊓ C i := by
      refine ⟨?_, ?_⟩
      · have : n * c * n⁻¹ * c⁻¹ = n * (c * n⁻¹ * c⁻¹) := by group
        rw [this]
        exact N.mul_mem hn (‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) c)
      · exact (C i).mul_mem (hnorm i n (hNP n hn) c hc) ((C i).inv_mem hc)
    rw [hbot, Subgroup.mem_bot] at hmem
    calc n * c = n * c * n⁻¹ * c⁻¹ * (c * n) := by group
      _ = c * n := by rw [hmem, one_mul]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnP : n ∈ P := hNP n hn
  have hnc : ∀ y ∈ P, n * y = y * n := by
    intro y hy
    induction hy using Subgroup.iSup_induction' with
    | hp i c hc => exact hNC n hn i c hc
    | h1 => simp
    | hmul a b _ _ ha hb =>
      calc n * (a * b) = (n * a) * b := by group
        _ = a * (n * b) := by rw [ha]; group
        _ = a * (b * n) := by rw [hb]
        _ = a * b * n := by group
  have hZ := exc3_center_le_iSup C hcomm hnP hnc
  have hZc : ∀ i j, ∀ a ∈ C i ⊓ Subgroup.centralizer (C i : Set G),
      ∀ b ∈ C j ⊓ Subgroup.centralizer (C j : Set G), a * b = b * a := by
    intro i j a ha b hb
    by_cases hij : i = j
    · subst hij
      exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
    · exact hcomm i j hij a ha.1 b hb.1
  obtain ⟨m, hm⟩ := exc3_iSup_pow_eq_one
    (fun i => C i ⊓ Subgroup.centralizer (C i : Set G)) hZc
    (fun i => exc3_center_pow_eq_one (hC i)) n hZ
  exact exc3_eq_one_of_pow_two_pow (hodd' n hn) hm

theorem exc3_member_eq_small (C : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, a * b = b * a)
    (hC : ∀ i, Exc3Big (C i) ∨ Exc3Small (C i))
    (hsub : ∀ i, Exc3Big (C i) → (C i).IsSubnormal)
    (hexp : ∀ g : G, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i)
    (hone : ∀ i j, Exc3Small (C i) → Exc3Small (C j) → i = j)
    {L : Subgroup G} (eL : SL(2, ZMod 3) ≃* L) (hL : L.IsSubnormal) :
    ∃ i, Exc3Small (C i) ∧ L = C i := by
  classical
  have hK3 : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have eL' : L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := eL.symm
  have hgen : Subgroup.closure {y : L | orderOf y = 3} = ⊤ :=
    closure_orderOf_three_eq_top_of_mulEquiv hK3 eL'
  have hLsolv : Group.IsSolvable L := isSolvable_of_mulEquiv hK3 eL'
  have hcent : ∀ i, Exc3Big (C i) → ∀ x ∈ L, ∀ s ∈ C i, x * s = s * x := by
    intro i hi x hx s hs
    have h := (CFSG.LocalCores.component_solvable_centralizer hLsolv hL).1 (C i)
      ⟨hi.1, hsub i hi⟩
    have hm := Subgroup.commutator_mem_commutator hs hx
    rw [h, Subgroup.mem_bot] at hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
  let Big := {i : ι // Exc3Big (C i)}
  let Small := {i : ι // ¬ Exc3Big (C i)}
  set P : Subgroup G := ⨆ i : Big, C i.1 with hP
  set Q : Subgroup G := ⨆ i : Small, C i.1 with hQ
  have hSPQ : (⨆ i, C i) = P ⊔ Q := by
    rw [iSup_split C (fun i => Exc3Big (C i)), iSup_subtype', iSup_subtype']
  have hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := by
    intro p hp q hq
    have hle : P ≤ Subgroup.centralizer (Q : Set G) := by
      refine iSup_le fun i u hu => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hle2 : Q ≤ Subgroup.centralizer (C i.1 : Set G) := by
        refine iSup_le fun j v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
        exact hcomm i.1 j.1 hij w hw v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle2 hv) u hu).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hp) q hq).symm
  have hLP : ∀ x ∈ L, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hle : P ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup_le fun i u hu => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent i.1 i.2 x hx u hu).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hord3 : ∀ x ∈ L, x ^ 3 = 1 → x ∈ Q := by
    intro x hx hx3
    have hoddx : Odd (orderOf x) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3)
    have hxS : x ∈ P ⊔ Q := by
      obtain ⟨m, hm⟩ := hexp x
      rw [← hSPQ]
      exact (Subgroup.zpowers_le.mpr hm) (exc3_mem_zpowers_pow_two_pow hoddx m)
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_commute hPQ).mp hxS
    have hpc : ∀ y ∈ P, p * y = y * p := by
      intro y hy
      have e1 := hLP (p * q) hx y hy
      have e2 := hPQ y hy q hq
      have e3 : p * y * q = y * p * q := by
        calc p * y * q = p * (y * q) := by group
          _ = p * (q * y) := by rw [e2]
          _ = p * q * y := by group
          _ = y * (p * q) := e1
          _ = y * p * q := by group
      exact mul_right_cancel e3
    have hcommB : ∀ i j : Big, i ≠ j → ∀ a ∈ C i.1, ∀ b ∈ C j.1, a * b = b * a :=
      fun i j hij a ha b hb => hcomm i.1 j.1 (fun h => hij (Subtype.ext h)) a ha b hb
    have hp2 : ∃ m : ℕ, p ^ (2 ^ m) = 1 := by
      have hmem := exc3_center_le_iSup (fun i : Big => C i.1) hcommB hp hpc
      refine exc3_iSup_pow_eq_one
        (fun i : Big => C i.1 ⊓ Subgroup.centralizer (C i.1 : Set G)) ?_
        (fun i => exc3_center_pow_eq_one (Or.inl i.2)) p hmem
      intro i j a ha b hb
      by_cases hij : i = j
      · subst hij
        exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
      · exact hcommB i j hij a ha.1 b hb.1
    obtain ⟨m, hm⟩ := hp2
    have hpk : ∃ k, orderOf p = 2 ^ k := by
      have h1 : orderOf p ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hpk
    have hpq : Commute p q := hPQ p hp q hq
    have h1 : (p * q) ^ 3 = p ^ 3 * q ^ 3 := hpq.mul_pow 3
    have h2 : p ^ 3 * q ^ 3 = 1 := by rw [← h1]; exact hx3
    have h3 : p ^ 3 = (q ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have hpQ : p ∈ Q := by
      refine (Subgroup.zpowers_le.mpr ?_) (exc3_mem_zpowers_pow_three hk)
      rw [h3]
      exact Q.inv_mem (Q.pow_mem hq 3)
    exact Q.mul_mem hpQ hq
  have hLQ : L ≤ Q := by
    intro x hx
    have hle : Subgroup.closure {y : L | orderOf y = 3} ≤ Q.subgroupOf L :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
        (hord3 y.1 y.2 (by
          have : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
          rw [← this]
          exact pow_orderOf_eq_one _))
    exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))
  by_cases hSm : Nonempty Small
  · obtain ⟨i₀⟩ := hSm
    have hsmall : ∀ i : Small, Exc3Small (C i.1) := fun i => (hC i.1).resolve_left i.2
    have hsub1 : Subsingleton Small :=
      ⟨fun i j => Subtype.ext (hone i.1 j.1 (hsmall i) (hsmall j))⟩
    have hQeq : Q = C i₀.1 :=
      le_antisymm (iSup_le fun i => by rw [Subsingleton.elim i i₀])
        (le_iSup (fun i : Small => C i.1) i₀)
    refine ⟨i₀.1, hsmall i₀, ?_⟩
    exact eq_of_le_of_natCard_le eL (hQeq ▸ hLQ) (by rw [exc3Small_natCard (hsmall i₀)])
  · exfalso
    rw [not_nonempty_iff] at hSm
    have hQbot : Q = ⊥ := by
      rw [hQ]
      exact iSup_of_empty _
    have hL1 : L = ⊥ := le_bot_iff.mp (hQbot ▸ hLQ)
    have hnt : Nontrivial (SL(2, ZMod 3)) := ⟨⟨-1, 1, by decide +kernel⟩⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : SL(2, ZMod 3))
    have := eL.injective (a₁ := a) (a₂ := 1) (by
      apply Subtype.ext
      have h1 : (eL a : G) ∈ (⊥ : Subgroup G) := hL1 ▸ (eL a).2
      rw [Subgroup.mem_bot] at h1
      simpa using h1)
    exact ha this

end Layer

section Ambient

variable {B : Type} [Group B] {ι : Type*} [Finite ι]

theorem exc3Big_subgroupOf {Y A : Subgroup B} (hA : A ≤ Y) (h : Exc3Big A) :
    Exc3Big (A.subgroupOf Y) := by
  obtain ⟨hq, h2⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA).symm hq,
    fun z hz hzc => ?_⟩
  obtain ⟨m, hm⟩ := h2 (z : B) hz (fun g hg => by
    have := hzc ⟨g, hA hg⟩ (Subgroup.mem_subgroupOf.2 hg)
    exact congrArg Subtype.val this)
  exact ⟨m, Subtype.ext hm⟩

theorem exc3Small_subgroupOf {Y A : Subgroup B} (hA : A ≤ Y) (h : Exc3Small A) :
    Exc3Small (A.subgroupOf Y) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe hA).symm⟩

theorem exc3_isSubnormal_subgroupOf {A Y : Subgroup B} (h : IsSubnormal A Y) :
    (A.subgroupOf Y).IsSubnormal := by
  have h1 := isSubnormal_subgroupOf h Y
  rw [Subgroup.subgroupOf_self] at h1
  exact (CFSG.Adapters.isSubnormal_top_iff _).1 h1

omit [Finite ι] in
theorem exc3_iSup_subgroupOf_mem {Y : Subgroup B} (C : ι → Subgroup B) (hCY : ∀ i, C i ≤ Y)
    {x : B} (hx : x ∈ ⨆ i, C i) :
    ∃ hxY : x ∈ Y, (⟨x, hxY⟩ : Y) ∈ ⨆ i, (C i).subgroupOf Y := by
  induction hx using Subgroup.iSup_induction' with
  | hp i y hy =>
    exact ⟨hCY i hy, Subgroup.mem_iSup_of_mem i (Subgroup.mem_subgroupOf.2 hy)⟩
  | h1 => exact ⟨one_mem _, one_mem _⟩
  | hmul a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    exact ⟨mul_mem h1 h3, mul_mem h2 h4⟩

omit [Finite ι] in
theorem exc3_subgroupOf_hexp {Y : Subgroup B} (C : ι → Subgroup B) (hCY : ∀ i, C i ≤ Y)
    (hexp : ∀ g ∈ Y, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i) (g : Y) :
    ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, (C i).subgroupOf Y := by
  obtain ⟨m, hm⟩ := hexp g.1 g.2
  obtain ⟨hY, h⟩ := exc3_iSup_subgroupOf_mem C hCY hm
  exact ⟨m, h⟩

theorem exc3_oddNormal_eq_bot_of_comp_amb {Y : Subgroup B} [Finite Y] (C : ι → Subgroup B)
    (hCY : ∀ i, C i ≤ Y) (hcomm : ∀ i j, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, a * b = b * a)
    (hC : ∀ i, Exc3Big (C i) ∨ Exc3Small (C i))
    (hexp : ∀ g ∈ Y, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i) {N : Subgroup B} (hNY : N ≤ Y)
    (hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hN' : (N.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g g.2 n hn
  have hodd' : Odd (Nat.card (N.subgroupOf Y)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]
  have hbot := exc3_oddNormal_eq_bot_of_comp (G := ↥Y) (fun i => (C i).subgroupOf Y)
    (fun i j hij a ha b hb => Subtype.ext (hcomm i j hij a ha b hb))
    (fun i => (hC i).imp (exc3Big_subgroupOf (hCY i)) (exc3Small_subgroupOf (hCY i)))
    (exc3_subgroupOf_hexp C hCY hexp) hodd'
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have h1 : (⟨n, hNY hn⟩ : Y) ∈ N.subgroupOf Y := Subgroup.mem_subgroupOf.2 hn
  rw [hbot, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

theorem exc3_member_eq_small_amb {Y : Subgroup B} [Finite Y] (C : ι → Subgroup B)
    (hCY : ∀ i, C i ≤ Y) (hcomm : ∀ i j, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, a * b = b * a)
    (hC : ∀ i, Exc3Big (C i) ∨ Exc3Small (C i))
    (hsub : ∀ i, Exc3Big (C i) → IsSubnormal (C i) Y)
    (hexp : ∀ g ∈ Y, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i)
    (hone : ∀ i j, Exc3Small (C i) → Exc3Small (C j) → i = j) {L : Subgroup B} (hLY : L ≤ Y)
    (eL : SL(2, ZMod 3) ≃* L) (hL : IsSubnormal L Y) : ∃ i, Exc3Small (C i) ∧ L = C i := by
  have eL' : SL(2, ZMod 3) ≃* L.subgroupOf Y := eL.trans (Subgroup.subgroupOfEquivOfLe hLY).symm
  obtain ⟨i, hi, hLi⟩ := exc3_member_eq_small (G := ↥Y) (fun i => (C i).subgroupOf Y)
    (fun i j hij a ha b hb => Subtype.ext (hcomm i j hij a ha b hb))
    (fun i => (hC i).imp (exc3Big_subgroupOf (hCY i)) (exc3Small_subgroupOf (hCY i)))
    (fun i hi => by
      have hi' : Exc3Big (C i) := by
        obtain ⟨hq, h2⟩ := hi
        refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (hCY i)) hq, fun z hz hzc => ?_⟩
        obtain ⟨m, hm⟩ := h2 ⟨z, hCY i hz⟩ (Subgroup.mem_subgroupOf.2 hz) (fun g hg =>
          Subtype.ext (hzc (g : B) (Subgroup.mem_subgroupOf.1 hg)))
        exact ⟨m, congrArg Subtype.val hm⟩
      exact exc3_isSubnormal_subgroupOf (hsub i hi'))
    (exc3_subgroupOf_hexp C hCY hexp)
    (fun i j hi hj => hone i j (by
      obtain ⟨e⟩ := hi
      exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (hCY i))⟩) (by
      obtain ⟨e⟩ := hj
      exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (hCY j))⟩))
    eL' (exc3_isSubnormal_subgroupOf hL)
  refine ⟨i, ?_, ?_⟩
  · obtain ⟨e⟩ := hi
    exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (hCY i))⟩
  · have := (Subgroup.subgroupOf_inj).1 hLi
    rwa [inf_eq_left.mpr hLY, inf_eq_left.mpr (hCY i)] at this

end Ambient

end CFSG.ClassicalInvolution.Q3
