module

public import CFSG.GH74.Uniqueness.Section164A
public import CFSG.GH74.Uniqueness.Section164Perfect

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

theorem isSylowOf_P_B0
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) : ABGLocalTools.IsSylowOf 2 c.P c.B0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hP2, hdvd⟩ := ABGLocalTools.isSylowOf_iff.mp c.hP
  refine ABGLocalTools.isSylowOf_iff.mpr ⟨hle.trans inf_le_left, hP2, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex c.P (c.B0 ⊓ M) c.B0 hle inf_le_left]
  intro h2
  have hidx : (c.B0 ⊓ M).relIndex c.B0 = (2 ^ n) ^ i + 1 := by
    rw [Subgroup.relIndex, inf_comm]
    exact hB.index_eq S
  have hodd : Odd ((2 ^ n) ^ i + 1) := by
    obtain ⟨hi, hn⟩ := hB.bender.two_le
    have : Even ((2 ^ n) ^ i) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩
    exact this.add_one
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hdvd h
  · rw [hidx] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem inf_T1_eq_P (c : Conf16 Z M) : c.B0 ⊓ c.T1 = c.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine c.hP.eq_of_le (le_inf (c.hP.le.trans inf_le_left) c.hPT1) ?_ c.hT1.isPGroup.to_inf_right
  exact le_inf inf_le_left (inf_le_right.trans (c.hT1.le.trans inf_le_right))

theorem odd_card_center_B0 (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    Odd (Nat.card (center ↥c.B0)) := by
  have h := odd_card_pPrimeCoreIn c.B0
  rwa [hB.core, card_map_of_injective c.B0.subtype_injective] at h

theorem closure_involutions_B0 (hZ : IsInvariantInvolutionSet Z) (c : Conf16 Z M) :
    closure {x : X | x ∈ c.B0 ∧ x * x = 1} = c.B0 := by
  apply le_antisymm
  · exact (closure_le _).mpr fun x hx => hx.1
  · exact closure_mono fun x hx => ⟨subset_closure hx, hZ.mul_self_eq_one hx.1⟩

theorem u_mem_T1 (c : Conf16 Z M) : c.u ∈ c.T1 :=
  mem_of_isSylowOf_centralizer c.u_mem_M c.hu2 c.hT1

theorem T1_le_B (c : Conf16 Z M) : c.T1 ≤ c.B := c.hT1.le.trans inf_le_left

theorem u_mem_BJ (c : Conf16 Z M) : c.u ∈ c.B ⊓ c.J := by
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  rw [mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.mp (B0_le_B c hh)

theorem eq_one_or_u_of_mem_BJ (c : Conf16 Z M)
    (hu : ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 →
    y = c.u) {j : X} (hj : j ∈ c.B ⊓ c.J) (hj2 : j * j = 1) : j = 1 ∨ j = c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hj1 : j = 1
  · exact Or.inl hj1
  · right
    refine hu j (mem_inf.mpr ⟨(mem_inf.mp hj).1, ?_⟩) (orderOf_eq_prime (by rw [sq]; exact hj2) hj1)
    rw [mem_centralizer_iff]
    intro h hh
    exact (mem_centralizer_iff.mp (mem_inf.mp hj).2) h (Bzero_le_B0 c hh)

theorem mem_Q_sup_of_mul (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e)
    (hu : ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 → y = c.u) {b j : X}
    (hb : b ∈ c.B0) (hj : j ∈ c.B ⊓ c.J) (hy : b * j ∈ c.T1) (hy2 : (b * j) * (b * j) = 1) :
    b * j ∈ c.Q ⊔ zpowers c.u := by
  have hjc : ∀ f ∈ c.B0, f * j = j * f := fun f hf =>
    mem_centralizer_iff.mp (mem_inf.mp hj).2 f hf
  have hbj : b * j = j * b := hjc b hb
  have hc0 : b * b ∈ c.J := by
    rw [mem_centralizer_iff]
    intro f hf
    have e : b * b = (j * j)⁻¹ := by
      have : b * b * (j * j) = 1 := by
        calc b * b * (j * j) = b * (b * j) * j := by group
          _ = b * (j * b) * j := by rw [hbj]
          _ = (b * j) * (b * j) := by group
          _ = 1 := hy2
      exact eq_inv_of_mul_eq_one_left this
    rw [e]
    have h1 : f * (j * j) = (j * j) * f := by
      calc f * (j * j) = (f * j) * j := by group
        _ = (j * f) * j := by rw [hjc f hf]
        _ = j * (f * j) := by group
        _ = j * (j * f) := by rw [hjc f hf]
        _ = (j * j) * f := by group
    calc f * (j * j)⁻¹ = (j * j)⁻¹ * ((j * j) * f) * (j * j)⁻¹ := by group
      _ = (j * j)⁻¹ * (f * (j * j)) * (j * j)⁻¹ := by rw [h1]
      _ = (j * j)⁻¹ * f := by group
  have hbbB : b * b ∈ c.B0 := mul_mem hb hb
  have hcen : (⟨b * b, hbbB⟩ : ↥c.B0) ∈ center ↥c.B0 := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hc0) g g.2)
  have hodd : Odd (orderOf (b * b)) := by
    have hdvd := orderOf_dvd_natCard (⟨⟨b * b, hbbB⟩, hcen⟩ : center ↥c.B0)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat (odd_card_center_B0 c hB) hdvd
  obtain ⟨m, hm⟩ := hodd
  generalize hk : orderOf (b * b) = k at hm
  have hbbk : (b * b) ^ k = 1 := hk ▸ pow_orderOf_eq_one (b * b)
  have hb' : b ^ k * b ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, sq, hbbk]
  have hb'B : b ^ k ∈ c.B0 := pow_mem hb k
  have hbk : b ^ k * j = j * b ^ k := (Commute.pow_left (show Commute b j from hbj) k).eq
  have hbk1 : b ^ k = b * b ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  set j' := (b ^ k)⁻¹ * (b * j) with hj'
  have hj'eq : j' = (b ^ (k - 1))⁻¹ * j := by
    rw [hj', hbk1]
    group
  have hpowJ : b ^ (k - 1) ∈ c.B ⊓ c.J := by
    have hk2 : k - 1 = 2 * m := by omega
    rw [hk2, pow_mul, sq]
    refine pow_mem (mem_inf.mpr ⟨?_, hc0⟩) m
    exact B0_le_B c hbbB
  have hj'BJ : j' ∈ c.B ⊓ c.J := by
    rw [hj'eq]
    exact mul_mem (inv_mem hpowJ) hj
  have hbb : b ^ k * b = b * b ^ k := (Commute.pow_left (Commute.refl b) k).eq
  have hcomm : b ^ k * (b * j) = (b * j) * b ^ k := by
    calc b ^ k * (b * j) = (b ^ k * b) * j := by group
      _ = (b * b ^ k) * j := by rw [hbb]
      _ = b * (b ^ k * j) := by group
      _ = b * (j * b ^ k) := by rw [hbk]
      _ = (b * j) * b ^ k := by group
  have hj'2 : j' * j' = 1 := by
    rw [hj']
    have hbki : (b ^ k)⁻¹ = b ^ k := inv_eq_of_mul_eq_one_right hb'
    rw [hbki]
    calc b ^ k * (b * j) * (b ^ k * (b * j)) = b ^ k * ((b * j) * b ^ k) * (b * j) := by group
      _ = b ^ k * (b ^ k * (b * j)) * (b * j) := by rw [hcomm]
      _ = (b ^ k * b ^ k) * ((b * j) * (b * j)) := by group
      _ = 1 := by rw [hb', hy2, one_mul]
  have hyeq : b * j = b ^ k * j' := by rw [hj']; group
  rcases eq_one_or_u_of_mem_BJ c hu hj'BJ hj'2 with h1 | h1
  ·
    have hbkT : b ^ k ∈ c.T1 := by
      have : b * j = b ^ k := by rw [hyeq, h1, mul_one]
      rw [← this]
      exact hy
    have hbkP : b ^ k ∈ c.P := by
      rw [← inf_T1_eq_P c]
      exact mem_inf.mpr ⟨hb'B, hbkT⟩
    rw [hyeq, h1, mul_one]
    exact mem_sup_left (subset_closure ⟨hbkP, hb'⟩)
  · have hbkT : b ^ k ∈ c.T1 := by
      have : b ^ k = (b * j) * c.u⁻¹ := by rw [hyeq, h1]; group
      rw [this]
      exact mul_mem hy (inv_mem (u_mem_T1 c))
    have hbkP : b ^ k ∈ c.P := by
      rw [← inf_T1_eq_P c]
      exact mem_inf.mpr ⟨hb'B, hbkT⟩
    rw [hyeq, h1]
    exact mul_mem (mem_sup_left (subset_closure ⟨hbkP, hb'⟩)) (mem_sup_right (mem_zpowers _))

theorem mem_Q_sup_of_mem_center
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e)
    (hu : ∀ y ∈ c.B ⊓ centralizer (c.Bzero : Set X), orderOf y = 2 → y = c.u) {x : X}
    (hx : x ∈ centerIn c.T1) (hx2 : x * x = 1) : x ∈ c.Q ⊔ zpowers c.u := by
  obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
  have hxB : x ∈ c.B := T1_le_B c hxT
  have hxN : x ∈ normalizer (c.B0 : Set X) := le_normalizer_zHull S.invariant _ hxB
  have hxP : ∀ p ∈ c.P, x * p = p * x := fun p hp =>
    ((mem_centralizer_iff.mp hxC) p (c.hPT1 hp)).symm
  obtain ⟨r, hrP, hr2, hr⟩ := exists_conj_of_centralizes_sylow (closure_involutions_B0 S.invariant c)
    (odd_card_center_B0 c hB) hB.bender (isSylowOf_P_B0 S c hB) hxN hxP
  have hrB0 : r ∈ c.B0 := (isSylowOf_P_B0 S c hB).le hrP
  have hjJ : r⁻¹ * x ∈ c.J := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 := hr f hf
    calc f * (r⁻¹ * x) = r⁻¹ * ((r * f * r⁻¹) * x) := by group
      _ = r⁻¹ * ((x * f * x⁻¹) * x) := by rw [h1]
      _ = r⁻¹ * x * f := by group
  have hjB : r⁻¹ * x ∈ c.B := mul_mem (inv_mem (B0_le_B c hrB0)) hxB
  have hrx : r * x = x * r := (hxP r hrP).symm
  have hT : r * (r⁻¹ * x) ∈ c.T1 := by rw [mul_inv_cancel_left]; exact hxT
  have hT2 : (r * (r⁻¹ * x)) * (r * (r⁻¹ * x)) = 1 := by rw [mul_inv_cancel_left]; exact hx2
  have := mem_Q_sup_of_mul c hB hu hrB0 (mem_inf.mpr ⟨hjB, hjJ⟩) hT hT2
  rwa [mul_inv_cancel_left] at this

end Sec164

theorem ZDSetup.lemma164b
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    closure ({c.u, c.z} : Set X) ≤ omegaOneSub (centerIn c.T1) ∧
      omegaOneSub (centerIn c.T1) ≤ c.Q ⊔ zpowers c.u ∧
      c.Q ⊔ zpowers c.u = omegaOneSub c.T := by
  have hu := (S.lemma164a h121 h161 h162 c).2
  have huT := Sec164.u_mem_T1 c
  refine ⟨?_, ?_, ?_⟩
  · refine (closure_le _).mpr ?_
    rintro y (rfl | rfl)
    · refine subset_closure ⟨mem_inf.mpr ⟨huT, ?_⟩, c.u_mul_self⟩
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (Sec164.T1_le_B c hh)
    · refine subset_closure ⟨mem_inf.mpr ⟨c.hz_T1.1, ?_⟩, S.invariant.mul_self_eq_one c.hz⟩
      rw [mem_centralizer_iff]
      intro h hh
      exact c.hz_T1.2 h hh
  · exact (closure_le _).mpr fun x hx => Sec164.mem_Q_sup_of_mem_center S c hB hu hx.1 hx.2
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · refine closure_mono ?_
        rintro y ⟨hyP, hy2⟩
        refine ⟨mem_inf.mpr ⟨c.hPT1 hyP, mem_sup_left ((Sec164.isSylowOf_P_B0 S c hB).le hyP)⟩,
          hy2⟩
      · refine zpowers_le.mpr (subset_closure ⟨mem_inf.mpr ⟨huT, mem_sup_right
          (Sec164.u_mem_BJ c)⟩, c.u_mul_self⟩)
    · refine (closure_le _).mpr ?_
      rintro y ⟨hyT, hy2⟩
      obtain ⟨hyT1, hysup⟩ := mem_inf.mp hyT
      have hle : c.B ⊓ c.J ≤ normalizer (c.B0 : Set X) :=
        inf_le_right.trans (centralizer_le_normalizer _)
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left c.B0 (c.B ⊓ c.J) hle
      have hy' : y ∈ ((c.B0 ⊔ c.B ⊓ c.J : Subgroup X) : Set X) := hysup
      rw [hset] at hy'
      obtain ⟨b, hb, j, hj, rfl⟩ := hy'
      exact Sec164.mem_Q_sup_of_mul c hB hu hb hj hyT1 hy2

end CFSG.GH74.Uniqueness
