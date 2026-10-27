module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped MatrixGroups commutatorElement

@[expose] def FrameOuterQ8Free (K : Type) [Group K] (J₂ J₄ : Subgroup K) : Prop :=
  ∀ ψ : QuaternionGroup 2 →* MulAut K, Function.Injective ψ → (∀ a, ∀ j ∈ J₂, ψ a j = j) →
    (∀ a, ∀ j ∈ J₄, ψ a j = j) → ∀ a, ∃ k : K, ψ a = MulAut.conj k

namespace TwinFr

variable {Y : Type} [Group Y]

structure Frame (L : Subgroup Y) (F' : Type) [Field F'] (x t : Y) (J₂ J₄ : Subgroup Y) :
    Prop where
  le₂ : J₂ ≤ L
  le₄ : J₄ ≤ L
  mem₂ : t ∈ J₂
  mem₄ : x * t ∈ J₄
  orderOf_xt : orderOf (x * t) = 2
  ne_one : x ≠ 1
  equiv₂ : Nonempty (J₂ ≃* SL(2, F'))
  equiv₄ : Nonempty (J₄ ≃* SL(2, F'))
  comm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a
  cent₂ : J₂ ≤ Subgroup.centralizer ({t} : Set Y)
  norm₂ : ∀ g ∈ L, g * t = t * g → ∀ j ∈ J₂, g * j * g⁻¹ ∈ J₂
  norm₄ : ∀ g ∈ L, g * t = t * g → ∀ j ∈ J₄, g * j * g⁻¹ ∈ J₄

variable {L : Subgroup Y} {F' : Type} [Field F'] {x t : Y} {J₂ J₄ : Subgroup Y}

theorem Frame.cent₄ (hfr : Frame L F' x t J₂ J₄) :
    J₄ ≤ Subgroup.centralizer ({t} : Set Y) := fun b hb => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hfr.comm t hfr.mem₂ b hb).symm

theorem comm_of_odd_of_sl2 [Finite Y] [Finite F'] (hodd : Odd (Nat.card F'))
    (h3 : 3 ≤ Nat.card F') {J N : Subgroup Y} (e : J ≃* SL(2, F'))
    (hNJ : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N) (hJN : ∀ n ∈ N, ∀ j ∈ J, n * j * n⁻¹ ∈ J)
    (hNodd : Odd (Nat.card N)) : ∀ n ∈ N, ∀ j ∈ J, n * j = j * n := by
  set M : Subgroup J := N.subgroupOf J with hM
  have hMn : M.Normal := ⟨fun m hm g => by
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    simpa using hNJ g g.2 m hm⟩
  have hMo : Odd (Nat.card M) := by
    have h1 : Nat.card M = Nat.card (M.map J.subtype) :=
      (Subgroup.card_map_of_injective J.subtype_injective).symm
    have h2 : M.map J.subtype ≤ N := by
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hm
    rw [h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le h2)
  have hMb := normal_odd_of_equiv_sl2 hodd h3 e M hMn hMo
  intro n hn j hj
  have hJ : n * j * n⁻¹ * j⁻¹ ∈ J := J.mul_mem (hJN n hn j hj) (J.inv_mem hj)
  have hc : (⟨n * j * n⁻¹ * j⁻¹, hJ⟩ : J) ∈ M := by
    rw [hM, Subgroup.mem_subgroupOf]
    show n * j * n⁻¹ * j⁻¹ ∈ N
    have h1 : j * n⁻¹ * j⁻¹ ∈ N := hNJ j hj _ (N.inv_mem hn)
    rw [show n * j * n⁻¹ * j⁻¹ = n * (j * n⁻¹ * j⁻¹) by group]
    exact N.mul_mem hn h1
  rw [hMb, Subgroup.mem_bot] at hc
  have h1 : n * j * n⁻¹ * j⁻¹ = 1 := congrArg Subtype.val hc
  calc n * j = n * j * n⁻¹ * j⁻¹ * (j * n) := by group
    _ = j * n := by rw [h1, one_mul]

theorem Frame.comm_of_odd [Finite Y] [Finite F'] (hfr : Frame L F' x t J₂ J₄)
    (hodd : Odd (Nat.card F')) (h3 : 3 ≤ Nat.card F') {N : Subgroup Y} (hNL : N ≤ L)
    (hNt : N ≤ Subgroup.centralizer ({t} : Set Y)) (hNodd : Odd (Nat.card N))
    (hNn : ∀ g ∈ L, g * t = t * g → ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    (∀ n ∈ N, ∀ j ∈ J₂, n * j = j * n) ∧ ∀ n ∈ N, ∀ j ∈ J₄, n * j = j * n := by
  obtain ⟨e₂⟩ := hfr.equiv₂
  obtain ⟨e₄⟩ := hfr.equiv₄
  have hct : ∀ {g : Y}, g ∈ Subgroup.centralizer ({t} : Set Y) → g * t = t * g := fun hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  refine ⟨comm_of_odd_of_sl2 hodd h3 e₂ (fun j hj => hNn j (hfr.le₂ hj) (hct (hfr.cent₂ hj)))
    (fun n hn => hfr.norm₂ n (hNL hn) (hct (hNt hn))) hNodd,
    comm_of_odd_of_sl2 hodd h3 e₄ (fun j hj => hNn j (hfr.le₄ hj) (hct (hfr.cent₄ hj)))
    (fun n hn => hfr.norm₄ n (hNL hn) (hct (hNt hn))) hNodd⟩

variable {R : Subgroup Y} {S : Sylow 2 R}

theorem oddCore_comm_of_perfect [Finite Y] (hD : TightDatum R S t) (hLn : L.Normal)
    {J : Subgroup Y} (hJL : J ≤ L) (hJt : J ≤ Subgroup.centralizer ({t} : Set Y))
    [Group.IsPerfect J] (hN : ∀ n ∈ oddCoreImg R ⊓ L, ∀ j ∈ J, n * j = j * n) :
    ∀ o ∈ oddCoreImg R, ∀ j ∈ J, o * j = j * o := by
  intro o ho
  set N := oddCoreImg R ⊓ L with hNdef
  have hc : ∀ j ∈ J, ⁅o, j⁆ ∈ N := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine (oddCoreImg R).mul_mem ho ?_
      rw [← mul_assoc]
      exact datum_conj_mem_oddCoreImg hD (hJt hj) ((oddCoreImg R).inv_mem ho)
    · rw [commutatorElement_def]
      exact L.mul_mem (hLn.conj_mem _ (hJL hj) o) (L.inv_mem (hJL hj))
  let φ : J →* N :=
    { toFun := fun j => ⟨⁅o, (j : Y)⁆, hc j j.2⟩
      map_one' := by ext; simp [commutatorElement_def]
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb : ⁅o, (b : Y)⁆ * a = a * ⁅o, (b : Y)⁆ := hN _ (hc b b.2) a a.2
        show ⁅o, (a : Y) * b⁆ = ⁅o, (a : Y)⁆ * ⁅o, (b : Y)⁆
        have e : ⁅o, (a : Y) * b⁆ = ⁅o, (a : Y)⁆ * ((a : Y) * ⁅o, (b : Y)⁆ * (a : Y)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e, ← hb, mul_assoc, mul_inv_cancel, mul_one] }
  have hNodd : Odd (Nat.card N) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hφ := eq_one_of_isPerfect_of_isSolvable φ
  intro j hj
  have h1 : ⁅o, j⁆ = 1 := congrArg Subtype.val (DFunLike.congr_fun hφ ⟨j, hj⟩)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem Frame.datum_comm [Finite Y] [Finite F'] (hfr : Frame L F' x t J₂ J₄) (hLn : L.Normal)
    (hodd : Odd (Nat.card F')) (h4 : 4 ≤ Nat.card F') (hD : TightDatum R S t) :
    (∀ r ∈ R, ∀ j ∈ J₂, r * j = j * r) ∧ ∀ r ∈ R, ∀ j ∈ J₄, r * j = j * r := by
  obtain ⟨e₂⟩ := hfr.equiv₂
  obtain ⟨e₄⟩ := hfr.equiv₄
  have hNodd : Odd (Nat.card ↥(oddCoreImg R ⊓ L)) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hN := hfr.comm_of_odd hodd (by omega) inf_le_right
    (fun n hn => hD.cent (oddCoreImg_le R hn.1)) hNodd (fun g hg hgt n hn =>
      ⟨datum_conj_mem_oddCoreImg hD (Subgroup.mem_centralizer_singleton_iff.mpr hgt) hn.1,
        hLn.conj_mem _ hn.2 g⟩)
  have : Group.IsPerfect J₂ := isPerfect_of_equiv_sl2 h4 e₂
  have : Group.IsPerfect J₄ := isPerfect_of_equiv_sl2 h4 e₄
  exact ⟨datum_commute_of_perfect hD hfr.cent₂
      (oddCore_comm_of_perfect hD hLn hfr.le₂ hfr.cent₂ hN.1),
    datum_commute_of_perfect hD hfr.cent₄
      (oddCore_comm_of_perfect hD hLn hfr.le₄ hfr.cent₄ hN.2)⟩

end TwinFr

end CFSG.ClassicalInvolution.Q3.TA3
