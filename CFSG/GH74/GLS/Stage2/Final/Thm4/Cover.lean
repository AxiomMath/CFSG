module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Group

variable {X : Type} [Group X] [Finite X]

theorem fitting_le_pCore_sup : fittingSubgroup X ≤ pCore 2 X ⊔ pPrimeCore 2 X := by
  have h := normal_nilpotent_le_sup_pCore (G := X) (N := fittingSubgroup X) inferInstance
    inferInstance
  refine h.trans (iSup_le fun q => ?_)
  by_cases hq : (q.1 : ℕ) = 2
  · rw [hq]
    exact le_sup_left
  · have hqprime : Nat.Prime (q.1 : ℕ) := Nat.prime_of_mem_primeFactors q.1.2
    have : Fact (Nat.Prime (q.1 : ℕ)) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := X) (p := (q.1 : ℕ))).exists_card_eq
    have hcop : Nat.Coprime 2 (Nat.card (pCore (q.1 : ℕ) X)) := by
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two hqprime).2 (Ne.symm hq)).pow_right n
    exact (le_sSup (show pCore (q.1 : ℕ) X ∈
      {K : Subgroup X | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
        ⟨inferInstance, hcop⟩)).trans le_sup_right

theorem generalizedFitting_le_sup :
    generalizedFitting X ≤ (layer X ⊔ pCore 2 X) ⊔ pPrimeCore 2 X := by
  refine sup_le ?_ (le_sup_left.trans le_sup_left)
  exact fitting_le_pCore_sup.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)

theorem odd_card_sup_of_odd {Y N : Subgroup X} [N.Normal] (hY : Odd (Nat.card Y))
    (hN : Odd (Nat.card N)) : Odd (Nat.card ↥(N ⊔ Y)) := by
  have h1 := Subgroup.relIndex_mul_card Y (N ⊔ Y)
  rw [inf_eq_left.mpr (le_sup_right : Y ≤ N ⊔ Y),
    CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N Y] at h1
  rw [← h1]
  exact Odd.mul (Odd.of_dvd_nat hN (Subgroup.relIndex_dvd_card Y N)) hY

theorem even_card_layer_sup_pCore (hF : Even (Nat.card ↥(generalizedFitting X))) :
    Even (Nat.card ↥(layer X ⊔ pCore 2 X)) := by
  by_contra hY
  have hY' : Odd (Nat.card ↥(layer X ⊔ pCore 2 X)) := Nat.not_even_iff_odd.mp hY
  have hN : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have hodd := odd_card_sup_of_odd hY' hN
  rw [sup_comm] at hodd
  have hdvd : Nat.card ↥(generalizedFitting X) ∣
      Nat.card ↥((layer X ⊔ pCore 2 X) ⊔ pPrimeCore 2 X) :=
    Subgroup.card_dvd_of_le generalizedFitting_le_sup
  exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd hdvd)) hF

end Group

section Amb0

variable {G : Type} [Group G]

theorem Em_sup_Op_eq (M : Subgroup G) :
    Em M ⊔ Op 2 M = (layer ↥M ⊔ pCore 2 ↥M).map M.subtype := by
  rw [Subgroup.map_sup]
  rfl

theorem le_normalizer_Y (M : Subgroup G) :
    M ≤ normalizer ((Em M ⊔ Op 2 M : Subgroup G) : Set G) := by
  rw [Em_sup_Op_eq]
  have hl : (layer ↥M).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (layer ↥M ⊔ pCore 2 ↥M).Normal := Subgroup.sup_normal _ _
  exact le_normalizer_map_subtype M _

end Amb0

section Amb

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem Ctx17.even_Y (h : Ctx17 G z k S M) : Even (Nat.card ↥(Em M ⊔ Op 2 M)) := by
  rw [Em_sup_Op_eq, Subgroup.card_map_of_injective M.subtype_injective]
  exact even_card_layer_sup_pCore h.even

theorem Ctx17.h17A (h : Ctx17 G z k S M) : H17A M := by
  intro hbot
  have := h.even_Y
  rw [hbot, Subgroup.card_bot] at this
  exact (Nat.not_even_one this)

theorem Ctx17.z_mem_Y (h : Ctx17 G z k S M) : z ∈ Em M ⊔ Op 2 M :=
  mem_of_even_normal h.sylow (by rw [Em_sup_Op_eq]; exact Subgroup.map_subtype_le _)
    (le_normalizer_Y M) h.even_Y h.ctx.data.base.zcen

theorem Em_le_centralizer_odd (M : Subgroup G) :
    Em M ≤ centralizer (pPrimeCoreOf 2 M : Set G) := by
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hsolv : Group.IsSolvable ↥(pPrimeCore 2 ↥M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (pPrimeCore_normal (p := 2) (G := ↥M)).isSubnormal).2
  have hle : layer ↥M ≤ centralizer (pPrimeCore 2 ↥M : Set ↥M) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨n, hn, rfl⟩
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp (hle hy)) n hn)

theorem Op_le_centralizer_odd (M : Subgroup G) :
    Op 2 M ≤ centralizer (pPrimeCoreOf 2 M : Set G) := by
  have := CFSG.pPrimeCore_map_le_centralizer_pCore_map (p := 2) M
  exact Subgroup.le_centralizer_iff.mpr this

theorem Y_le_centralizer_odd (M : Subgroup G) :
    Em M ⊔ Op 2 M ≤ centralizer (pPrimeCoreOf 2 M : Set G) :=
  sup_le (Em_le_centralizer_odd M) (Op_le_centralizer_odd M)

theorem Ctx17.eq_of_oddCover (h : Ctx17 G z k S M) (hc : OddCover z M) : M = Cen z := by
  refine le_antisymm (fun m hm => ?_) h.cen_le
  obtain ⟨c, hc1, o, ho, rfl⟩ := hc m hm
  have hzo : o ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp (Y_le_centralizer_odd M h.z_mem_Y) o ho
    exact this
  exact Subgroup.mul_mem _ hc1 hzo

end Amb

end CFSG.GH74.GLS.Stage2.Final.Thm4
