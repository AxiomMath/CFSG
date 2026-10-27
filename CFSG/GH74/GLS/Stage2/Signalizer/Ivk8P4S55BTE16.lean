module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTI

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G]

structure Data5A2 (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G)
    (t : G) (q : ℕ) (I Q₁ : Subgroup G) : Prop where
  u : UPart z k S T Tstar t q
  i : IPart H P T (L52Two.U4 z t) I
  Q₁_le : Q₁ ≤ I
  Q₁_four : IVK.IsFourSubgroup Q₁
  noE32 : L52Two.NoE32 G

variable {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G} {g : G}
  {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem exists_data5A2 [Finite G]
    (h : Cfg55E G z k S T Tstar p H P g X Y) :
    ∃ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ := by
  obtain ⟨t, q, hU⟩ := exists_uPart h
  obtain ⟨I, hI⟩ := exists_iPart h hU
  obtain ⟨Q₁, hQ₁I, hQ₁⟩ := hI.good.four
  exact ⟨t, q, I, Q₁, hU, hI, hQ₁I, hQ₁, L52Two.noE32_of_pRank_le_four h.ctx.std.rank.2⟩

@[expose] def E16 (z t : G) (Q₁ : Subgroup G) : Subgroup G := L52Two.U4 z t ⊔ Q₁

theorem Q₁_le_centralizer (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    Q₁ ≤ centralizer ((L52Two.U4 z t : Subgroup G) : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.2 fun u hu => hd.i.good.comm x (hd.Q₁_le hx) u hu

theorem inf_Q₁ (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : L52Two.U4 z t ⊓ Q₁ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxU, hxQ⟩
  have hxI : x ∈ I := hd.Q₁_le hxQ
  have hcomm : ∀ j ∈ I, ⁅x, j⁆ ∈ pPrimeCoreOf 2 H := by
    intro j hj
    have hxj : x * j = j * x := hd.i.good.comm j hj x hxU
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hxj]
    exact (pPrimeCoreOf 2 H).one_mem
  have hodd := hd.i.good.noCent x hxI hcomm
  have := hd.Q₁_four.1
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxQ
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem E16_elem (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    IsElementaryAbelian 2 ↥(E16 z t Q₁) := by
  have := hd.u.four.1
  have := hd.Q₁_four.1
  exact IsElementaryAbelian.sup_of_le_centralizer (Q₁_le_centralizer hd)

theorem card_E16 (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : Nat.card ↥(E16 z t Q₁) = 16 := by
  have hcomm : ∀ a ∈ L52Two.U4 z t, ∀ b ∈ Q₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (Q₁_le_centralizer hd hb) a ha
  rw [E16, L52Two.card_sup_eq_mul_of_commute hcomm (inf_Q₁ hd), hd.u.four.2, hd.Q₁_four.2]

theorem E16_isPGroup (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : IsPGroup 2 ↥(E16 z t Q₁) := by
  have := E16_elem hd
  exact IsElementaryAbelian.isPGroup 2 ↥(E16 z t Q₁)

theorem E16_le_H [Finite G] (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : E16 z t Q₁ ≤ H :=
  sup_le (U_le_H h hd.u) (hd.Q₁_le.trans hd.i.good.le_H)

theorem barIn_E16_elem [Finite G] (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) :
    IsElementaryAbelian 2 ↥(barIn H (E16 z t Q₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E16_elem hd
  have := IsElementaryAbelian.subgroupOf (p := 2) (E16_le_H h hd)
  exact IsElementaryAbelian.map (QuotientGroup.mk' (pPrimeCore 2 ↥H))

theorem card_barIn_E16 [Finite G] (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) : Nat.card ↥(barIn H (E16 z t Q₁)) = 16 := by
  rw [L52Two.card_barIn (E16_isPGroup hd) (E16_le_H h hd), card_E16 hd]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
