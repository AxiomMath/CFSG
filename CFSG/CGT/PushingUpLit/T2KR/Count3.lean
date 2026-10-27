module

public import CFSG.CGT.PushingUpLit.T2KR.Count2
public import CFSG.CGT.PushingUpLit.T2KR.MMPair

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

namespace PairFacts

variable {L M : Subgroup G} {n : ℕ} {H : MData G L M n} {P B D : Subgroup G}

theorem card_le_card_centralizer (hP : PairFacts H P B D) {E : Subgroup G} (hEB : E ≤ B)
    (hDE : D ≤ E) (hEL : E ≤ L ⊔ QM L M) {t : G} (htQ : t ∈ QM L M) (htP : t ∉ P) :
    Nat.card E ≤ Nat.card ↥(QM L M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => hP.B_sq x (hEB hx)
  set C : Subgroup G := QM L M ⊓ Subgroup.centralizer (E : Set G) with hC
  have hDC : D ≤ C := fun d hd =>
    ⟨hP.D_le_Q hd, Subgroup.mem_centralizer_iff.2 fun x hx => hP.B_comm x (hEB hx) d (hP.D_le_B hd)⟩
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => H.Q_comm a ha.1 b hb.1
  have hcomm_mem : ∀ e ∈ E, ⁅e, t⁆ ∈ blockU L ⊓ Subgroup.centralizer (E : Set G) := by
    intro e he
    have := H.commutator_mem_CV E hEL hE2 (u := t⁻¹) (inv_mem htQ) he
    have e1 : (t⁻¹)⁻¹ * (e * t⁻¹ * e⁻¹) = ⁅t, e⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1] at this
    have := inv_mem this
    rwa [commutatorElement_inv] at this
  have hmemC : ∀ e ∈ E, ⁅e, t⁆ ∈ C := fun e he =>
    inf_le_inf_right _ H.blockU_le_QM (hcomm_mem e he)
  have : (D.subgroupOf C).Normal := ⟨fun x hx g => by
    have : (g : ↥C) * x * g⁻¹ = x := by
      apply Subtype.ext
      have := hCcomm g g.2 x x.2
      calc ((g : ↥C) * x * g⁻¹ : ↥C).1 = (g.1 * x.1) * g.1⁻¹ := rfl
        _ = (x.1 * g.1) * g.1⁻¹ := by rw [this]
        _ = x.1 := by group
    rw [this]
    exact hx⟩
  let lam : ↥E →* ↥C :=
    { toFun := fun e => ⟨⁅(e : G), t⁆, hmemC e e.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun e e' => by
        apply Subtype.ext
        have hc' : (e : G) * ⁅(e' : G), t⁆ = ⁅(e' : G), t⁆ * (e : G) :=
          Subgroup.mem_centralizer_iff.1 (hcomm_mem e' e'.2).2 e e.2
        have hcc : ⁅(e : G), t⁆ * ⁅(e' : G), t⁆ = ⁅(e' : G), t⁆ * ⁅(e : G), t⁆ :=
          H.nat.blockU_comm _ (hcomm_mem e e.2).1 _ (hcomm_mem e' e'.2).1
        show ⁅(e : G) * e', t⁆ = ⁅(e : G), t⁆ * ⁅(e' : G), t⁆
        calc ⁅(e : G) * e', t⁆ = (e : G) * ⁅(e' : G), t⁆ * (t * (e : G)⁻¹ * t⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅(e' : G), t⁆ * (e : G) * (t * (e : G)⁻¹ * t⁻¹) := by rw [hc']
          _ = ⁅(e' : G), t⁆ * ⁅(e : G), t⁆ := by
              simp only [commutatorElement_def]
              group
          _ = ⁅(e : G), t⁆ * ⁅(e' : G), t⁆ := hcc.symm }
  let ψ : ↥E →* ↥C ⧸ D.subgroupOf C := (QuotientGroup.mk' (D.subgroupOf C)).comp lam
  have hker : ψ.ker ≤ D.subgroupOf E := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    have h1 : lam e ∈ D.subgroupOf C := (QuotientGroup.eq_one_iff _).1 he
    have h2 : ⁅(e : G), t⁆ ∈ D := h1
    exact hP.inj t htQ htP e (hEB e.2) h2
  have h1 : (D.subgroupOf E).index ≤ ψ.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hker)
  have h2 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have h3 : Nat.card ψ.range ≤ (D.subgroupOf C).index := by
    calc Nat.card ψ.range ≤ Nat.card (↥C ⧸ D.subgroupOf C) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = (D.subgroupOf C).index := rfl
  have hE := relIndex_mul_card_of_le hDE
  have hCC := relIndex_mul_card_of_le hDC
  rw [← hE, ← hCC]
  exact Nat.mul_le_mul_right _ (h1.trans (h2.symm ▸ h3))

theorem step69 (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    D.relIndex (B ⊓ (L ⊔ QM L M)) ≤ 2 := by
  classical
  set E : Subgroup G := B ⊓ (L ⊔ QM L M) with hE
  have hEB : E ≤ B := inf_le_left
  have hEL : E ≤ L ⊔ QM L M := inf_le_right
  have hQLQ : QM L M ≤ L ⊔ QM L M := le_sup_right
  have hDE : D ≤ E := le_inf hP.D_le_B (hP.D_le_Q.trans hQLQ)
  have hEQ : E ⊓ QM L M = D := by
    refine le_antisymm ?_ (le_inf hDE hP.D_le_Q)
    rw [← hP.B_inf_Q]
    exact inf_le_inf_right _ hEB
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => hP.B_sq x (hEB hx)
  by_contra hcon
  have h3 : 3 ≤ D.relIndex E := by omega
  have h3' : 3 ≤ (E ⊓ QM L M).relIndex E := by rw [hEQ]; exact h3
  obtain ⟨hcE, hcard⟩ := H.centralizer_QM_eq_of_three_le E hEL hE2 h3'
  have hCQ : Nat.card ↥(QM L M ⊓ Subgroup.centralizer (E : Set G)) = Nat.card (Fq n) := by
    rw [hcE]
    exact hcard
  obtain ⟨t, htQ, htP⟩ := IsConcreteLE.not_le_iff_exists.1
    (fun h : QM L M ≤ P => hP.P_ne_Q (le_antisymm hP.P_le_Q h))
  have hEC := hP.card_le_card_centralizer hEB hDE hEL htQ htP
  have hBE : E.relIndex B = 2 := hP.relIndex_E hBLQ
  have hBcard := relIndex_mul_card_of_le hEB
  have hPQ := hP.step67 hBLQ
  have hQcard := relIndex_mul_card_of_le hP.P_le_Q
  rw [hPQ] at hQcard
  rw [hBE] at hBcard
  have hVQ : Nat.card ↥(blockU L) ≤ Nat.card ↥(QM L M) := Subgroup.card_le_of_le H.blockU_le_QM
  rw [H.card_V] at hVQ
  have hq4 := four_le_card H
  have hq : Nat.card (Fq n) = 4 := by
    have : Nat.card (Fq n) ^ 2 ≤ 4 * Nat.card (Fq n) := by
      calc Nat.card (Fq n) ^ 2 ≤ Nat.card ↥(QM L M) := hVQ
        _ = 2 * Nat.card P := hQcard.symm
        _ = 2 * Nat.card B := by rw [hP.card_PB]
        _ = 2 * (2 * Nat.card E) := by rw [← hBcard]
        _ ≤ 4 * Nat.card (Fq n) := by
          have := hEC.trans hCQ.le
          omega
    nlinarith
  obtain ⟨b, hbB, hbn⟩ := IsConcreteLE.not_le_iff_exists.1 hBLQ
  have hbM : b ∈ M := hP.B_le_M hbB
  have hb2 : (⟨b, hbM⟩ : ↥M) * ⟨b, hbM⟩ = 1 := Subtype.ext (hP.B_sq b hbB)
  have hsq := H.relIndex_sq_le_card_of_commute E hEL hE2 hb2 (hP.chi_ne_one hbB hbn)
    (fun x hx => hP.B_comm b hbB x (hEB hx))
  rw [hEQ, hq] at hsq
  nlinarith

end PairFacts

end CFSG.CGT.PushingUpLit.T2KR
