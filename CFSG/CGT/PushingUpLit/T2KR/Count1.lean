module

public import CFSG.CGT.PushingUpLit.T2KR.MMCoord

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

structure PairFacts {L M : Subgroup G} {n : ℕ} (H : MData G L M n) (P B D : Subgroup G) : Prop where
  D_le_P : D ≤ P
  P_le_Q : P ≤ QM L M
  D_le_B : D ≤ B
  B_le_M : B ≤ M
  B_sq : ∀ x ∈ B, x * x = 1
  B_comm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  B_inf_Q : B ⊓ QM L M = D
  D_ne_B : D ≠ B
  P_ne_Q : P ≠ QM L M
  card_PB : Nat.card P = Nat.card B
  P_le_comm : P ≤ ⁅QM L M, B⁆ ⊔ D
  comm_mem : ∀ u ∈ QM L M, ∀ x ∈ B, ⁅u, x⁆ ∈ P
  P_comm : ∀ t ∈ P, ∀ x ∈ B, ⁅x, t⁆ ∈ D
  inj : ∀ t ∈ QM L M, t ∉ P → ∀ x ∈ B, ⁅x, t⁆ ∈ D → x ∈ D
  torus : 2 < P.relIndex (QM L M) →
    ∃ h ∈ M, ∀ x ∈ B, ∃ x' ∈ B, ∃ d ∈ D, x = ⁅x', h⁆ * d

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem card_V : Nat.card ↥(blockU L) = Nat.card (Fq n) ^ 2 := by
  rw [Nat.card_congr H.psiEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

include H in
theorem comm_le_CV (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (hX2 : ∀ x ∈ X, x * x = 1) :
    ⁅QM L M, X⁆ ≤ blockU L ⊓ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have := H.commutator_mem_CV X hX hX2 (u := u⁻¹) (inv_mem hu) hx
  have e : (u⁻¹)⁻¹ * (x * u⁻¹ * x⁻¹) = ⁅u, x⁆ := by
    simp only [commutatorElement_def]
    group
  rwa [e] at this

end MData

namespace PairFacts

variable {L M : Subgroup G} {n : ℕ} {H : MData G L M n} {P B D : Subgroup G}

theorem cent_le (hP : PairFacts H P B D) : QM L M ⊓ Subgroup.centralizer (B : Set G) ≤ P := by
  intro u hu
  by_contra hnot
  apply hP.D_ne_B
  refine le_antisymm hP.D_le_B fun x hx => ?_
  refine hP.inj u hu.1 hnot x hx ?_
  have h1 : x * u = u * x := Subgroup.mem_centralizer_iff.1 hu.2 x hx
  rw [commutatorElement_eq_one_iff_mul_comm.2 h1]
  exact D.one_mem

theorem rank (hP : PairFacts H P B D) : P.relIndex (QM L M) ≤ D.relIndex P := by
  classical
  obtain ⟨b, hbB, hbD⟩ := IsConcreteLE.not_le_iff_exists.1
    (fun h : B ≤ D => hP.D_ne_B (le_antisymm hP.D_le_B h))
  have hQc : ∀ a ∈ QM L M, ∀ c ∈ QM L M, a * c = c * a := H.Q_comm
  have hbt : ∀ t ∈ QM L M, ⁅b, t⁆ ∈ P := fun t ht => by
    have := inv_mem (hP.comm_mem t ht b hbB)
    rwa [commutatorElement_inv] at this
  have : (D.subgroupOf P).Normal := ⟨fun x hx g => by
    have h1 : (g : ↥P) * x * g⁻¹ = x := by
      apply Subtype.ext
      have := hQc g.1 (hP.P_le_Q g.2) x.1 (hP.P_le_Q x.2)
      calc ((g : ↥P) * x * g⁻¹ : ↥P).1 = (g.1 * x.1) * g.1⁻¹ := rfl
        _ = (x.1 * g.1) * g.1⁻¹ := by rw [this]
        _ = x.1 := by group
    rw [h1]
    exact hx⟩
  let phi : ↥(QM L M) →* ↥P ⧸ D.subgroupOf P :=
    { toFun := fun t => QuotientGroup.mk ⟨⁅b, (t : G)⁆, hbt t t.2⟩
      map_one' := by
        have : (⟨⁅b, ((1 : ↥(QM L M)) : G)⁆, hbt 1 (QM L M).one_mem⟩ : ↥P) = 1 :=
          Subtype.ext (by simp)
        rw [this]
        rfl
      map_mul' := fun t t' => by
        rw [← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have hcP : (t : G) * ⁅b, (t' : G)⁆ = ⁅b, (t' : G)⁆ * (t : G) :=
          hQc t t.2 _ (hP.P_le_Q (hbt t' t'.2))
        show ⁅b, (t : G) * t'⁆ = ⁅b, (t : G)⁆ * ⁅b, (t' : G)⁆
        calc ⁅b, (t : G) * t'⁆ = ⁅b, (t : G)⁆ * ((t : G) * ⁅b, (t' : G)⁆ * (t : G)⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅b, (t : G)⁆ * ⁅b, (t' : G)⁆ := by rw [hcP]; group }
  have hker : phi.ker ≤ P.subgroupOf (QM L M) := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have h1 : (⟨⁅b, (t : G)⁆, hbt t t.2⟩ : ↥P) ∈ D.subgroupOf P := (QuotientGroup.eq_one_iff _).1 ht
    have h2 : ⁅b, (t : G)⁆ ∈ D := h1
    by_contra htP
    exact hbD (hP.inj t t.2 htP b hbB h2)
  have h1 : (P.subgroupOf (QM L M)).index ≤ phi.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have h2 : phi.ker.index = Nat.card phi.range := Subgroup.index_ker phi
  have h3 : Nat.card phi.range ≤ (D.subgroupOf P).index := by
    calc Nat.card phi.range ≤ Nat.card (↥P ⧸ D.subgroupOf P) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = (D.subgroupOf P).index := rfl
  exact h1.trans (h2.symm ▸ h3)

theorem D_le_Q (hP : PairFacts H P B D) : D ≤ QM L M := hP.D_le_P.trans hP.P_le_Q

omit [Finite G] in
theorem relIndex_mul_card_of_le {A C : Subgroup G} (h : A ≤ C) :
    A.relIndex C * Nat.card A = Nat.card C := by
  have := Subgroup.relIndex_mul_card A C
  rwa [inf_of_le_left h] at this

theorem four_le_card (H : MData G L M n) : 4 ≤ Nat.card (Fq n) := by
  have hn : n ≠ 0 := H.n_ne_zero
  rw [GaloisField.card 2 n hn]
  have := H.nat.two_le
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

theorem step66 (hP : PairFacts H P B D) :
    ¬ B ≤ L ⊔ QM L M ∨ (D = ⊥ ∧ QM L M = blockU L) := by
  by_cases hBLQ : B ≤ L ⊔ QM L M
  swap
  · exact Or.inl hBLQ
  right
  have hq4 := four_le_card H
  have hVQ : blockU L ≤ QM L M := H.blockU_le_QM
  have hBD : D.relIndex B ≤ Nat.card (Fq n) := by
    have := H.relIndex_le_card B hBLQ hP.B_sq
    rwa [hP.B_inf_Q] at this
  have hnQ : ¬ B ≤ QM L M := by
    intro h
    apply hP.D_ne_B
    rw [← hP.B_inf_Q, inf_of_le_left h]
  have hCV : Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) = Nat.card (Fq n) :=
    H.card_CV_eq B hBLQ hP.B_sq hnQ
  have hDC : D ≤ QM L M ⊓ Subgroup.centralizer (B : Set G) := fun d hd =>
    ⟨hP.D_le_Q hd, Subgroup.mem_centralizer_iff.2 fun x hx => hP.B_comm x hx d (hP.D_le_B hd)⟩
  have hPC : P = QM L M ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_antisymm ?_ hP.cent_le
    refine hP.P_le_comm.trans (sup_le ?_ hDC)
    exact (H.comm_le_CV B hBLQ hP.B_sq).trans (inf_le_inf_right _ hVQ)
  have hVP : P ⊓ blockU L = blockU L ⊓ Subgroup.centralizer (B : Set G) := by
    ext x
    constructor
    · rintro ⟨hxP, hxV⟩
      have h1 : x ∈ QM L M ⊓ Subgroup.centralizer (B : Set G) := by rw [← hPC]; exact hxP
      exact ⟨hxV, h1.2⟩
    · rintro ⟨hxV, hxC⟩
      have h1 : x ∈ P := by rw [hPC]; exact ⟨hVQ hxV, hxC⟩
      exact ⟨h1, hxV⟩
  have hq0 : 0 < Nat.card (Fq n) := Nat.card_pos
  have hq2 : (blockU L ⊓ Subgroup.centralizer (B : Set G)).relIndex (blockU L) = Nat.card (Fq n) := by
    have h := relIndex_mul_card_of_le
      (inf_le_left : blockU L ⊓ Subgroup.centralizer (B : Set G) ≤ blockU L)
    rw [hCV, H.card_V] at h
    exact Nat.eq_of_mul_eq_mul_right hq0 (h.trans (sq _))
  have hPV : P.relIndex (blockU L) = Nat.card (Fq n) := by
    rw [← Subgroup.inf_relIndex_right P (blockU L), hVP, hq2]
  have hpos : ∀ A C : Subgroup G, 0 < A.relIndex C := fun A C =>
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card A C) Nat.card_pos
  have hPQ : P.relIndex (blockU L) ≤ P.relIndex (QM L M) :=
    Subgroup.relIndex_le_of_le_right hVQ (hpos P (QM L M)).ne'
  have hDPB : D.relIndex P = D.relIndex B := by
    have h1 := relIndex_mul_card_of_le hP.D_le_P
    have h2 := relIndex_mul_card_of_le hP.D_le_B
    rw [hP.card_PB, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrank := hP.rank
  have hrel : D.relIndex B = Nat.card (Fq n) := by
    refine le_antisymm hBD ?_
    calc Nat.card (Fq n) = P.relIndex (blockU L) := hPV.symm
      _ ≤ P.relIndex (QM L M) := hPQ
      _ ≤ D.relIndex P := hrank
      _ = D.relIndex B := hDPB
  have hrelPQ : P.relIndex (QM L M) = Nat.card (Fq n) := by
    refine le_antisymm (hrank.trans (hDPB.trans_le hrel.le)) ?_
    rw [← hPV]
    exact hPQ
  have h3 : 3 ≤ (B ⊓ QM L M).relIndex B := by
    rw [hP.B_inf_Q, hrel]
    omega
  obtain ⟨hcE, hcard⟩ := H.centralizer_QM_eq_of_three_le B hBLQ hP.B_sq h3
  have hPcard : Nat.card P = Nat.card (Fq n) := by
    rw [hPC, hcE]
    exact hCV
  have hDcard : Nat.card D = 1 := by
    have h1 := relIndex_mul_card_of_le hP.D_le_P
    rw [hDPB, hrel, hPcard] at h1
    have : Nat.card (Fq n) * Nat.card D = Nat.card (Fq n) * 1 := by rw [h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hq0 this
  refine ⟨Subgroup.eq_bot_of_card_eq D hDcard, ?_⟩
  have hQcard : Nat.card (QM L M) = Nat.card (Fq n) * Nat.card (Fq n) := by
    have h1 := relIndex_mul_card_of_le hP.P_le_Q
    rw [hrelPQ, hPcard] at h1
    exact h1.symm
  refine (Subgroup.eq_of_le_of_card_ge hVQ ?_).symm
  rw [hQcard, H.card_V, sq]

end PairFacts

end CFSG.CGT.PushingUpLit.T2KR
