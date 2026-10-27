module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G]

structure Cfg {L M : Subgroup G} {n : ℕ} (H : MData G L M n) (T' : Subgroup G) (x r b : G) :
    Prop where
  n_eq : n = 2
  syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤
  T'_M : T' ≤ M
  Q_le : QM L M ≤ T'
  card_V : Nat.card ↥(blockU L) = 16
  card_Q : Nat.card ↥(QM L M) = 32
  hO : oTwoIn L = blockU L
  QL : QM L M ⊓ L ≤ blockU L
  Q_eq : ∀ q ∈ QM L M, q ∈ blockU L ∨ x⁻¹ * q ∈ blockU L
  x_Q : x ∈ QM L M
  x_V : x ∉ blockU L
  x_sq : x * x = 1
  r_L : r ∈ L
  r_T : r ∈ T'
  r_sq : r * r = 1
  r_Q : r ∉ QM L M
  b_M : b ∈ M
  b_T : b ∈ T'
  b_sq : b * b = 1
  b_LQ : b ∉ L ⊔ QM L M
  xr : x * r = r * x
  xb : x * b = b * x
  rb : r * b = b * r

@[expose] def Concl613 (L T' : Subgroup G) (x r : G) : Prop :=
  ∃ z : G, z ∈ blockU L ∧ z ≠ 1 ∧ (∀ t ∈ T', t * z = z * t) ∧
    (∀ t ∈ T', t * t = 1 → t ≠ 1 → t ≠ z →
      t ∈ ⁅T' ⊓ Subgroup.centralizer ({t} : Set G), T' ⊓ Subgroup.centralizer ({t} : Set G)⁆ →
      ∀ u ∈ ⁅T' ⊓ Subgroup.centralizer ({t} : Set G), T' ⊓ Subgroup.centralizer ({t} : Set G)⁆,
        u = 1 ∨ u = t ∨ u = z ∨ u = t * z) ∧
    (z ∈ ⁅T' ⊓ Subgroup.centralizer ({x * r} : Set G),
        T' ⊓ Subgroup.centralizer ({x * r} : Set G)⁆ ∧
      ∃ w ∈ ⁅T' ⊓ Subgroup.centralizer ({x * r} : Set G),
        T' ⊓ Subgroup.centralizer ({x * r} : Set G)⁆, w ≠ 1 ∧ w ≠ z) ∧
    ⁅T', T'⁆ ≤ L

theorem exists_cfg (hE1 : FooteNonsolvableSimple) {L M T : Subgroup G} {n : ℕ} {D : Subgroup G}
    {g : G} (hs : Sit64 G L M T n D g)
    (hP : PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D) (hD4 : Nat.card D = 4) {T' : Subgroup G}
    (hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤) (hT'M : T' ≤ M) (hQT' : QOf L M ≤ T')
    (hBT' : normIn (Aof L M g) (QOf L M) ≤ T') {x : G} (hxD : x ∈ D) (hxV : x ∉ blockU L)
    {r : G} (hrB : r ∈ normIn (Aof L M g) (QOf L M)) (hrL : r ∈ L) (hrQ : r ∉ QOf L M) :
    ∃ b : G, Cfg (MData.ofSec6 hE1 hs.sec6) T' x r b := by
  classical
  set H := MData.ofSec6 hE1 hs.sec6 with hH
  set B := normIn (Aof L M g) (QOf L M) with hB
  have hD0 : D ≠ ⊥ := by
    rintro rfl
    simp at hD4
  rcases hP.step66 with hBLQ | ⟨hD', -⟩
  swap
  · exact absurd hD' hD0
  obtain ⟨hDE, -, hn⟩ := hP.step610 hBLQ
  have hQD := hP.relIndex_Q_eq hBLQ
  have hVQ : blockU L ≤ QM L M := H.blockU_le_QM
  have hF : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hVcard : Nat.card ↥(blockU L) = 16 := by
    rw [H.card_V, hF]; norm_num
  have hQcard : Nat.card ↥(QM L M) = 32 := by
    have := PairFacts.relIndex_mul_card_of_le hP.D_le_Q
    rw [hQD, hD4] at this
    omega
  have hVQrel : (blockU L).relIndex (QM L M) = 2 := by
    have := PairFacts.relIndex_mul_card_of_le hVQ
    rw [hVcard, hQcard] at this
    omega
  have hxB : x ∈ B := hP.D_le_B hxD
  have hx2 : x * x = 1 := hP.B_sq x hxB
  have hxQ : x ∈ QM L M := hP.D_le_Q hxD
  have hQeq : ∀ q ∈ QM L M, q ∈ blockU L ∨ x⁻¹ * q ∈ blockU L := by
    intro q hq
    by_cases hqV : q ∈ blockU L
    · exact Or.inl hqV
    · exact Or.inr (inv_mul_mem_of_relIndex_two hVQrel hxQ hq hxV hqV)
  have hr2 : r * r = 1 := hP.B_sq r hrB
  have hQL : QM L M ⊓ L ≤ blockU L := H.QL_le_blockU_of_involution hrL hr2 hrQ
  have hO : oTwoIn L = blockU L := by
    refine H.nat.oTwoIn_eq_blockU_of_sq_mem (r := r) hrL ?_ ?_
    · intro hrO
      apply hrQ
      rw [← H.nat.inf_centralizer_blockU] at hrO
      exact ⟨H.le hrO.1, hrO.2⟩
    · rw [pow_two, hr2]
      exact (blockU L).one_mem
  obtain ⟨b, hbB, hbE⟩ : ∃ b ∈ B, b ∉ B ⊓ (L ⊔ QM L M) := by
    by_contra hcon
    push Not at hcon
    have hBE : B ≤ B ⊓ (L ⊔ QM L M) := hcon
    have h1 : (B ⊓ (L ⊔ QM L M)).relIndex B = 1 := Subgroup.relIndex_eq_one.2 hBE
    have h2 : (B ⊓ (L ⊔ QM L M)).relIndex B = 2 := hP.relIndex_E hBLQ
    omega
  exact ⟨b,
    { n_eq := hn
      syl := hT'syl
      T'_M := hT'M
      Q_le := hQT'
      card_V := hVcard
      card_Q := hQcard
      hO := hO
      QL := hQL
      Q_eq := hQeq
      x_Q := hxQ
      x_V := hxV
      x_sq := hx2
      r_L := hrL
      r_T := hBT' hrB
      r_sq := hr2
      r_Q := hrQ
      b_M := hP.B_le_M hbB
      b_T := hBT' hbB
      b_sq := hP.B_sq b hbB
      b_LQ := fun h => hbE ⟨hbB, h⟩
      xr := hP.B_comm x hxB r hrB
      xb := hP.B_comm x hxB b hbB
      rb := hP.B_comm r hrB b hbB }⟩

end CFSG.CGT.PushingUpLit.T2KR.P613
