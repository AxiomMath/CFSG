module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporGen
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem a6Row_of_typeRow {s : TauCeti.SporadicName}
    (h : CFSG.LocalAnalysis.GLTheoremA.BMType.TypeRow S8.isA6 s) : A6Row s :=
  fun S _ _ e β hβ hβ1 J hJ hT _ => h S e β hβ hβ1 J hJ hT

variable {G : Type} [Group G] [Finite G]

theorem comp_data_of_isA6 {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥)
    (hJ : GLAPComponent 3 C J) (hT : catalogIs (PSimple 3 J) S8.isA6) :
    IsComponentOf J C ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) ∧
      (Subgroup.center ↥J).index = 360 ∧ (∃ a : ℕ, Nat.card ↥(Subgroup.center ↥J) = 3 ^ a) ∧
      Nat.card ↥J = Nat.card ↥(Subgroup.center ↥J) * 360 := by
  have hcore :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.glaPPrimeCore_eq_bot_of_glaPComponent hO hJ
  let e : PQuot 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let eS : (↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J :=
    QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4.nonempty_alt6_of_catalogIs_isA6 hT
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hidx : (Subgroup.center ↥J).index = 360 := by
    rw [Subgroup.index, ← hA6]
    exact Nat.card_congr (eS.trans eA).toEquiv
  have hZ : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      Nat.prime_three hcore
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hZ
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.YS08.isComponentOf_of_glaPComponent' hO hJ,
    ⟨eS.trans eA⟩, hidx, ⟨a, ha⟩, ?_⟩
  rw [← hidx]
  exact (Subgroup.card_mul_index _).symm

theorem not_pow_eight_dvd_card_mulAut_of_isA6 {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥)
    (hJ : GLAPComponent 3 C J) (hT : catalogIs (PSimple 3 J) S8.isA6) :
    ¬ 3 ^ 8 ∣ Nat.card (MulAut ↥J) := by
  obtain ⟨hcomp, ⟨eA⟩, -, -, -⟩ := comp_data_of_isA6 hO hJ hT
  have hinj :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hcomp.2.2.1
  have h1 : Nat.card (MulAut ↥J) ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) = 1440 := by
    rw [← CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
    exact Nat.card_congr (MulAut.congr eA).toEquiv
  rw [h2] at h1
  intro h8
  exact absurd (h8.trans h1) (by norm_num)

theorem false_of_inverted_isA6 {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hbig : ∀ k : ℕ, 360 ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial)
    {q : ℕ} (hq : q.Prime) (hqH : q ∣ Nat.card ↥H) (hq3 : q ≠ 3) (hq360 : ¬ q ∣ 360)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) S8.isA6) : False := by
  obtain ⟨-, -, hidx, ⟨a, ha⟩, hcard⟩ := comp_data_of_isA6 hO hJ hT
  have hnab : ∃ x y : ↥J, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hZtop : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcon y x
    rw [hZtop, Subgroup.index_top] at hidx
    omega
  refine CFSG.HardMathSupport.Solomon.Coordinator.false_of_inverted_component hα hinv hO hH hHα hHs
    hHn hCQ 360 hbig hJ (by rw [hcard, mul_comm]) hnab ?_
  intro hd
  have hq' : q ∣ (3 ^ a * 360) ^ 2 := by
    rw [hcard, ha] at hd
    exact hqH.trans hd
  rcases (Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow hq') with h2 | h2
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h2))
  · exact hq360 h2

theorem le_of_three_sixty_pow_le {N K k : ℕ} (hK : N < 360 ^ (K + 1)) (hk : 360 ^ k ≤ N) :
    k ≤ K := by
  by_contra hc
  push Not at hc
  have h1 : 360 ^ (K + 1) ≤ 360 ^ k := Nat.pow_le_pow_right (by norm_num) hc
  omega

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

end
