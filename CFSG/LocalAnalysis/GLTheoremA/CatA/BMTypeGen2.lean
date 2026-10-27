module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure TypeHyp2 (P : TauCeti.CFSGIndex → Prop) (n : ℕ) : Prop where
  card : ∀ (T : Type) [Group T] [Finite T], catalogIs T P → Nat.card T = n
  aut : ∀ (T : Type) [Group T] [Finite T], catalogIs T P → ¬ 3 ^ 6 ∣ Nat.card (Outer T) * n
  big : 25920 ≤ n
  eleven : ¬ 11 ∣ n
  thirtyone : ¬ 31 ∣ n
  nine : 9 ∣ n

variable {G : Type} [Group G] [Finite G]

theorem comp_data_of_type2 {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp2 P n)
    {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J)
    (hT : catalogIs (PSimple 3 J) P) :
    IsComponentOf J C ∧ catalogIs (↥J ⧸ Subgroup.center ↥J) P ∧
      (Subgroup.center ↥J).index = n ∧ (∃ a : ℕ, Nat.card ↥(Subgroup.center ↥J) = 3 ^ a) ∧
      Nat.card ↥J = Nat.card ↥(Subgroup.center ↥J) * n := by
  have hcore := CFSG.HardMathSupport.Solomon.Coordinator.YS08.glaPPrimeCore_eq_bot_of_glaPComponent
    hO hJ
  let e : PQuot 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let eS : (↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J :=
    QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)
  have hcat : catalogIs (↥J ⧸ Subgroup.center ↥J) P := catalogIs_of_mulEquiv eS hT
  have hidx : (Subgroup.center ↥J).index = n := by
    rw [Subgroup.index]
    exact hP.card _ hcat
  have hZ : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      Nat.prime_three hcore
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 hZ)
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.YS08.isComponentOf_of_glaPComponent' hO hJ,
    hcat, hidx, ⟨a, ha⟩, ?_⟩
  rw [← hidx, mul_comm]
  exact (Subgroup.card_mul_index _).symm.trans (by rw [mul_comm])

theorem not_pow_six_dvd_card_mulAut2 {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp2 P n)
    {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J)
    (hT : catalogIs (PSimple 3 J) P) : ¬ 3 ^ 6 ∣ Nat.card (MulAut ↥J) := by
  obtain ⟨hcomp, hcat, -, -, -⟩ := comp_data_of_type2 hP hO hJ hT
  have hperf : commutator ↥J = ⊤ := hcomp.2.2.1
  have hinj :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf
  have h1 : Nat.card (MulAut ↥J) ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 := CFSG.LocalAnalysis.GLTheoremA.card_mulAut_dvd_outer (↥J ⧸ Subgroup.center ↥J)
  have hn : Nat.card (↥J ⧸ Subgroup.center ↥J) = n := hP.card _ hcat
  rw [hn] at h2
  intro h6
  exact hP.aut _ hcat ((h6.trans h1).trans h2)

theorem false_of_inverted_type_prime {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp2 P n)
    {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hbig : ∀ k : ℕ, n ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial)
    {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) (hqH : q ∣ Nat.card ↥H) (hqn : ¬ q ∣ n)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  obtain ⟨-, -, hidx, ⟨a, ha⟩, hcard⟩ := comp_data_of_type2 hP hO hJ hT
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
    have := hP.big
    omega
  refine CFSG.HardMathSupport.Solomon.Coordinator.false_of_inverted_component hα hinv hO hH hHα hHs
    hHn hCQ n hbig hJ (by rw [hcard, mul_comm]) hnab ?_
  intro hd
  have hq' : q ∣ (3 ^ a * n) ^ 2 := by
    rw [hcard, ha] at hd
    exact hqH.trans hd
  have h1 := hq.dvd_of_dvd_pow hq'
  rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h2
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h2))
  · exact hqn h2

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
