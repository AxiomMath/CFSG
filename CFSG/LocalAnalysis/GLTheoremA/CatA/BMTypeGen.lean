module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07Rank3Aut
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvCore
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure TypeHyp (P : TauCeti.CFSGIndex → Prop) (n : ℕ) : Prop where
  card : ∀ (T : Type) [Group T] [Finite T], catalogIs T P → Nat.card T = n
  out : ∀ (T : Type) [Group T], catalogIs T P → ¬ 3 ∣ Nat.card (Outer T)
  big : 25920 ≤ n
  thirteen : ¬ 13 ∣ n
  pow_six : ¬ 3 ^ 6 ∣ n
  nine : 9 ∣ n

variable {G : Type} [Group G] [Finite G]

theorem catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {P : TauCeti.CFSGIndex → Prop} (h : catalogIs S' P) : catalogIs S P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem comp_data_of_type {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
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

theorem not_pow_six_dvd_card_mulAut {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
    {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J)
    (hT : catalogIs (PSimple 3 J) P) : ¬ 3 ^ 6 ∣ Nat.card (MulAut ↥J) := by
  obtain ⟨hcomp, hcat, hidx, -, -⟩ := comp_data_of_type hP hO hJ hT
  have hperf : commutator ↥J = ⊤ := hcomp.2.2.1
  have hinj :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf
  have h1 : Nat.card (MulAut ↥J) ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 := CFSG.LocalAnalysis.GLTheoremA.card_mulAut_dvd_outer (↥J ⧸ Subgroup.center ↥J)
  have hn : Nat.card (↥J ⧸ Subgroup.center ↥J) = n := hP.card _ hcat
  rw [hn] at h2
  have hout := hP.out _ hcat
  intro h6
  have h3 : 3 ^ 6 ∣ Nat.card (Outer (↥J ⧸ Subgroup.center ↥J)) * n := (h6.trans h1).trans h2
  have hcop : Nat.Coprime (3 ^ 6) (Nat.card (Outer (↥J ⧸ Subgroup.center ↥J))) :=
    Nat.Coprime.pow_left 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hout)
  exact hP.pow_six (hcop.dvd_of_dvd_mul_left h3)

theorem false_of_inverted_type {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
    {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hbig : ∀ k : ℕ, n ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial)
    (h13 : 13 ∣ Nat.card ↥H)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  obtain ⟨-, -, hidx, ⟨a, ha⟩, hcard⟩ := comp_data_of_type hP hO hJ hT
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
  have h13' : 13 ∣ (3 ^ a * n) ^ 2 := by
    rw [hcard, ha] at hd
    exact h13.trans hd
  have hp13 : Nat.Prime 13 := by norm_num
  have h1 := hp13.dvd_of_dvd_pow h13'
  rcases (Nat.Prime.dvd_mul hp13).1 h1 with h2 | h2
  · have := (Nat.prime_dvd_prime_iff_eq hp13 Nat.prime_three).1 (hp13.dvd_of_dvd_pow h2)
    omega
  · exact hP.thirteen h2

theorem not_dvd_factorial_of_bound {n N h K : ℕ} (hn : 25920 ≤ n) (hK : N < 25920 ^ (K + 1))
    (hKh : K.factorial < h) {k : ℕ} (hk : n ^ k ≤ N) : ¬ h ∣ k.factorial := by
  have hkK : k ≤ K := by
    by_contra hc
    push Not at hc
    have h1 : 25920 ^ (K + 1) ≤ 25920 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 25920 ^ k ≤ n ^ k := Nat.pow_le_pow_left hn k
    omega
  intro hd
  have h1 : h ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos k) hd
  have h2 : k.factorial ≤ K.factorial := Nat.factorial_le hkK
  omega

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
