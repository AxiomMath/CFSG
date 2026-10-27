module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Transport

variable {X : Type} [Group X] [Finite X] {n : ℕ}

@[expose] noncomputable def AhatModel.transport {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n B) :
    AhatModel X n E :=
  ⟨M.K, (quotOddCore_equiv_of_cover hEB hcov).choose.trans M.e, M.C⟩

theorem AhatModel.transport_e_mk {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n B) (a : ↥E) :
    (M.transport hEB hcov).e (QuotientGroup.mk a) =
      M.e (QuotientGroup.mk (⟨a, hEB a.2⟩ : ↥B)) := by
  have h := (quotOddCore_equiv_of_cover hEB hcov).choose_spec a
  show M.e ((quotOddCore_equiv_of_cover hEB hcov).choose (QuotientGroup.mk a)) = _
  rw [h]
  rfl

theorem AhatModel.autOf_transport {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n B) {c : X}
    (hcE : c ∈ normalizer (E : Set X)) (hcB : c ∈ normalizer (B : Set X)) :
    (M.transport hEB hcov).autOf c hcE = M.autOf c hcB := by
  refine MulEquiv.ext fun k => ?_
  obtain ⟨a, rfl⟩ := (M.transport hEB hcov).surj_mk k
  have e1 : ⟨((conjAut hcE a : ↥E) : X), hEB (conjAut hcE a).2⟩ =
      conjAut hcB ⟨a, hEB a.2⟩ := Subtype.ext (by simp only [coe_conjAut])
  have h1 : (M.transport hEB hcov).e (QuotientGroup.mk (conjAut hcE a)) =
      M.e (QuotientGroup.mk (conjAut hcB ⟨a, hEB a.2⟩)) := by
    rw [M.transport_e_mk hEB hcov (conjAut hcE a), e1]
  have h2 := M.autOf_mk hcB ⟨a, hEB a.2⟩
  have h3 : M.e (QuotientGroup.mk (⟨a, hEB a.2⟩ : ↥B)) =
      (M.transport hEB hcov).e (QuotientGroup.mk a) := (M.transport_e_mk hEB hcov a).symm
  exact ((M.transport hEB hcov).autOf_mk hcE a).trans
    (h1.trans (h2.symm.trans (congrArg (M.autOf c hcB) h3)))

theorem AhatModel.perm_transport (hn : 8 ≤ n) {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n B) {c : X}
    (hcE : c ∈ normalizer (E : Set X)) (hcB : c ∈ normalizer (B : Set X)) :
    (M.transport hEB hcov).perm c hcE = M.perm c hcB := by
  have h1 := (M.transport hEB hcov).induces_perm hn c hcE
  rw [M.autOf_transport hEB hcov hcE hcB] at h1
  exact ((M.perm_eq_of_induces hn hcB h1)).symm

theorem inf_oddCoreOf_le_oddCoreOf {A K : Subgroup X} (hAK : A ≤ K) :
    A ⊓ oddCoreOf K ≤ oddCoreOf A :=
  le_oddCoreOf_of_normalized inf_le_left
    (fun _ ha => mem_normalizer_inf (Subgroup.le_normalizer ha)
      (le_normalizer_oddCoreOf K (hAK ha)))
    (Odd.of_dvd_nat (odd_card_oddCoreOf K) (Subgroup.card_dvd_of_le inf_le_right))

end Transport

section Zeta

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem Sec5S.fixCount_pAct_le (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {w : X} (hwZ : w ∈ Z)
    (hwA : w ∈ A) (hw1 : w ≠ 1) (hwN : w ∈ normComps X n s) :
    fixCount (pAct hn hB M ⟨w, hwN⟩) ≤ 3 := by
  classical
  have hw2 : w * w = 1 := hS.data.Z_sq_eq_one hwZ
  have hws : w * s = s * w := hS.comm_of_mem_Z hA hwZ hwA hw1
  have hwinv : w ∈ invsOf s A := ⟨hwA, hw1, hw2, hws⟩
  have hwB : w ∈ normalizer (B : Set X) := normComps_le_normalizer hB hwN
  have hBK : B ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup hB
  obtain ⟨Zs, hZs, hwZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers w) (isPGroup_zpowers_of_mul_self hw2)
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hws))
  have hwn : w ∈ normalizer (Zs : Set X) := hwZs (Subgroup.mem_zpowers w)
  obtain ⟨g, S₁, hZsg, -, -, hS₁⟩ := hS.data.exists_mirror_of_sylow hS.inv hZs
  have hwnZs : w ∉ Zs := by
    intro hwZs'
    have hzs : w ∈ zStar (K0 X n (centralizer ({s} : Set X))) := hZs.1 hwZs'
    have hcent : CentModOdd B w := by
      intro b hb
      have h1 : ⁅b, w⁆ ∈ pPrimeCoreOf 2 (K0 X n (centralizer ({s} : Set X))) :=
        hzs.2.2.2 b (hBK hb)
      have h2 : ⁅b, w⁆ ∈ B := by
        have e : ⁅b, w⁆ = b * (w * b⁻¹ * w⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.1 hwB b⁻¹).1 (B.inv_mem hb))
      exact inf_oddCoreOf_le_oddCoreOf hBK ⟨h2, h1⟩
    exact hS.pAct_ne_one hn hB M hA hwinv ((pAct_eq_one_iff hn hB M ⟨w, hwN⟩).2 hcent)
  have hconj : ∃ g' : X, g'⁻¹ * w * g' ∈ Zs ∧ g'⁻¹ * w * g' ≠ 1 := by
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hZsg]
      exact ⟨w, hwZ, by simp [MulAut.conj_apply]⟩
    · intro h1
      apply hw1
      have h2 : g * w * g⁻¹ = 1 := by simpa using h1
      have h3 : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [h3, h2]; group
  have hinv : IsSec5Inv X Zs w := ⟨hwn, hwnZs, hw2, hconj⟩
  have hB' := hB
  obtain ⟨⟨u₀, hu₀⟩, hBn⟩ := hB'
  obtain ⟨u, huZs, hu⟩ := hS₁.pair.exists_witness_mem hu₀ hBn
  obtain ⟨h1, h2, h3⟩ := hS₁.pair.isIntrinsicIn_normalizer huZs hu hBn
  have hEc : Sec5Comp X n (normalizer (Zs : Set X))
      (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X))) := ⟨⟨u, h1⟩, h2⟩
  have hEB : oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) ≤ B :=
    (oTwoPrimeOf_le _).trans inf_le_left
  have hcov : ∀ c ∈ B, ∃ a ∈ oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)), ∃ o ∈ oddCoreOf B,
      c = a * o := by
    intro c hc
    have hc' : c ∈ pPrimeCoreOf 2 B ⊔ oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) := h3 hc
    obtain ⟨o, ho, a, ha, hoa⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
      (pPrimeCoreOf 2 B) (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)))
      (fun x hx => le_normalizer_oddCoreOf B (hEB hx)) c).1 hc'
    refine ⟨a, ha, a⁻¹ * o * a, ?_, ?_⟩
    · have hn1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf B (hEB (inv_mem ha))) o)
      have := hn1.1 ho
      simpa [mul_assoc] using this
    · rw [← hoa]; group
  have hwE : w ∈ normalizer ((oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) : Subgroup X) :
      Set X) :=
    mem_normalizer_of_map_conj_eq (hN X n s Zs S₁ hS₁ w hinv _ hEc)
  have hfr := (hF X n s Zs S₁ hS₁ w hinv).1 _ hEc hwE (M.transport hEB hcov)
  rw [M.perm_transport hn hEB hcov hwE hwB] at hfr
  exact hfr.1

end Zeta

end CFSG.OddStandard.Solomon75
