module

public import CFSG.ClassicalInvolution.Asc77.AscBSD5
public import CFSG.ClassicalInvolution.Asc77.AscBSDResid

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (ModelFund)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem bootNoManyTwins_of_models
    (hmodel : ∀ (t : LTag) (n : ℕ), ListedTwin t n → ¬ (t = .POmegaPlus ∧ n = 4) →
      FundTwoBound p t n)
    (hD4 : BootNoManyTwinsD4 p f) : BootNoManyTwins p f := by
  intro G _ _ _ K z hS D b hlist
  by_cases hd4 : D.tag b = .POmegaPlus ∧ D.rank b = 4
  · exact hD4 G K z hS D b hd4
  by_contra hcard
  have hcard4 : 3 < D.card := by omega
  have hno := noFuzzyFrame hS
  let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hlist' : ListedTwin (C.D.tag b) (C.D.rank b) := hlist
  have hnot : ¬ (C.D.tag b = .POmegaPlus ∧ C.D.rank b = 4) := hd4
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := by
    rintro ⟨h1, h2⟩
    rcases hlist' with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h1] at h
      exact absurd h (by decide)
    · omega
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [h1] at h
      exact absurd h (by decide)
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨e₁, e₂, he₁₂, he₁j, he₁b, he₂j, he₂b⟩ := exists_two_ne_of_three_lt hcard4 j₀ b hj₀b
  obtain ⟨hA₁, hall₁⟩ := nbar_eq_of_A1 C hno hb he₁b
  obtain ⟨hA₂, hall₂⟩ := nbar_eq_of_A1 C hno hb he₂b
  obtain ⟨m₁⟩ := exists_compMem C e₁
  obtain ⟨m₂⟩ := exists_compMem C e₂
  have hm₁ := hall₁ m₁
  have hm₂ := hall₂ m₂
  obtain ⟨hT₁cl, hT₁mod⟩ := classical_of_nbar_eq C hA₁ m₁ hm₁
  obtain ⟨hT₂cl, hT₂mod⟩ := classical_of_nbar_eq C hA₂ m₂ hm₂
  have hKT₁ : m₁.N ≠ C.K := twin_ne_K C hj₀ hK₀ he₁j hA₁ m₁ hm₁
  have hKT₂ : m₂.N ≠ C.K := twin_ne_K C hj₀ hK₀ he₂j hA₂ m₂ hm₂
  have hT₁T₂ : m₁.N ≠ m₂.N := twin_ne_twin he₁₂ hA₁ hA₂ m₁ hm₁ m₂ hm₂
  obtain ⟨mb⟩ := exists_compMem C b
  obtain ⟨g, -, hg⟩ := exists_conj_of_compMem C mb
  have hKr : modOdd z C.K = (C.psi j₀).range := by rw [← hK₀, C.exactCore_K]
  obtain ⟨h0tq, h0cl, R₀, hR₀, himg₀, r₀, hr₀R, hm₀, hr₀⟩ :=
    exists_fund_conj_twin hno hb mb hg C.hK C.K_cl fun y hy =>
      nb_comm_of_range hj₀b mb (hKr ▸ hy)
  obtain ⟨h1tq, h1cl, R₁, hR₁, himg₁, r₁, hr₁R, hm₁', hr₁⟩ :=
    exists_fund_conj_twin hno hb mb hg m₁.hN.1 hT₁cl fun y hy =>
      nb_comm_of_range he₁b mb (hT₁mod ▸ hy)
  obtain ⟨h2tq, h2cl, R₂, hR₂, himg₂, r₂, hr₂R, hm₂', hr₂⟩ :=
    exists_fund_conj_twin hno hb mb hg m₂.hN.1 hT₂cl fun y hy =>
      nb_comm_of_range he₂b mb (hT₂mod ▸ hy)
  have hmsq : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 :=
    (isCentralInvolution_of_isClassicalMember h0cl).sq
  have hm1 : g⁻¹ * z * g ≠ 1 := (isCentralInvolution_of_isClassicalMember h0cl).ne_one
  have hi₀ := isInvIn_of_psi_eq hb hR₀ hr₀R hm₀ hmsq hm1 hr₀
  have hi₁ := isInvIn_of_psi_eq hb hR₁ hr₁R hm₁' hmsq hm1 hr₁
  have hi₂ := isInvIn_of_psi_eq hb hR₂ hr₂R hm₂' hmsq hm1 hr₂
  have hc01 : r₀ * r₁⁻¹ ∈ Subgroup.center (compModel C.D b).K := by
    refine C.psi_ker b ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr₀, hr₁, mul_inv_cancel]
  have hc12 : r₁ * r₂⁻¹ ∈ Subgroup.center (compModel C.D b).K := by
    refine C.psi_ker b ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr₁, hr₂, mul_inv_cancel]
  have hne01 : R₀ ≠ R₁ := fun h => hKT₁ (conjSub_inj g⁻¹
    (eq_of_fund_eq C.hz2 h0tq h1tq h0cl h1cl (by rw [himg₀, himg₁, h]))).symm
  have hne12 : R₁ ≠ R₂ := fun h => hT₁T₂ (conjSub_inj g⁻¹
    (eq_of_fund_eq C.hz2 h1tq h2tq h1cl h2cl (by rw [himg₁, himg₂, h])))
  have hne02 : R₀ ≠ R₂ := fun h => hKT₂ (conjSub_inj g⁻¹
    (eq_of_fund_eq C.hz2 h0tq h2tq h0cl h2cl (by rw [himg₀, himg₂, h]))).symm
  have hexp : C.D.exp b = f := C.exp_eq b (fun h => by
    rcases hlist' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;>
      rw [h'] at h <;> exact absurd h (by decide))
  have hq : 5 ≤ p ^ C.D.exp b := by rw [hexp]; exact hS.five
  rcases hmodel (C.D.tag b) (C.D.rank b) hlist' hnot (C.D.exp b) hS.odd hq (C.D.admissible b)
      hR₀ hR₁ hR₂ hi₀ hi₁ hi₂ hc01 hc12 with h | h | h
  exacts [hne01 h, hne12 h, hne02 h]

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
