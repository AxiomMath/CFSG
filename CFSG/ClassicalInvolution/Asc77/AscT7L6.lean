module

public import CFSG.ClassicalInvolution.Asc77.AscT7L3
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
public import CFSG.ClassicalInvolution.Asc77.AscSix63

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected

variable (p : ℕ) [Fact p.Prime]

@[expose] def E4TwinGen : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 3) ∨
      (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1)) →
    ∀ R ∈ ModelFund p t k e, ∀ R' ∈ ModelFund p t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
          (⊤ : Subgroup (modelUniv t k p e Fact.out).K) =
            Subgroup.center (modelUniv t k p e Fact.out).K ⊔
              (Subgroup.centralizer ({x} : Set (modelUniv t k p e Fact.out).K) ⊔
                Subgroup.centralizer ({a * b} : Set (modelUniv t k p e Fact.out).K) ⊔
                Subgroup.centralizer ({a⁻¹ * b} : Set (modelUniv t k p e Fact.out).K))

variable {p}

structure TwinSect {X : Type} [Group X] (Φ : Set (Subgroup X)) (A A' : Subgroup X)
    (z a₀ b₀ w : X) : Prop where
  hA : A ∈ Φ
  hA' : A' ∈ Φ
  ne : A ≠ A'
  hzA : IsUniqueInvolution A z
  hzA' : IsUniqueInvolution A' z
  ha₀ : a₀ ∈ A
  hb₀ : b₀ ∈ A'
  ha₀sq : a₀ * a₀ = z
  hb₀sq : b₀ * b₀ = z
  hw : w = a₀ * b₀ ∨ w = a₀⁻¹ * b₀
  hF : ∀ L ∈ Φ, ∃ m ∈ L, w * m ≠ m * w
  nbA : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A'
  nbA' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A

@[expose] def ConjTwinInv {X : Type} [Group X] (Φ : Set (Subgroup X)) (z : X) : Prop :=
  ∀ B ∈ Φ, ∀ zB : X, IsUniqueInvolution B zB → ∃ y : X, y * z * y⁻¹ = zB

namespace T7L

variable {f : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem conjTwinInv_of_conn {A A' : Subgroup X} {z : X} (hzA : IsUniqueInvolution A z)
    (hzA' : IsUniqueInvolution A' z) (h : ∀ L ∈ Φ, L = A ∨ L = A') : ConjTwinInv Φ z := by
  intro B hB zB hzB
  refine ⟨1, ?_⟩
  rcases h B hB with rfl | rfl
  · rw [hzB.eq hzA]
    group
  · rw [hzB.eq hzA']
    group

omit [Finite X]
    in
theorem conjTwinInv_of_model {tg : StatedLieTag} {k ee : ℕ} (M : Ih8Model p f Φ tg k ee)
    (hG2 : tg ≠ .G2) (hD4 : tg ≠ .trialityD4) {A : Subgroup X} {z : X} (hA : A ∈ Φ)
    (hzA : IsUniqueInvolution A z) : ConjTwinInv Φ z := by
  intro B hB zB hzB
  have hsc := ModelFacts.fundamentalSingleClass tg k p ee Fact.out
    (ih8_isFundTag_mf M.isFundTag) M.admissible hG2 hD4
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RB, hRB, rfl⟩ := (M.mem_iff B).mp hB
  obtain ⟨g, hg⟩ := hsc RA (M.cls_sub hRA) RB (M.cls_sub hRB)
  have hg' : RB = conjSub g RA := hg
  have e : RB.map M.ψ = conjSub (M.ψ g) (RA.map M.ψ) := by
    rw [conjSub_map M.ψ g RA, hg']
    rfl
  have h1 : IsUniqueInvolution (RB.map M.ψ) (M.ψ g * z * (M.ψ g)⁻¹) := by
    rw [e]
    exact hzA.conj (M.ψ g)
  exact ⟨M.ψ g, (hzB.eq h1).symm⟩

noncomputable def toModelOfGen (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) (hcard : D.card = 1)
    (hgen : omegaGen Φ = ⊤) (i : Fin D.card) :
    Ih8Model p f Φ (D.tag i) (D.rank i) (D.exp i) where
  isFundTag := D.isFundTag i
  admissible := D.admissible i
  exp_eq := D.exp_eq i
  ψ := D.hom i
  ker_le_center := D.ker_le_center i
  surj := D.hom_surjective_of_gen hcard hgen i
  cls := D.cls i
  cls_sub := fun _ hR => hR.1
  mem_iff := fun _ => D.mem_iff_exists_cls hcard i
  cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g

theorem twinSection_cases (htcf : TwinCentralFact p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hBelow : CITBelowU p f n) (hlt : Nat.card X < n) (hS : GenSection p f Φ)
    {A A' : Subgroup X} {z a₀ b₀ w : X} (T : TwinSect Φ A A' z a₀ b₀ w) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (D : OmegaLie p f Φ) (_ : D.card = 1) (i : Fin D.card),
        (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ f % 4 = 3) ∨
          (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 1) := by
  classical
  have hΦ : HypOmegaMod p f Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · left
    have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N →
        N = A ∨ N = A' := by
      intro N hN
      induction hN with
      | refl => exact Or.inl rfl
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        have hMΦ : M ∈ Φ := by
          rcases ih with rfl | rfl
          · exact T.hA
          · exact T.hA'
        rcases ih with rfl | rfl
        · refine Or.inr (T.nbA N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
        · refine Or.inl (T.nbA' N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
    intro L hL
    exact hpath L (hconn _ T.hA L hL)
  · right
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases mem_kPerp_of_twin hΦ T.hA T.hA' T.hzA T.hzA' with h' | h'
      · exact T.ne h'
      · exact h _ T.hA' _ T.hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      thm8SectBelow'_of_citBelow G2D4Models.ih8G2D4_unconditional hBelow hp hq X hlt Φ hS
        ⟨_, T.hA⟩ hNE hconn
    have hsix : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
        (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
      rw [htag, hrank]
      rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
        ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
      · exact Or.inl ⟨ht, hn⟩
      · exact Or.inr (Or.inl ⟨ht, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))
    let M := toModelOfGen hΦ D hcard hS.gen i
    exact ⟨D, hcard, i, e4Tag_of_model htcf hp hq hΦ M hsix T.hA T.hA' T.ne T.hzA T.hzA' T.ha₀
      T.hb₀ T.ha₀sq T.hb₀sq T.hw T.hF⟩

omit [Finite X] in
theorem twinSection_central {A A' : Subgroup X} {z : X} (hzA : IsUniqueInvolution A z)
    (hzA' : IsUniqueInvolution A' z) (h : ∀ L ∈ Φ, L = A ∨ L = A') (hgen : omegaGen Φ = ⊤) :
    z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hle : omegaGen Φ ≤ Subgroup.centralizer ({z} : Set X) := by
    refine iSup₂_le fun L hL => ?_
    rcases h L hL with rfl | rfl
    · exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hzA.commute_of_mem ha).symm
    · exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hzA'.commute_of_mem ha).symm
  rw [hgen] at hle
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))


end T7L

end CFSG.ClassicalInvolution.Asc77
