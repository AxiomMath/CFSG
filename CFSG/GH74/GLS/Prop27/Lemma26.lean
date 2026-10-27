module

public import CFSG.GH74.GLS.Prop27.Comp
public import CFSG.GH74.GLS.Prop27.Orders
public import CFSG.GH74.GLS.Prop27.Transport

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem false_of_component_psl2_odd
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hK : IsComponent K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel ↥K .PSL 2 p f) : False :=
  false_of_lieModel_psl2_odd_of_shapes7
    (shapes7_bar L hgen hx (hL2 x hx K hK).1 (hL2 x hx K hK).2) hp hp2 hL

omit [Finite G] in
theorem isQuasisimple_of_isCompIn {x : G} {K : Subgroup G}
    (hK : IsCompIn (centralizer ({x} : Set G)) K) : IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1) hK.2.1

theorem false_of_terminal_psl2
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9) {x : G} {K : Subgroup G} (hT : IsTerminalPair 2 x K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : LieModel ↥K .PSL 2 p f) : False := by
  obtain ⟨hx, hcomp, -, -⟩ := hT
  have hq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn hcomp
  obtain ⟨Kb, hKb, f', hf, hker⟩ := exists_component_bar hx hcomp
  have hbot : center ↥K = ⊥ := center_eq_bot_of_lieModel hq hL
  have hinj : Function.Injective f' :=
    (MonoidHom.ker_eq_bot_iff f').mp (eq_bot_iff.mpr (hker.trans hbot.le))
  let e : ↥K ≃* ↥Kb := MulEquiv.ofBijective f' ⟨hinj, hf⟩
  exact false_of_component_psl2_odd L hgen hL2 hx hKb hp hp2 (lieModel_of_mulEquiv e hL)

theorem false_of_terminal_L34
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9) {x : G} {K : Subgroup G} (hT : IsTerminalPair 2 x K)
    (h34 : IsL34Quotient ↥K) : False := by
  obtain ⟨hx, hcomp, -, -⟩ := hT
  have hq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn hcomp
  obtain ⟨Kb, hKb, f', hf, hker⟩ := exists_component_bar hx hcomp
  have hcard := card_quotient_center_eq_of_surjective hq f' hf hker
  have h20160 : Nat.card (↥K ⧸ center ↥K) = 20160 := by
    have := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) h34
    rw [this]
    decide
  exact card_quotient_ne_L34_of_shapes7
    (shapes7_bar L hgen hx (hL2 x hx Kb hKb).1 (hL2 x hx Kb hKb).2) (hcard.trans h20160)

theorem isRestrictedEvenType_of_oddCoreFree
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hrank : 3 ≤ pRank 2 G)
    (hL2 : L2Sub G (fun K _ => InC2 K ∧ ¬ HasL2Model K IsFM9))
    (hO : ∀ x : G, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) :
    IsRestrictedEvenType G := by
  refine ⟨⟨fun x hx K hK => (hL2 x hx K hK).1, hO, hrank⟩, ?_, ?_, ?_⟩
  · intro x hx K hK p f hp hp2 hL
    exact (false_of_component_psl2_odd L hgen hL2 hx hK hp hp2 hL).elim
  · intro x K hT p f hp hp2 hL
    exact (false_of_terminal_psl2 L hgen hL2 hT hp hp2 hL).elim
  · intro x y K hx hy hxy hT h34 hU
    exact (false_of_terminal_L34 L hgen hL2 hT h34).elim

theorem lemma26G_of_leaves
    (L : Prop27Leaves) : S_lemma26G := by
  intro G _ _ hG hgen hK hrank hL2
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hRE, hO⟩ := hcon
  refine hRE (isRestrictedEvenType_of_oddCoreFree L hgen hrank.ge hL2 ?_)
  intro x hx
  by_contra hne
  exact hO ⟨x, hx, hne⟩

end CFSG.GH74.GLS.Prop27
