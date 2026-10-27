module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup

@[expose] def IsWBlock (X : Type) [Group X] : Prop :=
  (CFSG.Open.IsQuasisimple X ∧ Odd (Nat.card (center X))) ∨ IsSymThreeOrSUThreeTwo X

theorem IsWBlock.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') (h : IsWBlock X) :
    IsWBlock X' := by
  rcases h with ⟨hq, ho⟩ | hs
  · exact Or.inl ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv ▸ ho⟩
  · exact Or.inr (IsSymThreeOrSUThreeTwo.of_mulEquiv e hs)

@[expose] def HasLeviCensus (R : Type) [Group R] (B : (X : Type) → [Group X] → Prop) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (σ : Q →* R) (k : ℕ) (G : Fin k → Type)
    (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j)) (S : ∀ j, Subgroup (G j))
    (β : Q →* ∀ j, G j),
    Function.Surjective σ ∧ σ.ker ≤ center Q ∧ Odd (Nat.card σ.ker) ∧ IsPGroup 2 β.ker ∧
    Subgroup.pi Set.univ S ≤ β.range ∧
    β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)) ∧
    ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range ∧ (∀ j, S j = ⊥ ∨ B ↥(S j)) ∧
    ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z ∈ σ.ker,
      β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1

theorem HasLeviCensus.of_mulEquiv {R R' : Type} [Group R] [Group R']
    {B : (X : Type) → [Group X] → Prop} (e : R ≃* R') (h : HasLeviCensus R B) :
    HasLeviCensus R' B := by
  obtain ⟨Q, _, _, σ, k, G, _, _, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, hZ⟩ := h
  have hker : (e.toMonoidHom.comp σ).ker = σ.ker := by
    ext z
    simp [MonoidHom.mem_ker]
  refine ⟨Q, inferInstance, inferInstance, e.toMonoidHom.comp σ, k, G, inferInstance,
    inferInstance, S, β, e.surjective.comp hσ, hker ▸ hc, hker ▸ ho, hβ, hle, hn, hi, hS, ?_⟩
  intro j hj z hz
  exact hZ j hj z (hker ▸ hz)

@[expose] def IsSpTwoFactor (X : Type) [Group X] : Prop :=
  Subsingleton X ∨
    (IsWBlock X ∧ center X = ⊥ ∧
      ∀ T : Sylow 2 X, normalizer ((T : Subgroup X) : Set X) = T) ∨
    Nonempty (X ≃* Equiv.Perm (Fin 6))

@[expose] def IsSpTwoLeviProduct (R : Type) [Group R] : Prop :=
  ∃ (k : ℕ) (X : Fin k → Type) (_ : ∀ i, Group (X i)) (_ : ∀ i, Finite (X i)),
    Nonempty (R ⧸ CFSG.pCore 2 R ≃* ∀ i, X i) ∧ ∀ i, IsSpTwoFactor (X i)

@[expose] def IdxBTwo : TauCeti.LieTypeIndex → Prop
  | .B _ q => q.card = 2
  | _ => False

@[expose] def IdxBBig : TauCeti.LieTypeIndex → Prop
  | .B _ q => q.p = 2 ∧ q.card ≠ 2
  | _ => False

theorem isLieOf_idxB_cases {X : Type} [Group X] (h : IsLieOf IdxB X) :
    IsLieOf IdxBTwo X ∨ IsLieOf IdxBBig X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d with
  | B r q =>
    by_cases h2 : q.card = 2
    · exact Or.inl ⟨⟨_, hv⟩, h2, he⟩
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, h2⟩, he⟩
  | _ => exact hd.elim

open CFSG.Open TenThreeThree in
theorem le_wSup_of_subnormal_of_isQuasisimple {Q : Type} [Group Q] {T : Subgroup Q}
    (hsub : IsSubnormal T ⊤) (hq : CFSG.Open.IsQuasisimple ↥T) : T ≤ wSup Q := by
  unfold wSup
  exact le_iSup₂ (f := fun (T : Subgroup Q)
      (_ : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T)
    T ⟨hsub, Or.inl ⟨le_top, hsub, hq⟩⟩

open CFSG.Open TenThreeThree in
theorem le_wSup_of_subnormal_of_symThree {Q : Type} [Group Q] {T : Subgroup Q}
    (hsub : IsSubnormal T ⊤) (hsym : IsSymThreeOrSUThreeTwo ↥T) : T ≤ wSup Q := by
  unfold wSup
  exact le_iSup₂ (f := fun (T : Subgroup Q)
      (_ : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T)
    T ⟨hsub, Or.inr hsym⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
