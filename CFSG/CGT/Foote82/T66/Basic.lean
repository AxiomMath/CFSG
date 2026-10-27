module

public import CFSG.CGT.Foote82.Thm66

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def FaithfulTildeV (L : Subgroup (GLV V)) : Prop :=
  ∀ ℓ ∈ L, (∀ w ∈ commSpace L ⊤, ℓ w - w ∈ fixedSpace L) → ℓ = 1

structure Conf66 (G S L : Subgroup (GLV V)) : Prop where
  kProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥G
  setup : Setup6Irr G S L
  fmod : IsFPrimeModule L

@[expose] def Concl66 (G L : Subgroup (GLV V)) : Prop :=
  L = G ∨
    (∃ n k : ℕ, 6 ≤ n ∧ 1 ≤ k ∧ Nonempty (↥L ≃* alternatingGroup (Fin n)) ∧
      IsAltHeartFor (layerIn G) (n + 2 * k)) ∨
    (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ IsOmegaMinusFor (layerIn G) 2)

theorem thm66F_iff : Thm66F ↔ ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (G S L : Subgroup (GLV V)), Conf66 G S L → Concl66 G L :=
  ⟨fun h V _ _ _ G S L hc => h V G S L hc.kProper hc.setup hc.fmod,
    fun h V _ _ _ G S L hK hs hf => h V G S L ⟨hK, hs, hf⟩⟩

@[expose] def Thm66FFaith : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G S L : Subgroup (GLV V)),
    Conf66 G S L → FaithfulTildeV L → Concl66 G L

@[expose] def Thm66FNonFaith : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G S L : Subgroup (GLV V)),
    Conf66 G S L → ¬ FaithfulTildeV L → Concl66 G L

theorem thm66F_of_faith (h₁ : Thm66FFaith) (h₂ : Thm66FNonFaith) : Thm66F :=
  thm66F_iff.2 fun V _ _ _ G S L hc => by
    by_cases hf : FaithfulTildeV L
    · exact h₁ V G S L hc hf
    · exact h₂ V G S L hc hf

theorem Conf66.L_le {G S L : Subgroup (GLV V)} (hc : Conf66 G S L) : L ≤ G :=
  hc.setup.component.1.trans inf_le_left

structure Extremal (G S L : Subgroup (GLV V)) : Prop extends Conf66 G S L where
  faithful : FaithfulTildeV L
  not_concl : ¬ Concl66 G L
  min : ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (G' S' L' : Subgroup (GLV V')), Nat.card G' < Nat.card G → Conf66 G' S' L' →
      FaithfulTildeV L' → Concl66 G' L'
  max : ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (G' S' L' : Subgroup (GLV V')), Nat.card G' = Nat.card G → Nat.card L < Nat.card L' →
      Conf66 G' S' L' → FaithfulTildeV L' → Concl66 G' L'

instance instFiniteGLVT66 : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

theorem thm66FFaith_of_noExtremal
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (G S L : Subgroup (GLV V)), Extremal G S L → False) : Thm66FFaith := by
  suffices key : ∀ n m : ℕ, ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (G S L : Subgroup (GLV V)), Nat.card G = n → Nat.card G - Nat.card L = m →
        Conf66 G S L → FaithfulTildeV L → Concl66 G L from
    fun V _ _ _ G S L hc hf => key _ _ V G S L rfl rfl hc hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
  intro V _ _ _ G S L hn hm hc hf
  by_contra hne
  refine h V G S L ⟨hc, hf, hne, ?_, ?_⟩
  · intro V' _ _ _ G' S' L' hlt hc' hf'
    exact IHn _ (hn ▸ hlt) _ V' G' S' L' rfl rfl hc' hf'
  · intro V' _ _ _ G' S' L' heq hlt hc' hf'
    have hle : Nat.card L ≤ Nat.card G := Subgroup.card_le_of_le hc.L_le
    have hle' : Nat.card L' ≤ Nat.card G' := Subgroup.card_le_of_le hc'.L_le
    exact IHm _ (by omega) V' G' S' L' (heq.trans hn) rfl hc' hf'

structure StdForm (G L : Subgroup (GLV V)) (s : GLV V) : Prop where
  extremal : Extremal G (Subgroup.zpowers s) L
  orderOf_s : orderOf s = 2
  eq_layerIn_sup : G = layerIn G ⊔ Subgroup.zpowers s
  component_of_inv : ∀ t ∈ G, orderOf t = 2 → t ∈ Subgroup.centralizer (L : Set (GLV V)) →
    IsComponentOf L (G ⊓ Subgroup.centralizer ({t} : Set (GLV V)))
  quasisimple : 4 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V))) →
    G = layerIn G ∧ IsQuasisimple ↥G
  commutator_ne_bot : ∀ g ∈ G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  tight : ∀ g ∈ G, g ∉ Subgroup.normalizer (L : Set (GLV V)) →
    Odd (Nat.card ↥((G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
      (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom))
  normalizer_eq : G ⊓ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (L : Set (GLV V)) : Subgroup (GLV V)) : Set (GLV V)) =
    G ⊓ Subgroup.normalizer (L : Set (GLV V))

end CFSG.CGT.Foote82
