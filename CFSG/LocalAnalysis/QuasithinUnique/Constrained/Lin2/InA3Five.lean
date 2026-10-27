module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_23_main : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 →
      ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
          IsLin2Type (L ⊓ Subgroup.centralizer ({s} : Set G)) m ∧
          blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
            blockU (L ⊓ Subgroup.centralizer ({s} : Set G))) ∨
        (n = 2 ∧
          (Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃*
              Equiv.Perm (Fin 4)) ∨
            Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃*
              Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∧
      thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) =
        strongClosure (pCoreOf 2 H) (T ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      (blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
          pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
        Subgroup.normalizer ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :
            Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      (T = thompsonJ S ⊔ (T ⊓ Subgroup.centralizer ({s} : Set G)) ∧
        (∃ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S) ∧
        IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G)) (Subgroup.centralizer ({s} : Set G)))

@[expose] def Lemma2_4_23_five : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 →
      (centerOf L ≠ ⊥ → 4 < 2 ^ n →
        ∀ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S →
          (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ (n / 2) ∧
            Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
                conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) ≃*
              Matrix.symplecticGroup (Fin 2) F)) ∧
          T ⊓ Subgroup.centralizer ({s} : Set G) ⊓
              Subgroup.centralizer ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
                conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) : Set G) =
            Subgroup.zpowers s ∧
          (∃ t ∈ T ⊓ Subgroup.centralizer ({s} : Set G),
            T ⊓ Subgroup.centralizer ({s} : Set G) =
              (Subgroup.zpowers s ⊔ thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) ⊔
                Subgroup.zpowers t) ∧
          (Subgroup.zpowers s ⊔ thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)).relIndex
              (T ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ (n.factorization 2))

theorem lemma2_4_23_of_main_five (h : Lemma2_4_23_main) (h5 : Lemma2_4_23_five) : Lemma2_4_23 :=
  fun G _ _ T M H S L D n hcfg s hs hsR hs2 =>
    ⟨(h G T M H S L D n hcfg s hs hsR hs2).1, (h G T M H S L D n hcfg s hs hsR hs2).2.1,
      (h G T M H S L D n hcfg s hs hsR hs2).2.2.1, (h G T M H S L D n hcfg s hs hsR hs2).2.2.2,
      h5 G T M H S L D n hcfg s hs hsR hs2⟩

end CFSG.QuasithinUnique.Lin2
