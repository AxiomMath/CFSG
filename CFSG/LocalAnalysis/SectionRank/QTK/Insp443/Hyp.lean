module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
  CFSG.QuasithinUnique

structure Hyp (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G) : Prop where
  setting : CFSG.Quasithin.H13.Ch4.Setting443 G T M L B Tp VB
  unique : IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
    (Tp ⊓ Subgroup.normalizer (B : Set G))) M
  oddCore_le : oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G)
  K_le : K ≤ Subgroup.normalizer (B : Set G)
  normalizer_le : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G)
  quasisimple : CFSG.IsQuasisimple ↥K
  not_le : ¬ K ≤ M
  VB_le : VB ≤ K
  LB_le : perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ K
  centralizer_eq : Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer (K : Set G) =
    oddCoreIn (Subgroup.normalizer (B : Set G))

@[expose] def For (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    Hyp G T M L B Tp VB K → P (↥K ⧸ Subgroup.center ↥K) →
    Concl443B G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB

theorem For.mono {P Q : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S], P S → Q S) (hQ : For Q) : For P := by
  intro G _ _ T M L B Tp VB K hH hP
  exact hQ G T M L B Tp VB K hH (h _ hP)

theorem For.or {P Q : (S : Type) → [Group S] → Prop} (hP : For P) (hQ : For Q) :
    For (fun S _ => P S ∨ Q S) := by
  intro G _ _ T M L B Tp VB K hH h
  rcases h with h' | h'
  · exact hP G T M L B Tp VB K hH h'
  · exact hQ G T M L B Tp VB K hH h'

end CFSG.SectionRank.QTK.Insp443
