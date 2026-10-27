module

public import CFSG.CGT.PushingUpLit.CGT6.EmbX
public import CFSG.CGT.PushingUpLit.CGT6.Embedding

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Defs

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def ClassX4 (Y : Subgroup (MulAut V)) : Prop :=
  InClassX ↥(yuHol Y) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaPlusAct n) Y (commV Y) ⊥)

@[expose] def NatOmegaN (n : ℕ) (X : Subgroup (MulAut V)) : Prop :=
  IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥ ∨ IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥

structure Adm4 (G T Y : Subgroup (MulAut V)) : Prop where
  hTG : T ≤ G
  hT1 : T ≠ ⊥
  hT2 : IsPGroup 2 ↥T
  hYC : Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V))
  hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal
  hperf : ⁅Y, Y⁆ = Y
  hcls : ClassX4 Y

structure Adm5 (G T Y : Subgroup (MulAut V)) : Prop where
  hTG : T ≤ G
  hT1 : T ≠ ⊥
  hT2 : IsPGroup 2 ↥T
  hYC : Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V))
  hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal
  h3 : Nat.card ↥Y = 3
  h4 : Nat.card ↥(commV Y) = 4

@[expose] def Lift4 (G Y X : Subgroup (MulAut V)) : Prop :=
  Y ≤ X ∧ X ≤ G ∧ (X.subgroupOf G).IsSubnormal ∧
    ((InClassX ↥(yuHol X) ∧ ArrowNat (yuHol Y) (yuHol X)) ∨
      ∃ n : ℕ, 2 ≤ n ∧
        (IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥ ∨
          IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥) ∧
        (Y = X ∨ (InClassX ↥(yuHol Y) ∧
          Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
          Nat.card ↥(commV Y) = 2 ^ (3 * n))))

@[expose] def Lift5 (G Y X : Subgroup (MulAut V)) : Prop :=
  Y ≤ X ∧ X ≤ G ∧ (X.subgroupOf G).IsSubnormal ∧ InClassX ↥(yuHol X) ∧
    ArrowNat (yuHol Y) (yuHol X)

@[expose] def Emb4At (G : Subgroup (MulAut V)) : Prop :=
  ∀ T Y : Subgroup (MulAut V), Adm4 G T Y → ∃ X, Lift4 G Y X

@[expose] def Emb5At (G : Subgroup (MulAut V)) : Prop :=
  ∀ T Y : Subgroup (MulAut V), Adm5 G T Y → ∃ X, Lift5 G Y X

end Defs

@[expose] def Emb4All : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G → Emb4At G

@[expose] def Emb5All : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G → Emb5At G

@[expose] def Omega4OrderThree : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ n : ℕ, 2 ≤ n →
    ∀ X Y : Subgroup (MulAut V), NatOmegaN n X → Y ≤ X → Nat.card ↥Y = 3 →
      4 < Nat.card ↥(commV Y)

section Defs

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def Smaller {V' : Type} [CommGroup V'] [Finite V'] (G' : Subgroup (MulAut V'))
    (G : Subgroup (MulAut V)) : Prop :=
  Nat.card ↥G' < Nat.card ↥G ∨ (Nat.card ↥G' = Nat.card ↥G ∧ Nat.card V' < Nat.card V)

structure Emb4Cfg (G T Y : Subgroup (MulAut V)) : Prop where
  adm : Adm4 G T Y
  kgroup : CFSG.IsKGroup ↥G
  sylow : ∀ T' : Subgroup (MulAut V), T ≤ T' →
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T
  nolift : ¬ ∃ X, Lift4 G Y X
  ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
    ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb4At G'
  maxY : ∀ T' Y' : Subgroup (MulAut V), Adm4 G T' Y' → (¬ ∃ X, Lift4 G Y' X) →
    Nat.card ↥Y' ≤ Nat.card ↥Y
  o2 : CFSG.pCore 2 ↥G = ⊥
  comm : commV G = ⊤
  cent : ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal
  gen : conjClosure Y G ⊔ T = G

structure Emb5Cfg (G T Y : Subgroup (MulAut V)) : Prop where
  adm : Adm5 G T Y
  kgroup : CFSG.IsKGroup ↥G
  sylow : ∀ T' : Subgroup (MulAut V), T ≤ T' →
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T
  nolift : ¬ ∃ X, Lift5 G Y X
  ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
    ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb5At G'
  h4 : Emb4All
  m6 : Omega4OrderThree
  o2 : CFSG.pCore 2 ↥G = ⊥
  comm : commV G = ⊤
  cent : ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal
  gen : conjClosure Y G ⊔ T = G

end Defs

@[expose] def Emb4End : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → False

@[expose] def Emb5End : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb5Cfg G T Y → False

theorem isKGroup_subgroup {G : Type} [Group G] (hK : CFSG.IsKGroup G) (H : Subgroup G) :
    CFSG.IsKGroup ↥H :=
  hK.subgroup H

theorem le_centralizer_of_le_centralizer {M : Type*} [Group M] {Y T' : Subgroup M}
    (h : T' ≤ Subgroup.centralizer (Y : Set M)) : Y ≤ Subgroup.centralizer (T' : Set M) :=
  fun y hy _ ht => (Subgroup.mem_centralizer_iff.mp (h ht) y hy).symm

section Basic

variable {V : Type} [CommGroup V] [Finite V]

theorem Adm4.restrict {G T Y H : Subgroup (MulAut V)} (h : Adm4 G T Y) (hTH : T ≤ H)
    (hHG : H ≤ G) (hYH : Y ≤ H) : Adm4 H T Y where
  hTG := hTH
  hT1 := h.hT1
  hT2 := h.hT2
  hYC := le_inf hYH fun _ hy => (h.hYC hy).2
  hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hHG) h.hsub
  hperf := h.hperf
  hcls := h.hcls

omit [Finite V] in
theorem Adm5.restrict {G T Y H : Subgroup (MulAut V)} (h : Adm5 G T Y) (hTH : T ≤ H)
    (hHG : H ≤ G) (hYH : Y ≤ H) : Adm5 H T Y where
  hTG := hTH
  hT1 := h.hT1
  hT2 := h.hT2
  hYC := le_inf hYH fun _ hy => (h.hYC hy).2
  hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hHG) h.hsub
  h3 := h.h3
  h4 := h.h4

theorem Adm4.enlarge {G T Y T' : Subgroup (MulAut V)} (h : Adm4 G T Y) (hTT : T ≤ T')
    (hT'G : T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (hT'2 : IsPGroup 2 ↥T') :
    Adm4 G T' Y where
  hTG := hT'G.trans inf_le_left
  hT1 := fun h0 => h.hT1 (eq_bot_iff.mpr (hTT.trans h0.le))
  hT2 := hT'2
  hYC := le_inf (fun _ hy => (h.hYC hy).1)
    (le_centralizer_of_le_centralizer (hT'G.trans inf_le_right))
  hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
    (inf_le_inf_left _ (Subgroup.centralizer_le hTT)) h.hsub
  hperf := h.hperf
  hcls := h.hcls

omit [Finite V] in
theorem Adm5.enlarge {G T Y T' : Subgroup (MulAut V)} (h : Adm5 G T Y) (hTT : T ≤ T')
    (hT'G : T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (hT'2 : IsPGroup 2 ↥T') :
    Adm5 G T' Y where
  hTG := hT'G.trans inf_le_left
  hT1 := fun h0 => h.hT1 (eq_bot_iff.mpr (hTT.trans h0.le))
  hT2 := hT'2
  hYC := le_inf (fun _ hy => (h.hYC hy).1)
    (le_centralizer_of_le_centralizer (hT'G.trans inf_le_right))
  hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
    (inf_le_inf_left _ (Subgroup.centralizer_le hTT)) h.hsub
  h3 := h.h3
  h4 := h.h4

theorem Adm4.le_centralizer {G T Y : Subgroup (MulAut V)} (h : Adm4 G T Y) :
    T ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
  le_centralizer_of_le_centralizer fun _ hy => (h.hYC hy).2

omit [Finite V] in
theorem Adm5.le_centralizer {G T Y : Subgroup (MulAut V)} (h : Adm5 G T Y) :
    T ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
  le_centralizer_of_le_centralizer fun _ hy => (h.hYC hy).2

end Basic

end CFSG.CGT.PushingUpLit.CGT6
