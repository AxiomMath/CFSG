module

public import CFSG.GH74.QTGen4.U42.VertexGen4
public import CFSG.Quasithin.Background.Harris.F112S3Big.Defs

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def dsOmega1 (X : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ X ∧ x ^ 2 = 1}

@[expose] def dsFrattini (X : Subgroup G) : Subgroup G := (frattini ↥X).map X.subtype

@[expose] def dsZ (S : Subgroup G) : Subgroup G := dsOmega1 (centerOf S)

@[expose] def dsConjClosure (Y X : Subgroup G) : Subgroup G :=
  ⨆ y ∈ Y, X.map (MulAut.conj y).toMonoidHom

@[expose] def dsZi (Li S : Subgroup G) : Subgroup G := dsConjClosure Li (dsZ S)

@[expose] def dsQ (Li Lj S : Subgroup G) : Subgroup G := pCoreOf 2 (Li ⊔ bigB Li Lj S)

@[expose] def dsV1 (L1 L2 S : Subgroup G) : Subgroup G :=
  dsConjClosure (L1 ⊔ bigB L1 L2 S) (dsZi L2 S)

@[expose] def IsElemSec (K E : Subgroup G) : Prop := K ≤ E ∧ ⁅E, E⁆ ≤ K ∧ ∀ e ∈ E, e ^ 2 ∈ K

@[expose] def FixFree (K E : Subgroup G) (x : G) : Prop := ∀ e ∈ E, ⁅e, x⁆ ∈ K → e ∈ K

@[expose] def NatSec (L K E : Subgroup G) : Prop := ∀ x ∈ L, orderOf x = 3 → FixFree K E x

@[expose] def dsCentMod (P L Q : Subgroup G) : Subgroup G where
  carrier := {p | p ∈ P ∧ p ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅p, l⁆ ∈ Q}
  one_mem' := ⟨P.one_mem, Subgroup.one_mem _, fun l _ => by simpa using Q.one_mem⟩
  mul_mem' := by
    rintro p p' ⟨hp, hpN, hpc⟩ ⟨hp', hp'N, hp'c⟩
    refine ⟨P.mul_mem hp hp', Subgroup.mul_mem _ hpN hp'N, fun l hl => ?_⟩
    have e : ⁅p * p', l⁆ = p * ⁅p', l⁆ * p⁻¹ * ⁅p, l⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine Q.mul_mem ?_ (hpc l hl)
    exact (Subgroup.mem_normalizer_iff.mp hpN _).mp (hp'c l hl)
  inv_mem' := by
    rintro p ⟨hp, hpN, hpc⟩
    refine ⟨P.inv_mem hp, Subgroup.inv_mem _ hpN, fun l hl => ?_⟩
    have e : ⁅p⁻¹, l⁆ = p⁻¹ * ⁅p, l⁆⁻¹ * p := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅p, l⁆⁻¹ ∈ Q := Q.inv_mem (hpc l hl)
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpN) _).mp h1
    simpa using this

@[expose] def S3Type2 (P : Subgroup G) (k d : G) : Prop :=
  FixFree (dsFrattini (pCoreOf 2 P)) (pCoreOf 2 P) k ∧
    FixFree (dsFrattini (pCoreOf 2 P)) (pCoreOf 2 P) d ∧
    ∀ X : Subgroup G, dsFrattini (pCoreOf 2 P) ≤ X → X ≤ pCoreOf 2 P →
      P ≤ Subgroup.normalizer (X : Set G) → X = dsFrattini (pCoreOf 2 P) ∨ X = pCoreOf 2 P

@[expose] def S3Type1 (P L : Subgroup G) (k d : G) : Prop :=
  ∃ W' W'' : Subgroup G,
    dsFrattini (pCoreOf 2 P) ≤ W' ∧ W' ≤ pCoreOf 2 P ∧
    dsFrattini (pCoreOf 2 P) ≤ W'' ∧ W'' ≤ pCoreOf 2 P ∧
    P ≤ Subgroup.normalizer (W' : Set G) ∧ P ≤ Subgroup.normalizer (W'' : Set G) ∧
    W' ⊓ W'' = dsFrattini (pCoreOf 2 P) ∧ W' ⊔ W'' = pCoreOf 2 P ∧
    (dsFrattini (pCoreOf 2 P)).relIndex W' = 4 ∧ (dsFrattini (pCoreOf 2 P)).relIndex W'' = 4 ∧
    (∀ l ∈ L, ∀ w ∈ W', ⁅l, w⁆ ∈ dsFrattini (pCoreOf 2 P)) ∧
    FixFree (dsFrattini (pCoreOf 2 P)) W' d ∧
    (∀ w ∈ W'', ⁅d, w⁆ ∈ dsFrattini (pCoreOf 2 P)) ∧
    FixFree (dsFrattini (pCoreOf 2 P)) W'' k ∧
    (∃ l ∈ L, ∃ w ∈ W'', ⁅l, w⁆ ∉ dsFrattini (pCoreOf 2 P))

structure A5Chief (P L E K : Subgroup G) : Prop where
  le : L ≤ P
  norm_L : P ≤ Subgroup.normalizer (L : Set G)
  E_le : E ≤ P
  norm_E : P ≤ Subgroup.normalizer (E : Set G)
  norm_K : P ≤ Subgroup.normalizer (K : Set G)
  sec : IsElemSec K E
  card : K.relIndex E = 16
  irred : ∀ X : Subgroup G, K ≤ X → X ≤ E → P ≤ Subgroup.normalizer (X : Set G) → X = K ∨ X = E
  core : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K
  quot : IsL2Quot 2 (oTwoQuot ↥L)
  nontriv : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K

structure A5Par (L P : Subgroup G) : Prop where
  le : L ≤ P
  norm : P ≤ Subgroup.normalizer (L : Set G)
  charTwo : CharTwo P
  quot : IsL2Quot 2 (oTwoQuot ↥L)

structure S3Par (L P : Subgroup G) (d : G) : Prop where
  le : L ≤ P
  norm : P ≤ Subgroup.normalizer (L : Set G)
  charTwo : CharTwo P
  quot : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))
  d_mem : d ∈ P
  d_ord : orderOf d = 3
  d_cent : ∀ l ∈ L, ⁅d, l⁆ ∈ pCoreOf 2 P

structure ZSetting (L1 L2 S : Subgroup G) : Prop where
  hyp : Hyp111R L1 L2 S
  bnorm : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)

structure DSAHyp (L1 L2 S : Subgroup G) : Prop where
  hyp : Hyp111R L1 L2 S
  ns1 : ¬ Group.IsSolvable ↥L1
  ns2 : ¬ Group.IsSolvable ↥L2
  norm : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal

structure DSBHyp0 (L1 L2 S : Subgroup G) : Prop where
  hyp : Hyp111R L1 L2 S
  ns1 : ¬ Group.IsSolvable ↥L1
  s3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))

structure DSBHyp (L1 L2 S : Subgroup G) : Prop extends DSBHyp0 L1 L2 S where
  red : S = (S ⊓ L1) ⊔ (S ⊓ L2)

theorem DSAHyp.symm {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) : DSAHyp L2 L1 S :=
  ⟨h.hyp.symm, h.ns2, h.ns1, h.norm.symm⟩

theorem ZSetting.symm {L1 L2 S : Subgroup G} (h : ZSetting L1 L2 S) : ZSetting L2 L1 S :=
  ⟨h.hyp.symm, by rw [bigB_comm]; exact h.bnorm⟩

theorem dsZ_le_center (S : Subgroup G) : dsZ S ≤ centerOf S :=
  (Subgroup.closure_le (centerOf S)).2 fun _ hx => hx.1

theorem dsZ_le_dsZi (Li S : Subgroup G) : dsZ S ≤ dsZi Li S := by
  refine le_iSup₂_of_le (1 : G) Li.one_mem ?_
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem dsZi_eq_dsZ_of_commutator_eq_bot {Li S : Subgroup G} (h : ⁅dsZi Li S, Li⁆ = ⊥) :
    dsZi Li S = dsZ S := by
  refine le_antisymm (iSup₂_le fun y hy => ?_) (dsZ_le_dsZi Li S)
  rintro _ ⟨z, hz, rfl⟩
  have hzi : z ∈ dsZi Li S := dsZ_le_dsZi Li S hz
  have hc : ⁅z, y⁆ ∈ ⁅dsZi Li S, Li⁆ := Subgroup.commutator_mem_commutator hzi hy
  rw [h, Subgroup.mem_bot] at hc
  have : y * z * y⁻¹ = z := by
    have h1 : z * y * z⁻¹ * y⁻¹ = 1 := hc
    calc y * z * y⁻¹ = (z * y * z⁻¹ * y⁻¹)⁻¹ * z * 1 := by group
      _ = z := by rw [h1]; group
  show y * z * y⁻¹ ∈ dsZ S
  rw [this]
  exact hz

theorem coreFree [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXle : X ≤ L1 ⊔ L2 ⊔ S)
    (h1 : L1 ≤ Subgroup.normalizer (X : Set G)) (h2 : L2 ≤ Subgroup.normalizer (X : Set G))
    (hS : S ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : X ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXle (sup_le (sup_le h1 h2) hS) hX
  rw [h.o2] at h3
  exact le_bot_iff.mp h3

theorem A5Par.of_hyp111R [Finite G] (hG : CFSG.GH74.Gen4 G) {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hns : ¬ Group.IsSolvable ↥L1) : A5Par L1 (L1 ⊔ bigB L1 L2 S) :=
  ⟨le_sup_left, F1.parabolic_le_normalizer h, F1.parabolic_charTwo h,
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 hG h.hyp.h1 hns⟩

theorem normalizer_inf_eq_bigB [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXle : X ≤ L1 ⊔ L2 ⊔ S) (hX0 : X ≠ ⊥)
    (h1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G)) :
    (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (X : Set G) = bigB L1 L2 S := by
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans h1
  have hm := F1.bigB_maximal_in_parabolic h.symm
    ((L2 ⊔ bigB L2 L1 S) ⊓ Subgroup.normalizer (X : Set G))
    (by rw [bigB_comm]; exact le_inf le_sup_right hBN) inf_le_left
  rw [bigB_comm] at hm
  rcases hm with hm | hm
  · exact hm
  · exfalso
    have hP2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G) := inf_eq_left.mp hm
    refine hX0 (coreFree h.hyp hX hXle (le_sup_left.trans h1) (le_sup_left.trans hP2) ?_)
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans hBN

theorem DSBHyp.bnorm [Finite G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
  have h1 := (F1.bigB_le_normalizer_sylow h.hyp).1
  have h2 := (F1.bigB_le_normalizer_sylow h.hyp).2
  have h3 : bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L1 ⊔ S ⊓ L2 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup h1 h2
  rwa [← h.red] at h3

structure L34Model where
  Y : Type
  [grp : Group Y]
  T0 : Subgroup Y
  M1 : Subgroup Y
  M2 : Subgroup Y
  lie : IsLieOverTwo .PSL 3 2 Y
  pair : IsYAmalgamPair T0 M1 M2

attribute [instance] L34Model.grp

structure L34ModelFacts (Mdl : L34Model) : Prop where
  T0_le : Mdl.T0 ≤ Mdl.M1 ⊓ Mdl.M2
  card_T0 : Nat.card ↥Mdl.T0 = 64
  card_B0 : Nat.card ↥(Mdl.M1 ⊓ Mdl.M2) = 192
  normalizer_T0 : Subgroup.normalizer (Mdl.T0 : Set Mdl.Y) = Mdl.M1 ⊓ Mdl.M2
  sylow1 : IsSylowTwoOf Mdl.T0 Mdl.M1
  sylow2 : IsSylowTwoOf Mdl.T0 Mdl.M2
  quot1 : IsL2Quot 2 (oTwoQuot ↥Mdl.M1)
  quot2 : IsL2Quot 2 (oTwoQuot ↥Mdl.M2)
  charTwo1 : CharTwo Mdl.M1
  charTwo2 : CharTwo Mdl.M2
  elem1 : IsElemAbelian 2 (pCoreOf 2 Mdl.M1)
  elem2 : IsElemAbelian 2 (pCoreOf 2 Mdl.M2)
  card1 : Nat.card (pCoreOf 2 Mdl.M1) = 16
  card2 : Nat.card (pCoreOf 2 Mdl.M2) = 16
  nat1 : NatSec Mdl.M1 ⊥ (pCoreOf 2 Mdl.M1)
  nat2 : NatSec Mdl.M2 ⊥ (pCoreOf 2 Mdl.M2)
  ne : pCoreOf 2 Mdl.M1 ≠ pCoreOf 2 Mdl.M2
  le1 : pCoreOf 2 Mdl.M1 ≤ Mdl.T0
  le2 : pCoreOf 2 Mdl.M2 ≤ Mdl.T0
  only : ∀ E : Subgroup Mdl.Y, E ≤ Mdl.T0 → IsElemAbelian 2 E → Nat.card E = 16 →
    E = pCoreOf 2 Mdl.M1 ∨ E = pCoreOf 2 Mdl.M2

end CFSG.GH74.QTGen4.DSGen4
