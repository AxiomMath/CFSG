module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1P

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped commutatorElement

abbrev RP := (Fin 5 → ZMod 2) × Equiv.Perm (Fin 5)

@[expose] def rmul (x y : RP) : RP := (x.1 + pact x.2 y.1, x.2 * y.2)

@[expose] def rone : RP := (0, 1)

@[expose] def rpow (x : RP) : ℕ → RP
  | 0 => rone
  | n + 1 => rmul x (rpow x n)

@[expose] def s1 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def s3 : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 1 2

@[expose] def gA1 : RP := (![0, 0, 1, 1, 0], s3)

@[expose] def gA2 : RP := (![0, 1, 0, 1, 0], s1)

@[expose] def gB1 : RP := (![0, 1, 1, 0, 0], s1)

@[expose] def gB2 : RP := (![0, 1, 0, 1, 0], s3)

@[expose] def qtab (α β : RP) : QuaternionGroup 2 → RP
  | .a i => rpow α i.val
  | .xa i => rmul β (rpow α i.val)

theorem qA_mul : ∀ x y : QuaternionGroup 2,
    rmul (qtab gA1 gA2 x) (qtab gA1 gA2 y) = qtab gA1 gA2 (x * y) := by decide +kernel

theorem qB_mul : ∀ x y : QuaternionGroup 2,
    rmul (qtab gB1 gB2 x) (qtab gB1 gB2 y) = qtab gB1 gB2 (x * y) := by decide +kernel

theorem qA_inj : ∀ x y : QuaternionGroup 2, qtab gA1 gA2 x = qtab gA1 gA2 y → x = y := by
  decide +kernel

theorem qB_inj : ∀ x y : QuaternionGroup 2, qtab gB1 gB2 x = qtab gB1 gB2 y → x = y := by
  decide +kernel

theorem q_comm : ∀ x y : QuaternionGroup 2,
    rmul (qtab gA1 gA2 x) (qtab gB1 gB2 y) = rmul (qtab gB1 gB2 y) (qtab gA1 gA2 x) := by
  decide +kernel

theorem qA_V : ∀ x : QuaternionGroup 2, (qtab gA1 gA2 x).2 ∈ Vset ∧ (qtab gA1 gA2 x).1 4 = 0 ∧
    isEven (qtab gA1 gA2 x).1 := by decide +kernel

theorem qB_V : ∀ x : QuaternionGroup 2, (qtab gB1 gB2 x).2 ∈ Vset ∧ (qtab gB1 gB2 x).1 4 = 0 ∧
    isEven (qtab gB1 gB2 x).1 := by decide +kernel

theorem q_cover : ∀ v : Fin 5 → ZMod 2, ∀ σ ∈ Vset, isEven v → v 4 = 0 →
    ∃ x y : QuaternionGroup 2, rmul (qtab gA1 gA2 x) (qtab gB1 gB2 y) = (v, σ) := by
  decide +kernel

@[expose] def Praw : Finset RP :=
  Finset.univ.filter fun p : RP => isE8 p.1 ∧ p.2 ∈ Vset

theorem Praw_card : Praw.card = 32 := by decide +kernel

theorem mem_Praw {p : RP} : p ∈ Praw ↔ isE8 p.1 ∧ p.2 ∈ Vset := by simp [Praw]

theorem qA_ev : ∀ x, isEven (qtab gA1 gA2 x).1 := fun x => (qA_V x).2.2

theorem qB_ev : ∀ x, isEven (qtab gB1 gB2 x).1 := fun x => (qB_V x).2.2

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem emb_congr {u u' : evenWeight 5} {σ σ' : Equiv.Perm (Fin 5)} (hu : u = u') (hσ : σ = σ') :
    X.emb u σ = X.emb u' σ' := by
  subst hu
  subst hσ
  rfl

theorem card_P : Nat.card ↥(borelP M L) = 32 := by
  rw [X.borelP_eq]
  let f : {p : RP // p ∈ Praw} → ↥X.Psub := fun p =>
    ⟨((X.emb ⟨p.1.1, ((mem_Praw.mp p.2).1).1⟩ p.1.2 : ↥H) : G),
      ⟨_, _, (mem_Vstd _).mpr (mem_Praw.mp p.2).2, ((mem_Praw.mp p.2).1).2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h1 : ((X.emb ⟨p.1.1, ((mem_Praw.mp p.2).1).1⟩ p.1.2 : ↥H) : G) =
          ((X.emb ⟨q.1.1, ((mem_Praw.mp q.2).1).1⟩ q.1.2 : ↥H) : G) := congrArg (fun y : ↥X.Psub => (y : G)) hpq
      obtain ⟨h2, h3⟩ := X.emb_inj (Subtype.ext h1)
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val h2) h3
    · rintro ⟨x, w, σ, hσ, hw, rfl⟩
      exact ⟨⟨(w.1, σ), mem_Praw.mpr ⟨⟨w.2, hw⟩, hσ⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe, Praw_card]

@[expose] noncomputable def qhom (α β : RP) (hev : ∀ x, isEven (qtab α β x).1)
    (hmul : ∀ x y, rmul (qtab α β x) (qtab α β y) = qtab α β (x * y)) :
    QuaternionGroup 2 →* ↥H where
  toFun g := X.emb ⟨(qtab α β g).1, hev g⟩ (qtab α β g).2
  map_one' := by
    have h : qtab α β 1 = rone := rfl
    show X.emb ⟨(qtab α β 1).1, hev 1⟩ (qtab α β 1).2 = 1
    rw [← X.emb_zero_one]
    exact X.emb_congr (Subtype.ext (congrArg Prod.fst h)) (congrArg Prod.snd h)
  map_mul' x y := by
    have h := hmul x y
    have h1 : (qtab α β x).1 + pact (qtab α β x).2 (qtab α β y).1 = (qtab α β (x * y)).1 :=
      congrArg Prod.fst h
    have h2 : (qtab α β x).2 * (qtab α β y).2 = (qtab α β (x * y)).2 := congrArg Prod.snd h
    show X.emb _ _ = X.emb _ _ * X.emb _ _
    rw [X.emb_mul]
    exact X.emb_congr (Subtype.ext h1.symm) h2.symm

theorem qhom_inj (α β : RP) (hev : ∀ x, isEven (qtab α β x).1)
    (hmul : ∀ x y, rmul (qtab α β x) (qtab α β y) = qtab α β (x * y))
    (hinj : ∀ x y, qtab α β x = qtab α β y → x = y) :
    Function.Injective (X.qhom α β hev hmul) := by
  intro x y hxy
  obtain ⟨h1, h2⟩ := X.emb_inj hxy
  exact hinj x y (Prod.ext (congrArg Subtype.val h1) h2)

theorem qhom_mem (α β : RP) (hev : ∀ x, isEven (qtab α β x).1)
    (hmul : ∀ x y, rmul (qtab α β x) (qtab α β y) = qtab α β (x * y))
    (hV : ∀ x, (qtab α β x).2 ∈ Vset ∧ (qtab α β x).1 4 = 0) (g : QuaternionGroup 2) :
    ((X.qhom α β hev hmul g : ↥H) : G) ∈ borelP M L := by
  rw [X.borelP_eq]
  exact ⟨⟨(qtab α β g).1, hev g⟩, (qtab α β g).2, (mem_Vstd _).mpr (hV g).1, (hV g).2, rfl⟩

@[expose] noncomputable def QA : Subgroup G :=
  (X.qhom gA1 gA2 qA_ev qA_mul).range.map H.subtype

@[expose] noncomputable def QB : Subgroup G :=
  (X.qhom gB1 gB2 qB_ev qB_mul).range.map H.subtype

theorem QA_le_P : X.QA ≤ borelP M L := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact X.qhom_mem gA1 gA2 qA_ev qA_mul (fun x => ⟨(qA_V x).1, (qA_V x).2.1⟩) g

theorem QB_le_P : X.QB ≤ borelP M L := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact X.qhom_mem gB1 gB2 qB_ev qB_mul (fun x => ⟨(qB_V x).1, (qB_V x).2.1⟩) g

theorem QA_iso : Nonempty (↥X.QA ≃* QuaternionGroup 2) := by
  have hinj := X.qhom_inj gA1 gA2 qA_ev qA_mul qA_inj
  exact ⟨((MonoidHom.ofInjective hinj).trans
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)).symm⟩

theorem QB_iso : Nonempty (↥X.QB ≃* QuaternionGroup 2) := by
  have hinj := X.qhom_inj gB1 gB2 qB_ev qB_mul qB_inj
  exact ⟨((MonoidHom.ofInjective hinj).trans
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)).symm⟩

theorem QA_comm_QB : ⁅X.QA, X.QB⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [Subgroup.mem_bot]
  have h := q_comm x y
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hc : X.qhom gA1 gA2 qA_ev qA_mul x * X.qhom gB1 gB2 qB_ev qB_mul y =
      X.qhom gB1 gB2 qB_ev qB_mul y * X.qhom gA1 gA2 qA_ev qA_mul x := by
    show X.emb _ _ * X.emb _ _ = X.emb _ _ * X.emb _ _
    rw [X.emb_mul, X.emb_mul]
    exact X.emb_congr (Subtype.ext h1) h2
  have hcomm := congrArg H.subtype hc
  rw [map_mul, map_mul] at hcomm
  show _ * _ * _⁻¹ * _⁻¹ = 1
  rw [mul_inv_eq_one, hcomm]
  group

theorem QA_sup_QB : X.QA ⊔ X.QB = borelP M L := by
  apply le_antisymm (sup_le X.QA_le_P X.QB_le_P)
  rw [X.borelP_eq]
  rintro _ ⟨w, σ, hσ, hw, rfl⟩
  obtain ⟨x, y, hxy⟩ := q_cover w.1 σ ((mem_Vstd σ).mp hσ) w.2 hw
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  have hprod : X.emb w σ = X.qhom gA1 gA2 qA_ev qA_mul x * X.qhom gB1 gB2 qB_ev qB_mul y := by
    show _ = X.emb _ _ * X.emb _ _
    rw [X.emb_mul]
    exact X.emb_congr (Subtype.ext h1.symm) h2.symm
  rw [hprod]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, ⟨x, rfl⟩, rfl⟩) (Subgroup.mem_sup_right ⟨_, ⟨y, rfl⟩, rfl⟩)

theorem q8 : IsQ8Square (borelP M L) :=
  ⟨X.card_P, X.QA, X.QB, X.QA_le_P, X.QB_le_P, X.QA_sup_QB, X.QA_comm_QB, X.QA_iso, X.QB_iso⟩

end Sec

end CFSG.QuasithinUnique.A5
