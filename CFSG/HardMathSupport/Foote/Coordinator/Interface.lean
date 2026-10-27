module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndFoote

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

structure FooteK (Q : Type) [Group Q] {V : Type} [CommGroup V] [Finite V]
    (L Y : Subgroup (MulAut V)) (z : MulAut V) (π : ↥L →* Q) : Prop where
  elem : ∀ v : V, v ^ 2 = 1
  quasi : CFSG.Open.IsQuasisimple ↥L
  oddZ : Odd (Nat.card ↥(Subgroup.center ↥L))
  surj : Function.Surjective π
  ker : π.ker = Subgroup.center ↥L
  le : Y ≤ L
  sl5 : YSL5 Y
  mem : z ∈ Y
  central : ∀ y ∈ Y, z * y = y * z
  ne_one : z ≠ 1
  invol : z * z = 1
  commZ : Nat.card ↥(commSub z) ≤ 4
  commFive : ∀ y ∈ Y, y ^ 5 = 1 → Nat.card ↥(commSub y) ≤ 16
  subnormal : (Y.subgroupOf (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)))).IsSubnormal

@[expose] def End415K (Q : Type) [Group Q] : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L Y : Subgroup (MulAut V)) (z : MulAut V)
    (π : ↥L →* Q), FooteK Q L Y z π → False

theorem FooteK.mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {V : Type}
    [CommGroup V] [Finite V] {L Y : Subgroup (MulAut V)} {z : MulAut V} {π : ↥L →* Q}
    (h : FooteK Q L Y z π) : FooteK Q' L Y z (e.toMonoidHom.comp π) where
  elem := h.elem
  quasi := h.quasi
  oddZ := h.oddZ
  surj := e.surjective.comp h.surj
  ker := by
    rw [← h.ker]
    ext x
    simp
  le := h.le
  sl5 := h.sl5
  mem := h.mem
  central := h.central
  ne_one := h.ne_one
  invol := h.invol
  commZ := h.commZ
  commFive := h.commFive
  subnormal := h.subnormal

theorem End415K.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : End415K Q') : End415K Q :=
  fun V _ _ L Y z π hK => h V L Y z (e.toMonoidHom.comp π) (hK.mulEquiv e)

@[expose] def FooteClassicalParam (t : Assembly.LowTwoRank.StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 3 ∧ f = 1) ∨ (t = .PSp ∧ n = 2 ∧ f = 1) ∨
    (t = .PSL ∧ n = 4 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1)

@[expose] def FooteExcParam (t : Assembly.LowTwoRank.StatedLieTag) (f : ℕ) : Prop :=
  (t = .G2 ∧ f = 1) ∨ (t = .trialityD4 ∧ 1 ≤ f)

@[expose] def AltTarget : Prop :=
  ∀ n : ℕ, 5 ≤ n → End415K (alternatingGroup (Fin n))

@[expose] def SporTarget : Prop :=
  ∀ s : TauCeti.SporadicName, End415K (Blueprint.NativeSporadic.Carrier s)

@[expose] def ClassicalOffFiveTarget : Prop :=
  ∀ (Q : Type) [Group Q] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), p ≠ 5 →
    Assembly.LowTwoRank.StatedClassicalModel Q t n p f → End415K Q

@[expose] def ExcOffFiveTarget : Prop :=
  ∀ (Q : Type) [Group Q] (t : Assembly.LowTwoRank.StatedLieTag) (p f : ℕ), p ≠ 5 →
    t ∈ Blueprint.chevalleyExceptionalTags → Blueprint.ChevalleyExceptionalModel Q t p f →
      End415K Q

@[expose] def ReeTitsSuzukiTarget : Prop :=
  (∀ (Q : Type) [Group Q] (t : Assembly.LowTwoRank.StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.reeTitsTags → Blueprint.ReeTitsModel Q t p f → End415K Q) ∧
    ∀ (Q : Type) [Group Q] (p f : ℕ), Blueprint.SuzukiModel Q p f → End415K Q

@[expose] def ClassicalFiveTarget : Prop :=
  ∀ (Q : Type) [Group Q] (t : Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
    Assembly.LowTwoRank.StatedClassicalModel Q t n 5 f → ¬ FooteClassicalParam t n f →
      End415K Q

@[expose] def ExcFiveTarget : Prop :=
  ∀ (Q : Type) [Group Q] (t : Assembly.LowTwoRank.StatedLieTag) (f : ℕ),
    t ∈ Blueprint.chevalleyExceptionalTags → Blueprint.ChevalleyExceptionalModel Q t 5 f →
      ¬ FooteExcParam t f → End415K Q

theorem open_statedClassicalModel_of_footeParam {Q : Type} [Group Q]
    {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ} (hp : FooteClassicalParam t n f)
    (h : Assembly.LowTwoRank.StatedClassicalModel Q t n 5 f) : FooteList Q := by
  rcases hp with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem footeList_of_excParam {Q : Type} [Group Q] {t : Assembly.LowTwoRank.StatedLieTag}
    {f : ℕ} (hp : FooteExcParam t f) (h : Blueprint.ChevalleyExceptionalModel Q t 5 f) :
    FooteList Q := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, hf⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩)))

theorem footeList_or_end415K (hA : AltTarget) (hS : SporTarget) (hC : ClassicalOffFiveTarget)
    (hE : ExcOffFiveTarget) (hR : ReeTitsSuzukiTarget) (hC5 : ClassicalFiveTarget)
    (hE5 : ExcFiveTarget) (Q : Type) [Group Q] (hnab : ∃ a b : Q, a * b ≠ b * a)
    (hcat : Blueprint.Catalog Q) : FooteList Q ∨ End415K Q := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ |
      (⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩) | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact Or.inr (End415K.of_mulEquiv e (hA n hn))
  · by_cases hp : p = 5
    · subst hp
      by_cases hpar : FooteClassicalParam t n f
      · exact Or.inl (open_statedClassicalModel_of_footeParam hpar hm)
      · exact Or.inr (hC5 Q t n f hm hpar)
    · exact Or.inr (hC Q t n p f hp hm)
  · by_cases hp : p = 5
    · subst hp
      by_cases hpar : FooteExcParam t f
      · exact Or.inl (footeList_of_excParam hpar hm)
      · exact Or.inr (hE5 Q t f ht hm hpar)
    · exact Or.inr (hE Q t p f hp ht hm)
  · exact Or.inr (hR.1 Q t p f ht hm)
  · exact Or.inr (hR.2 Q p f hm)
  · exact Or.inr (End415K.of_mulEquiv e (hS s))

end CFSG.HardMathSupport.Foote.Coordinator
