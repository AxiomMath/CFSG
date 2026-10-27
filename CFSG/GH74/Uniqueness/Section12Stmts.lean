module

public import CFSG.GH74.Uniqueness.Section12Basic
public import CFSG.GH74.Uniqueness.Section5Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

structure LData {Z : Set X} {M : Subgroup X} (c : Ctx12 Z M) (n i : ℕ) : Prop where
  hi : i = 1 ∨ i = 2
  hn : 2 ≤ n
  bender : Bender.BenderType ↥c.L n i 1
  borel : ∃ Q : Sylow 2 ↥c.L, (M ⊓ c.L).subgroupOf c.L = normalizer (Q : Set ↥c.L)
  invol : ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z
  m_abelian : Open.IsElemAbelian 2 (zHull Z M)
  m_card : Nat.card ↥(zHull Z M) = 2 ^ n
  m_le : zHull Z M ≤ c.L
  m_normal : ∀ g ∈ M, ∀ x ∈ zHull Z M, g * x * g⁻¹ ∈ zHull Z M
  zM_eq : zM Z M = (zHull Z M : Set X) \ {1}
  prod_eq : productInvolutions Z = Z
  normalizer_eq : (normalizer (c.L : Set X) : Set X) = (c.L : Set X) * (c.D : Set X)
  centralizer_le : centralizer (c.L : Set X) ≤ c.D
  nM_eq : ∃ T : Subgroup X, T ≤ c.L ⊓ M ∧ IsPGroup 2 T ∧ ABGLocalTools.IsSylowOf 2 T (c.L ⊓ M) ∧
    (∀ g ∈ c.L ⊓ M, ∀ x ∈ T, g * x * g⁻¹ ∈ T) ∧
    ((M ⊓ normalizer (c.L : Set X) : Subgroup X) : Set X) = (T : Set X) * (c.D : Set X)
  dihedral : ∀ u : X, orderOf u = 2 → u ∉ Z →
    (Nat.card ↥(closure ({u, c.z} : Set X)) = 8 ∨
      ∃ k : ℕ, Odd k ∧ Nat.card ↥(closure ({u, c.z} : Set X)) = 4 * k) ∧
    ∀ w ∈ zpowers (u * c.z), orderOf w = 2 → Nat.card ↥(closure ({u, c.z} : Set X)) = 8 →
      closure ({w, c.z} : Set X) ≤ zHull Z M ∧ u ∈ M ∧ u ∉ centralizer (zHull Z M : Set X)
  k_eq : (kGrp M c.t : Set X) = CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t
  k_eq' : kGrp M c.t = c.D ⊓ c.L
  k_cyclic : IsCyclic ↥(c.D ⊓ c.L)
  k_card : Nat.card ↥(c.D ⊓ c.L) = 2 ^ n - 1

section Stmts

variable (Z : Set X) (M : Subgroup X)

@[expose] def Lemma122Stmt : Prop := ∀ c : Ctx12 Z M, ∃ n i : ℕ, LData c n i

@[expose] def Lemma123Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ v ∈ centralizer (c.L : Set X), v ≠ 1 →
    cenHull Z v = c.L ∨ (i = 1 ∧ c.L < cenHull Z v ∧ ∃ e, BenderSub Z M (cenHull Z v) n 3 e)

@[expose] def Lemma124Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 →
    ¬ centralizer ({u} : Set X) ≤ M ∧
    ((∀ y ∈ c.L, y * u = u * y) ∨
      (i = 1 ∧ ∃ k : ℕ, 2 ≤ k ∧ n = 2 * k ∧ qU Z M u = 2 ^ k ∧
        Bender.BenderType ↥(c.L ⊓ centralizer ({u} : Set X)) k 1 1)) ∧
    (∃ m j e : ℕ, 2 ≤ m ∧ qU Z M u = 2 ^ m ∧ BenderSub Z M (cenHull Z u) m j e) ∧
    (∀ x ∈ deltaSet Z M u, ∀ y ∈ deltaSet Z M u, x ≠ u → y ≠ u →
      ∃ g ∈ M ⊓ cenHull Z u, g⁻¹ * x * g = y) ∧
    ((centralizer ({u} : Set X) : Set X) =
      (cenHull Z u : Set X) * ((centralizer ({u} : Set X) ⊓ c.D : Subgroup X) : Set X))

@[expose] def Lemma126Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D ⊓ centralizer ({c.z} : Set X), orderOf u = 2 →
    (∀ x ∈ deltaSet Z M u, x = u ∨ IsConj (u * c.z) x) ∧
    (¬ Shears Z M u →
      zHull Z M ≤ centralizer ({u} : Set X) ∧
      (∀ u' ∈ deltaSet Z M u, u' ≠ u → centralizer ({u'} : Set X) ≤ M) ∧
      (∀ w : X, orderOf w = 2 → ¬ IsConj (u * c.z) w →
        ShultStronglyClosedTI.InvolutionCounting.thompsonPairCount u c.z w = 0) ∧
      ShultStronglyClosedTI.InvolutionCounting.thompsonPairCount u c.z (u * c.z) = 1)

@[expose] def Lemma127Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 →
    Shears Z M u ∧ ∀ u' z' : X, IsConj u u' → IsConj c.z z' → u' * z' = z' * u' → IsConj u (u' * z')

@[expose] def Lemma128Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 → ∀ m j e : ℕ,
    BenderSub Z M (cenHull Z u) m j e → qU Z M u = 2 ^ m →
    (omegaFix M ({u} : Set X)).ncard = (2 ^ m) ^ j + 1 ∧
    ((u ∈ centralizer (zHull Z M : Set X) ∧ m = n ∧
        (omega M).ncard = ((2 ^ m) ^ j + 1) * ((2 ^ m) ^ j * (2 ^ m - 1) + 1)) ∨
      (u ∉ centralizer (zHull Z M : Set X) ∧ n = 2 * m ∧
        (omega M).ncard * (2 ^ m + 1) =
          ((2 ^ m) ^ j + 1) * ((2 ^ m) ^ j * (2 ^ m - 1) + 2 ^ m + 1)))

@[expose] def Lemma129Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 →
    (∀ x ∈ zHull Z M, u * x = x * u) ∧ c.L ≤ cenHull Z u

@[expose] def Lemma1210Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i →
    (i = 1 ∧ (omega M).ncard = (2 ^ n) ^ 3 + 1 ∧
      (∀ u ∈ c.D, orderOf u = 2 → cenHull Z u = c.L ∧ (omegaFix M ({u} : Set X)).ncard = 2 ^ n + 1 ∧
        Nat.card ↥c.L + (omegaFix M ({u} : Set X)).ncard = (omega M).ncard) ∧
      (Nat.card X).factorization 2 = 3 * n + (Nat.card ↥c.D).factorization 2) ∨
    (i = 2 ∧ (omega M).ncard + (2 ^ n) ^ 4 = (2 ^ n) ^ 5 + (2 ^ n) ^ 3 + 1 ∧
      (∀ u ∈ c.D, orderOf u = 2 → cenHull Z u = c.L ∧
        (omegaFix M ({u} : Set X)).ncard = (2 ^ n) ^ 2 + 1 ∧
        Nat.card ↥c.L + (omegaFix M ({u} : Set X)).ncard = (omega M).ncard) ∧
      (Nat.card X).factorization 2 = 3 * n + (Nat.card ↥c.D).factorization 2) ∨
    (i = 1 ∧ (omega M).ncard + (2 ^ n) ^ 6 = (2 ^ n) ^ 7 + (2 ^ n) ^ 4 + 1 ∧
      (∀ u ∈ c.D, orderOf u = 2 → c.L < cenHull Z u ∧ (∃ e, BenderSub Z M (cenHull Z u) n 3 e) ∧
        (omegaFix M ({u} : Set X)).ncard = (2 ^ n) ^ 3 + 1) ∧
      (Nat.card X).factorization 2 = 4 * n + (Nat.card ↥c.D).factorization 2)

@[expose] def Lemma1211Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i →
    (∀ s : X, orderOf s = 2 → (IsCentralInvolution s ↔ s ∈ Z)) ∧
    (∀ S : Sylow 2 ↥M, ∀ x : X, x ∈ M → x * x = 1 →
      x ∈ ((S : Subgroup ↥M).map M.subtype) → (∀ y ∈ (S : Subgroup ↥M).map M.subtype, x * y = y * x) →
        x ∈ zHull Z M) ∧
    (∀ s : X, orderOf s = 2 → ¬ IsCentralInvolution s → ∃ u ∈ c.D, orderOf u = 2 ∧ IsConj s u)

@[expose] def Lemma1212Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ Y : Subgroup X, Odd (Nat.card Y) →
    (∃ s ∈ Z, s ∈ normalizer (Y : Set X) ∧ ∃ y ∈ Y, s * y ≠ y * s) →
    Open.pRank 2 (zHull Z (normalizer (Y : Set X))) = 1 ∧
      zHull Z (centralizer (Y : Set X)) = ⊥

@[expose] def Prop1213Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ x ∈ kGrp M c.t, x ≠ 1 →
    omegaFix M ({x} : Set X) = {M, conjugate M c.t}

@[expose] def Lemma1214Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 → cenHull Z u = c.L →
    ((∀ x ∈ c.L, x ≠ 1 → ∀ β ∈ omega M, β ∉ omegaFix M ({u} : Set X) → conjugate β x ≠ β) ∧
      (∀ β ∈ omega M, β ∉ omegaFix M ({u} : Set X) → ∀ γ ∈ omega M,
        γ ∉ omegaFix M ({u} : Set X) → ∃ x ∈ c.L, conjugate β x = γ)) ∧
    ∃ f : ↥(centralizer (c.L : Set X)) →* ↥c.L, Function.Injective f

structure Sec12Results : Prop where
  l122 : Lemma122Stmt Z M
  l123 : Lemma123Stmt Z M
  l124 : Lemma124Stmt Z M
  l126 : Lemma126Stmt Z M
  l127 : Lemma127Stmt Z M
  l128 : Lemma128Stmt Z M
  l129 : Lemma129Stmt Z M
  l1210 : Lemma1210Stmt Z M
  l1211 : Lemma1211Stmt Z M
  l1212 : Lemma1212Stmt Z M
  p1213 : Prop1213Stmt Z M
  l1214 : Lemma1214Stmt Z M

@[expose] def Prop131Stmt : Prop :=
  ∀ (c : Ctx12 Z M) (n i : ℕ), LData c n i → ∀ u ∈ c.D, orderOf u = 2 → cenHull Z u = c.L

@[expose] def Prop141Stmt : Prop := ∀ (c : Ctx12 Z M) (n : ℕ), LData c n 2 → False

@[expose] def Prop151Stmt : Prop := ∀ (c : Ctx12 Z M) (n : ℕ), LData c n 1 → False

@[expose] def Thm121Stmt : Prop :=
  ∀ t z : X, t ∈ Z → t ∉ M → z ∈ Z → z ∈ M → Even (Nat.card ↥(M ⊓ conjugate M t)) →
    lSubgroup M z t = ⊤

theorem thm121_of (h122 : Lemma122Stmt Z M) (h141 : Prop141Stmt Z M) (h151 : Prop151Stmt Z M) :
    Thm121Stmt Z M := by
  intro t z ht htM hz hzM hD
  by_contra hL
  let c : Ctx12 Z M := ⟨t, z, ht, htM, hz, hzM, hD, hL⟩
  obtain ⟨n, i, hdata⟩ := h122 c
  rcases hdata.hi with rfl | rfl
  · exact h151 c n hdata
  · exact h141 c n hdata

end Stmts

end CFSG.GH74.Uniqueness
