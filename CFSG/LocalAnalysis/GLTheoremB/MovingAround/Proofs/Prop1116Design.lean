module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped MatrixGroups Matrix

namespace Prop1116Design

section Heis

variable {n : ℕ} {F : Type} [Field F]

@[expose] def GUn (n Q : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin n) F) :=
  Subgroup.closure {A | ((A : Matrix (Fin n) (Fin n) F).map (· ^ Q))ᵀ * (A : Matrix (Fin n) (Fin n) F) = 1}

@[expose] def InducedByConj (H : Subgroup (GL (Fin n) F)) (g : GL (Fin n) F)
    (φ : MulAut (StatedProj H)) : Prop :=
  g ∈ Subgroup.normalizer (H : Set (GL (Fin n) F)) ∧
    ∀ A A' : ↥H, (A' : GL (Fin n) F) = g * (A : GL (Fin n) F) * g⁻¹ →
      φ (QuotientGroup.mk A) = QuotientGroup.mk A'

variable {Y : Type*} [Group Y]

@[expose] def ActsAsConj (H : Subgroup (GL (Fin n) F)) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H)
    (g : GL (Fin n) F) (b : MulAut Y) : Prop :=
  ∃ φ : MulAut (StatedProj H), InducedByConj H g φ ∧
    ∀ y : Y, θ (QuotientGroup.mk (b y)) = φ (θ (QuotientGroup.mk y))

@[expose] def IsImageOfNonabelianP (p : ℕ) (H Γ : Subgroup (GL (Fin n) F))
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (B : Subgroup (MulAut Y)) : Prop :=
  ∃ P : Subgroup (GL (Fin n) F), P ≤ Γ ∧ IsPGroup p ↥P ∧ (∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧
    (∀ b ∈ B, ∃ g ∈ P, ActsAsConj H θ g b) ∧ (∀ g ∈ P, ∃ b ∈ B, ActsAsConj H θ g b)

end Heis

@[expose] def HeisenbergImageL (p Q : ℕ) {Y : Type*} [Group Y] (B : Subgroup (MulAut Y)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL p F)),
    Nat.card F = Q ∧ IsImageOfNonabelianP p (StatedSL p F) ⊤ θ B

@[expose] def HeisenbergImageU (p Q : ℕ) {Y : Type*} [Group Y] (B : Subgroup (MulAut Y)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU p Q F)),
    Nat.card F = Q ^ 2 ∧ IsImageOfNonabelianP p (StatedSU p Q F) (GUn p Q F) θ B

@[expose] def IsLieOverField (Q : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((X ⧸ Subgroup.center X) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ idx.1.fieldOrder = Q

theorem characteristic_dvd_fieldOrder (d : TauCeti.LieTypeIndex) : d.characteristic ∣ d.fieldOrder := by
  cases d <;> simp
  all_goals exact Or.inl (Nat.pos_iff_ne_zero.mp (TauCeti.PrimePower.exponent_pos _))

theorem characteristic_eq_of_fieldOrder_eq {d : TauCeti.LieTypeIndex} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : d.fieldOrder = ℓ) : d.characteristic = ℓ := by
  have h1 : d.characteristic ∣ ℓ := h ▸ characteristic_dvd_fieldOrder d
  exact (Nat.prime_dvd_prime_iff_eq d.characteristic_prime hℓ).mp h1

theorem not_isCommutative_barQuot (X : Type) [Group X]
    (hq : CFSG.Open.IsQuasisimple X) : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : commutator X ≤ Subgroup.center X := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ _ g₂ _
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center X)]
    have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) g₁ g₂
    simp only [QuotientGroup.mk'_apply] at this
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)
  have htop : Subgroup.center X = ⊤ := top_le_iff.mp (hq.1 ▸ hc)
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  have hnt : Nontrivial (X ⧸ Subgroup.center X) := IsSimpleGroup.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) x
  apply hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, htop]
  exact Subgroup.mem_top y

theorem centralizer_ne_top {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) {e : G} (he : e ≠ 1) :
    Subgroup.centralizer ({e} : Set G) ≠ ⊤ := by
  intro htop
  have hcen : e ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({e} : Set G) := htop ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp this) e rfl).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact he (Subgroup.mem_bot.mp (h ▸ hcen))
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact (Subgroup.mem_center_iff.mp this) a

noncomputable def mulEquivQuotCenterOfEqBot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    X ≃* (X ⧸ Subgroup.center X) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center X))
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, h] at hx
      exact Subgroup.mem_bot.mp hx, QuotientGroup.mk'_surjective _⟩

theorem card_eq_card_quot_center {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    Nat.card X = Nat.card (X ⧸ Subgroup.center X) :=
  Nat.card_congr (mulEquivQuotCenterOfEqBot h).toEquiv

theorem prime_dvd_sixty {p : ℕ} (hp : p.Prime) (h : p ∣ 60) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have h1 : p ∣ 2 * 2 * 3 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h2))

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide

end Prop1116Design

open Prop1116Design

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop1116Iii (p q : ℕ) (E A K : Subgroup G) : Prop :=
  (∃ n : ℕ,
      (IsLpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n - 1 ∧
        HeisenbergImageL p (q ^ n) (autBar p (E ⊓ A) K)) ∨
      (IsUpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n + 1 ∧
        HeisenbergImageU p (q ^ n) (autBar p (E ⊓ A) K))) ∧
    E ⊓ A ≤ Subgroup.normalizer (K : Set G) ∧ Nat.card (E ⊓ A : Subgroup G) = p ^ 2 ∧
      ∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1

@[expose] def Prop1116Iv (p : ℕ) (A K : Subgroup G) : Prop :=
  p = 13 ∧ CFSG.Open.pRank 13 A = 3 ∧
    (IsLpType 3 (3 ^ 13) (barOf p K) ∨ IsLieOverField 3 (barOf p K))

@[expose] def Prop1116StrongStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G} (hK : GLAPComponent p (Cg a) K) {q : ℕ}
    (hq : q.Prime ∧ q ≠ 2 ∧ q ≠ p) (hchev : IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K))),
    K ≤ M ∨ (∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) ∨ Prop1116Iii p q E A K ∨ Prop1116Iv p A K

end Statements

namespace Prop1116Design

section Contexts

variable {G : Type} [Group G] [Finite G]

structure Cex1116 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K : Subgroup G) (q : ℕ) : Prop extends Sec11 G m p B M E A where
  ha : a ∈ A ∧ a ≠ 1
  hK : GLAPComponent p (Cg a) K
  hq : q.Prime ∧ q ≠ 2 ∧ q ≠ p
  hchev : IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K))
  notM : ¬ K ≤ M
  notD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
  notIii : ¬ Prop1116Iii p q E A K
  notIv : ¬ Prop1116Iv p A K

structure Prep1116 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K : Subgroup G) (q : ℕ) (e : G) (J0 J1 : Subgroup G) : Prop
    extends Cex1116 G m p B M E A a K q where
  he : e ∈ E ⊓ A ∧ e ≠ 1
  hJ0 : GLAPComponent p (Cg2 e a) J0
  hJ0K : J0 ≤ ⨆ x ∈ E ⊓ A, GLBConj x K
  hJ0M : ¬ J0 ≤ M
  hJ0chev : IsChevSimple q (barOf p J0 ⧸ Subgroup.center (barOf p J0))
  hJ1 : GLAPComponent p (Cg e) J1
  hJstar : Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1
  hcov : ¬ Covers p (Cg e) (M ⊓ Cg e) (Kx p J0 e)

section PrepFacts

variable {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ} {e : G} {J0 J1 : Subgroup G}

theorem Prep1116.hp (P : Prep1116 G m p B M E A a K q e J0 J1) : p.Prime := P.standing.prime

theorem sec11_isElemAbelian_A (h : Sec11 G m p B M E A) : IsElemAbelian p A :=
  h.pair.1.2.1.1.1.2.1

theorem elemAbelian_isPGroup {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) : IsPGroup p ↥E :=
  fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩

theorem sec11_isElemAbelian_E (h : Sec11 G m p B M E A) : IsElemAbelian p E :=
  h.pair.1.1.1.1.2.1

theorem not_coprime_card_of_pComponent {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : ¬ Nat.Coprime p (Nat.card J) := by
  intro hcop
  have hnt : Nontrivial (barOf p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial
      (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    refine eq_top_iff.2 (le_sSup ⟨inferInstance, ?_⟩)
    rwa [Subgroup.card_top]
  have hss : Subsingleton (barOf p J) := by
    unfold barOf
    rw [QuotientGroup.subsingleton_iff]
    exact htop
  exact (not_subsingleton_iff_nontrivial.2 hnt) hss

theorem Prep1116.hJ0p (P : Prep1116 G m p B M E A a K q e J0 J1) : p ∣ Nat.card (barOf p J0) := by
  have hp := P.hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (barOf p J0)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hO : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J0)) := CFSG.pPrimeCore_coprime_card (p := p)
  have hcard : Nat.card ↥J0 = Nat.card (barOf p J0) * Nat.card (GLAPPrimeCore p ↥J0) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥J0)
  exact not_coprime_card_of_pComponent hp P.hJ0 (by rw [hcard]; exact Nat.Coprime.mul_right hcop hO)

theorem kx_le_cg {p : ℕ} {J : Subgroup G} {x : G} (hJ : J ≤ Cg x) : Kx p J x ≤ Cg x := by
  have hL : GLAPLayer p (Cg x) ≤ Cg x := sSup_le fun L hL => (show GLAPComponent p (Cg x) L from hL).1
  refine iSup₂_le fun g hg => ?_
  intro y hy
  have hgC : g ∈ Cg x := hL hg
  have h1 : g * y * g⁻¹ ∈ Cg x := hJ (mem_gLBConj.1 hy)
  have h2 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [h2]
  exact (Cg x).mul_mem ((Cg x).mul_mem ((Cg x).inv_mem hgC) h1) hgC

theorem Prep1116.hJ0' (P : Prep1116 G m p B M E A a K q e J0 J1) :
    GLAPComponent p (GLAPLayer p (Kx p J0 e ⊓ Cg a)) J0 := by
  have hp := P.hp
  have hJ0T : J0 ≤ Cg2 e a := P.hJ0.1
  have hCe : Cg2 e a ≤ Cg e := Subgroup.centralizer_le (by intro x hx; simp at hx ⊢; exact Or.inl hx)
  have hCa : Cg2 e a ≤ Cg a := Subgroup.centralizer_le (by intro x hx; simp at hx ⊢; exact Or.inr hx)
  have hKx : Kx p J0 e ≤ Cg e := kx_le_cg (hJ0T.trans hCe)
  have hY : Kx p J0 e ⊓ Cg a ≤ Cg2 e a := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.1 (hKx hx.1) _ (Set.mem_singleton _)
    · exact Subgroup.mem_centralizer_iff.1 hx.2 _ (Set.mem_singleton _)
  have hJ0Kx : J0 ≤ Kx p J0 e :=
    le_iSup₂_of_le (1 : G) (GLAPLayer p (Cg e)).one_mem (le_of_eq (gLBConj_one J0).symm)
  have hJ0Y : J0 ≤ Kx p J0 e ⊓ Cg a := le_inf hJ0Kx (hJ0T.trans hCa)
  have hP1 : GLAPComponent p (Kx p J0 e ⊓ Cg a) J0 := glaPComponent_of_le hp P.hJ0 hJ0Y hY
  have hJL : J0 ≤ GLAPLayer p (Kx p J0 e ⊓ Cg a) :=
    le_sSup (s := {L | GLAPComponent p (Kx p J0 e ⊓ Cg a) L}) hP1
  have hLY : GLAPLayer p (Kx p J0 e ⊓ Cg a) ≤ Kx p J0 e ⊓ Cg a :=
    sSup_le fun L hL => (show GLAPComponent p (Kx p J0 e ⊓ Cg a) L from hL).1
  exact glaPComponent_of_le hp hP1 hJL hLY

theorem Prep1116.hgamma (P : Prep1116 G m p B M E A a K q e J0 J1) :
    ¬ barX p (Cg e) (Kx p J0 e) ≤ GLBCore p 2 (barX p (Cg e) E) := by
  intro hle
  have hp := P.hp
  have hEel : IsElemAbelian p E := sec11_isElemAbelian_E P.toSec11
  have hEp : IsPGroup p E := elemAbelian_isPGroup hEel
  have heE : e ∈ E := (Subgroup.mem_inf.1 P.he.1).1
  have hEC : E ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hEel heE hx
  have hEM : GLBCore p 2 E ≤ M := P.pair.1.1.2.clause_d
  have hO : GLAPPrimeCoreOf p (Cg e) ≤ M := le_trans le_sup_left (P.pair.1.1.2.clause_a e heE P.he.2)
  have hJ0Ce : J0 ≤ Cg e := P.hJ0.1.trans (Subgroup.centralizer_le
    (by intro x hx; simp at hx ⊢; exact Or.inl hx))
  have hKx : Kx p J0 e ≤ Cg e := kx_le_cg hJ0Ce
  have hKM : Kx p J0 e ≤ M :=
    le_of_barX_le_glbCore hp 2 hEp hEC hKx
      (fun E' hE' hr' => (le_sSup ⟨E', hE', hr', rfl⟩ :
        Subgroup.normalizer (E' : Set G) ≤ GLBCore p 2 E).trans hEM) hO hle
  exact P.hcov (Subgroup.map_mono (Subgroup.subgroupOf_mono _ (le_inf hKM hKx)))

end PrepFacts

theorem type_trichotomy {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ} {e : G}
    {J0 J1 : Subgroup G} (P : Prep1116 G m p B M E A a K q e J0 J1) :
    (∃ r : ℕ, IsChevSimple r (barOf p J1 ⧸ Subgroup.center (barOf p J1))) ∨
    (∃ n : ℕ, IsAltType n (barOf p J1 ⧸ Subgroup.center (barOf p J1))) ∨
    (∃ s : TauCeti.SporadicName, IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1))) := by
  have hS : GLStanding G m p := P.standing
  have hp : p.Prime := hS.prime
  have hCe : Subgroup.centralizer ({e} : Set G) ≠ ⊤ :=
    centralizer_ne_top hS.simple hS.nonabelian P.he.2
  have hJ1top : J1 ≠ ⊤ := fun h => hCe (top_le_iff.mp (h ▸ P.hJ1.1))
  have hq1 : CFSG.Open.IsQuasisimple (barOf p J1) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hJ1
  haveI : IsSimpleGroup (barOf p J1 ⧸ Subgroup.center (barOf p J1)) := hq1.2
  have hnonab := not_isCommutative_barQuot (barOf p J1) hq1
  let φ : ↥J1 →* (barOf p J1 ⧸ Subgroup.center (barOf p J1)) :=
    (QuotientGroup.mk' (Subgroup.center (barOf p J1))).comp
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J1))
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨i, ⟨f⟩⟩ := CFSG.KCore.KProperNonab.catalogue_of_surjective
    CFSG.Open.isCatalogGroup_isoInvariant hS.kProper J1 hJ1top hnonab φ hφ
  rcases i with ⟨p', hp'⟩ | ⟨n, hn⟩ | idx | s
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnonab
    apply hxy
    apply f.injective
    rw [map_mul, map_mul]
    have : ∀ x y : Multiplicative (ZMod p'), x * y = y * x := fun x y => mul_comm x y
    exact this _ _
  · exact Or.inr (Or.inl ⟨n, ⟨f⟩⟩)
  · exact Or.inl ⟨idx.1.characteristic, Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩⟩
  · exact Or.inr (Or.inr ⟨s, ⟨f⟩⟩)

end Contexts

end Prop1116Design

open Prop1116Design

section Pieces

@[expose] def Prop1116PrepStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
    (_ : Cex1116 G m p B M E A a K q),
    ∃ (e : G) (J0 J1 : Subgroup G), Prep1116 G m p B M E A a K q e J0 J1

@[expose] def Prop1116Chev2Statement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
    {e : G} {J0 J1 : Subgroup G} (_ : Prep1116 G m p B M E A a K q e J0 J1),
    IsChevSimple 2 (barOf p J0 ⧸ Subgroup.center (barOf p J0)) → q = 3

@[expose] def Prop1116ChevrStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
    {e : G} {J0 J1 : Subgroup G} (_ : Prep1116 G m p B M E A a K q e J0 J1),
    (IsChevSimple 2 (barOf p J0 ⧸ Subgroup.center (barOf p J0)) → q = 3) →
      ∀ r : ℕ, ¬ IsChevSimple r (barOf p J1 ⧸ Subgroup.center (barOf p J1))

@[expose] def Prop1116SporStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
    {e : G} {J0 J1 : Subgroup G} (_ : Prep1116 G m p B M E A a K q e J0 J1)
    (s : TauCeti.SporadicName), ¬ IsSporType s (barOf p J1 ⧸ Subgroup.center (barOf p J1))

@[expose] def Prop1116AltStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} {q : ℕ}
    {e : G} {J0 J1 : Subgroup G} (_ : Prep1116 G m p B M E A a K q e J0 J1)
    (n : ℕ), ¬ IsAltType n (barOf p J1 ⧸ Subgroup.center (barOf p J1))

end Pieces

theorem prop1116_of_strong (hS : Prop1116StrongStatement) : Prop1116Statement := by
  intro G _ _ m p B M E A h a ha ha1 K hK hq
  obtain ⟨idx, hidx, hP⟩ := hq
  have hqprime : idx.1.characteristic.Prime := idx.1.characteristic_prime
  have hchev : IsChevSimple idx.1.characteristic (barOf p K ⧸ Subgroup.center (barOf p K)) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, hidx⟩
  rcases hS h ha ha1 hK ⟨hqprime, hP.1, hP.2⟩ hchev with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨⟨n, hn⟩, hN, hc, hcen⟩ := h3
    refine Or.inr (Or.inr (Or.inl ⟨⟨idx.1.characteristic ^ n, ?_⟩, hN, hc, hcen, ⟨trivial⟩⟩))
    rcases hn with hn | hn
    · exact Or.inl ⟨hn.1, hn.2.1⟩
    · exact Or.inr ⟨hn.1, hn.2.1⟩
  · obtain ⟨hp13, hr, hK'⟩ := h4
    refine Or.inr (Or.inr (Or.inr ⟨hp13, hr, ?_⟩))
    rcases hK' with h | ⟨idx', hidx', hfo⟩
    · exact Or.inl h
    · exact Or.inr ⟨idx', hidx', characteristic_eq_of_fieldOrder_eq Nat.prime_three hfo⟩

theorem prop1116_strong_of_pieces (hprep : Prop1116PrepStatement) (hchev2 : Prop1116Chev2Statement)
    (hchevr : Prop1116ChevrStatement) (hspor : Prop1116SporStatement) (halt : Prop1116AltStatement) :
    Prop1116StrongStatement := by
  intro G _ _ m p B M E A h a ha ha1 K hK q hq hchev
  by_contra hcon
  rw [not_or, not_or, not_or] at hcon
  obtain ⟨hnotM, hnotD, hnotIii, hnotIv⟩ := hcon
  have hcex : Cex1116 G m p B M E A a K q :=
    { h with ha := ⟨ha, ha1⟩, hK := hK, hq := hq, hchev := hchev, notM := hnotM, notD := hnotD,
             notIii := hnotIii, notIv := hnotIv }
  obtain ⟨e, J0, J1, P⟩ := hprep hcex
  rcases type_trichotomy P with ⟨r, hr⟩ | ⟨n, hn⟩ | ⟨s, hs⟩
  · exact hchevr P (hchev2 P) r hr
  · exact halt P n hn
  · exact hspor P s hs

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
