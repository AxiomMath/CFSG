module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShClaim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBaseW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUBlockInnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldType
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryProjConj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ElemAbelianPlaneAction
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriD4Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.RankThree.PartOne.CTP.StdSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.T171Sh CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz
  CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix
open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

private theorem uni_catalogue_facts {G : Type} [Group G] {p N m : ℕ} {L : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs (PSimple p L) (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .twistedA (N - 1) q ∧ q.exponent = m ∧ I171.I171LieShape p i)) :
    p ∣ N ∧ p ∣ 2 ^ m + 1 ∧ 3 ≤ N ∧ (N, 2 ^ m) ≠ (3, 2) ∧
      catalogIs (PSimple p L) (onLie fun i => ∃ q : TauCeti.PrimePower,
        i = .twistedA (N - 1) q ∧ q.card = 2 ^ m) := by
  obtain ⟨i, hv, hi, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  obtain ⟨q, rfl, hqexp, hshape⟩ := hi
  obtain ⟨hqp, hpgcd⟩ := hshape
  have hcardq : q.card = 2 ^ m := by
    rw [TauCeti.PrimePower.card_def, hqp, hqexp]
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h
    · rw [h0] at hpgcd
      simp only [Nat.zero_sub, Nat.zero_add, Nat.gcd_one_left] at hpgcd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hpgcd
      have := hp.two_le
      omega
    · exact h
  have hgcd : p ∣ Nat.gcd N (2 ^ m + 1) := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ N), hcardq] at hpgcd
  have hpN : p ∣ N := (Nat.dvd_gcd_iff.mp hgcd).1
  have hpq : p ∣ 2 ^ m + 1 := (Nat.dvd_gcd_iff.mp hgcd).2
  have h3N : 3 ≤ N := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact le_trans hp3 (Nat.le_of_dvd hNpos hpN)
  have hNq : (N, 2 ^ m) ≠ (3, 2) := by
    intro heq
    have hN3 : N = 3 := congrArg Prod.fst heq
    have hq2 : 2 ^ m = 2 := congrArg Prod.snd heq
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have h3q : 3 ≤ q.card := hrange.2 (by omega)
    rw [hcardq, hq2] at h3q
    omega
  exact ⟨hpN, hpq, h3N, hNq,
    ⟨.lie ⟨.twistedA (N - 1) q, hv⟩, ⟨q, rfl, hcardq⟩, ⟨e⟩⟩⟩

private theorem uni_field_type_data {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    {A₀ : GL (Fin N) K} {c₀ lam : Kˣ}
    (hA₀ : A₀ ∈ primeFormUnitary hUF (idGram K N))
    (hA₀p : A₀ ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (c₀ ^ p * lam))
    (hcube : ¬ ∃ x : Kˣ, x ^ p = lam)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hcompT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩))) :
    p ∣ N ∧ 2 ≤ N / p ∧
      (∀ T' : Subgroup (primeFormP hUF (idGram K N)),
        CFSG.Open.IsComponentOf T'
          (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩)) → T' = T) ∧
      ((N / p = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = 2 ^ (m * p) ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (3 ≤ N / p ∧ ∃ (E : Type) (_ : Field E) (_ : Fintype E),
          Fintype.card E = (2 ^ (m * p)) ^ 2 ∧
          ∃ g : ↥(StatedSU (N / p) (2 ^ (m * p)) E) →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center ↥(StatedSU (N / p) (2 ^ (m * p)) E))) := by
  have hc₁ : ∀ y : K, y ^ p ≠ ((c₀ ^ p * lam : Kˣ) : K) := by
    intro y hy
    have hc0 : (c₀ : K) ≠ 0 := Units.ne_zero c₀
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [zero_pow hpre.prime.pos.ne'] at hy
      exact (Units.ne_zero (c₀ ^ p * lam)) hy.symm
    · refine hcube ⟨Units.mk0 y hy0 / c₀, ?_⟩
      have hu : (Units.mk0 y hy0 : Kˣ) ^ p = c₀ ^ p * lam := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul,
          Units.val_pow_eq_pow_val]
        exact hy
      rw [div_pow, hu]
      exact mul_div_cancel_left (c₀ ^ p) lam
  exact unitary_fieldType_component (p := p) (ℓ := 2) (f := m) (n := N) hpre.prime hUF hpre.odd
    ⟨A₀, hA₀⟩ hA₀p hc₁ hcompT

private theorem uni_field_layer {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    {A₀ : GL (Fin N) K}
    (hA₀ : A₀ ∈ primeFormUnitary hUF (idGram K N))
    (e : LargeEvenProj (unitarySU 2 m K N) ≃* primeFormP hUF (idGram K N))
    (huniq : ∀ T' : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf T'
        (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩)) →
        T' = ((J.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom)
    {φ : MulAut (LargeEvenProj (unitarySU 2 m K N))}
    (hind : LargeEvenInduces θ (conjRel d) φ)
    (hfix : fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩) =
      (fixSubgroup φ).map e.toMonoidHom)
    (hpN : p ∣ N) (hNp2 : 2 ≤ N / p)
    (hcompJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G))) :
    (2 * p ≤ N ∧ GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) := by
  constructor
  · have h1 : p * 2 ≤ p * (N / p) := Nat.mul_le_mul_left p hNp2
    rw [Nat.mul_div_cancel' hpN] at h1
    omega
  · refine glaLayer_eq_of_forall_map_eq inf_le_left θ hcompJ ?_
    intro K' hK'
    have hK'Ass : CFSG.Assembly.IsComponentOf K'
        (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
      (CFSG.Assembly.isComponentOf_iff_open).2 hK'
    have hdesc := componentDescent_component θ (hpre.norm hpre.d_mem) hind hK'Ass
    have hdescO : CFSG.Open.IsComponentOf
        ((K'.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ) :=
      (CFSG.Assembly.isComponentOf_iff_open).1 hdesc
    have hK'e : CFSG.Open.IsComponentOf
        (((K'.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom)
        (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩)) := by
      rw [hfix]
      exact (Y10F.isComponentOf_map_iff e.injective).2 hdescO
    exact Subgroup.map_injective e.injective (huniq _ hK'e)

private theorem uni_centralQuotient_equiv {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    {φ : MulAut (LargeEvenProj (unitarySU 2 m K N))}
    (hJbar : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hcompJbar : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T)
    {S : Type} [Group S] (g : S →* ↥T) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center S) [IsSimpleGroup (S ⧸ Subgroup.center S)] :
    Nonempty (PSimple p J ≃* S ⧸ Subgroup.center S) := by
  let g' : S →* ↥((J.subgroupOf L).map (piCenterQuot θ)) :=
    eJ.symm.toMonoidHom.comp g
  have hg' : Function.Surjective g' := eJ.symm.surjective.comp hg
  have hgk' : g'.ker ≤ Subgroup.center S := by
    rw [show g' = eJ.symm.toMonoidHom.comp g from rfl,
      MonoidHom.ker_comp_of_injective g eJ.symm.toMonoidHom eJ.symm.injective]
    exact hgk
  exact nonempty_pSimple_equiv_of_central_surjective (p := p) hpre.prime inf_le_left θ hpre.pcomp
    hJbar hcompJbar g' hg' hgk' inferInstance

private theorem uni_catalogue_linear {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    {φ : MulAut (LargeEvenProj (unitarySU 2 m K N))}
    (hJbar : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hcompJbar : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T)
    {F : Type} [Field F] [Fintype F] (hNp2 : N / p = 2)
    (hcardF : Fintype.card F = 2 ^ (m * p))
    {g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      q.p = 2 ∧ q.exponent = m * p ∧
      ((N / p = 2 ∧ i = .A 1 q) ∨ (3 ≤ N / p ∧ i = .twistedA (N / p - 1) q))) := by
  have hmp3 : 3 ≤ m * p :=
    (hpre.prime.odd_iff.1 (hpre.prime.odd_of_ne_two hpre.odd)).trans
      (Nat.le_mul_of_pos_left p hUF.one_le)
  have hcardF' : Nat.card F = 2 ^ (m * p) := by
    rw [Nat.card_eq_fintype_card, hcardF]
  let q : TauCeti.PrimePower :=
    ⟨2, m * p, Nat.prime_two, Nat.mul_pos hUF.one_le hpre.prime.pos⟩
  have hqcard : Nat.card F = q.card := by
    rw [hcardF', TauCeti.PrimePower.card_def]
  have hqcard8 : 8 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    calc 2 ^ (m * p) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hmp3
      _ = 8 := by norm_num
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid :=
    CFSG.LocalAnalysis.GLTheoremA.l2c_valid_A1 (n := m * p) hmp3
  have h4F : 4 ≤ Nat.card F := by
    rw [hcardF']
    calc 2 ^ (m * p) ≥ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num : 2 ≤ 3) hmp3)
      _ = 4 := by norm_num
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4F
  obtain ⟨ePJ⟩ := uni_centralQuotient_equiv hUF hpre θ hJbar hcompJbar eJ g hg hgk
  let eS : Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≃*
      LinearFlag.projectiveSL 2 F :=
    QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 2 F).symm
  obtain ⟨eCat⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
      (n := 1) q hv hqcard
  exact ⟨.lie ⟨.A 1 q, hv⟩, ⟨q, rfl, rfl, Or.inl ⟨hNp2, rfl⟩⟩,
    ⟨ePJ.trans (eS.trans eCat)⟩⟩

private theorem uni_catalogue_unitary {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    {φ : MulAut (LargeEvenProj (unitarySU 2 m K N))}
    (hJbar : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hcompJbar : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T)
    {E : Type} [Field E] [Fintype E] (h3Np : 3 ≤ N / p)
    (hcardE : Fintype.card E = (2 ^ (m * p)) ^ 2)
    {g : ↥(StatedSU (N / p) (2 ^ (m * p)) E) →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU (N / p) (2 ^ (m * p)) E)) :
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      q.p = 2 ∧ q.exponent = m * p ∧
      ((N / p = 2 ∧ i = .A 1 q) ∨ (3 ≤ N / p ∧ i = .twistedA (N / p - 1) q))) := by
  have hmp3 : 3 ≤ m * p :=
    (hpre.prime.odd_iff.1 (hpre.prime.odd_of_ne_two hpre.odd)).trans
      (Nat.le_mul_of_pos_left p hUF.one_le)
  have hcardE' : Fintype.card E = (2 ^ (m * p)) ^ 2 := hcardE
  have hNat : Nat.card E = (2 ^ (m * p)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hcardE']
  have hne : (N / p, 2 ^ (m * p)) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ (m * p) = 2 := congrArg Prod.snd h
    have h8 : 8 ≤ 2 ^ (m * p) := by
      calc 2 ^ (m * p) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hmp3
        _ = 8 := by norm_num
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := E) (p := 2) (f := m * p) (n := N / p) hNat h3Np hne
  haveI : IsSimpleGroup (↥(StatedSU (N / p) (2 ^ (m * p)) E) ⧸
      Subgroup.center ↥(StatedSU (N / p) (2 ^ (m * p)) E)) := hQ.1.2.1
  obtain ⟨ePJ⟩ := uni_centralQuotient_equiv hUF hpre θ hJbar hcompJbar eJ g hg hgk
  obtain ⟨q', hv', hq'p, hq'card, ⟨eCat⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := N / p) (q := 2 ^ (m * p)) hcardE' h3Np hne
  have hq'card' : q'.card = 2 ^ (m * p) := hq'card
  have hq'p2 : q'.p = 2 := by
    have hdvd : q'.p ∣ 2 ^ (m * p) := by
      rw [← hq'card', TauCeti.PrimePower.card_def]
      exact dvd_pow_self q'.p q'.exponent_pos.ne'
    have hdvd2 : q'.p ∣ 2 := q'.prime_p.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact absurd h q'.prime_p.ne_one
    · exact h
  have hq'exp : q'.exponent = m * p := by
    have h1 : q'.p ^ q'.exponent = 2 ^ (m * p) := by
      rw [← TauCeti.PrimePower.card_def, hq'card']
    rw [hq'p2] at h1
    exact Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2) h1
  exact ⟨.lie ⟨.twistedA (N / p - 1) q', hv'⟩,
    ⟨q', hq'p2, hq'exp, Or.inr ⟨h3Np, rfl⟩⟩, ⟨ePJ.trans eCat⟩⟩

private theorem uni_catalogue_field {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 m K) (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    {φ : MulAut (LargeEvenProj (unitarySU 2 m K N))}
    (hJbar : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hcompJbar : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T)
    (hcase : (N / p = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = 2 ^ (m * p) ∧
        ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
          g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (3 ≤ N / p ∧ ∃ (E : Type) (_ : Field E) (_ : Fintype E),
        Fintype.card E = (2 ^ (m * p)) ^ 2 ∧
        ∃ g : ↥(StatedSU (N / p) (2 ^ (m * p)) E) →* ↥T, Function.Surjective g ∧
          g.ker ≤ Subgroup.center ↥(StatedSU (N / p) (2 ^ (m * p)) E))) :
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      q.p = 2 ∧ q.exponent = m * p ∧
      ((N / p = 2 ∧ i = .A 1 q) ∨ (3 ≤ N / p ∧ i = .twistedA (N / p - 1) q))) := by
  rcases hcase with
      ⟨hNp2, F, hF, hFt, hcardF, ⟨g, hg, hgk⟩⟩ |
      ⟨h3Np, E, hE, hEt, hcardE, ⟨g, hg, hgk⟩⟩
  · letI := hF
    letI := hFt
    exact uni_catalogue_linear hUF hpre θ hJbar hcompJbar eJ hNp2 hcardF hg hgk
  · letI := hE
    letI := hEt
    exact uni_catalogue_unitary hUF hpre θ hJbar hcompJbar eJ h3Np hcardE hg hgk

private theorem uni_typeOne_false {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hT : T158UniTypeOneW) (hMI : T158MISetup) (hUF : UnitaryFieldData 2 m K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ m + 1) (hN : 3 ≤ N) (hNq : (N, 2 ^ m) ≠ (3, 2))
    (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 m K N))
    (hact : ∀ a ∈ (Subgroup.zpowers d ⊔ Subgroup.zpowers b),
      ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (unitarySU 2 m K N)) (LargeEvenGUSet (Fin N) K (2 ^ m)),
        LargeEvenInduces θ (conjRel a) φ)
    (hS : LargeEvenGUSet (Fin N) K (2 ^ m) ⊆ Subgroup.normalizer
      (unitarySU 2 m K N : Set (GL (Fin N) K)))
    (hw : T171Sh.WSetup p L J (Subgroup.zpowers d ⊔ Subgroup.zpowers b) d b)
    (hcompJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (M : LiftMap (L := L) (A := Subgroup.zpowers d ⊔ Subgroup.zpowers b)
      (S := LargeEvenGUSet (Fin N) K (2 ^ m)) θ hact hS)
    (lam : Kˣ) (hlam : (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam)
    (hcube : ∃ x : Kˣ, x ^ p = lam) : False := by
  obtain ⟨x, hx⟩ := hcube
  exact hT G p N m L J (Subgroup.zpowers d ⊔ Subgroup.zpowers b) d b K hUF hp hpq hN hNq
    θ hact hS hw hcompJ (hpre.not_innDiagOn_of_mi hMI) M ⟨x, by rw [hlam, hx]⟩

theorem t158CompUni_of (hUM : T171Sh.UniMarking) (hMI : T158MISetup)
    (hT : T158UniTypeOneW) : T158CompUni := by
  intro G _ _ p L J A d b N m hpre hcat
  obtain ⟨hpN, hpq, hN, hNq, hcatUni⟩ := uni_catalogue_facts hpre.prime hpre.odd hcat
  have hw : T171Sh.WSetup p L J (Subgroup.zpowers d ⊔ Subgroup.zpowers b) d b :=
    hpre.toWSetup
  obtain ⟨K, hK, hKfin, hUF, θ, hact⟩ :=
    hUM G p L J (Subgroup.zpowers d ⊔ Subgroup.zpowers b) d b N m hw hcatUni
  letI := hK
  letI := hKfin
  have hS : LargeEvenGUSet (Fin N) K (2 ^ m) ⊆ Subgroup.normalizer
      (unitarySU 2 m K N : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF
  obtain ⟨M⟩ := LiftMap.exists (L := L) (A := Subgroup.zpowers d ⊔ Subgroup.zpowers b)
    (S := LargeEvenGUSet (Fin N) K (2 ^ m)) θ hact hS
  have hDp := M.dpow_mem_scalars_of_wSetup hw
    (uniKernelScalar (K := K) hUF hN hNq hpre.prime hpq)
  obtain ⟨lam, hlam⟩ := hDp
  have hlam' : (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam := hlam.symm
  obtain ⟨c₀, hc₀⟩ := exists_scalar_mul_primeFormUnitary (a := N) (n := m) hUF
    (M.mem ⟨d, hw.d_mem⟩)
  let A₀ : GL (Fin N) K :=
    GeneralLinearGroup.scalar (Fin N) c₀ * M.mat ⟨d, hw.d_mem⟩
  have hA₀ : A₀ ∈ primeFormUnitary hUF (idGram K N) := hc₀
  have hA₀p : A₀ ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (c₀ ^ p * lam) := by
    rw [show A₀ = GeneralLinearGroup.scalar (Fin N) c₀ * M.mat ⟨d, hw.d_mem⟩ from rfl,
      Commute.mul_pow (commute_scalar c₀ (M.mat ⟨d, hw.d_mem⟩)).symm p,
      ← map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c₀ p, ← hlam,
      ← map_mul (Matrix.GeneralLinearGroup.scalar (Fin N))]
  let e : LargeEvenProj (unitarySU 2 m K N) ≃*
      primeFormP hUF (idGram K N) :=
    statedProjEquivPrimeFormOne hUF (by omega)
  let φ : MulAut (LargeEvenProj (unitarySU 2 m K N)) :=
    TableB.projConj (unitarySU 2 m K N)
      ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩
  have hind : LargeEvenInduces θ (conjRel d) φ := M.ind ⟨d, hw.d_mem⟩
  have hcongr : MulAut.congr e φ =
      primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩ :=
    congr_statedProjEquivPrimeFormOne_projConj (a := N) (n := m) hUF (by omega)
      (M.mat ⟨d, hw.d_mem⟩) (hS (M.mem ⟨d, hw.d_mem⟩)) c₀ hA₀
  have hfix : fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩) =
      (fixSubgroup φ).map e.toMonoidHom := by
    rw [← hcongr]
    exact fixSubgroup_congr e φ
  have hJbar : GLAPComponent p (fixSubgroup φ)
      ((J.subgroupOf L).map (piCenterQuot θ)) :=
    glaPComponent_fixSubgroup_map_piCenterQuot hpre.prime (hpre.norm hpre.d_mem) hpre.pcomp θ hind
  have hJbar_e : GLAPComponent p
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩))
      (((J.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom) := by
    have h1 : GLAPComponent p ((fixSubgroup φ).map e.toMonoidHom)
        (((J.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom) :=
      (Y10F.glaPComponent_map_iff hpre.prime e.injective).2 hJbar
    rwa [← hfix] at h1
  have hperf : PerfectInLayer (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩) :=
    perfectInLayer_primeFormConjHom hUF hpre.prime hpre.odd ⟨A₀, hA₀⟩ hA₀p
  have hcompJbar_e : CFSG.Open.IsComponentOf
      (((J.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom)
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨A₀, hA₀⟩)) :=
    (glaPComponent_isComponent_of_le_layer hJbar_e
      (hperf _ hJbar_e.1 (glaPComponent_perfect hJbar_e))).1
  have hcompJbar : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ) :=
    (Y10F.isComponentOf_map_iff e.injective).1 (hfix ▸ hcompJbar_e)
  have hcompJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    isComponentOf_of_isComponentOf_map_piCenterQuot inf_le_left θ hpre.pcomp hcompJbar
  by_cases hcube : ∃ x : Kˣ, x ^ p = lam
  · exact (uni_typeOne_false hT hMI hUF hpre.prime hpq hN hNq hpre θ hact hS hw hcompJ
      M lam hlam' hcube).elim
  · have hFT := uni_field_type_data hUF hpre hA₀ hA₀p hcube hcompJbar_e
    have hlayer := uni_field_layer hUF hpre θ hA₀ e hFT.2.2.1 hind hfix hFT.1 hFT.2.1 hcompJ
    let eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃*
        ↥(((J.subgroupOf L).map (piCenterQuot θ)).map e.toMonoidHom) :=
      Subgroup.equivMapOfInjective ((J.subgroupOf L).map (piCenterQuot θ))
        e.toMonoidHom e.injective
    have hcat := uni_catalogue_field hUF hpre θ hJbar hcompJbar eJ hFT.2.2.2
    exact ⟨⟨hcompJ, hlayer.2⟩, hlayer.1, hcat⟩

end CFSG.LocalAnalysis.GLTheoremA.T158

end
