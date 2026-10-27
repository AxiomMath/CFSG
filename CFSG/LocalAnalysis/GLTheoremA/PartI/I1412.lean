module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk)

@[expose] def DownLe (p j : ℕ) (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
    kLevel p (PSimple p I) ≤ j

@[expose] def KDLevel (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → DownLe p (kLevel p S) S

private noncomputable def i1412QuotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ)
    (e : S ≃* S') (X : Subgroup S) :
    (↥X ⧸ GLAPPrimeCore p ↥X) ≃*
      (↥(X.map e.toMonoidHom) ⧸ GLAPPrimeCore p ↥(X.map e.toMonoidHom)) :=
  QuotientGroup.congr _ _ (X.equivMapOfInjective e.toMonoidHom e.injective)
    (glaPPrimeCore_map_iso p (X.equivMapOfInjective e.toMonoidHom e.injective))

private theorem i1412_map_subgroupOf {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (X K : Subgroup S) :
    (K.subgroupOf X).map (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.1, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨w, hwX, hwy⟩ := y.2
    have hzw : z = w := e.injective (hzy.trans hwy.symm)
    have hzX : z ∈ X := by
      rw [hzw]
      exact hwX
    exact ⟨⟨z, hzX⟩, Subgroup.mem_subgroupOf.2 hz, Subtype.ext hzy⟩

private theorem i1412_barX_quotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ) (e : S ≃* S')
    (X K : Subgroup S) :
    ((K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
        (i1412QuotEquiv p e X).toMonoidHom =
      ((K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))) := by
  have hcomm : (i1412QuotEquiv p e X).toMonoidHom.comp
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))).comp
        (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, i1412_map_subgroupOf]

private theorem i1412_map_map_symm {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem i1412_map_symm_map {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S') : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem i1412_glaPComponent_map {S S' : Type} [Group S] [Group S'] {p : ℕ} (e : S ≃* S')
    {X L : Subgroup S} (h : GLAPComponent p X L) :
    GLAPComponent p (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  obtain ⟨hLX, hsn, hcomp, hmin⟩ := h
  refine ⟨Subgroup.map_mono hLX, CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e hsn,
    ?_, ?_⟩
  · have h1 : IsComponentOf
        (((L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
          (i1412QuotEquiv p e X).toMonoidHom)
        ((⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)).map (i1412QuotEquiv p e X).toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (i1412QuotEquiv p e X) hcomp
    have htop : Subgroup.map (i1412QuotEquiv p e X).toMonoidHom
        (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) = ⊤ :=
      Subgroup.map_top_of_surjective _ (i1412QuotEquiv p e X).surjective
    rw [htop, i1412_barX_quotEquiv] at h1
    exact h1
  · intro J' hJ' hJ'sn heq
    have hJe : (J'.map e.symm.toMonoidHom).map e.toMonoidHom = J' := i1412_map_symm_map e J'
    have hJL : J'.map e.symm.toMonoidHom < L := by
      refine lt_of_le_of_ne ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hly⟩ := hJ'.le hy
        rw [← hly]
        simpa using hl
      · intro hEq
        apply hJ'.ne
        rw [← hJe, hEq]
    have hJsn : IsSubnormal (J'.map e.symm.toMonoidHom) X := by
      have h2 : IsSubnormal (J'.map e.symm.toMonoidHom)
          ((X.map e.toMonoidHom).map e.symm.toMonoidHom) :=
        CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hJ'sn
      rwa [i1412_map_map_symm e X] at h2
    refine hmin _ hJL hJsn ?_
    apply Subgroup.map_injective (f := (i1412QuotEquiv p e X).toMonoidHom)
      (i1412QuotEquiv p e X).injective
    rw [i1412_barX_quotEquiv, i1412_barX_quotEquiv, hJe]
    exact heq

theorem downLe_of_mulEquiv {p j : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : DownLe p j S) : DownLe p j S' := by
  intro α' hα' I' hI'
  have hα : MulAut.congr e.symm α' ^ p = 1 := by
    rw [← map_pow, hα', map_one]
  have hfix : fixSubgroup (MulAut.congr e.symm α') =
      (fixSubgroup α').map e.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      have hx' : e.symm (α' (e x)) = x := hx
      refine ⟨e x, ?_, by simp⟩
      have h4 := congrArg e hx'
      exact mem_fixSubgroup.2 (by simpa using h4)
    · rintro ⟨y, hy, rfl⟩
      show e.symm (α' (e (e.symm y))) = e.symm y
      have hy' : α' y = y := hy
      simp [hy']
  have hI : GLAPComponent p (fixSubgroup (MulAut.congr e.symm α'))
      (I'.map e.symm.toMonoidHom) := by
    rw [hfix]
    exact i1412_glaPComponent_map e.symm hI'
  have hle := h _ hα _ hI
  have f : PSimple p I' ≃* PSimple p (I'.map e.symm.toMonoidHom) :=
    QuotientGroup.congr _ _ (i1412QuotEquiv p e.symm I') (Subgroup.map_center_eq _)
  rwa [← kLevel_congr p f] at hle

section Central

variable {A B : Type} [Group A] [Group B] [Finite A] {p : ℕ}

private theorem i1412_map_glaPPrimeCore_le (hp : p.Prime) (f : A →* B)
    (hf : Function.Surjective f) : (GLAPPrimeCore p A).map f ≤ GLAPPrimeCore p B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := Finite.of_surjective f hf
  exact le_sSup ⟨Subgroup.Normal.map inferInstance f hf,
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card⟩

private noncomputable def i1412PQuotMap (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    PQuot p J →* PQuot p (J.map π) :=
  QuotientGroup.map _ _ (π.subgroupMap J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact i1412_map_glaPPrimeCore_le hp _ (π.subgroupMap_surjective J))

private theorem i1412PQuotMap_surjective (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    Function.Surjective (i1412PQuotMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := π.subgroupMap_surjective J y
  exact ⟨QuotientGroup.mk x, rfl⟩

private noncomputable def i1412PSimpleMap (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    PSimple p J →* PSimple p (J.map π) :=
  QuotientGroup.map _ _ (i1412PQuotMap hp π J) (by
    rw [← Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_center_le_center (i1412PQuotMap_surjective hp π J))

private theorem i1412PSimpleMap_surjective (hp : p.Prime) (π : A →* B) (J : Subgroup A) :
    Function.Surjective (i1412PSimpleMap hp π J) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := i1412PQuotMap_surjective hp π J y
  exact ⟨QuotientGroup.mk x, rfl⟩

private theorem i1412_nonempty_pSimple_equiv_map [Finite B] (hp : p.Prime) (π : A →* B)
    {X : Subgroup A} {Y : Subgroup B} {J : Subgroup A} (hJ : GLAPComponent p X J)
    (hJπ : GLAPComponent p Y (J.map π)) :
    Nonempty (PSimple p J ≃* PSimple p (J.map π)) := by
  haveI : IsSimpleGroup (PSimple p J) := (isQuasisimple_pQuot_of_glaPComponent hp hJ).2
  haveI : IsSimpleGroup (PSimple p (J.map π)) := (isQuasisimple_pQuot_of_glaPComponent hp hJπ).2
  have hinj : Function.Injective (i1412PSimpleMap hp π J) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (i1412PSimpleMap hp π J).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple p (J.map π))
      obtain ⟨a', rfl⟩ := i1412PSimpleMap_surjective hp π J a
      obtain ⟨b', rfl⟩ := i1412PSimpleMap_surjective hp π J b
      apply hab
      have h1 : i1412PSimpleMap hp π J a' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : i1412PSimpleMap hp π J b' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      rw [h1, h2]
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, i1412PSimpleMap_surjective hp π J⟩⟩

end Central

private theorem i1412_isCatalogGroup_center_quotient {Y : Type*} [Group Y]
    (hY : CFSG.Open.IsKGroup Y) (hq : CFSG.Open.IsQuasisimple Y) :
    IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  refine hY.isCatalogGroup_of_surjective ⊤
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq)
    ((QuotientGroup.mk' (Subgroup.center Y)).comp (⊤ : Subgroup Y).subtype) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩

private theorem i1412_kLevel_le {p : ℕ} (hp : p.Prime) (h : KDLevel p) {Y : Type} [Group Y]
    [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hcat : IsCatalogGroup (Y ⧸ Subgroup.center Y))
    {β : MulAut Y} (hβ : β ^ p = 1) {J : Subgroup Y} (hJ : GLAPComponent p (fixSubgroup β) J) :
    kLevel p (PSimple p J) ≤ kLevel p (Y ⧸ Subgroup.center Y) := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  have hαp : centerQuotientHom Y β ^ p = 1 := by
    rw [← map_pow, hβ, map_one]
  have hαβ : ∀ k, π (β k) = centerQuotientHom Y β (π k) := fun k =>
    (onCenterQuotient_apply_mk β k).symm
  have hJ' := glaPComponent_map_fixSubgroup π hker β (centerQuotientHom Y β) hαβ hπs hp hJ
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hle := h (Y ⧸ Subgroup.center Y) ‹_› hnonab hcat (centerQuotientHom Y β) hαp (J.map π) hJ'
  obtain ⟨f⟩ := i1412_nonempty_pSimple_equiv_map hp π hJ hJ'
  rwa [← kLevel_congr p f] at hle

private theorem i1412_exists_conjAut {Q : Type} [Group Q] {K : Subgroup Q} {y : Q}
    (hyN : y ∈ Subgroup.normalizer (K : Set Q)) {n : ℕ} (hy : y ^ n = 1) :
    ∃ β : MulAut ↥K, β ^ n = 1 ∧
      fixSubgroup β = (K ⊓ Subgroup.centralizer ({y} : Set Q)).subgroupOf K := by
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut ↥K, β = Subgroup.normalizerMonoidHom K ⟨y, hyN⟩ :=
    ⟨_, rfl⟩
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Q) = y * (k : Q) * y⁻¹ := by
    intro k
    rw [hβdef]
    rfl
  refine ⟨β, ?_, ?_⟩
  · have h3 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set Q)) ^ n = 1 := Subtype.ext hy
    rw [hβdef, ← map_pow, h3, map_one]
  · ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Q) = (k : Q) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm

theorem i1412UsedAt_of_kdLevel {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : KDLevel p) : I1412UsedAt G p := by
  intro X K y hX hK hyp hyN J hJ
  have hy : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, -, hcomp⟩ := exists_pQuot_transfer hp hy hyN
  obtain ⟨J', hJ', ⟨eJ⟩⟩ := hcomp J hJ
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hq
  have eS : (↥K' ⧸ Subgroup.center ↥K') ≃* PSimple p K :=
    QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  have hcatK : IsCatalogGroup (PSimple p K) :=
    i1412_isCatalogGroup_center_quotient ((hX.of_le hK.1).quotient _) hq
  have hcat' : IsCatalogGroup (↥K' ⧸ Subgroup.center ↥K') := by
    obtain ⟨i, ⟨f⟩⟩ := hcatK
    exact ⟨i, ⟨eS.trans f⟩⟩
  obtain ⟨β, hβp, hβfix⟩ := i1412_exists_conjAut hnorm (hpow p hyp)
  have hJ₁ : GLAPComponent p (fixSubgroup β) (J'.subgroupOf K') := by
    rw [hβfix]
    exact glaPComponent_subgroupOf hp inf_le_left hJ'
  have hle := i1412_kLevel_le hp h hq' hcat' hβp hJ₁
  obtain ⟨f₁⟩ := nonempty_pQuot_equiv_subgroupOf p (hJ'.1.trans inf_le_left)
  have g : PQuot p (J'.subgroupOf K') ≃* PQuot p J := f₁.trans eJ.symm
  have fJ : PSimple p (J'.subgroupOf K') ≃* PSimple p J :=
    QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)
  rwa [kLevel_congr p fJ, kLevel_congr p eS] at hle

end CFSG.LocalAnalysis.GLTheoremA
