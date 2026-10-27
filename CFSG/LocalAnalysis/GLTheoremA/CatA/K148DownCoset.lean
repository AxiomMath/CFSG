module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2C
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

@[expose] def k148Rho {J I : Subgroup G} (hIJ : I ≤ J) : ↥I →* PQuot 3 J :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp (Subgroup.inclusion hIJ)

theorem k148_ker_le {J I : Subgroup G} (hIJ : I ≤ J) :
    (k148Rho hIJ).ker ≤ GLAPPrimeCore 3 ↥I := by
  intro x hx
  have hO : Subgroup.inclusion hIJ x ∈ GLAPPrimeCore 3 ↥J := by
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hIJ x) : PQuot 3 J) = 1 := hx
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcop : Nat.Coprime 3 (Nat.card ((GLAPPrimeCore 3 ↥J).comap (Subgroup.inclusion hIJ))) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hIJ))
      (CFSG.coprime_card_pPrimeCore 3 ↥J)
  have hle : (GLAPPrimeCore 3 ↥J).comap (Subgroup.inclusion hIJ) ≤ GLAPPrimeCore 3 ↥I :=
    le_sSup ⟨inferInstance, hcop⟩
  exact hle (Subgroup.mem_comap.2 hO)

theorem k148_mk_mem_fix {J Y : Subgroup G} (hYJ : Y ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hdY : ∀ y ∈ Y, d * y = y * d) (y : ↥Y) :
    (QuotientGroup.mk (Subgroup.inclusion hYJ y) : PQuot 3 J) ∈ lemma102_fixSub 3 hdN := by
  show lemma102_conjQ 3 hdN (QuotientGroup.mk (Subgroup.inclusion hYJ y)) =
    QuotientGroup.mk (Subgroup.inclusion hYJ y)
  rw [lemma102_conjQ_mk]
  congr 1
  apply Subtype.ext
  rw [lemma102_conjHomL_val]
  have hc : d * ((Subgroup.inclusion hYJ y : ↥J) : G) = ((Subgroup.inclusion hYJ y : ↥J) : G) * d :=
    hdY _ y.2
  calc d⁻¹ * ((Subgroup.inclusion hYJ y : ↥J) : G) * d
      = d⁻¹ * (((Subgroup.inclusion hYJ y : ↥J) : G) * d) := by group
    _ = d⁻¹ * (d * ((Subgroup.inclusion hYJ y : ↥J) : G)) := by rw [hc]
    _ = ((Subgroup.inclusion hYJ y : ↥J) : G) := by group

theorem k148_range_le_fix {J I : Subgroup G} (hIJ : I ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hdI : ∀ i ∈ I, d * i = i * d) :
    (k148Rho hIJ).range ≤ lemma102_fixSub 3 hdN := by
  rintro _ ⟨x, rfl⟩
  exact k148_mk_mem_fix hIJ hdN hdI x

theorem k148_fix_lift {J : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hd3 : d ^ 3 = 1)
    (y : PQuot 3 J) (hy : lemma102_conjQ 3 hdN y = y) :
    ∃ x : ↥J, (QuotientGroup.mk x : PQuot 3 J) = y ∧ d * (x : G) = (x : G) * d := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have hmem : ((a : G))⁻¹ * (d⁻¹ * (a : G) * d) ∈ GLAPPrimeCoreOf 3 J := by
    have h1 : lemma102_conjQ 3 hdN (QuotientGroup.mk a) = QuotientGroup.mk a := hy
    rw [lemma102_conjQ_mk] at h1
    have h3 : (a⁻¹ * lemma102_conjHomL hdN a : ↥J) ∈ GLAPPrimeCore 3 ↥J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, inv_mul_cancel]
    have h4 := (lemma102_mem_glaPPrimeCore_iff (p := 3) (H := J)
      (x := ((a⁻¹ * lemma102_conjHomL hdN a : ↥J) : G)) (a⁻¹ * lemma102_conjHomL hdN a).2).1 h3
    rw [Subgroup.coe_mul, Subgroup.coe_inv, lemma102_conjHomL_val] at h4
    exact h4
  have hT : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 J) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf Nat.prime_three J) h
  have hg3 : (d⁻¹) ^ 3 = 1 := by rw [inv_pow, hd3, inv_one]
  have hgT : d⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 J : Set G) :=
    Subgroup.inv_mem _ (normalizer_le_normalizer_glaPPrimeCoreOf 3 J hdN)
  have haT : (a : G) ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 J : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 J a.2
  have hc : (a : G)⁻¹ * (d⁻¹ * (a : G) * (d⁻¹)⁻¹) ∈ GLAPPrimeCoreOf 3 J := by
    rw [inv_inv]
    exact hmem
  obtain ⟨n, hn, hfix⟩ := td4g2_fix_lift (GLAPPrimeCoreOf 3 J) hT hg3 hgT haT hc
  rw [inv_inv] at hfix
  have hnJ : n ∈ J := lemma102_core_le (p := 3) J hn
  have hy'J : (a : G) * n ∈ J := J.mul_mem a.2 hnJ
  have hcomm : d * ((a : G) * n) = ((a : G) * n) * d := by
    calc d * ((a : G) * n) = d * (d⁻¹ * ((a : G) * n) * d) := by rw [hfix]
      _ = ((a : G) * n) * d := by group
  refine ⟨⟨(a : G) * n, hy'J⟩, ?_, hcomm⟩
  rw [QuotientGroup.eq]
  have hnO : (⟨n, hnJ⟩ : ↥J) ∈ GLAPPrimeCore 3 ↥J :=
    (lemma102_mem_glaPPrimeCore_iff (p := 3) (H := J) (x := n) hnJ).2 hn
  have heq : (⟨(a : G) * n, hy'J⟩ : ↥J)⁻¹ * a = (⟨n, hnJ⟩ : ↥J)⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
  rw [heq]
  exact Subgroup.inv_mem _ hnO

@[expose] def k148Psi {J X : Subgroup G} (hXJ : X ≤ J) : ↥X →* PQuot 3 J :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp (Subgroup.inclusion hXJ)

theorem k148Psi_apply {J X : Subgroup G} (hXJ : X ≤ J) (x : ↥X) :
    k148Psi hXJ x = QuotientGroup.mk (Subgroup.inclusion hXJ x) := rfl

@[expose] def k148Phi {J I : Subgroup G} (hIJ : I ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hdI : ∀ i ∈ I, d * i = i * d) :
    ↥I →* ↥(lemma102_fixSub 3 hdN) where
  toFun x := ⟨k148Psi hIJ x, k148_range_le_fix hIJ hdN hdI ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (k148Psi hIJ))
  map_mul' x y := Subtype.ext (map_mul (k148Psi hIJ) x y)

theorem k148Phi_val {J I : Subgroup G} (hIJ : I ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hdI : ∀ i ∈ I, d * i = i * d) (i : ↥I) :
    ((k148Phi hIJ hdN hdI i : ↥(lemma102_fixSub 3 hdN)) : PQuot 3 J) = k148Psi hIJ i := by
  unfold k148Phi
  rfl

@[expose] def k148PhiX {J : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (J : Set G)) :
    ↥(J ⊓ Subgroup.centralizer ({d} : Set G)) →* ↥(lemma102_fixSub 3 hdN) where
  toFun x := ⟨k148Psi inf_le_left x,
    k148_mk_mem_fix inf_le_left hdN (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm) x⟩
  map_one' := Subtype.ext (map_one (k148Psi inf_le_left))
  map_mul' x y := Subtype.ext (map_mul (k148Psi inf_le_left) x y)

theorem k148PhiX_val {J : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (J : Set G))
    (x : ↥(J ⊓ Subgroup.centralizer ({d} : Set G))) :
    ((k148PhiX hdN x : ↥(lemma102_fixSub 3 hdN)) : PQuot 3 J) = k148Psi inf_le_left x := by
  unfold k148PhiX
  rfl

theorem k148PhiX_surjective {J : Subgroup G} {d : G} (hdN : d ∈ Subgroup.normalizer (J : Set G))
    (hd3 : d ^ 3 = 1) : Function.Surjective (k148PhiX hdN) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hxz, hdx⟩ := k148_fix_lift hdN hd3 z hz
  refine ⟨⟨(x : G), x.2, Subgroup.mem_centralizer_singleton_iff.2 hdx.symm⟩, ?_⟩
  apply Subtype.ext
  rw [k148PhiX_val, k148Psi_apply]
  exact hxz

theorem k148_sub_fix {J I : Subgroup G} (hIJ : I ≤ J) {d : G}
    (hdN : d ∈ Subgroup.normalizer (J : Set G)) (hd3 : d ^ 3 = 1) (hdI : ∀ i ∈ I, d * i = i * d)
    (hIX : I ≤ J ⊓ Subgroup.centralizer ({d} : Set G))
    (hI : CFSG.Open.IsSubnormal I (J ⊓ Subgroup.centralizer ({d} : Set G))) :
    (k148Phi hIJ hdN hdI).range.IsSubnormal := by
  have hXsub : (I.subgroupOf (J ⊓ Subgroup.centralizer ({d} : Set G))).IsSubnormal :=
    CFSG.Open.IsSubnormal.subgroupOf hI
  have hmap := Subgroup.IsSubnormal.map (k148PhiX_surjective hdN hd3) hXsub
  have heq : (I.subgroupOf (J ⊓ Subgroup.centralizer ({d} : Set G))).map (k148PhiX hdN) =
      (k148Phi hIJ hdN hdI).range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, ?_⟩
      apply Subtype.ext
      rw [k148Phi_val, k148PhiX_val]
      rfl
    · rintro ⟨i, rfl⟩
      refine ⟨⟨(i : G), hIX i.2⟩, Subgroup.mem_subgroupOf.2 i.2, ?_⟩
      apply Subtype.ext
      rw [k148Phi_val, k148PhiX_val]
      rfl
  rw [heq] at hmap
  exact hmap

theorem k148_quot_hom {H : Type} [Group H] {I : Subgroup G} (Φ : ↥I →* H)
    (hΦ : Φ.ker ≤ GLAPPrimeCore 3 ↥I) :
    ∃ φ : ↥Φ.range →* PQuot 3 I, Function.Surjective φ := by
  classical
  let Φ' : ↥I →* ↥Φ.range := Φ.rangeRestrict
  have hΦ' : Function.Surjective Φ' := MonoidHom.rangeRestrict_surjective Φ
  have hker : Φ'.ker ≤ (GLAPPrimeCore 3 ↥I).comap (MonoidHom.id ↥I) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict] at hx
    exact hΦ hx
  let e := QuotientGroup.quotientKerEquivOfSurjective Φ' hΦ'
  let m : ↥I ⧸ Φ'.ker →* PQuot 3 I :=
    QuotientGroup.map Φ'.ker (GLAPPrimeCore 3 ↥I) (MonoidHom.id ↥I) hker
  refine ⟨m.comp e.symm.toMonoidHom, ?_⟩
  intro z
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨e (QuotientGroup.mk i), ?_⟩
  show m (e.symm (e (QuotientGroup.mk i))) = QuotientGroup.mk i
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem k148_iso_of_simple {R Q : Type} [Group R] [Group Q] [IsSimpleGroup R] (φ : R →* Q)
    (hφ : Function.Surjective φ) (hQ : Nontrivial Q) : Nonempty (R ≃* Q) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exact ⟨MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).1 h, hφ⟩⟩
  · exfalso
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨r, hr⟩ := hφ q
    have hrk : r ∈ φ.ker := by
      rw [h]
      exact Subgroup.mem_top r
    have h1 : φ r = 1 := MonoidHom.mem_ker.1 hrk
    rw [hr] at h1
    exact hq h1

end CFSG.LocalAnalysis.GLTheoremA

end
