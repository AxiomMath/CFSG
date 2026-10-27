module

public import CFSG.CharacterTheory.Semidihedral.LocalInvertedHallSubgroups

public noncomputable section

namespace CFSG.Semidihedral.LocalInvertedLiftContainment

open scoped Pointwise
open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.OrderedPairLocalTransport

universe u v

variable {G : Type u} [Group G]

@[expose] def originalSubgroupConjugation (Y : Subgroup G) [Y.Normal] (b : G) : MulAut Y :=
  Y.normalizerMonoidHom ⟨b, by rw [Subgroup.normalizer_eq_top]; trivial⟩

theorem originalSubgroupConjugation_apply (Y : Subgroup G) [Y.Normal] (b : G) (y : Y) :
    (originalSubgroupConjugation Y b y : G) = b * (y : G) * b⁻¹ := rfl

theorem originalSubgroupConjugation_symm_apply (Y : Subgroup G) [Y.Normal]
    (b : G) (y : Y) :
    ((originalSubgroupConjugation Y b).symm y : G) = b⁻¹ * (y : G) * b := by
  have h := congrArg (fun x : Y => (x : G))
    ((originalSubgroupConjugation Y b).apply_symm_apply y)
  rw [originalSubgroupConjugation_apply] at h
  calc
    ((originalSubgroupConjugation Y b).symm y : G) =
        b⁻¹ * (b * ((originalSubgroupConjugation Y b).symm y : G) * b⁻¹) * b := by
      group
    _ = b⁻¹ * (y : G) * b := by rw [h]

theorem originalSubgroupConjugation_preserves_kernel (Y K : Subgroup G)
    [Y.Normal] [K.Normal] (b : G) :
    (K.subgroupOf Y).map (originalSubgroupConjugation Y b).toMonoidHom =
      K.subgroupOf Y := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (originalSubgroupConjugation Y b y : G) ∈ K
    rw [originalSubgroupConjugation_apply]
    exact Subgroup.Normal.conj_mem inferInstance (y : G) hy b
  · intro hx
    refine ⟨(originalSubgroupConjugation Y b).symm x, ?_,
      (originalSubgroupConjugation Y b).apply_symm_apply x⟩
    change ((originalSubgroupConjugation Y b).symm x : G) ∈ K
    rw [originalSubgroupConjugation_symm_apply]
    simpa only [inv_inv] using Subgroup.Normal.conj_mem inferInstance (x : G) hx b⁻¹

@[expose] def originalQuotientConjugation (Y K : Subgroup G) [Y.Normal] [K.Normal]
    (b : G) : MulAut (Y ⧸ K.subgroupOf Y) :=
  QuotientGroup.congr (K.subgroupOf Y) (K.subgroupOf Y)
    (originalSubgroupConjugation Y b) (originalSubgroupConjugation_preserves_kernel Y K b)

theorem originalQuotientConjugation_apply (Y K : Subgroup G) [Y.Normal] [K.Normal]
    (b : G) (y : Y) :
    originalQuotientConjugation Y K b (QuotientGroup.mk' (K.subgroupOf Y) y) =
      QuotientGroup.mk' (K.subgroupOf Y) (originalSubgroupConjugation Y b y) :=
  QuotientGroup.congr_mk' _ _ _ _ y

theorem normal_join_quotient_conjugation_trivial
    (Y J N U A : Subgroup G) [Y.Normal] [J.Normal] [U.Normal]
    (hY : Y = J ⊔ N) (hN : N = U ⊔ A) (b : G)
    (hfixed : ∀ a ∈ A, b * a * b⁻¹ = a) :
    J ⊔ U ≤ Y ∧
      (∀ y : Y, QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)
        (originalSubgroupConjugation Y b y) =
          QuotientGroup.mk' ((J ⊔ U).subgroupOf Y) y) ∧
      ∀ z : Y ⧸ (J ⊔ U).subgroupOf Y,
        originalQuotientConjugation Y (J ⊔ U) b z = z := by
  have hJY : J ≤ Y := hY ▸ le_sup_left
  have hNY : N ≤ Y := hY ▸ le_sup_right
  have hUN : U ≤ N := hN ▸ le_sup_left
  have hAN : A ≤ N := hN ▸ le_sup_right
  have hUY : U ≤ Y := hUN.trans hNY
  let q := QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)
  let alpha := originalSubgroupConjugation Y b
  have htrivial : ∀ y : Y, q (alpha y) = q y := by
    intro y
    have hy : (y : G) ∈ J ⊔ N := hY ▸ y.property
    obtain ⟨j, hj, n, hn, hjn⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hnprod : n ∈ U ⊔ A := hN ▸ hn
    obtain ⟨x, hx, a, ha, hxa⟩ := Subgroup.mem_sup_of_normal_left.mp hnprod
    let jy : Y := ⟨j, hJY hj⟩
    let xy : Y := ⟨x, hUY hx⟩
    let ay : Y := ⟨a, hNY (hAN ha)⟩
    have hrep : y = jy * (xy * ay) := by
      apply Subtype.ext
      exact hjn.symm.trans (congrArg (fun z => j * z) hxa.symm)
    have hjone : q jy = 1 := (QuotientGroup.eq_one_iff jy).mpr
      (show (jy : G) ∈ J ⊔ U from Subgroup.mem_sup_left hj)
    have hxone : q xy = 1 := (QuotientGroup.eq_one_iff xy).mpr
      (show (xy : G) ∈ J ⊔ U from Subgroup.mem_sup_right hx)
    have hajone : q (alpha jy) = 1 := by
      apply (QuotientGroup.eq_one_iff (alpha jy)).mpr
      change (alpha jy : G) ∈ J ⊔ U
      rw [originalSubgroupConjugation_apply]
      exact Subgroup.mem_sup_left (Subgroup.Normal.conj_mem inferInstance j hj b)
    have haxone : q (alpha xy) = 1 := by
      apply (QuotientGroup.eq_one_iff (alpha xy)).mpr
      change (alpha xy : G) ∈ J ⊔ U
      rw [originalSubgroupConjugation_apply]
      exact Subgroup.mem_sup_right (Subgroup.Normal.conj_mem inferInstance x hx b)
    have haa : alpha ay = ay := by
      apply Subtype.ext
      exact hfixed a ha
    rw [hrep]
    simp only [map_mul, hjone, hxone, hajone, haxone, haa, one_mul]
  refine ⟨sup_le hJY hUY, htrivial, ?_⟩
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((J ⊔ U).subgroupOf Y) z
  rw [originalQuotientConjugation_apply]
  exact htrivial y

theorem normal_join_quotient_is_image_of_odd_factor
    (Y J N U : Subgroup G) [J.Normal] [U.Normal]
    (hY : Y = J ⊔ N) (hNodd : Odd (Nat.card N)) :
    ∃ hNY : N ≤ Y,
      Function.Surjective ((QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)).comp
        (Subgroup.inclusion hNY)) ∧ Odd (Nat.card (Y ⧸ (J ⊔ U).subgroupOf Y)) ∧
      ∃ gamma : N ⧸ U.subgroupOf N →* Y ⧸ (J ⊔ U).subgroupOf Y,
        Function.Surjective gamma ∧
        ∀ n : N, gamma (QuotientGroup.mk' (U.subgroupOf N) n) =
          QuotientGroup.mk' ((J ⊔ U).subgroupOf Y) (Subgroup.inclusion hNY n) := by
  have hJY : J ≤ Y := hY ▸ le_sup_left
  have hNY : N ≤ Y := hY ▸ le_sup_right
  let q := QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)
  let f := q.comp (Subgroup.inclusion hNY)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((J ⊔ U).subgroupOf Y) z
    have hy : (y : G) ∈ J ⊔ N := hY ▸ y.property
    obtain ⟨j, hj, n, hn, hjn⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    let jy : Y := ⟨j, hJY hj⟩
    have hrep : y = jy * Subgroup.inclusion hNY ⟨n, hn⟩ := Subtype.ext hjn.symm
    have hjone : q jy = 1 := (QuotientGroup.eq_one_iff jy).mpr
      (show (jy : G) ∈ J ⊔ U from Subgroup.mem_sup_left hj)
    refine ⟨⟨n, hn⟩, ?_⟩
    change q (Subgroup.inclusion hNY ⟨n, hn⟩) = q y
    rw [hrep, map_mul, hjone, one_mul]
  have hker : U.subgroupOf N ≤
      ((J ⊔ U).subgroupOf Y).comap (Subgroup.inclusion hNY) := by
    intro n hn
    exact Subgroup.mem_sup_right hn
  let gamma := QuotientGroup.map (U.subgroupOf N) ((J ⊔ U).subgroupOf Y)
    (Subgroup.inclusion hNY) hker
  have hvalue : ∀ n : N, gamma (QuotientGroup.mk' (U.subgroupOf N) n) =
      q (Subgroup.inclusion hNY n) := QuotientGroup.map_mk' _ _ _ _
  have hgamma : Function.Surjective gamma := by
    intro z
    obtain ⟨n, hn⟩ := hf z
    exact ⟨QuotientGroup.mk' (U.subgroupOf N) n, (hvalue n).trans hn⟩
  exact ⟨hNY, hf, hNodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hf),
    gamma, hgamma, hvalue⟩

theorem normal_complement_quotient_conjugation_trivial
    (N U A : Subgroup G) [N.Normal] [U.Normal]
    (hN : N = U ⊔ A) (b : G) (hfixed : ∀ a ∈ A, b * a * b⁻¹ = a) :
    (∀ n : N, QuotientGroup.mk' (U.subgroupOf N)
      (originalSubgroupConjugation N b n) = QuotientGroup.mk' (U.subgroupOf N) n) ∧
      ∀ z : N ⧸ U.subgroupOf N, originalQuotientConjugation N U b z = z := by
  have hUN : U ≤ N := hN ▸ le_sup_left
  have hAN : A ≤ N := hN ▸ le_sup_right
  let q := QuotientGroup.mk' (U.subgroupOf N)
  let alpha := originalSubgroupConjugation N b
  have htrivial : ∀ n : N, q (alpha n) = q n := by
    intro n
    have hn : (n : G) ∈ U ⊔ A := hN ▸ n.property
    obtain ⟨u, hu, a, ha, hua⟩ := Subgroup.mem_sup_of_normal_left.mp hn
    let un : N := ⟨u, hUN hu⟩
    let an : N := ⟨a, hAN ha⟩
    have hrep : n = un * an := Subtype.ext hua.symm
    have huone : q un = 1 := (QuotientGroup.eq_one_iff un).mpr hu
    have haone : q (alpha un) = 1 := by
      apply (QuotientGroup.eq_one_iff (alpha un)).mpr
      change (alpha un : G) ∈ U
      rw [originalSubgroupConjugation_apply]
      exact Subgroup.Normal.conj_mem inferInstance u hu b
    have hfix : alpha an = an := by
      apply Subtype.ext
      exact hfixed a ha
    rw [hrep]
    simp only [map_mul, huone, haone, hfix, one_mul]
  refine ⟨htrivial, ?_⟩
  intro z
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf N) z
  rw [originalQuotientConjugation_apply]
  exact htrivial n

theorem odd_inverted_subgroup_le_normal_join
    (Y J U W : Subgroup G) [Y.Normal] [J.Normal] [U.Normal]
    (b : G) (hWY : W ≤ Y) (hWodd : Odd (Nat.card W))
    (hinv : ∀ w ∈ W, b * w * b⁻¹ = w⁻¹)
    (hfixed : ∀ y : Y, QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)
      (originalSubgroupConjugation Y b y) =
        QuotientGroup.mk' ((J ⊔ U).subgroupOf Y) y) :
    W ≤ J ⊔ U ∧
      ∀ w : W, QuotientGroup.mk' ((J ⊔ U).subgroupOf Y) ⟨w, hWY w.property⟩ = 1 := by
  let q := QuotientGroup.mk' ((J ⊔ U).subgroupOf Y)
  have hkill : ∀ w : W, q ⟨w, hWY w.property⟩ = 1 := by
    intro w
    let wy : Y := ⟨w, hWY w.property⟩
    have hwy : originalSubgroupConjugation Y b wy = wy⁻¹ := by
      apply Subtype.ext
      exact hinv w w.property
    have hself : q wy = (q wy)⁻¹ := by
      have h := hfixed wy
      rw [hwy, map_inv] at h
      exact h.symm
    have hpow : (q wy) ^ 2 = 1 := by
      calc
        (q wy) ^ 2 = q wy * (q wy)⁻¹ := by
          rw [pow_two]
          exact congrArg (fun z => q wy * z) hself
        _ = 1 := mul_inv_cancel _
    let f : W →* Y ⧸ (J ⊔ U).subgroupOf Y := q.comp (Subgroup.inclusion hWY)
    have hodd : Odd (orderOf (q wy)) := hWodd.of_dvd_nat
      ((orderOf_map_dvd f w).trans (orderOf_dvd_natCard w))
    exact orderOf_eq_one_iff.mp ((Nat.coprime_two_right.mpr hodd).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one hpow))
  refine ⟨?_, hkill⟩
  intro w hw
  exact (QuotientGroup.eq_one_iff (⟨w, hWY hw⟩ : Y)).mp (hkill ⟨w, hw⟩)

theorem abelian_factor_centralizes_contained_subgroup (J U W : Subgroup G)
    (hUab : IsMulCommutative U) (hJU : ⁅J, U⁆ = ⊥) (hW : W ≤ J ⊔ U) :
    U ≤ Subgroup.centralizer (W : Set G) := by
  let := hUab
  have hJoin : J ⊔ U ≤ Subgroup.centralizer (U : Set G) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJU)
      (Subgroup.le_centralizer U)
  exact Subgroup.le_centralizer_iff.mp (hW.trans hJoin)

theorem characteristic_comap_original_equiv {B : Type v} [Group B]
    (e : G ≃* B) (K : Subgroup B) (hK : K.Characteristic) :
    (K.comap e.toMonoidHom).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro phi x hx
  change e (phi x) ∈ K
  let psi := e.symm.trans (phi.trans e)
  have h : psi (e x) ∈ K := Subgroup.characteristic_iff_le_comap.mp hK psi hx
  simpa only [psi, MulEquiv.trans_apply, e.symm_apply_apply] using h

theorem literal_hall_subgroup_intrinsic_facts (C N0 : Subgroup G)
    (N : Subgroup C) (hN0 : N0 = N.map C.subtype) (U : Subgroup G)
    (hUN0 : U ≤ N0) (hUab : IsMulCommutative U)
    (hUchar : (U.subgroupOf N0).Characteristic)
    (hHall : Nat.Coprime (Nat.card U) (U.relIndex N0)) :
    let Ui := U.subgroupOf C
    Ui ≤ N ∧ IsMulCommutative Ui ∧ (Ui.subgroupOf N).Characteristic ∧
      Nat.Coprime (Nat.card Ui) (Ui.relIndex N) ∧
      Ui.map C.subtype = U ∧
      ((Ui.subgroupOf N).map N.subtype).map C.subtype = U := by
  intro Ui
  have hUC : U ≤ C := hUN0.trans (hN0 ▸ Subgroup.map_subtype_le N)
  have hUiN : Ui ≤ N := by
    intro x hx
    have h : (x : G) ∈ N.map C.subtype := hN0 ▸ hUN0 hx
    exact (Subgroup.mem_map_iff_mem Subtype.val_injective).mp h
  have hUiMap : Ui.map C.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUC
  let e : N ≃* N0 := (N.equivMapOfInjective C.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr hN0.symm)
  have hchar : (Ui.subgroupOf N).Characteristic := by
    have h := characteristic_comap_original_equiv e (U.subgroupOf N0) hUchar
    exact h
  have hab : IsMulCommutative Ui := by
    let := hUab
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    apply Subtype.ext
    exact congrArg (fun z : U => (z : G))
      (mul_comm' (⟨x, hx⟩ : U) (⟨y, hy⟩ : U))
  have hcoprime : Nat.Coprime (Nat.card Ui) (Ui.relIndex N) := by
    have hcard : Nat.card Ui = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
    have hindex : Ui.relIndex N = U.relIndex N0 := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := C.subtype) Ui N Subtype.val_injective,
        hUiMap, ← hN0]
    rw [hcard, hindex]
    exact hHall
  refine ⟨hUiN, hab, hchar, hcoprime, hUiMap, ?_⟩
  rw [Subgroup.map_subgroupOf_eq_of_le hUiN, hUiMap]

@[expose] def OriginalCentralizingLiftFacts (i : G) : Prop :=
  let J := originalCentralizingResidual i
  let E := originalResidualOverlap i
  Group.IsPerfect J ∧ J.Normal ∧ tInC i ∈ J ∧ J.map (nu i) = originalSection i ∧
    ⁅J, N i⁆ = ⊥ ∧ originalLayerPreimage i = J ⊔ N i ∧
    ((nu i).comp J.subtype).ker = E.subgroupOf J ∧
    E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E)

@[expose] def OriginalInvertedHallFacts (i t : G) (U : Subgroup G) : Prop :=
  let Na := (N i).map (C i).subtype
  let A := Na ⊓ Subgroup.centralizer ({t} : Set G)
  Odd (Nat.card Na) ∧ Group.IsSolvable Na ∧
    (∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (N i) →
      ∀ P : Sylow ell (N i), OriginalStationaryCoverAt i t ell P →
      ((∀ x ∈ originalSylowAmbient i P, t * x * t⁻¹ = x) ∨
        (∀ x ∈ originalSylowAmbient i P, t * x * t⁻¹ = x⁻¹)) ∧
      ((∀ x ∈ originalSylowAmbient i P, t * x * t⁻¹ = x⁻¹) →
        IsMulCommutative (originalSylowAmbient i P))) ∧
    Nat.Coprime (Nat.card A) (A.relIndex Na) ∧
    ((∀ x : G, x ∈ U ↔ x ∈ Na ∧ t * x * t⁻¹ = x⁻¹) ∧
    (U : Set G) = CFSG.OddInversion.invertedSet Na t ∧
    U = ⁅Na, Subgroup.zpowers t⁆ ∧ U ≤ Na ∧ IsMulCommutative U ∧
    (U.subgroupOf Na).Characteristic ∧
    Nat.Coprime (Nat.card U) (U.relIndex Na) ∧ (U.subgroupOf Na).Normal ∧
    U ⊔ A = Na ∧ U ⊓ A = ⊥ ∧ U ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ ∧
    Nat.card U = A.relIndex Na ∧
    (∀ W : Subgroup G, W ≤ Na →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card U) → W ≤ U) ∧
    (∀ W : Subgroup G, W ≤ Na →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card W → q ∣ Nat.card U) →
      Nat.Coprime (W.relIndex Na) (Nat.card U) → W = U) ∧
    Subgroup.normalizer (Na : Set G) ≤ Subgroup.normalizer (U : Set G) ∧
    (Na = ⊥ → U = ⊥ ∧ A = ⊥) ∧
    (A = ⊥ → U = Na) ∧ (U = ⊥ → A = Na) ∧
    ∃ phi : A →* MulAut U,
      (∀ a : A, ∀ x : U, (phi a x : G) = (a : G) * x * (a : G)⁻¹) ∧
      ∃ e : U ⋊[phi] A ≃* Na,
        (∀ x : U ⋊[phi] A, (e x : G) = (x.left : G) * x.right) ∧
        (∀ z : Na, ∃ x : U, ∃ a : A, (e ⟨x, a⟩ : G) = z))

@[expose] def OriginalLiftHallQuotientFacts (i t : G) (htC : t ∈ C i)
    (U : Subgroup G) : Prop :=
  let Y := originalLayerPreimage i
  let J := originalCentralizingResidual i
  let Ui := U.subgroupOf (C i)
  let Ai := (N i).map (C i).subtype ⊓ Subgroup.centralizer ({t} : Set G)
  let A := Ai.subgroupOf (C i)
  ∃ hY : Y.Normal, ∃ hUi : Ui.Normal, ∃ hJoin : (J ⊔ Ui).Normal,
    letI := hY
    letI := hUi
    letI := hJoin
    Ui.map (C i).subtype = U ∧
    ((Ui.subgroupOf (N i)).map (N i).subtype).map (C i).subtype = U ∧
    IsMulCommutative Ui ∧ (Ui.subgroupOf (N i)).Characteristic ∧
    Nat.Coprime (Nat.card Ui) (Ui.relIndex (N i)) ∧
    (∀ x : C i, x ∈ Ui ↔ x ∈ N i ∧ t * (x : G) * t⁻¹ = (x : G)⁻¹) ∧
    N i = Ui ⊔ A ∧ ⁅J, Ui⁆ = ⊥ ∧ J ⊔ Ui ≤ Y ∧
    Odd (Nat.card (Y ⧸ (J ⊔ Ui).subgroupOf Y)) ∧
    (∃ hNY : N i ≤ Y,
      Function.Surjective ((QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y)).comp
        (Subgroup.inclusion hNY)) ∧
      ∃ gamma : N i ⧸ Ui.subgroupOf (N i) →* Y ⧸ (J ⊔ Ui).subgroupOf Y,
        Function.Surjective gamma ∧
        ∀ x : N i, gamma (QuotientGroup.mk' (Ui.subgroupOf (N i)) x) =
          QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y) (Subgroup.inclusion hNY x)) ∧
    (∀ x : N i, QuotientGroup.mk' (Ui.subgroupOf (N i))
      (originalSubgroupConjugation (N i) ⟨t, htC⟩ x) =
        QuotientGroup.mk' (Ui.subgroupOf (N i)) x) ∧
    (∀ z : N i ⧸ Ui.subgroupOf (N i),
      originalQuotientConjugation (N i) Ui ⟨t, htC⟩ z = z) ∧
    ∃ alpha : MulAut Y,
      (∀ y : Y, (alpha y : G) = t * (y : G) * t⁻¹) ∧
      ∃ beta : MulAut (Y ⧸ (J ⊔ Ui).subgroupOf Y),
        (∀ y : Y, beta (QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y) y) =
          QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y) (alpha y)) ∧
        (∀ y : Y, QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y) (alpha y) =
          QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y) y) ∧
        (∀ z : Y ⧸ (J ⊔ Ui).subgroupOf Y, beta z = z) ∧
        alpha = originalSubgroupConjugation Y ⟨t, htC⟩ ∧
        beta = originalQuotientConjugation Y (J ⊔ Ui) ⟨t, htC⟩

@[expose] def OriginalInvertedSubgroupConclusion (i : G) (U W : Subgroup G)
    (hWC : W ≤ C i) : Prop :=
  let Y := originalLayerPreimage i
  let J := originalCentralizingResidual i
  let Ui := U.subgroupOf (C i)
  let Wi := W.subgroupOf (C i)
  W ≤ J.map (C i).subtype ⊔ U ∧ U ≤ Subgroup.centralizer (W : Set G) ∧
    Wi ≤ J ⊔ Ui ∧
    ∃ hJoin : (J ⊔ Ui).Normal,
      letI := hJoin
      ∃ hWiY : Wi ≤ Y,
        (∀ w : Wi, QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y)
          ⟨w, hWiY w.property⟩ = 1) ∧
        ∀ w : W, ∀ hwY : (⟨(w : G), hWC w.property⟩ : C i) ∈ Y,
          QuotientGroup.mk' ((J ⊔ Ui).subgroupOf Y)
            ⟨⟨(w : G), hWC w.property⟩, hwY⟩ = 1

theorem original_all_prime_stationary_inverted_subgroups_lie_in_lift_join_hall
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i t : G) (hi : orderOf i = 2) (ht : orderOf t = 2) (htC : t ∈ C i) (hit : i ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hprimes : OriginalAllPrimeStationaryCover i t) :
    OriginalCentralizingLiftFacts i ∧
      ∃ U : Subgroup G, OriginalInvertedHallFacts i t U ∧
        OriginalLiftHallQuotientFacts i t htC U ∧
        ∀ (W : Subgroup G) (hWC : W ≤ C i), Odd (Nat.card W) →
          (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) →
          W ≤ (originalLayerPreimage i).map (C i).subtype →
          OriginalInvertedSubgroupConclusion i U W hWC := by
  have hcov : ∀ (ell : ℕ) [Fact ell.Prime], ell ∣ Nat.card (N i) →
      ∃ P : Sylow ell (N i),
        (Subgroup.centralizer (((P : Subgroup (N i)).map (N i).subtype) : Set (C i)) ⊓
          originalLayerPreimage i).map (nu i) = originalSection i := by
    intro ell hell hellN
    obtain ⟨P, hP⟩ := hprimes ell hellN
    exact ⟨P, hP.2.2⟩
  have hLift : OriginalCentralizingLiftFacts i :=
    PerfectLayerNormalization.original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 (PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab)
      i hi hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨hodd, hsolv, hscalar, hhallA, U, hU⟩ :=
    LocalInvertedHallSubgroups.original_all_prime_stationary_local_inverted_hall_subgroup
      hGnonab hrecognition n hn S0 f0 i t hi ht htC hit
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hprimes
  have hHall : OriginalInvertedHallFacts i t U := ⟨hodd, hsolv, hscalar, hhallA, hU⟩
  rcases hU with ⟨hUmem, hUset, hUcomm, hUN, hUab, hUchar, hUhall, hUn,
    hNgen, hdisj, hfixed, hcard, hsupport, hunique, hnorm, hbotN, hbotA, hbotU, hsemi⟩
  let Y := originalLayerPreimage i
  let J := originalCentralizingResidual i
  let Na := (N i).map (C i).subtype
  let Ai := Na ⊓ Subgroup.centralizer ({t} : Set G)
  let Ui := U.subgroupOf (C i)
  let A := Ai.subgroupOf (C i)
  have hJnormal : J.Normal := hLift.2.1
  let := hJnormal
  have hYnormal : Y.Normal := by infer_instance
  let := hYnormal
  have hUC : U ≤ C i := hUN.trans (Subgroup.map_subtype_le _)
  have hAC : Ai ≤ C i := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hUmap : Ui.map (C i).subtype = U := Subgroup.map_subgroupOf_eq_of_le hUC
  have hAmap : A.map (C i).subtype = Ai := Subgroup.map_subgroupOf_eq_of_le hAC
  have hCnorm : C i ≤ Subgroup.normalizer (U : Set G) :=
    (StationaryOddLocalization.actual_centralizer_core_normalized i (C i) le_rfl).trans hnorm
  have hUnormal : Ui.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUC).mpr hCnorm
  let := hUnormal
  obtain ⟨hUiN, hUiab, hUichar, hUihall, -, hUdoublemap⟩ :=
    literal_hall_subgroup_intrinsic_facts (C i) Na (N i) rfl U hUN hUab hUchar hUhall
  have hNprod : N i = Ui ⊔ A := by
    apply Subgroup.map_injective (f := (C i).subtype) Subtype.val_injective
    rw [Subgroup.map_sup, hUmap, hAmap]
    exact hNgen.symm
  have hJU : ⁅J, Ui⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono le_rfl hUiN).trans
      (show ⁅J, N i⁆ = ⊥ from hLift.2.2.2.2.1).le
  have hAfixed : ∀ a ∈ A, (⟨t, htC⟩ : C i) * a * (⟨t, htC⟩ : C i)⁻¹ = a := by
    intro a ha
    apply Subtype.ext
    change t * (a : G) * t⁻¹ = (a : G)
    have hcomm : (a : G) * t = t * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp ha.2
    rw [← hcomm, mul_inv_cancel_right]
  obtain ⟨hJUiY, htrivial, haction⟩ := normal_join_quotient_conjugation_trivial
    Y J (N i) Ui A (show Y = J ⊔ N i from hLift.2.2.2.2.2.1)
    hNprod ⟨t, htC⟩ hAfixed
  obtain ⟨hNY, hsurj, hquotodd, gamma, hgamma, hgammaValue⟩ :=
    normal_join_quotient_is_image_of_odd_factor
    Y J (N i) Ui (show Y = J ⊔ N i from hLift.2.2.2.2.2.1)
    (StationaryOddLocalization.actual_centralizer_core_odd i)
  obtain ⟨hNtrivial, hNaction⟩ := normal_complement_quotient_conjugation_trivial
    (N i) Ui A hNprod ⟨t, htC⟩ hAfixed
  have hQuotient : OriginalLiftHallQuotientFacts i t htC U := by
    refine ⟨hYnormal, hUnormal, inferInstance, hUmap, hUdoublemap, hUiab, hUichar, hUihall,
      ?_, hNprod, hJU, hJUiY, hquotodd, ⟨hNY, hsurj, gamma, hgamma, hgammaValue⟩,
      hNtrivial, hNaction,
      originalSubgroupConjugation Y ⟨t, htC⟩, ?_,
      originalQuotientConjugation Y (J ⊔ Ui) ⟨t, htC⟩,
      originalQuotientConjugation_apply Y (J ⊔ Ui) ⟨t, htC⟩,
      htrivial, haction, rfl, rfl⟩
    · intro x
      change (x : G) ∈ U ↔ _
      rw [hUmem]
      exact and_congr_left fun _ =>
        Subgroup.mem_map_iff_mem (f := (C i).subtype) Subtype.val_injective
    · intro y
      exact congrArg (fun x : C i => (x : G))
        (originalSubgroupConjugation_apply Y ⟨t, htC⟩ y)
  refine ⟨hLift, U, hHall, hQuotient, ?_⟩
  intro W hWC hWodd hWinv hWY
  let Wi := W.subgroupOf (C i)
  have hWiY : Wi ≤ Y := by
    intro w hw
    exact (Subgroup.mem_map_iff_mem (f := (C i).subtype) Subtype.val_injective).mp (hWY hw)
  have hWiodd : Odd (Nat.card Wi) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact hWodd
  have hWiinv : ∀ w ∈ Wi, (⟨t, htC⟩ : C i) * w * (⟨t, htC⟩ : C i)⁻¹ = w⁻¹ := by
    intro w hw
    apply Subtype.ext
    exact hWinv w hw
  obtain ⟨hWiJU, hkill⟩ := odd_inverted_subgroup_le_normal_join
    Y J Ui Wi ⟨t, htC⟩ hWiY hWiodd hWiinv htrivial
  have hWJU : W ≤ J.map (C i).subtype ⊔ U := by
    have h : Wi.map (C i).subtype ≤ (J ⊔ Ui).map (C i).subtype :=
      Subgroup.map_mono hWiJU
    rw [Subgroup.map_sup, hUmap, Subgroup.map_subgroupOf_eq_of_le hWC] at h
    exact h
  have hJUambient : ⁅J.map (C i).subtype, U⁆ = ⊥ := by
    rw [← hUmap, ← Subgroup.map_commutator, hJU, Subgroup.map_bot]
  refine ⟨hWJU, abelian_factor_centralizes_contained_subgroup _ U W hUab hJUambient hWJU,
    hWiJU, inferInstance, hWiY, hkill, ?_⟩
  intro w hwY
  exact hkill ⟨⟨w, hWC w.property⟩, w.property⟩

end CFSG.Semidihedral.LocalInvertedLiftContainment
