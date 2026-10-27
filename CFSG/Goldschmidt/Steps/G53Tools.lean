module

import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Walter.Bender1970.S3.PGroupFStar
public import CFSG.Walter.Bender1970.S3.TransitivityTools

public section

namespace CFSG.Goldschmidt.G53

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_normalizer_subgroupOf {X U : Subgroup G} (hUX : U ≤ X) :
    (Subgroup.normalizer ((U.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      X ⊓ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem isPGroup_generalizedFitting_inf_normalizer {X U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p (generalizedFittingSubgroupOf X)) (hUX : U ≤ X) (hU : IsPGroup p U) :
    IsPGroup p (generalizedFittingSubgroupOf (X ⊓ Subgroup.normalizer (U : Set G))) := by
  have hX' : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup X)) := by
    have e : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≃* generalizedFittingSubgroupOf X :=
      ((generalizedFittingSubgroupOf (⊤ : Subgroup X)).equivMapOfInjective X.subtype
        X.subtype_injective).trans
        (MulEquiv.subgroupCongr (generalizedFittingSubgroupOf_subgroup_top_eq X))
    exact hX.of_equiv e.symm
  have hU' : IsPGroup p (U.subgroupOf X) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have h := (bender1970_1_8_centralizerNormalizer_pGroup (G := X) p hp hX' _ hU').2
  have hmap := h.map X.subtype
  rwa [generalizedFittingSubgroupOf_map_subtype', map_subtype_normalizer_subgroupOf hUX] at hmap

omit [Finite G] in
theorem lowerCentralSeries_le_self (R : Subgroup G) (i : ℕ) : R.lowerCentralSeries i ≤ R := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro l hl r hr
    exact R.mul_mem (R.mul_mem (R.mul_mem (ih hl) hr) (R.inv_mem (ih hl))) (R.inv_mem hr)

omit [Finite G] in
theorem le_of_commutator_zpowers_eq_self {N R V : Subgroup G} {r : G}
    (hR : Group.IsNilpotent R) (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hrR : r ∈ R)
    (hVNR : V ≤ N ⊔ R) (hV : ⁅V, Subgroup.zpowers r⁆ = V) : V ≤ N := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries R).mp hR
  have key : ∀ i, V ≤ N ⊔ R.lowerCentralSeries i := by
    intro i
    induction i with
    | zero => exact hVNR
    | succ i ih =>
      have hLR : R.lowerCentralSeries i ≤ R := lowerCentralSeries_le_self R i
      rw [← hV, Subgroup.commutator_le]
      intro v hv s hs
      have hsR : s ∈ R := (Subgroup.zpowers_le.mpr hrR) hs
      have hv' : v ∈ R.lowerCentralSeries i ⊔ N := by
        rw [sup_comm]
        exact ih hv
      obtain ⟨l, hl, m, hm, rfl⟩ := mem_sup_of_le_normalizer (hLR.trans hRN) hv'
      have h1 : ⁅l * m, s⁆ = (l * ⁅m, s⁆ * l⁻¹) * ⁅l, s⁆ := by
        simp only [commutatorElement_def]
        group
      rw [h1]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · have hms : ⁅m, s⁆ ∈ N := by
          rw [commutatorElement_def]
          have : s * m⁻¹ * s⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hRN hsR) _).mp (N.inv_mem hm)
          have h2 := N.mul_mem hm this
          simpa [mul_assoc] using h2
        exact (Subgroup.mem_normalizer_iff.mp (hRN (hLR hl)) _).mp hms
      · exact Subgroup.commutator_mem_commutator hl hsR
  have := key n
  rwa [hn, sup_bot_eq] at this

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem eq_bot_of_commutator_eq_self_of_isPGroup_two {V : Subgroup G} {a : G} (ha : a * a = 1)
    (hVp : IsPGroup 2 V) (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hV : ⁅V, Subgroup.zpowers a⁆ = V) : V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 (V ⊔ Subgroup.zpowers a : Subgroup G) :=
    hVp.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self ha) (Subgroup.zpowers_le.mpr haV)
  have hN : V ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  refine eq_bot_iff.mpr (le_of_commutator_zpowers_eq_self hR.isNilpotent hN
    (le_sup_right (a := V) (Subgroup.mem_zpowers a)) ?_ hV)
  rw [bot_sup_eq]
  exact le_sup_left

omit [Finite G] in
theorem le_centralizer_of_isCyclic {Z : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZp : IsPGroup p Z) (hZc : IsCyclic Z) {e : G} (he : e * e = 1)
    (heZ : e ∈ Subgroup.normalizer (Z : Set G)) {w : G} (hwZ : w ∈ Z) (hw1 : w ≠ 1)
    (hwe : e * w * e⁻¹ = w) : ∀ z ∈ Z, e * z * e⁻¹ = z := by
  have : Fact p.Prime := ⟨hp⟩
  let σ : Z →* Z :=
    { toFun := fun z => ⟨e * z * e⁻¹, (Subgroup.mem_normalizer_iff.mp heZ z).mp z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨m, hm⟩ := σ.map_cyclic
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hσσ : ∀ z : Z, σ (σ z) = z := fun z => Subtype.ext (by
    show e * (e * (z : G) * e⁻¹) * e⁻¹ = z
    rw [heinv]
    calc e * (e * (z : G) * e) * e = (e * e) * z * (e * e) := by group
      _ = z := by rw [he]; group)
  have hσ : ∀ z (hz : z ∈ Z), e * z * e⁻¹ = (((⟨z, hz⟩ : Z) ^ m : Z) : G) := fun z hz =>
    congrArg Subtype.val (hm ⟨z, hz⟩)
  have hord : ∀ z : Z, ∃ j : ℕ, orderOf z = p ^ j := fun z => by
    obtain ⟨k, hk⟩ := hZp z
    exact (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk) |>.imp fun _ h => h.2
  have hpm : (p : ℤ) ∣ m - 1 := by
    have h1 : (⟨w, hwZ⟩ : Z) ^ (m - 1) = 1 := by
      have h2 : (⟨w, hwZ⟩ : Z) ^ m = ⟨w, hwZ⟩ := Subtype.ext (by rw [← hσ w hwZ, hwe])
      rw [zpow_sub, h2, zpow_one, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one] at h1
    obtain ⟨j, hj⟩ := hord ⟨w, hwZ⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hw1 (congrArg Subtype.val hj)
    rw [hj] at h1
    exact (Int.natCast_dvd_natCast.mpr (dvd_pow_self p hj0)).trans (by exact_mod_cast h1)
  have hpm' : ¬ (p : ℤ) ∣ m + 1 := by
    intro h
    have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h hpm
      rwa [show m + 1 - (m - 1) = (2 : ℤ) by ring] at this
    have h3 : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro z hz
  rw [hσ z hz]
  obtain ⟨j, hj⟩ := hord ⟨z, hz⟩
  have hzz : (⟨z, hz⟩ : Z) ^ (m * m - 1) = 1 := by
    have h1 := hσσ ⟨z, hz⟩
    rw [hm, hm, ← zpow_mul] at h1
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  rw [← orderOf_dvd_iff_zpow_eq_one, hj] at hzz
  have hcop : IsCoprime ((p : ℤ) ^ j) (m + 1) :=
    ((hpz.coprime_iff_not_dvd).mpr hpm').pow_left
  have hdvd : ((p ^ j : ℕ) : ℤ) ∣ m - 1 := by
    push_cast
    refine hcop.dvd_of_dvd_mul_right ?_
    have : (m - 1) * (m + 1) = m * m - 1 := by ring
    rw [this]
    exact_mod_cast hzz
  have : (⟨z, hz⟩ : Z) ^ m = ⟨z, hz⟩ := by
    have h1 : (⟨z, hz⟩ : Z) ^ (m - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hj]
      exact hdvd
    rw [show m = (m - 1) + 1 by ring, zpow_add, h1, one_mul, zpow_one]
  rw [this]

omit [Finite G] in
theorem exists_ne_one_mem_of_le_zpowers_sup {V C : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) (hV : V ≤ Subgroup.zpowers y ⊔ C)
    (hVc : ¬ IsCyclic V) : ∃ v ∈ V, v ≠ 1 ∧ v ∈ C := by
  set K := Subgroup.zpowers y ⊔ C with hKdef
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (C : Set G) := Subgroup.zpowers_le.mpr hy
  have hKN : K ≤ Subgroup.normalizer (C : Set G) := sup_le hyN Subgroup.le_normalizer
  have hCK : C ≤ K := le_sup_right
  have hn : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mpr hKN
  have hyK : y ∈ K := (le_sup_left : Subgroup.zpowers y ≤ K) (Subgroup.mem_zpowers y)
  have hcyc : IsCyclic (K ⧸ C.subgroupOf K) := by
    refine ⟨⟨QuotientGroup.mk ⟨y, hyK⟩, fun q => ?_⟩⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, c, hc, hbc⟩ := mem_sup_of_le_normalizer hyN k.2
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine ⟨j, ?_⟩
    show (QuotientGroup.mk ⟨y, hyK⟩ : K ⧸ C.subgroupOf K) ^ j = QuotientGroup.mk k
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((⟨y, hyK⟩ : K) ^ j)⁻¹ * k : K) = (c : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, ← hbc]
      group
    rw [this]
    exact hc
  set φ : V →* K ⧸ C.subgroupOf K := (QuotientGroup.mk' (C.subgroupOf K)).comp
    (Subgroup.inclusion hV) with hφ
  have hker : φ.ker ≠ ⊥ := by
    intro h
    exact hVc (isCyclic_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp h))
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨((u : V) : G), (u : V).2, fun h => hu1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have hmem : (QuotientGroup.mk' (C.subgroupOf K)) (Subgroup.inclusion hV (u : V)) = 1 :=
    (u : φ.ker).2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem eq_of_le_isCyclic_of_card_eq {Z Y₁ Y₂ : Subgroup G} (hZ : IsCyclic Z) (h1 : Y₁ ≤ Z)
    (h2 : Y₂ ≤ Z) (hc : Nat.card Y₁ = Nat.card Y₂) : Y₁ = Y₂ := by
  have h : Y₁.subgroupOf Z = Y₂.subgroupOf Z := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2).toEquiv]
    exact hc
  rw [← Subgroup.map_subgroupOf_eq_of_le h1, ← Subgroup.map_subgroupOf_eq_of_le h2, h]

theorem le_of_isCyclic_of_card_eq_prime {Z Y W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ : IsCyclic Z) (hZp : IsPGroup p Z) (hYZ : Y ≤ Z) (hY : Nat.card Y = p) (hWZ : W ≤ Z)
    (hW : W ≠ ⊥) : Y ≤ W := by
  have : Fact p.Prime := ⟨hp⟩
  have hWp : IsPGroup p W := hZp.to_le hWZ
  obtain ⟨k, hk⟩ := hWp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hW hk
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) p (hk ▸ dvd_pow_self p hk0)
  have hwW : Subgroup.zpowers (w : G) ≤ W := Subgroup.zpowers_le.mpr w.2
  have hcard : Nat.card (Subgroup.zpowers (w : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  rw [eq_of_le_isCyclic_of_card_eq hZ hYZ (hwW.trans hWZ) (hY.trans hcard.symm)]
  exact hwW

omit [Finite G] in
theorem exists_orderOf_eq_conj_eq_inv {D : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hDp : IsPGroup p D) {a : G} (ha : a * a = 1) (haD : a ∈ Subgroup.normalizer (D : Set G))
    (h : ⁅Subgroup.zpowers a, D⁆ ≠ ⊥) : ∃ y ∈ D, orderOf y = p ∧ a * y * a⁻¹ = y⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Ne, commutator_zpowers_eq_bot_iff] at h
  push Not at h
  obtain ⟨x, hxD, hxa⟩ := h
  set w := ⁅x, a⁆ with hw
  have hwD : w ∈ D := by
    rw [hw, commutatorElement_def]
    have : a * x⁻¹ * a⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp haD _).mp (D.inv_mem hxD)
    have h2 := D.mul_mem hxD this
    simpa [mul_assoc] using h2
  have hw1 : w ≠ 1 := by
    rw [hw, Ne, commutatorElement_eq_one_iff_mul_comm]
    exact hxa
  have hwinv : a * w * a⁻¹ = w⁻¹ := conj_commutatorElement_eq_inv ha x
  have hwp : IsPGroup p (Subgroup.zpowers w) := hDp.to_le (Subgroup.zpowers_le.mpr hwD)
  have hfin : Finite (Subgroup.zpowers w) := by
    obtain ⟨k, hk⟩ := hDp ⟨w, hwD⟩
    have hk' : w ^ p ^ k = 1 := congrArg Subtype.val hk
    have hpos : 0 < p ^ k := pow_pos hp.pos k
    have hfo : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, hpos, hk'⟩
    exact Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact hfo.orderOf_pos.ne')
  obtain ⟨k, hk⟩ := hwp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at hk
    exact hw1 hk
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers w) p
    (hk ▸ dvd_pow_self p hk0)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
  refine ⟨y, (Subgroup.zpowers_le.mpr hwD) y.2, by rw [Subgroup.orderOf_coe, hy], ?_⟩
  rw [← hj, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hwinv, inv_zpow]

omit [Finite G] in
theorem not_isCyclic_of_isElemAbelian {V : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hV : CFSG.Open.IsElemAbelian p V) (hcard : Nat.card V = p ^ 2) : ¬ IsCyclic V := by
  intro hc
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hexp : Monoid.exponent V ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hV.2 x x.2)
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

theorem exists_hyperplane_commutator_ne_bot {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    {t : G} (htA : t ∈ A) (ht1 : t ≠ 1) {D : Subgroup G}
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (htD : ⁅Subgroup.zpowers t, D⁆ ≠ ⊥) :
    ∃ A₁ ≤ A, (A₁.subgroupOf A).index = 2 ∧
      ⁅Subgroup.zpowers t, D ⊓ Subgroup.centralizer (A₁ : Set G)⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcomm := hA.1
  have : IsElementaryAbelian 2 A :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA.2 x x.2) }
  have : Nontrivial A := ⟨⟨⟨t, htA⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  let _ : MulDistribMulAction A D := Subgroup.conjMulDistribMulActionOfLeNormalizer A D hAD
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := D) hp
  by_contra hcon
  push Not at hcon
  apply htD
  rw [commutator_zpowers_eq_bot_iff]
  set Ct : Subgroup D := (Subgroup.centralizer ({t} : Set G)).comap D.subtype
  have hle : ⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤ Ct := by
    refine iSup₂_le fun B hB => ?_
    set R : Subgroup G := B.map A.subtype
    have hRA : R ≤ A := Subgroup.map_subtype_le B
    have hRi : (R.subgroupOf A).index = 2 := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
      exact hB
    have h := hcon R hRA hRi
    rw [commutator_zpowers_eq_bot_iff] at h
    intro x hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr (h x ⟨x.2, ?_⟩)
    show (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
    change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [hbx]
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxC : (⟨x, hx⟩ : D) ∈ Ct := hle ▸ Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.mp hxC

end General

section Fitting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem goldOddCoreOf_eq (H : Subgroup G) :
    Goldschmidt.oddCoreOf H = GorensteinWalter.oddCoreOf H := by
  unfold Goldschmidt.oddCoreOf GorensteinWalter.oddCoreOf
  rw [goldschmidtOddCore_eq_pPrimeCore]

omit [Finite G] in
theorem mem_normalizer_fittingSubgroupOf {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf X : Set G) :=
  normalizer_le_normalizer_map_of_characteristic (CFSG.fittingSubgroup X) hg

omit [Finite G] in
theorem mem_normalizer_oddFitting {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) : Set G) := by
  rw [goldOddCoreOf_eq]
  exact normalizer_le_normalizer_map_of_characteristic (CFSG.pPrimeCore 2 _)
    (mem_normalizer_fittingSubgroupOf hg)

theorem mem_normalizer_qCoreOf {X : Subgroup G} {g : G} (p : ℕ)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (qCoreOf X p : Set G) :=
  normalizer_le_normalizer_map_of_characteristic (CFSG.pCore p X) hg

omit [Finite G] in
theorem mem_normalizer_layer_sup_oddFitting {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((componentLayerOf X ⊔
      Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) : Subgroup G) : Set G) :=
  mem_normalizer_sup (mem_normalizer_componentLayerOf hg) (mem_normalizer_oddFitting hg)

omit [Finite G] in
theorem oddFitting_le (X : Subgroup G) :
    Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) ≤ X :=
  (Subgroup.map_subtype_le _).trans (fittingSubgroupOf_isNormalIn X).1

omit [Finite G] in
theorem layer_sup_oddFitting_le (X : Subgroup G) :
    componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) ≤ X :=
  sup_le (componentLayerOf_isNormalIn X).1 (oddFitting_le X)

theorem layer_le_and_oddFitting_le (X : Subgroup G) :
    componentLayerOf X ≤
        componentLayerOf (componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X)) ∧
      Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) ≤
        Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf
          (componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X))) := by
  set X₁ := componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X)
  have hX₁X : X₁ ≤ X := layer_sup_oddFitting_le X
  refine ⟨sSup_le fun K hK => le_sSup (IsComponentOf.of_le hK ((le_sSup hK).trans le_sup_left)
    hX₁X), ?_⟩
  rw [goldOddCoreOf_eq, goldOddCoreOf_eq]
  have hOn := oddCoreOf_fittingSubgroupOf_isNormalIn X
  have hOX₁ : GorensteinWalter.oddCoreOf (CFSG.fittingSubgroupOf X) ≤ X₁ := by
    rw [← goldOddCoreOf_eq]
    exact le_sup_right
  refine le_oddCoreOf_fittingSubgroupOf ⟨hOX₁, fun h hh k hk => hOn.2 h (hX₁X hh) k hk⟩ ?_
    (odd_card_oddCoreOf _)
  exact isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent X) (Subgroup.map_subtype_le _)

theorem layer_sup_oddFitting_eq (X : Subgroup G) :
    componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) =
      componentLayerOf (componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X)) ⊔
        Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf
          (componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X))) := by
  obtain ⟨h1, h2⟩ := layer_le_and_oddFitting_le X
  exact le_antisymm (sup_le_sup h1 h2) (layer_sup_oddFitting_le _)

theorem oddFitting_eq_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) : Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) = X := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : CFSG.fittingSubgroupOf X = X := fittingSubgroupOf_eq_self_of_isNilpotent hX.isNilpotent
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  rw [hF]
  unfold Goldschmidt.oddCoreOf
  have htop : CFSG.Open.goldschmidtOddCore X = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨Subgroup.normal_top, by rw [Subgroup.card_top]; exact hodd⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_layer_sup_oddFitting_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : IsPGroup p X) :
    X = componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
  have hE : componentLayerOf X = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup X hp (hX.to_le (generalizedFittingSubgroupOf_le X))
  rw [hE, oddFitting_eq_of_isPGroup hp hp2 hX, bot_sup_eq]

theorem le_layer_sup_oddFitting {X V : Subgroup G} {a : G}
    (hXF : generalizedFittingSubgroupOf X = X) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (ha2 : a * a = 1) (hVX : V ≤ X) (hV : ⁅V, Subgroup.zpowers a⁆ = V) :
    V ≤ componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) with hNdef
  set T := qCoreOf X 2 with hTdef
  set R := Subgroup.zpowers a ⊔ T with hRdef
  have hR : IsPGroup 2 R :=
    (isPGroup_zpowers_of_mul_self ha2).to_sup_of_normal_right' (qCoreOf_isPGroup X 2)
      (Subgroup.zpowers_le.mpr (mem_normalizer_qCoreOf 2 haX))
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_layer_sup_oddFitting (Subgroup.le_normalizer hx)
  have hRN : R ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_layer_sup_oddFitting haX))
      ((qCoreOf_le X 2).trans hXN)
  have hFT : CFSG.fittingSubgroupOf X ≤ T ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
    have hqle : ∀ q : ℕ, q.Prime →
        qCoreOf X q ≤ T ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
      intro q hq
      by_cases hq2 : q = 2
      · rw [hq2]
        exact le_sup_left
      · refine le_sup_of_le_right ?_
        rw [goldOddCoreOf_eq]
        have : Fact q.Prime := ⟨hq⟩
        refine le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent X)
          (qCoreOf_le_fittingSubgroupOf X q hq) ?_
        obtain ⟨k, hk⟩ := (qCoreOf_isPGroup X q).exists_card_eq
        rw [hk]
        exact (hq.odd_of_ne_two hq2).pow
    calc CFSG.fittingSubgroupOf X = ⨆ q : (Nat.card X).primeFactors.attach, qCoreOf X q.1.1 :=
          fittingSubgroupOf_eq_iSup_qCoreOf X
      _ ≤ _ := iSup_le fun q => hqle _ (Nat.prime_of_mem_primeFactors q.1.2)
  have hVNR : V ≤ N ⊔ R := by
    refine hVX.trans ?_
    rw [← hXF, generalizedFittingSubgroupOf]
    refine sup_le (hFT.trans (sup_le ?_ ?_)) ?_
    · exact (le_sup_right : T ≤ R).trans le_sup_right
    · exact (le_sup_right : _ ≤ N).trans le_sup_left
    · exact (le_sup_left : _ ≤ N).trans le_sup_left
  exact le_of_commutator_zpowers_eq_self hR.isNilpotent hRN
    ((le_sup_left : Subgroup.zpowers a ≤ R) (Subgroup.mem_zpowers a)) hVNR hV

end Fitting

section Maximal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_ne_top_of_le_isCoatom (hsimple : IsSimpleGroup G) {H V : Subgroup G}
    (hH : IsCoatom H) (hVH : V ≤ H) (hV1 : V ≠ ⊥) : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
  intro h
  have hn : V.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases hsimple.eq_bot_or_eq_top_of_normal V with h' | h'
  · exact hV1 h'
  · exact hH.1 (top_le_iff.mp (h' ▸ hVH))

theorem exists_isCoatom_normalizer_le (hsimple : IsSimpleGroup G) {H V : Subgroup G}
    (hH : IsCoatom H) (hVH : V ≤ H) (hV1 : V ≠ ⊥) :
    ∃ B : Subgroup G, IsCoatom B ∧ Subgroup.normalizer (V : Set G) ≤ B := by
  rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (V : Set G)) with h | ⟨B, hB, hNB⟩
  · exact absurd h (normalizer_ne_top_of_le_isCoatom hsimple hH hVH hV1)
  · exact ⟨B, hB, hNB⟩

theorem normalizer_le_of_mem_goldA (hsimple : IsSimpleGroup G) {a : G} {H Y : Subgroup G}
    (hH : IsCoatom H) (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (hY : Y ∈ goldA a H) : Subgroup.normalizer (Y : Set G) ≤ H := by
  have hYH : Y ≤ H := hY.2.1.trans (generalizedFittingSubgroupOf_le H)
  obtain ⟨B, hB, hNB⟩ := exists_isCoatom_normalizer_le hsimple hH hYH hY.1
  rcases hY.2.2.2.2 B hB hNB with rfl | ⟨q, hq, -, hHq⟩
  · exact hNB
  · have := card_primesOfOrder_le_one_of_isPGroup hq hHq
    omega

theorem exists_isCoatom_isPGroup_of_mem_goldA (hsimple : IsSimpleGroup G) {a : G}
    {H Y : Subgroup G} (hH : IsCoatom H) (hH1 : H ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hFp : IsPGroup p (generalizedFittingSubgroupOf H)) (hY : Y ∈ goldA a H) :
    ∃ B : Subgroup G, IsCoatom B ∧ Subgroup.normalizer (Y : Set G) ≤ B ∧
      IsPGroup p (generalizedFittingSubgroupOf B) := by
  have hYH : Y ≤ H := hY.2.1.trans (generalizedFittingSubgroupOf_le H)
  obtain ⟨B, hB, hNB⟩ := exists_isCoatom_normalizer_le hsimple hH hYH hY.1
  refine ⟨B, hB, hNB, ?_⟩
  rcases hY.2.2.2.2 B hB hNB with rfl | ⟨q, hq, hBq, hHq⟩
  · exact hFp
  · rwa [eq_of_isPGroup_of_isPGroup hp hq hFp hHq (generalizedFittingSubgroupOf_ne_bot hH1)]

theorem isPGroup_generalizedFitting_of_normalizer (hsimple : IsSimpleGroup G)
    {M P₀ : Subgroup G} (hM : IsCoatom M) {p : ℕ} (hp : p.Prime) (hP₀ : P₀ ≤ qCoreOf M p)
    (hOp : qCoreOf M p ≠ ⊥)
    (hK : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer (P₀ : Set G)))) :
    IsPGroup p (generalizedFittingSubgroupOf M) := by
  have : Fact p.Prime := ⟨hp⟩
  set PM := qCoreOf M p with hPMdef
  set Z := (Subgroup.center PM).map PM.subtype with hZdef
  have hZn : IsNormalIn Z M :=
    map_characteristic_isNormalIn_of_isNormalIn _ inferInstance (qCoreOf_normal_in M p)
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial PM := (Subgroup.nontrivial_iff_ne_bot PM).mpr hOp
    have := (qCoreOf_isPGroup M p).center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center PM)
    intro h
    have hzZ : ((z : PM) : G) ∈ Z := ⟨z, z.2, rfl⟩
    rw [h, Subgroup.mem_bot] at hzZ
    exact hz (Subtype.ext (Subtype.ext hzZ))
  have hZP₀ : Z ≤ Subgroup.centralizer (P₀ : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨w, hP₀ hw⟩)
  set U := Z ⊔ P₀ with hUdef
  have hUO : U ≤ PM := sup_le (Subgroup.map_subtype_le _) hP₀
  have hNZ : Subgroup.normalizer (Z : Set G) = M :=
    normalizer_eq_of_nontrivial_normal_in_coatom hsimple hM hZn.1 hZ1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hZn.1).mpr (le_normalizer_of_isNormalIn hZn))
  have hCM : Subgroup.centralizer (U : Set G) ≤ M :=
    ((Subgroup.centralizer_le (le_sup_left : Z ≤ U)).trans
      (Subgroup.centralizer_le_normalizer _)).trans hNZ.le
  have hUK : U ≤ Subgroup.normalizer (P₀ : Set G) :=
    sup_le (hZP₀.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hUp : IsPGroup p U := (qCoreOf_isPGroup M p).to_le hUO
  have hCK : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    (Subgroup.centralizer_le (le_sup_right : P₀ ≤ U)).trans (Subgroup.centralizer_le_normalizer _)
  have hC := isPGroup_generalizedFitting_inf_centralizer hp hK hUK hUp
  rw [inf_eq_right.mpr hCK] at hC
  exact isPGroup_generalizedFitting_of_le_qCoreOf hp hUO hCM hC

theorem pResidualOf_eq_self_of_not_dvd {K : Subgroup G} {p : ℕ} (hK : ¬ p ∣ Nat.card K) :
    pResidualOf K p = K := by
  unfold pResidualOf
  have htop : sInf {N : Subgroup K | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n} = ⊤ := by
    refine eq_top_iff.mpr (le_sInf fun N hN => ?_)
    obtain ⟨-, n, hn⟩ := hN
    have hdvd : N.index ∣ Nat.card K := N.index_dvd_card
    rw [hn] at hdvd
    rcases n with _ | n
    · rw [pow_zero, Subgroup.index_eq_one] at hn
      rw [hn]
    · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hdvd) hK
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_ne_bot_of_isPGroup {H X : Subgroup G} {a : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hFp : IsPGroup p (generalizedFittingSubgroupOf H)) (haH : a ∈ H)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hXF : X ≤ generalizedFittingSubgroupOf H)
    (hCX : generalizedFittingSubgroupOf H ⊓ Subgroup.centralizer (X : Set G) ≤ X) :
    ⁅X, Subgroup.zpowers a⁆ ≠ ⊥ := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  set F := generalizedFittingSubgroupOf H with hFdef
  have hFn := generalizedFittingSubgroupOf_isNormalIn H
  have haF : a ∈ Subgroup.normalizer (F : Set G) := le_normalizer_of_isNormalIn hFn haH
  have ha2' : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hres : pResidualOf (Subgroup.zpowers a) p = Subgroup.zpowers a := by
    refine pResidualOf_eq_self_of_not_dvd fun hdvd => hp2 ?_
    rw [Nat.card_zpowers, ha2'] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
  have hcent := bender1970_1_1_thompson p hp X (Subgroup.zpowers a) F (hFp.to_le hXF) hFp hres
    (fun x hx => le_normalizer_of_isNormalIn hFn (generalizedFittingSubgroupOf_le H (hXF hx)))
    (Subgroup.zpowers_le.mpr haF) h
    (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hCX le_rfl))
  have haC : a ∈ Subgroup.centralizer (F : Set G) := hcent (Subgroup.mem_zpowers a)
  have haFF : a ∈ F := Bender35.inf_centralizer_le_generalizedFitting H ⟨haH, haC⟩
  obtain ⟨k, hk⟩ := hFp ⟨a, haFF⟩
  have hk' : a ^ p ^ k = 1 := congrArg Subtype.val hk
  have h2 : 2 ∣ p ^ k := ha2' ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem four_le_card_of_goldSetting {S : Sylow 2 G} {A : Subgroup G} (hG : GoldSetting G S A) :
    4 ≤ Nat.card A := by
  have hsimple := hG.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hG.ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hA2 : IsPGroup 2 A := IsPGroup.of_exponent_dvd_pow (n := 1) (by
    rw [pow_one]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hG.elem.2 x x.2))
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  by_contra h4
  push Not at h4
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hG.elem.2 a haA) ha1'
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · rw [pow_zero, Subgroup.card_eq_one] at hk
      exact absurd hk hG.ne_bot
    · rfl
    · exfalso
      have h5 : 2 ^ 2 ≤ Nat.card A := hk ▸ Nat.pow_le_pow_right two_pos (by omega)
      norm_num at h5
      omega
  have hzA : Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) ?_
    rw [hk, hk1, Nat.card_zpowers, ha2, pow_one]
  have hb : ∀ b ∈ A, b ≠ 1 → b = a := fun b hb hb1 => by
    rcases eq_one_or_eq_of_mem_zpowers ha2 (hzA ▸ hb) with h | h
    · exact absurd h hb1
    · exact h
  have hC : Subgroup.centralizer ({a} : Set G) = ⊤ := by
    rw [eq_top_iff, ← hG.gen]
    refine iSup_le fun x => ?_
    rw [hb x.1 x.2.1 x.2.2]
  have haZ : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC ▸ Subgroup.mem_top g)
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at haZ
    exact ha1' haZ
  · obtain ⟨x, y, hxy⟩ := hG.nonabelian
    exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x)

end Maximal

section ThreeSeven

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_conjSub_inf {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (g : G)
    (M : Subgroup G) : CFSG.Open.IsElemAbelian 2 (conjSub g A ⊓ M) := by
  have hmem : ∀ x ∈ conjSub g A ⊓ M, g * x * g⁻¹ ∈ A := fun x hx => mem_conjSub.mp hx.1
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h := congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hmem x x.2⟩ ⟨_, hmem y y.2⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    have h2 : g * ((x : G) * y) * g⁻¹ = g * ((y : G) * x) * g⁻¹ := by
      calc g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * ((y : G) * x) * g⁻¹ := by group
    simpa using h2
  · have h := hA.2 _ (hmem x hx)
    have h2 : g * x ^ 2 * g⁻¹ = 1 := by
      rw [← h, pow_two, pow_two]
      group
    have h3 : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
    rw [h3, h2]
    group

theorem commutator_le_qCoreOf_of_isPGroup (h37 : S_G37) {M A₁ X : Subgroup G}
    (hSS : IsSStarIn M A₁) (hA₁ : CFSG.Open.IsElemAbelian 2 A₁) {a : G} (haA : a ∈ A₁)
    (ha1 : a ≠ 1) (hXM : X ≤ M)
    (hXC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p X) :
    ⁅X, Subgroup.zpowers a⁆ ≤ qCoreOf M p := by
  obtain ⟨⟨h1, h2⟩, -⟩ :=
    h37 G M A₁ hSS hA₁ a haA ha1 X hXM hXC (eq_layer_sup_oddFitting_of_isPGroup hp hp2 hXp)
  have haM : a ∈ M := hSS.1 haA
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hXC ⟨haM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact le_qCoreOf_of_isSubnormal_isPGroup M _ p (h1.trans (generalizedFittingSubgroupOf_le M))
    (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting h1 h2)
    (hXp.to_le (commutator_zpowers_le_of_mem_normalizer haX))

theorem exists_ne_one_le_centralizer_of_isComponentOf (h37 : S_G37) {M A₁ X : Subgroup G}
    (hSS : IsSStarIn M A₁) (hA₁ : CFSG.Open.IsElemAbelian 2 A₁) {a : G} (haA : a ∈ A₁)
    (ha1 : a ≠ 1) (hXM : X ≤ M)
    (hXC : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X))
    {V : Subgroup G} (hVX : V ≤ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X))
    (hVc : ¬ IsCyclic V) {L : Subgroup G} (hL : IsComponentOf L M) :
    ∃ v ∈ V, v ≠ 1 ∧ L ≤ Subgroup.centralizer ({v} : Set G) := by
  have key : ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (L : Set G) := by
    by_cases hYL : Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) ≤
        Subgroup.centralizer (L : Set G)
    · have hV1 : V ≠ ⊥ := fun h => hVc (by rw [h]; infer_instance)
      obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
      exact ⟨v, v.2, fun h => hv1 (Subtype.ext h), hYL (hVX v.2)⟩
    · obtain ⟨-, -, hYLC, ⟨y, hyY, hyle⟩, -⟩ :=
        (h37 G M A₁ hSS hA₁ a haA ha1 X hXM hXC hXeq).2.2.2 L hL hYL
      have hyN : y ∈ Subgroup.normalizer (L : Set G) :=
        (sup_le Subgroup.le_normalizer (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
          (hYLC hyY)
      have hyC : y ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
        normalizer_le_normalizer_centralizer_subgroup L hyN
      exact exists_ne_one_mem_of_le_zpowers_sup hyC (hVX.trans hyle) hVc
  obtain ⟨v, hv, hv1, hvL⟩ := key
  refine ⟨v, hv, hv1, fun l hl => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hvL l hl)

end ThreeSeven

end CFSG.Goldschmidt.G53
