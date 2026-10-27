module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalQuotientFrattini
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.OddInversion
public import CFSG.CharacterTheory.Semidihedral.PerfectLayerNormalization

public noncomputable section

namespace CFSG.Semidihedral.StationaryOddLocalization

open scoped Classical Pointwise IsKleinFour
open CFSG.SignalizerFunctor.Helpers
open CFSG.Wreathed.OriginalSylowNormalizerWitness

universe u v

variable {G : Type u} [Group G]

theorem conj_fixed_iff (t x : G) :
    t * x * t⁻¹ = x ↔ x ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (· * t) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem odd_card_of_pgroup [Finite G] {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell)
    (H : Subgroup G) (hH : IsPGroup ell H) : Odd (Nat.card H) := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  exact hellodd.pow

theorem fixed_on_conjugate_sylow
    {A : Type v} [Group A] [MulDistribMulAction A G]
    {ell : ℕ} (a : A) (P Q : Sylow ell G) (c : G)
    (hc : c • P = Q) (hcfix : a • c = c)
    (hPfix : ∀ x ∈ (P : Subgroup G), a • x = x) :
    ∀ x ∈ (Q : Subgroup G), a • x = x := by
  have hQ : (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  intro x hx
  rw [hQ] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change a • (c * y * c⁻¹) = c * y * c⁻¹
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv',
    hcfix, hPfix y hy]

theorem fixed_on_invariant_pgroups_of_fixed_sylow
    {A : Type v} [Group A] [Finite G] [MulDistribMulAction A G]
    {r ell : ℕ} (hr : r.Prime) (hell : ell.Prime) (hA : IsPGroup r A)
    (hcop : Nat.Coprime r (Nat.card G)) (a : A) (P : Sylow ell G)
    (hPInv : ∀ b : A, b • P = P)
    (hPfix : ∀ x ∈ (P : Subgroup G), a • x = x)
    (W : Subgroup G) (hWp : IsPGroup ell W)
    (hWInv : ∀ b : A, ∀ x ∈ W, b • x ∈ W) :
    ∀ x ∈ W, a • x = x := by
  obtain ⟨Q, hWQ, hQInv⟩ := invariant_sylow_containing r ell hr hell hA hcop W hWp hWInv
  obtain ⟨c, hc, hcfix⟩ := invariant_sylows_conjugate_by_fixed_element
    r ell hr hell A hA G hcop P Q hPInv hQInv
  exact fun x hx => fixed_on_conjugate_sylow a P Q c hc (hcfix a) hPfix x (hWQ hx)

theorem zpowers_involution_pgroup (t : G) (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [Nat.card_zpowers, pow_one] using ht

theorem invariant_sylow_containing_ambient [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t : G) (ht : orderOf t = 2)
    (R W : Subgroup G) (hRodd : Odd (Nat.card R))
    (htR : t ∈ Subgroup.normalizer (R : Set G))
    (hWR : W ≤ R) (hWp : IsPGroup ell W)
    (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    ∃ Q : Sylow ell R, W ≤ (Q : Subgroup R).map R.subtype ∧
      t ∈ Subgroup.normalizer ((Q : Subgroup R).map R.subtype : Set G) := by
  let A := Subgroup.zpowers t
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr htR
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr htW
  let _action := conjugationAction A R hAR
  obtain ⟨Q, hWQ, hQInv⟩ := invariant_sylow_containing 2 ell Nat.prime_two hell
    (zpowers_involution_pgroup t ht) hRodd.coprime_two_left
    (W.subgroupOf R) (hWp.comap_subtype)
    (normalized_subgroup_invariant_subgroup A R W hAR hAW)
  refine ⟨Q, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := R.subtype) hWQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hWR] at h
  · apply (invariant_subgroup_map_normalized A R hAR (Q : Subgroup R) ?_)
      (Subgroup.mem_zpowers t)
    change ∀ a : A, ∀ x ∈ (Q : Subgroup R), a • x ∈ (Q : Subgroup R)
    intro a x hx
    have himage := Subgroup.smul_mem_pointwise_smul x a (Q : Subgroup R) hx
    rw [← Sylow.pointwise_smul_def, hQInv] at himage
    exact himage

theorem centralized_invariant_pgroups_of_centralized_sylow [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t : G) (ht : orderOf t = 2)
    (R : Subgroup G) (hRodd : Odd (Nat.card R))
    (htR : t ∈ Subgroup.normalizer (R : Set G))
    (P : Sylow ell R)
    (htP : t ∈ Subgroup.normalizer ((P : Subgroup R).map R.subtype : Set G))
    (hPC : (P : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({t} : Set G))
    (W : Subgroup G) (hWR : W ≤ R) (hWp : IsPGroup ell W)
    (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    W ≤ Subgroup.centralizer ({t} : Set G) := by
  let A := Subgroup.zpowers t
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr htR
  have hAP : A ≤ Subgroup.normalizer ((P : Subgroup R).map R.subtype : Set G) :=
    Subgroup.zpowers_le.mpr htP
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.mpr htW
  let _action := conjugationAction A R hAR
  let a : A := ⟨t, Subgroup.mem_zpowers t⟩
  have hPfix : ∀ x ∈ (P : Subgroup R), a • x = x := by
    intro x hx
    apply Subtype.ext
    exact (conj_fixed_iff t x).mpr (hPC (Subgroup.mem_map_of_mem R.subtype hx))
  have hall := fixed_on_invariant_pgroups_of_fixed_sylow Nat.prime_two hell
    (zpowers_involution_pgroup t ht) hRodd.coprime_two_left a P
    (invariant_subgroup_sylow_fixed A R hAR ell P hAP) hPfix
    (W.subgroupOf R) (hWp.comap_subtype)
    (normalized_subgroup_invariant_subgroup A R W hAR hAW)
  intro x hx
  exact (conj_fixed_iff t x).mp
    (congrArg (fun z : R => (z : G)) (hall ⟨x, hWR hx⟩ hx))

theorem centralized_of_kernel_commutators [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (t : G) (ht : orderOf t = 2)
    (R W : Subgroup G) (hWp : IsPGroup ell W)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ w ∈ W, w⁻¹ * (t * w * t⁻¹) ∈ R)
    (hfixed : ∀ D : Subgroup G, D ≤ R → IsPGroup ell D →
      t ∈ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.centralizer ({t} : Set G)) :
    W ≤ Subgroup.centralizer ({t} : Set G) := by
  let D := Subgroup.closure {d : G | ∃ w ∈ W, d = w⁻¹ * (t * w * t⁻¹)}
  have hDW : D ≤ W := by
    apply (Subgroup.closure_le W).mpr
    rintro d ⟨w, hw, rfl⟩
    exact W.mul_mem (W.inv_mem hw) ((Subgroup.mem_normalizer_iff.mp htW w).mp hw)
  have hDR : D ≤ R := by
    apply (Subgroup.closure_le R).mpr
    rintro d ⟨w, hw, rfl⟩
    exact hcomm w hw
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro d
    constructor
    · intro hd
      have hmap : D.map (MulAut.conj t).toMonoidHom ≤ D := by
        change (Subgroup.closure {d : G | ∃ w ∈ W, d = w⁻¹ * (t * w * t⁻¹)}).map
          (MulAut.conj t).toMonoidHom ≤ D
        rw [MonoidHom.map_closure]
        apply (Subgroup.closure_le D).mpr
        rintro z ⟨d, ⟨w, hw, rfl⟩, rfl⟩
        apply Subgroup.subset_closure
        refine ⟨t * w * t⁻¹, (Subgroup.mem_normalizer_iff.mp htW w).mp hw, ?_⟩
        change (MulAut.conj t) (w⁻¹ * ((MulAut.conj t) w)) = _
        rw [map_mul, map_inv]
        rfl
      exact hmap (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hd)
    · intro hd
      have hmap : D.map (MulAut.conj t).toMonoidHom ≤ D := by
        change (Subgroup.closure {d : G | ∃ w ∈ W, d = w⁻¹ * (t * w * t⁻¹)}).map
          (MulAut.conj t).toMonoidHom ≤ D
        rw [MonoidHom.map_closure]
        apply (Subgroup.closure_le D).mpr
        rintro z ⟨d, ⟨w, hw, rfl⟩, rfl⟩
        apply Subgroup.subset_closure
        refine ⟨t * w * t⁻¹, (Subgroup.mem_normalizer_iff.mp htW w).mp hw, ?_⟩
        change (MulAut.conj t) (w⁻¹ * ((MulAut.conj t) w)) = _
        rw [map_mul, map_inv]
        rfl
      have h := hmap (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hd)
      change t * (t * d * t⁻¹) * t⁻¹ ∈ D at h
      rwa [CFSG.OddInversion.conj_conj_of_orderOf_eq_two ht d] at h
  have hDC := hfixed D hDR (hWp.to_le hDW) htD
  intro w hw
  let d := w⁻¹ * (t * w * t⁻¹)
  have hdD : d ∈ D := Subgroup.subset_closure ⟨w, hw, rfl⟩
  have hdfix : t * d * t⁻¹ = d := (conj_fixed_iff t d).mpr (hDC hdD)
  have hdInv : t * d * t⁻¹ = d⁻¹ := by
    dsimp [d]
    change (MulAut.conj t) (w⁻¹ * ((MulAut.conj t) w)) = _
    rw [map_mul, map_inv]
    change (t * w * t⁻¹)⁻¹ * (t * (t * w * t⁻¹) * t⁻¹) = _
    rw [CFSG.OddInversion.conj_conj_of_orderOf_eq_two ht]
    group
  have hdsq : d ^ 2 = 1 := by
    calc
      d ^ 2 = d * d := pow_two d
      _ = d⁻¹ * d := congrArg (· * d) (hdfix.symm.trans hdInv)
      _ = 1 := inv_mul_cancel d
  have hd1 : d = 1 := CFSG.OddInversion.sq_injOn
    (odd_card_of_pgroup hell hellodd W hWp) (hDW hdD) W.one_mem (by simpa using hdsq)
  apply (conj_fixed_iff t w).mp
  exact (inv_mul_eq_one.mp hd1).symm

theorem normalizer_step_index [Finite G] {ell : ℕ} (hell : ell.Prime)
    (P U : Subgroup G) (hP : IsPGroup ell P) (hUP : U < P) :
    U < P ⊓ Subgroup.normalizer (U : Set G) ∧
      (P ⊓ Subgroup.normalizer (U : Set G)).relIndex P < U.relIndex P := by
  let : Fact ell.Prime := ⟨hell⟩
  have hinternal : U.subgroupOf P < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro h
    have hmap := congrArg (Subgroup.map P.subtype) h
    rw [Subgroup.map_subgroupOf_eq_of_le hUP.le, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    exact hUP.ne hmap
  have hn := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition hP hinternal
  rw [← Subgroup.subgroupOf_normalizer_eq hUP.le] at hn
  have hlt : U < P ⊓ Subgroup.normalizer (U : Set G) := by
    apply lt_of_le_of_ne (le_inf hUP.le Subgroup.le_normalizer)
    intro h
    have hsub := congrArg (fun K : Subgroup G => K.subgroupOf P) h
    have hinf : (P ⊓ Subgroup.normalizer (U : Set G)).subgroupOf P =
        (Subgroup.normalizer (U : Set G)).subgroupOf P := by
      ext x
      exact and_iff_right x.property
    rw [hinf] at hsub
    exact hn.ne hsub
  refine ⟨hlt, ?_⟩
  change ((P ⊓ Subgroup.normalizer (U : Set G)).subgroupOf P).index <
    (U.subgroupOf P).index
  apply Subgroup.index_strictAnti
  apply lt_of_le_of_ne (Subgroup.subgroupOf_mono P hlt.le)
  intro h
  have hmap := congrArg (Subgroup.map P.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hUP.le,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  exact hlt.ne hmap

theorem involution_zpowers_square (t : G) (ht : orderOf t = 2)
    (x : Subgroup.zpowers t) : x ^ 2 = 1 := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
  change (x : G) ^ 2 = 1
  rw [← hk, ← ht]
  exact zpow_pow_orderOf

theorem odd_pgroup_inverted_centralizing_witness [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell)
    (t : G) (ht : orderOf t = 2) (Q : Subgroup G) (hQp : IsPGroup ell Q)
    (htQ : t ∈ Subgroup.normalizer (Q : Set G))
    (hQnot : ¬ Q ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ x ∈ Q, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ ∧
      (∀ y ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), Commute x y) ∧
      x ∉ Subgroup.centralizer ({t} : Set G) := by
  let T := Subgroup.zpowers t
  let A := T × T
  let : Monoid A := (inferInstance : Group A).toMonoid
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  let a : A := (⟨t, Subgroup.mem_zpowers t⟩, 1)
  let b : A := (1, ⟨t, Subgroup.mem_zpowers t⟩)
  have ha : a ≠ 1 := by
    intro h
    exact ht1 (congrArg (fun z : A => (z.1 : G)) h)
  have hb : b ≠ 1 := by
    intro h
    exact ht1 (congrArg (fun z : A => (z.2 : G)) h)
  have hab : a ≠ b := by
    intro h
    exact ht1 (congrArg (fun z : A => (z.1 : G)) h)
  have hA2 : ∀ z : A, z ^ 2 = 1 := by
    intro z
    apply Prod.ext
    · exact involution_zpowers_square t ht z.1
    · exact involution_zpowers_square t ht z.2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsKleinFour A := {
    card_four := by simp [A, T, Nat.card_zpowers, ht]
    exponent_two := Nat.dvd_antisymm
      (Monoid.exponent_dvd_of_forall_pow_eq_one hA2)
      (by
        have hao : orderOf a = 2 := orderOf_eq_prime (hA2 a) ha
        exact hao ▸ Monoid.order_dvd_exponent a) }
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr htQ
  let _tAction := conjugationAction T Q hTQ
  let _aAction : MulDistribMulAction A Q :=
    MulDistribMulAction.compHom Q (MonoidHom.fst T T)
  have hF : actionCentralizer (X := Q) a ≠ ⊤ := by
    intro hFtop
    apply hQnot
    intro x hx
    have hfix := (mem_actionCentralizer (a := a) (g := (⟨x, hx⟩ : Q))).mp
      (hFtop ▸ Subgroup.mem_top _)
    exact (conj_fixed_iff t x).mp (congrArg (fun z : Q => (z : G)) hfix)
  obtain ⟨c, _, x, hx1, hxinv, _, hxcomm, hxnot⟩ :=
    four_group_odd_p_group_centralizing_inverted_witness
      hell hellodd hQp a b ha hb hab hF
  refine ⟨x, x.property, ?_, ?_, ?_, ?_⟩
  · intro hx
    exact hx1 (Subtype.ext hx)
  · exact congrArg (fun z : Q => (z : G)) hxinv
  · intro y hy
    let yQ : Q := ⟨y, hy.1⟩
    have hyfix : yQ ∈ actionCentralizer (X := Q) a := by
      apply (mem_actionCentralizer (a := a) (g := yQ)).mpr
      apply Subtype.ext
      exact (conj_fixed_iff t y).mpr hy.2
    exact (hxcomm yQ hyfix).map Q.subtype
  · intro hxC
    apply hxnot
    apply (mem_actionCentralizer (a := a) (g := x)).mpr
    apply Subtype.ext
    exact (conj_fixed_iff t x).mpr hxC

theorem kernel_commutators_of_factorization
    (H R : Subgroup G) (hRH : R ≤ H) (hRnormal : (R.subgroupOf H).Normal)
    (t : G) (htH : t ∈ H)
    (hfactor : R ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H) :
    ∀ w ∈ H, w⁻¹ * (t * w * t⁻¹) ∈ R := by
  let R0 := R.subgroupOf H
  let : R0.Normal := hRnormal
  let q := QuotientGroup.mk' R0
  let tH : H := ⟨t, htH⟩
  have hfull : R0 ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hRH inf_le_left, hfactor, Subgroup.subgroupOf_self]
  intro w hw
  let wH : H := ⟨w, hw⟩
  obtain ⟨r, hr, c, hc, hrc⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hfull ▸ Subgroup.mem_top wH)
  have hqr : q r = 1 := (QuotientGroup.eq_one_iff (N := R0) (x := r)).mpr hr
  have hqc : q wH = q c := by rw [← hrc, map_mul, hqr, one_mul]
  have hct : Commute tH c := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
  have hqcomm : q (wH⁻¹ * (tH * wH * tH⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hqc,
      (hct.map q).mul_inv_cancel, inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff (N := R0) (x := wH⁻¹ * (tH * wH * tH⁻¹))).mp hqcomm

theorem centralized_pgroups_of_sylow_and_factorization [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (t : G) (ht : orderOf t = 2)
    (H R : Subgroup G) (hRH : R ≤ H) (hRnormal : (R.subgroupOf H).Normal)
    (hRodd : Odd (Nat.card R)) (htH : t ∈ H)
    (hfactor : R ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H)
    (P : Sylow ell R)
    (htP : t ∈ Subgroup.normalizer ((P : Subgroup R).map R.subtype : Set G))
    (hPC : (P : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({t} : Set G))
    (W : Subgroup G) (hWH : W ≤ H) (hWp : IsPGroup ell W)
    (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    W ≤ Subgroup.centralizer ({t} : Set G) := by
  have htR : t ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRnormal htH
  apply centralized_of_kernel_commutators hell hellodd t ht R W hWp htW
  · exact fun w hw => kernel_commutators_of_factorization H R hRH hRnormal t htH
      hfactor w (hWH hw)
  · exact fun D hDR hDp htD => centralized_invariant_pgroups_of_centralized_sylow
      hell t ht R hRodd htR P htP hPC D hDR hDp htD

theorem ambient_normal_sylow_intersection [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H R : Subgroup G) (hRH : R ≤ H)
    (hRnormal : (R.subgroupOf H).Normal) (Q : Sylow ell H) :
    ∃ P : Sylow ell R,
      (P : Subgroup R).map R.subtype = R ⊓ (Q : Subgroup H).map H.subtype := by
  let R0 := R.subgroupOf H
  let : R0.Normal := hRnormal
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨P0, hP0⟩ := normal_subgroup_sylow_intersection ell hell R0 Q
  let e := Subgroup.subgroupOfEquivOfLe hRH
  have heSurj : Function.Surjective e.toMonoidHom := e.surjective
  let P := P0.mapSurjective (f := e.toMonoidHom) heSurj
  refine ⟨P, ?_⟩
  have he : R.subtype.comp e.toMonoidHom = H.subtype.comp R0.subtype := by
    ext x
    rfl
  have hPcoe : (P : Subgroup R) = (P0 : Subgroup R0).map e.toMonoidHom :=
    Sylow.coe_mapSurjective heSurj P0
  rw [hPcoe, Subgroup.map_map, he, ← Subgroup.map_map, hP0]
  rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hRH]

theorem odd_card_sup_in_parent
    (H R B : Subgroup G) (hRH : R ≤ H) (hBH : B ≤ H)
    (hRnormal : (R.subgroupOf H).Normal)
    (hRodd : Odd (Nat.card R)) (hBodd : Odd (Nat.card B)) :
    Odd (Nat.card (R ⊔ B : Subgroup G)) := by
  let : (R.subgroupOf H).Normal := hRnormal
  have hRodd0 : Odd (Nat.card (R.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
    exact hRodd
  have hBodd0 : Odd (Nat.card (B.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv]
    exact hBodd
  have h := CFSG.ComponentClassification.OddCore.odd_card_sup
    (R.subgroupOf H) (B.subgroupOf H) hRodd0 hBodd0
  rw [← Subgroup.subgroupOf_sup hRH hBH,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hRH hBH)).toEquiv] at h
  exact h

theorem stationary_localization_from_actual_factorizations [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (t : G) (ht : orderOf t = 2)
    (V P : Subgroup G) (htV : t ∈ V) (hPp : IsPGroup ell P)
    (hVP : V ≤ Subgroup.normalizer (P : Set G))
    (hPC : P ≤ Subgroup.centralizer ({t} : Set G))
    (hstationary : ∃ P0 : Sylow ell (ambientOddCore (Subgroup.normalizer (P : Set G))),
      (P0 : Subgroup _).map (ambientOddCore (Subgroup.normalizer (P : Set G))).subtype = P)
    (hfactor : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P →
      V ≤ Subgroup.normalizer (U : Set G) →
      ambientOddCore (Subgroup.normalizer (U : Set G)) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
          Subgroup.normalizer (U : Set G)) :
    ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P → V ≤ Subgroup.normalizer (U : Set G) →
      ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ Subgroup.centralizer ({t} : Set G) := by
  have hall : ∀ n : ℕ, ∀ U : Subgroup G, U.relIndex P = n → U ≠ ⊥ → U ≤ P →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ Subgroup.centralizer ({t} : Set G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hindex hU hUP hVU W hWH hWp htW
      let H := Subgroup.normalizer (U : Set G)
      let R := ambientOddCore H
      have hRH : R ≤ H := ambientOddCore_le H
      have hRnormal : (R.subgroupOf H).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr (ambientOddCore_normalized H)
      have hRodd : Odd (Nat.card R) := ambientOddCore_odd H
      have htH : t ∈ H := hVU htV
      have htR : t ∈ Subgroup.normalizer (R : Set G) := ambientOddCore_normalized H htH
      have hfac := hfactor U hU hUP hVU
      by_cases hUeq : U = P
      · subst U
        obtain ⟨P0, hP0⟩ := hstationary
        apply centralized_pgroups_of_sylow_and_factorization hell hellodd t ht H R
          hRH hRnormal hRodd htH hfac P0
        · rw [hP0]
          exact hVP htV
        · rw [hP0]
          exact hPC
        · exact hWH
        · exact hWp
        · exact htW
      · let P1 := P ⊓ H
        have hstep := normalizer_step_index hell P U hPp (lt_of_le_of_ne hUP hUeq)
        have hUP1 : U ≤ P1 := hstep.1.le
        have hP1P : P1 ≤ P := inf_le_left
        have hP1H : P1 ≤ H := inf_le_right
        have hP1 : P1 ≠ ⊥ := by
          intro hbot
          exact hU (le_antisymm (hUP1.trans_eq hbot) bot_le)
        have hVP1 : V ≤ Subgroup.normalizer (P1 : Set G) :=
          (le_inf hVP (hVU.trans H.le_normalizer)).trans
            Subgroup.inf_normalizer_le_normalizer_inf
        have htP1 : t ∈ Subgroup.normalizer (P1 : Set G) := hVP1 htV
        have hP1C : P1 ≤ Subgroup.centralizer ({t} : Set G) := hP1P.trans hPC
        have hsmaller : P1.relIndex P < n := hstep.2.trans_eq hindex
        have hind := ih (P1.relIndex P) hsmaller P1 rfl hP1 hP1P hVP1
        by_contra hWC
        let M := R ⊔ P1
        have hMH : M ≤ H := sup_le hRH hP1H
        have hRM : R ≤ M := le_sup_left
        have hP1M : P1 ≤ M := le_sup_right
        have hModd : Odd (Nat.card M) := odd_card_sup_in_parent H R P1 hRH hP1H
          hRnormal hRodd (odd_card_of_pgroup hell hellodd P1 (hPp.to_le hP1P))
        have htM : t ∈ Subgroup.normalizer (M : Set G) :=
          (Subgroup.inf_normalizer_le_normalizer_sup R P1) ⟨htR, htP1⟩
        obtain ⟨Q, hP1Q, htQ⟩ := invariant_sylow_containing_ambient hell t ht M P1
          hModd htM hP1M (hPp.to_le hP1P) htP1
        let QG := (Q : Subgroup M).map M.subtype
        have hRnormalM : (R.subgroupOf M).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer
            (hMH.trans (ambientOddCore_normalized H))
        obtain ⟨S, hS⟩ := ambient_normal_sylow_intersection hell M R hRM hRnormalM Q
        have htS : t ∈ Subgroup.normalizer ((S : Subgroup R).map R.subtype : Set G) := by
          rw [hS]
          exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htR, htQ⟩
        have hQnot : ¬ QG ≤ Subgroup.centralizer ({t} : Set G) := by
          intro hQC
          apply hWC
          apply centralized_pgroups_of_sylow_and_factorization hell hellodd t ht H R
            hRH hRnormal hRodd htH hfac S htS
          · rw [hS]
            exact inf_le_right.trans hQC
          · exact hWH
          · exact hWp
          · exact htW
        obtain ⟨x, hxQ, hx1, hxinv, hxcomm, _⟩ :=
          odd_pgroup_inverted_centralizing_witness hell hellodd t ht QG
            (Q.isPGroup'.map M.subtype) htQ hQnot
        have hxC : x ∈ Subgroup.centralizer (P1 : Set G) := by
          apply Subgroup.mem_centralizer_iff.mpr
          intro y hy
          exact (hxcomm y ⟨hP1Q hy, hP1C hy⟩).eq.symm
        have hxN : x ∈ Subgroup.normalizer (P1 : Set G) :=
          Subgroup.centralizer_le_normalizer (P1 : Set G) hxC
        let X := Subgroup.zpowers x
        have hXQ : X ≤ QG := Subgroup.zpowers_le.mpr hxQ
        have hXN : X ≤ Subgroup.normalizer (P1 : Set G) := Subgroup.zpowers_le.mpr hxN
        have htX : t ∈ Subgroup.normalizer (X : Set G) := by
          apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          rw [MonoidHom.map_zpowers]
          change Subgroup.zpowers (t * x * t⁻¹) = X
          rw [hxinv, Subgroup.zpowers_inv]
        have hXC := hind X hXN ((Q.isPGroup'.map M.subtype).to_le hXQ) htX
        have hxfix := (conj_fixed_iff t x).mpr (hXC (Subgroup.mem_zpowers x))
        have hxsq : x ^ 2 = 1 := by
          calc
            x ^ 2 = x * x := pow_two x
            _ = x⁻¹ * x := congrArg (· * x) (hxfix.symm.trans hxinv)
            _ = 1 := inv_mul_cancel x
        exact hx1 (CFSG.OddInversion.sq_injOn hModd
          ((Subgroup.map_subtype_le (Q : Subgroup M)) hxQ) M.one_mem
          (by simpa using hxsq))
  intro U hU hUP hVU
  exact hall (U.relIndex P) U rfl hU hUP hVU

theorem normalized_map_of_fixed (e : G ≃* G) (V U : Subgroup G)
    (heV : ∀ v ∈ V, e v = v) (hVU : V ≤ Subgroup.normalizer (U : Set G)) :
    V ≤ Subgroup.normalizer (U.map e.toMonoidHom : Set G) := by
  intro v hv
  have h := Subgroup.mem_map_of_mem e.toMonoidHom (hVU hv)
  rw [Subgroup.map_equiv_normalizer_eq] at h
  change e v ∈ Subgroup.normalizer (U.map e.toMonoidHom : Set G) at h
  rwa [heV v hv] at h

theorem centralized_of_map_fixed (e : G ≃* G) (t : G) (het : e t = t)
    (W : Subgroup G)
    (hmap : W.map e.toMonoidHom ≤ Subgroup.centralizer ({t} : Set G)) :
    W ≤ Subgroup.centralizer ({t} : Set G) := by
  intro w hw
  apply (conj_fixed_iff t w).mp
  apply e.injective
  simp only [map_mul, map_inv, het]
  exact (conj_fixed_iff t (e w)).mpr (hmap (Subgroup.mem_map_of_mem e.toMonoidHom hw))

theorem localization_map_fixed_automorphism
    (t : G) (V P : Subgroup G) (e : G ≃* G) (het : e t = t)
    (heV : ∀ v ∈ V, e v = v) {ell : ℕ}
    (hloc : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P → V ≤ Subgroup.normalizer (U : Set G) →
      ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) → W ≤ Subgroup.centralizer ({t} : Set G))
    (U : Subgroup G) (hU : U ≠ ⊥) (hUP : U ≤ P.map e.toMonoidHom)
    (hVU : V ≤ Subgroup.normalizer (U : Set G))
    (W : Subgroup G) (hWN : W ≤ Subgroup.normalizer (U : Set G))
    (hWp : IsPGroup ell W) (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    W ≤ Subgroup.centralizer ({t} : Set G) := by
  have hsymt : e.symm t = t := by
    apply e.injective
    rw [e.apply_symm_apply, het]
  have hsymV : ∀ v ∈ V, e.symm v = v := by
    intro v hv
    apply e.injective
    rw [e.apply_symm_apply, heV v hv]
  let U0 := U.map e.symm.toMonoidHom
  let W0 := W.map e.symm.toMonoidHom
  have hU0 : U0 ≠ ⊥ := by
    intro hbot
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U e.symm.injective).mp hbot)
  have hU0P : U0 ≤ P := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hUP
    rw [Subgroup.map_map] at h
    have heid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    rwa [heid, Subgroup.map_id] at h
  have hVU0 : V ≤ Subgroup.normalizer (U0 : Set G) :=
    normalized_map_of_fixed e.symm V U hsymV hVU
  have hW0N : W0 ≤ Subgroup.normalizer (U0 : Set G) := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hWN
    rwa [Subgroup.map_equiv_normalizer_eq] at h
  have htW0 : t ∈ Subgroup.normalizer (W0 : Set G) := by
    have h := Subgroup.mem_map_of_mem e.symm.toMonoidHom htW
    rw [Subgroup.map_equiv_normalizer_eq] at h
    change e.symm t ∈ Subgroup.normalizer (W0 : Set G) at h
    rwa [hsymt] at h
  exact centralized_of_map_fixed e.symm t hsymt W
    (hloc U0 hU0 hU0P hVU0 W0 hW0N (hWp.map e.symm.toMonoidHom) htW0)

theorem inverted_of_trivial_fixed_subgroup (t : G) (ht : orderOf t = 2)
    (W : Subgroup G) (hWodd : Odd (Nat.card W))
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ := by
  intro w hw
  obtain ⟨⟨c, x⟩, ⟨hc, hx⟩, hcx⟩ :=
    (CFSG.OddInversion.odd_involution_product_decomposition hWodd ht htW).1.surjOn hw
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hfixed ▸ hc)
  have hxw : x = w := by simpa only [hc1, one_mul] using hcx
  exact hxw ▸ hx.2

theorem abelian_of_inverted (t : G) (W : Subgroup G)
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : IsMulCommutative W := by
  constructor
  constructor
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  have h := hinv ((x : G) * (y : G)) (W.mul_mem x.property y.property)
  change (MulAut.conj t) ((x : G) * (y : G)) = _ at h
  rw [map_mul, mul_inv_rev] at h
  change (t * (x : G) * t⁻¹) * (t * (y : G) * t⁻¹) = (y : G)⁻¹ * (x : G)⁻¹ at h
  rw [hinv x x.property, hinv y y.property] at h
  have h' := congrArg Inv.inv h
  simpa only [mul_inv_rev, inv_inv] using h'.symm

theorem trivial_fixed_subgroup_of_inverted (t : G)
    (W : Subgroup G) (hWodd : Odd (Nat.card W))
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) :
    W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  apply Subgroup.mem_bot.mpr
  have heq : w = w⁻¹ := ((conj_fixed_iff t w).mpr hw.2).symm.trans (hinv w hw.1)
  have hsq : w ^ 2 = 1 := by
    calc
      w ^ 2 = w * w := pow_two w
      _ = w⁻¹ * w := congrArg (· * w) heq
      _ = 1 := inv_mul_cancel w
  exact CFSG.OddInversion.sq_injOn hWodd hw.1 W.one_mem (by simpa using hsq)

theorem invariant_pgroup_le_fixed_conjugate_sylow [Finite G]
    {ell : ℕ} (hell : ell.Prime) (V N F : Subgroup G) (hV2 : IsPGroup 2 V)
    (hVN : V ≤ Subgroup.normalizer (N : Set G)) (hNodd : Odd (Nat.card N))
    (P : Sylow ell N)
    (hVP : V ≤ Subgroup.normalizer ((P : Subgroup N).map N.subtype : Set G))
    (hFN : F ≤ N) (hFp : IsPGroup ell F)
    (hVF : V ≤ Subgroup.normalizer (F : Set G)) :
    ∃ c ∈ N ⊓ Subgroup.centralizer (V : Set G),
      F ≤ ((P : Subgroup N).map N.subtype).map (MulAut.conj c).toMonoidHom := by
  let _action := conjugationAction V N hVN
  obtain ⟨Q, hFQ, hQInv⟩ := invariant_sylow_containing 2 ell Nat.prime_two hell
    hV2 hNodd.coprime_two_left (F.subgroupOf N) (hFp.comap_subtype)
    (normalized_subgroup_invariant_subgroup V N F hVN hVF)
  obtain ⟨c, hc, hcfix⟩ := invariant_sylows_conjugate_by_fixed_element
    2 ell Nat.prime_two hell V hV2 N hNodd.coprime_two_left P Q
    (invariant_subgroup_sylow_fixed V N hVN ell P hVP) hQInv
  have hcc : (c : G) ∈ Subgroup.centralizer (V : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    have hfix := congrArg (fun z : N => (z : G)) (hcfix (⟨v, hv⟩ : V))
    have hcv : (c : G) * v = v * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp ((conj_fixed_iff v c).mp hfix)
    exact hcv.symm
  have hQ : (Q : Subgroup N).map N.subtype =
      ((P : Subgroup N).map N.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
    have hs := congrArg (fun S : Sylow ell N => (S : Subgroup N).map N.subtype) hc
    rw [Sylow.coe_subgroup_smul] at hs
    change ((P : Subgroup N).map (MulAut.conj c).toMonoidHom).map N.subtype = _ at hs
    rw [Subgroup.map_map] at hs
    rw [Subgroup.map_map]
    exact hs.symm
  refine ⟨c, ⟨c.property, hcc⟩, ?_⟩
  rw [← hQ, ← Subgroup.map_subgroupOf_eq_of_le hFN]
  exact Subgroup.map_mono hFQ

theorem scalar_dichotomy_from_original_localization [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (t : G) (ht : orderOf t = 2)
    (V N : Subgroup G) (htV : t ∈ V) (hV2 : IsPGroup 2 V)
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G))
    (hVN : V ≤ Subgroup.normalizer (N : Set G)) (hNodd : Odd (Nat.card N))
    (hNC : N ≤ Subgroup.centralizer ({t} : Set G))
    (P : Sylow ell N)
    (hVP : V ≤ Subgroup.normalizer ((P : Subgroup N).map N.subtype : Set G))
    (hloc : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ (P : Subgroup N).map N.subtype →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ Subgroup.centralizer ({t} : Set G))
    (W : Subgroup G) (hWp : IsPGroup ell W)
    (hVW : V ≤ Subgroup.normalizer (W : Set G))
    (hfixedN : W ⊓ Subgroup.centralizer ({t} : Set G) ≤ N) :
    (W ≤ N ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
      ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) →
        IsMulCommutative W ∧ W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) ∧
      (W ≠ ⊥ → ¬ (W ≤ N ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) := by
  have hWodd := odd_card_of_pgroup hell hellodd W hWp
  have htW := hVW htV
  let F := W ⊓ Subgroup.centralizer ({t} : Set G)
  have hFcases : F = W ∨ F = ⊥ := by
    by_contra hcases
    have hFW : F ≠ W := fun h => hcases (Or.inl h)
    have hFbot : F ≠ ⊥ := fun h => hcases (Or.inr h)
    have hVF : V ≤ Subgroup.normalizer (F : Set G) :=
      (le_inf hVW (hVC.trans (Subgroup.centralizer ({t} : Set G)).le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    obtain ⟨c, hc, hFcP⟩ := invariant_pgroup_le_fixed_conjugate_sylow hell V N F hV2
      hVN hNodd P hVP hfixedN (hWp.to_le inf_le_left) hVF
    have hcV : ∀ v ∈ V, (MulAut.conj c) v = v := by
      intro v hv
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 v hv
      change c * v * c⁻¹ = v
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hct : (MulAut.conj c) t = t := hcV t htV
    have hWnot : ¬ W ≤ Subgroup.centralizer ({t} : Set G) := by
      intro hWC
      exact hFW (inf_eq_left.mpr hWC)
    obtain ⟨x, hxW, hx1, hxinv, hxcomm, hxnot⟩ :=
      odd_pgroup_inverted_centralizing_witness hell hellodd t ht W hWp htW hWnot
    have hxCF : x ∈ Subgroup.centralizer (F : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      exact (hxcomm y hy).eq.symm
    let X := Subgroup.zpowers x
    have hXN : X ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (F : Set G) hxCF)
    have hXW : X ≤ W := Subgroup.zpowers_le.mpr hxW
    have htX : t ∈ Subgroup.normalizer (X : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (t * x * t⁻¹) = X
      rw [hxinv, Subgroup.zpowers_inv]
    have hXC := localization_map_fixed_automorphism t V
      ((P : Subgroup N).map N.subtype) (MulAut.conj c) hct hcV hloc
      F hFbot hFcP hVF X hXN (hWp.to_le hXW) htX
    exact hxnot (hXC (Subgroup.mem_zpowers x))
  have hscalar : W ≤ N ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ := by
    rcases hFcases with hFW | hFbot
    · exact Or.inl (hFW ▸ hfixedN)
    · exact Or.inr (inverted_of_trivial_fixed_subgroup t ht W hWodd htW hFbot)
  refine ⟨hscalar, ?_, ?_⟩
  · intro hinv
    exact ⟨abelian_of_inverted t W hinv, trivial_fixed_subgroup_of_inverted t W hWodd hinv⟩
  · intro hWne ⟨hWN, hinv⟩
    have hWfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = W :=
      inf_eq_left.mpr (hWN.trans hNC)
    have hbot := trivial_fixed_subgroup_of_inverted t W hWodd hinv
    exact hWne (hWfixed.symm.trans hbot)

theorem centralizer_zpowers_eq (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers t))
  · intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact (hxt.zpow_right k).eq.symm

theorem localization_commutator_conclusion (t : G) (W : Subgroup G)
    (hWC : W ≤ Subgroup.centralizer ({t} : Set G)) :
    ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w := by
  constructor
  · apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rwa [centralizer_zpowers_eq]
  · exact fun w hw => (conj_fixed_iff t w).mpr (hWC hw)

theorem closure_pair_eq_zpowers_sup (t s : G) :
    Subgroup.closure ({t, s} : Set G) = Subgroup.zpowers t ⊔ Subgroup.zpowers s := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · apply sup_le
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

theorem original_involution_pair_properties (t s : G)
    (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ Subgroup.centralizer ({t} : Set G)) :
    t ∈ Subgroup.closure ({t, s} : Set G) ∧
      IsPGroup 2 (Subgroup.closure ({t, s} : Set G)) ∧
      Subgroup.closure ({t, s} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  refine ⟨Subgroup.subset_closure (by simp), ?_, ?_⟩
  · rw [closure_pair_eq_zpowers_sup]
    apply (zpowers_involution_pgroup t ht).to_sup_of_normal_left'
      (zpowers_involution_pgroup s hs)
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer (Subgroup.zpowers t : Set G)
    rwa [centralizer_zpowers_eq]
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact hsC

theorem centralizer_cover_descends {Q : Type v} [Group Q]
    (C : Subgroup G) (f : C →* Q) (T : Subgroup Q) (P U : Subgroup G)
    (hUP : U ≤ P)
    (hcover : ((Subgroup.centralizer (P : Set G)).subgroupOf C ⊓ T.comap f).map f = T) :
    ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f = T := by
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · calc
      T = ((Subgroup.centralizer (P : Set G)).subgroupOf C ⊓ T.comap f).map f :=
        hcover.symm
      _ ≤ ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f :=
        Subgroup.map_mono (inf_le_inf
          (Subgroup.subgroupOf_mono C (Subgroup.centralizer_le hUP)) le_rfl)

theorem prime_divisor_of_odd_subgroup {ell : ℕ} (N : Subgroup G)
    (hNodd : Odd (Nat.card N)) (hellN : ell ∣ Nat.card N) : Odd ell :=
  hNodd.of_dvd_nat hellN

theorem fixed_points_in_odd_subgroup_of_core_intersection
    (t : G) (H N W : Subgroup G) (hWR : W ≤ ambientOddCore H)
    (hinter : ambientOddCore H ⊓ Subgroup.centralizer ({t} : Set G) = N ⊓ H) :
    W ⊓ Subgroup.centralizer ({t} : Set G) ≤ N := by
  exact ((inf_le_inf hWR le_rfl).trans_eq hinter).trans inf_le_left

theorem scalar_dichotomy_on_original_local_odd_core [Finite G]
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (t : G) (ht : orderOf t = 2)
    (V N : Subgroup G) (htV : t ∈ V) (hV2 : IsPGroup 2 V)
    (hVC : V ≤ Subgroup.centralizer ({t} : Set G))
    (hVN : V ≤ Subgroup.normalizer (N : Set G)) (hNodd : Odd (Nat.card N))
    (hNC : N ≤ Subgroup.centralizer ({t} : Set G)) (P : Sylow ell N)
    (hVP : V ≤ Subgroup.normalizer ((P : Subgroup N).map N.subtype : Set G))
    (hloc : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ (P : Subgroup N).map N.subtype →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ Subgroup.centralizer ({t} : Set G))
    (H : Subgroup G)
    (hinter : ambientOddCore H ⊓ Subgroup.centralizer ({t} : Set G) = N ⊓ H)
    (W : Subgroup G) (hWR : W ≤ ambientOddCore H) (hWp : IsPGroup ell W)
    (hVW : V ≤ Subgroup.normalizer (W : Set G)) :
    (W ≤ N ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
      ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) →
        IsMulCommutative W ∧ W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) ∧
      (W ≠ ⊥ → ¬ (W ≤ N ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
      (¬ W ≤ Subgroup.centralizer ({t} : Set G) →
        IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  have hfixedN := fixed_points_in_odd_subgroup_of_core_intersection t H N W hWR hinter
  obtain ⟨hscalar, hinverted, hdisjoint⟩ := scalar_dichotomy_from_original_localization
    hell hellodd t ht V N htV hV2 hVC hVN hNodd hNC P hVP hloc W hWp hVW hfixedN
  refine ⟨hscalar, hinverted, hdisjoint, ?_⟩
  intro hnotC
  rcases hscalar with hWN | hinv
  · exact False.elim (hnotC (hWN.trans hNC))
  · exact ⟨(hinverted hinv).1, hinv⟩

theorem original_oddCore_eq_twoPrimeCore {H : Type v} [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext R
  exact and_congr_right (fun _ => Nat.coprime_two_left.symm)

theorem ambient_sylow_from_intrinsic [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H : Subgroup G) (R : Subgroup H) (P : Sylow ell R) :
    ∃ Q : Sylow ell (R.map H.subtype),
      (Q : Subgroup (R.map H.subtype)).map (R.map H.subtype).subtype =
        ((P : Subgroup R).map R.subtype).map H.subtype := by
  let : Fact ell.Prime := ⟨hell⟩
  let e := R.equivMapOfInjective H.subtype H.subtype_injective
  have he : Function.Surjective e.toMonoidHom := by
    intro y
    refine ⟨e.symm y, ?_⟩
    exact e.apply_symm_apply y
  refine ⟨P.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective he P, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem stationary_sylow_from_intrinsic_core [Finite G] {ell : ℕ} (hell : ell.Prime)
    (P : Subgroup G)
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (P : Set G))).subtype).map
          (Subgroup.normalizer (P : Set G)).subtype = P) :
    ∃ P0 : Sylow ell (ambientOddCore (Subgroup.normalizer (P : Set G))),
      (P0 : Subgroup _).map (ambientOddCore (Subgroup.normalizer (P : Set G))).subtype = P :=
  by
  obtain ⟨P0, hP0⟩ := hstationary
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore]
  obtain ⟨Q, hQ⟩ := ambient_sylow_from_intrinsic hell (Subgroup.normalizer (P : Set G))
    (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))) P0
  exact ⟨Q, hQ.trans hP0⟩

section ActualCentralizer

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem actual_centralizer_core_odd [Finite G] (t : G) :
    Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem actual_centralizer_ambient_core (t : G) :
    ambientOddCore (C t) = (N t).map (C t).subtype := by
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore]

theorem actual_centralizer_core_normalized (t : G) (V : Subgroup G) (hVC : V ≤ C t) :
    V ≤ Subgroup.normalizer ((N t).map (C t).subtype : Set G) :=
  characteristic_subgroup_map_normalized V (C t) (hVC.trans (C t).le_normalizer) (N t)

theorem actual_stationary_localization_of_cover_factorizations [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t : G) (ht : orderOf t = 2)
    (V : Subgroup G) (htV : t ∈ V) (P : Sylow ell (N t))
    (hellN : ell ∣ Nat.card (N t))
    (hVP : V ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
    (hfactor : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ (N t).map (C t).subtype →
      V ≤ Subgroup.normalizer (U : Set G) →
      ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ambientOddCore (Subgroup.normalizer (U : Set G)) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ C t) = Subgroup.normalizer (U : Set G)) :
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa → V ≤ Subgroup.normalizer (U : Set G) →
      (∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w) ∧
      (∀ W : Subgroup G, W ≤ Subgroup.centralizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w) := by
  intro Pa U hU hUP hVU
  have hellodd : Odd ell := (actual_centralizer_core_odd t).of_dvd_nat hellN
  have hPp : IsPGroup ell Pa := (P.isPGroup'.map (N t).subtype).map (C t).subtype
  have hPN : Pa ≤ (N t).map (C t).subtype :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hPC : Pa ≤ C t := Subgroup.map_subtype_le _
  have hlocal : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa →
      V ≤ Subgroup.normalizer (U : Set G) →
      ambientOddCore (Subgroup.normalizer (U : Set G)) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ C t) = Subgroup.normalizer (U : Set G) := by
    intro U hU hUP hVU
    exact hfactor U hU (hUP.trans hPN) hVU
      (centralizer_cover_descends (C t) (nu t)
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) Pa U hUP hcover)
  have hloc := stationary_localization_from_actual_factorizations hell hellodd t ht
    V Pa htV hPp hVP hPC (stationary_sylow_from_intrinsic_core hell Pa hstationary)
    hlocal U hU hUP hVU
  have hconclusion : ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) →
      IsPGroup ell W → t ∈ Subgroup.normalizer (W : Set G) →
      W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w := by
    intro W hWN hWp htW
    have hWC := hloc W hWN hWp htW
    exact ⟨hWC, localization_commutator_conclusion t W hWC⟩
  exact ⟨hconclusion, fun W hWC hWp htW =>
    hconclusion W (hWC.trans (Subgroup.centralizer_le_normalizer (U : Set G))) hWp htW⟩

theorem actual_scalar_dichotomy_of_original_localization [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hloc : ∀ U : Subgroup G, U ≠ ⊥ →
      U ≤ ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype →
      Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ C t) :
    let Na := (N t).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    (∀ W : Subgroup G, IsPGroup ell W → V ≤ Subgroup.normalizer (W : Set G) →
      W ⊓ C t ≤ Na →
      (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
        ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
        (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹))) ∧
      (∀ H : Subgroup G, ambientOddCore H ⊓ C t = Na ⊓ H →
        ∀ W : Subgroup G, W ≤ ambientOddCore H → IsPGroup ell W →
          V ≤ Subgroup.normalizer (W : Set G) →
          (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
            ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
            (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
            (¬ W ≤ C t → IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) := by
  intro Na V
  have hNodd : Odd (Nat.card Na) := by
    change Odd (Nat.card ((N t).map (C t).subtype))
    rw [Subgroup.card_subtype]
    exact actual_centralizer_core_odd t
  have hellodd : Odd ell := (actual_centralizer_core_odd t).of_dvd_nat hellN
  obtain ⟨htV, hV2, hVC⟩ := original_involution_pair_properties t s ht hs hsC
  have hVN : V ≤ Subgroup.normalizer (Na : Set G) :=
    actual_centralizer_core_normalized t V hVC
  have hNC : Na ≤ C t := Subgroup.map_subtype_le _
  obtain ⟨Q, hQ⟩ := ambient_sylow_from_intrinsic hell (C t) (N t) P
  have hVQ : V ≤ Subgroup.normalizer ((Q : Subgroup Na).map Na.subtype : Set G) := by
    rw [hQ]
    exact hVP
  have hlocQ : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ (Q : Subgroup Na).map Na.subtype →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ C t := by
    rw [hQ]
    exact hloc
  constructor
  · intro W hWp hVW hfixedN
    exact scalar_dichotomy_from_original_localization hell hellodd t ht V Na htV hV2
      hVC hVN hNodd hNC Q hVQ hlocQ W hWp hVW hfixedN
  · intro H hinter W hWR hWp hVW
    exact scalar_dichotomy_on_original_local_odd_core hell hellodd t ht V Na htV hV2
      hVC hVN hNodd hNC Q hVQ hlocQ H hinter W hWR hWp hVW

theorem actual_odd_kernel_conjugation_quotient (t : G) (c : C t) (hc : c ∈ N t)
    (x : C t) : nu t ((MulAut.conj c) x) = nu t x := by
  have hc1 : nu t c = 1 := by
    exact (QuotientGroup.eq_one_iff c).mpr hc
  change nu t (c * x * c⁻¹) = nu t x
  rw [map_mul, map_mul, map_inv, hc1, one_mul, inv_one, mul_one]

theorem actual_centralizer_cover_conjugation (t : G) (c : C t) (hc : c ∈ N t)
    (P : Subgroup G)
    (hcover : ((Subgroup.centralizer (P : Set G)).subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ((Subgroup.centralizer (P.map (MulAut.conj (c : G)).toMonoidHom : Set G)).subgroupOf
      (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
        (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  let T0 := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · intro q hq
    obtain ⟨x, ⟨hxP, hxY⟩, hxq⟩ := Subgroup.mem_map.mp (hcover.symm ▸ hq)
    let x' := (MulAut.conj c) x
    have hx'P : x' ∈ (Subgroup.centralizer
        (P.map (MulAut.conj (c : G)).toMonoidHom : Set G)).subgroupOf (C t) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm : z * (x : G) = (x : G) * z :=
        Subgroup.mem_centralizer_iff.mp hxP z hz
      have h := congrArg (MulAut.conj (c : G)) hcomm
      change (MulAut.conj (c : G)) z * ((MulAut.conj (c : G)) (x : G)) =
        ((MulAut.conj (c : G)) (x : G)) * (MulAut.conj (c : G)) z
      simpa only [map_mul] using h
    have hx'image : nu t x' = nu t x := actual_odd_kernel_conjugation_quotient t c hc x
    have hx'Y : x' ∈ T0.comap (nu t) := by
      change nu t x' ∈ T0
      rw [hx'image]
      exact hxY
    exact Subgroup.mem_map.mpr ⟨x', ⟨hx'P, hx'Y⟩, hx'image.trans hxq⟩

end ActualCentralizer

theorem ambient_oddCore_map_isomorphism {G' : Type v} [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    (ambientOddCore H).map e.toMonoidHom = ambientOddCore (H.map e.toMonoidHom) := by
  let eH := H.equivMapOfInjective e.toMonoidHom e.injective
  have hcore := CFSG.pPrimeCore_map_iso 2 eH
  rw [ambientOddCore, ambientOddCore, original_oddCore_eq_twoPrimeCore,
    original_oddCore_eq_twoPrimeCore, Subgroup.map_map]
  rw [← hcore, Subgroup.map_map]
  rfl

theorem stationary_sylow_map_isomorphism [Finite G] {G' : Type v} [Group G']
    {ell : ℕ} (hell : ell.Prime) (e : G ≃* G') (P : Subgroup G)
    (hstationary : ∃ P0 : Sylow ell (ambientOddCore (Subgroup.normalizer (P : Set G))),
      (P0 : Subgroup _).map (ambientOddCore (Subgroup.normalizer (P : Set G))).subtype = P) :
    ∃ Q : Sylow ell (ambientOddCore
      (Subgroup.normalizer (P.map e.toMonoidHom : Set G'))),
      (Q : Subgroup _).map (ambientOddCore
        (Subgroup.normalizer (P.map e.toMonoidHom : Set G'))).subtype = P.map e.toMonoidHom :=
  by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨P0, hP0⟩ := hstationary
  let R := ambientOddCore (Subgroup.normalizer (P : Set G))
  let R' := ambientOddCore (Subgroup.normalizer (P.map e.toMonoidHom : Set G'))
  have hR : R.map e.toMonoidHom = R' := by
    rw [ambient_oddCore_map_isomorphism, Subgroup.map_equiv_normalizer_eq]
  let eR := (R.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hR)
  have heR : Function.Surjective eR.toMonoidHom := by
    intro y
    exact ⟨eR.symm y, eR.apply_symm_apply y⟩
  refine ⟨P0.mapSurjective heR, ?_⟩
  rw [Sylow.coe_mapSurjective heR P0, Subgroup.map_map]
  have hmaps : R'.subtype.comp eR.toMonoidHom = e.toMonoidHom.comp R.subtype := by
    ext x
    rfl
  rw [hmaps, ← Subgroup.map_map, hP0]

theorem original_odd_subgroup_le_normalizer_core (U : Subgroup G)
    (hUodd : Odd (Nat.card U)) :
    U ≤ ambientOddCore (Subgroup.normalizer (U : Set G)) := by
  let H := Subgroup.normalizer (U : Set G)
  have hUH : U ≤ H := U.le_normalizer
  have hnormal : (U.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr le_rfl
  have hodd : Odd (Nat.card (U.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
    exact hUodd
  have hcore : U.subgroupOf H ≤ CFSG.oddCore H :=
    CFSG.ComponentClassification.OddCore.maximal H (U.subgroupOf H) hnormal hodd
  have hmap := Subgroup.map_mono (f := H.subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hUH] at hmap
  exact hmap

theorem original_normalizer_layer_coverage {Q : Type v} [Group Q]
    (C : Subgroup G) (f : C →* Q) (T : Subgroup Q) (U : Subgroup G)
    (hcover : ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f = T) :
    ((Subgroup.normalizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f = T := by
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · calc
      T = ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f :=
        hcover.symm
      _ ≤ ((Subgroup.normalizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f :=
        Subgroup.map_mono (inf_le_inf (Subgroup.subgroupOf_mono C
          (Subgroup.centralizer_le_normalizer (U : Set G))) le_rfl)

theorem original_quotient_involution_central_of_factorization
    (H R : Subgroup G) (hRH : R ≤ H) (hRnormal : (R.subgroupOf H).Normal)
    (t : G) (htH : t ∈ H)
    (hfactor : R ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H) :
    letI := hRnormal
    QuotientGroup.mk' (R.subgroupOf H) (⟨t, htH⟩ : H) ∈
      Subgroup.center (H ⧸ R.subgroupOf H) := by
  let : (R.subgroupOf H).Normal := hRnormal
  let q := QuotientGroup.mk' (R.subgroupOf H)
  let tH : H := ⟨t, htH⟩
  apply Subgroup.mem_center_iff.mpr
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf H) x
  have hcomm := kernel_commutators_of_factorization H R hRH hRnormal t htH hfactor
    (w : G) w.property
  have hfixed : q (tH * w * tH⁻¹) = q w := by
    exact (QuotientGroup.eq (s := R.subgroupOf H)).mpr hcomm |>.symm
  change q w * q tH = q tH * q w
  have h := congrArg (· * q tH) hfixed
  simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using h.symm

theorem original_normalizer_cover_inputs {Q : Type v} [Group Q]
    (C : Subgroup G) (f : C →* Q) (T : Subgroup Q) (V U : Subgroup G)
    (hU : U ≠ ⊥) (hUodd : Odd (Nat.card U))
    (hVU : V ≤ Subgroup.normalizer (U : Set G))
    (hcover : ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f = T) :
    let H := Subgroup.normalizer (U : Set G)
    V ≤ H ∧ U ≤ ambientOddCore H ∧ ambientOddCore H ≠ ⊥ ∧
      ((H.subgroupOf C) ⊓ T.comap f).map f = T := by
  intro H
  have hUcore := original_odd_subgroup_le_normalizer_core U hUodd
  have hcore : ambientOddCore H ≠ ⊥ := by
    intro hbot
    exact hU (eq_bot_iff.mpr (hUcore.trans_eq hbot))
  exact ⟨hVU, hUcore, hcore, original_normalizer_layer_coverage C f T U hcover⟩

theorem original_odd_subgroup_normalizer_is_smaller [Finite G] [IsSimpleGroup G]
    (t : G) (ht : orderOf t = 2) (U : Subgroup G)
    (hU : U ≠ ⊥) (hUodd : Odd (Nat.card U)) :
    Subgroup.normalizer (U : Set G) < ⊤ ∧
      Nat.card (Subgroup.normalizer (U : Set G)) < Nat.card G := by
  let H := Subgroup.normalizer (U : Set G)
  have hUcore := original_odd_subgroup_le_normalizer_core U hUodd
  have hcore : ambientOddCore H ≠ ⊥ := by
    intro hbot
    exact hU (eq_bot_iff.mpr (hUcore.trans_eq hbot))
  have hR : CFSG.pPrimeCore 2 H ≠ ⊥ := by
    intro hbot
    apply hcore
    simp only [ambientOddCore, original_oddCore_eq_twoPrimeCore, hbot, Subgroup.map_bot]
  have hH :=
    CFSG.Semidihedral.PerfectLayerNormalization.original_nontrivial_odd_core_subgroup_is_proper
      t ht H hR
  exact ⟨hH, (Subgroup.card_lt_of_lt hH).trans_eq Subgroup.card_top⟩

theorem original_normalizer_cover_inputs_with_smaller_order [Finite G] [IsSimpleGroup G]
    {Q : Type v} [Group Q] (t : G) (ht : orderOf t = 2)
    (C : Subgroup G) (f : C →* Q) (T : Subgroup Q) (V U : Subgroup G)
    (hU : U ≠ ⊥) (hUodd : Odd (Nat.card U))
    (hVU : V ≤ Subgroup.normalizer (U : Set G))
    (hcover : ((Subgroup.centralizer (U : Set G)).subgroupOf C ⊓ T.comap f).map f = T) :
    let H := Subgroup.normalizer (U : Set G)
    H < ⊤ ∧ Nat.card H < Nat.card G ∧ V ≤ H ∧ U ≤ ambientOddCore H ∧
      ambientOddCore H ≠ ⊥ ∧ ((H.subgroupOf C) ⊓ T.comap f).map f = T := by
  intro H
  obtain ⟨hH, hcard⟩ := original_odd_subgroup_normalizer_is_smaller t ht U hU hUodd
  obtain ⟨hVH, hUcore, hcore, hcov⟩ :=
    original_normalizer_cover_inputs C f T V U hU hUodd hVU hcover
  exact ⟨hH, hcard, hVH, hUcore, hcore, hcov⟩

section ActualFourGroup

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem original_centralizer_four_subgroup_image (t s : G) (hsC : s ∈ C t) :
    (KleinFourOddKernel.fourSubgroup (tInC t) (⟨s, hsC⟩ : C t)).map (C t).subtype =
      Subgroup.closure ({t, s} : Set G) := by
  rw [KleinFourOddKernel.fourSubgroup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, closure_pair_eq_zpowers_sup]
  rfl

theorem actual_involution_pair_isKleinFour [Finite G] (t s : G)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s) :
    IsKleinFour (Subgroup.closure ({t, s} : Set G)) := by
  let sC : C t := ⟨s, hsC⟩
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe _).symm.trans ht
  have hsCorder : orderOf sC = 2 := (Subgroup.orderOf_coe _).symm.trans hs
  have hne : tInC t ≠ sC := fun h => hts (congrArg Subtype.val h)
  let F := KleinFourOddKernel.fourSubgroup (tInC t) sC
  let hF : IsKleinFour F := KleinFourOddKernel.fourSubgroup_isKleinFour
    (tInC t) sC (tInC_central t) htC hsCorder hne
  let eF := (F.equivMapOfInjective (C t).subtype (C t).subtype_injective).trans
    (MulEquiv.subgroupCongr (original_centralizer_four_subgroup_image t s hsC))
  exact ⟨(Nat.card_congr eF.toEquiv).symm.trans hF.card_four,
    (Monoid.exponent_eq_of_mulEquiv eF).symm.trans hF.exponent_two⟩

theorem actual_involution_pair_disjoint_odd_core [Finite G] (t s : G)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s) :
    Disjoint ((N t).map (C t).subtype) (Subgroup.closure ({t, s} : Set G)) := by
  let hV : IsKleinFour (Subgroup.closure ({t, s} : Set G)) :=
    actual_involution_pair_isKleinFour t s ht hs hsC hts
  have hNodd : Odd (Nat.card ((N t).map (C t).subtype)) := by
    rw [Subgroup.card_subtype]
    exact actual_centralizer_core_odd t
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hV.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact hNodd.coprime_two_right.pow_right 2

theorem actual_involution_pair_odd_quotient [Finite G] (t s : G)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s) :
    let V := Subgroup.closure ({t, s} : Set G)
    let VC := V.subgroupOf (C t)
    Function.Injective ((nu t).subgroupMap VC) ∧ Nat.card (VC.map (nu t)) = 4 ∧
      orderOf (nu t (tInC t)) = 2 ∧ orderOf (nu t (⟨s, hsC⟩ : C t)) = 2 ∧
      nu t (tInC t) ≠ nu t (⟨s, hsC⟩ : C t) := by
  intro V VC
  have hVC : V ≤ C t := (original_involution_pair_properties t s ht hs hsC).2.2
  have hdisj := actual_involution_pair_disjoint_odd_core t s ht hs hsC hts
  have hinj : Function.Injective ((nu t).subgroupMap VC) := by
    intro x y heq
    apply Subtype.ext
    apply Subtype.ext
    have hq : nu t ((y : C t)⁻¹ * (x : C t)) = 1 := by
      rw [map_mul, map_inv]
      have hxy : nu t (x : C t) = nu t (y : C t) := congrArg Subtype.val heq
      rw [hxy, inv_mul_cancel]
    have hN : ((y : C t)⁻¹ * (x : C t)) ∈ N t :=
      (QuotientGroup.eq_one_iff _).mp hq
    have hV : ((y : G)⁻¹ * (x : G)) ∈ V :=
      V.mul_mem (V.inv_mem y.property) x.property
    have hNimage : ((y : G)⁻¹ * (x : G)) ∈ (N t).map (C t).subtype :=
      Subgroup.mem_map_of_mem (C t).subtype hN
    exact (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hdisj hNimage hV)).symm
  let eV := MulEquiv.ofBijective ((nu t).subgroupMap VC)
    ⟨hinj, (nu t).subgroupMap_surjective VC⟩
  have hcard : Nat.card (VC.map (nu t)) = 4 := by
    rw [← Nat.card_congr eV.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv]
    exact (actual_involution_pair_isKleinFour t s ht hs hsC hts).card_four
  let tV : VC := ⟨tInC t, Subgroup.subset_closure (by
    change t = t ∨ t = s
    exact Or.inl rfl)⟩
  let sV : VC := ⟨⟨s, hsC⟩, Subgroup.subset_closure (by simp)⟩
  have htV : orderOf tV = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact ht
  have hsV : orderOf sV = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hs
  have htq : orderOf (nu t (tInC t)) = 2 := by
    exact (Subgroup.orderOf_coe _).trans ((equiv_orderOf eV tV).trans htV)
  have hsq : orderOf (nu t (⟨s, hsC⟩ : C t)) = 2 := by
    exact (Subgroup.orderOf_coe _).trans ((equiv_orderOf eV sV).trans hsV)
  have hneq : nu t (tInC t) ≠ nu t (⟨s, hsC⟩ : C t) := by
    intro heq
    have h := hinj (Subtype.ext heq : (nu t).subgroupMap VC tV =
      (nu t).subgroupMap VC sV)
    exact hts (congrArg (fun x : VC => (x : G)) h)
  exact ⟨hinj, hcard, htq, hsq, hneq⟩

end ActualFourGroup

theorem intrinsic_sylow_from_ambient [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H : Subgroup G) (R : Subgroup H) (Q : Sylow ell (R.map H.subtype)) :
    ∃ P : Sylow ell R, ((P : Subgroup R).map R.subtype).map H.subtype =
      (Q : Subgroup (R.map H.subtype)).map (R.map H.subtype).subtype := by
  let : Fact ell.Prime := ⟨hell⟩
  let e := R.equivMapOfInjective H.subtype H.subtype_injective
  have hesym : Function.Surjective e.symm.toMonoidHom := by
    intro y
    exact ⟨e y, e.symm_apply_apply y⟩
  refine ⟨Q.mapSurjective hesym, ?_⟩
  rw [Sylow.coe_mapSurjective hesym Q, Subgroup.map_map, Subgroup.map_map]
  have hmaps : (H.subtype.comp R.subtype).comp e.symm.toMonoidHom =
      (R.map H.subtype).subtype := by
    ext x
    change (e (e.symm x) : G) = (x : G)
    exact congrArg (fun y : R.map H.subtype => (y : G)) (e.apply_symm_apply x)
  rw [hmaps]

theorem stationary_sylow_to_intrinsic_core [Finite G] {ell : ℕ} (hell : ell.Prime)
    (P : Subgroup G)
    (hstationary : ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (P : Set G))),
      (Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer (P : Set G))).subtype = P) :
    ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (P : Set G))).subtype).map
          (Subgroup.normalizer (P : Set G)).subtype = P := by
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore] at hstationary
  obtain ⟨Q, hQ⟩ := hstationary
  obtain ⟨P0, hP0⟩ := intrinsic_sylow_from_ambient hell (Subgroup.normalizer (P : Set G))
    (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))) Q
  exact ⟨P0, hP0.trans hQ⟩

section ActualSylowTransport

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem actual_stationary_covered_sylow_containing [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (P : Sylow ell (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
    (F : Subgroup G) (hFN : F ≤ (N t).map (C t).subtype) (hFp : IsPGroup ell F)
    (hVF : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (F : Set G)) :
    ∃ c : C t, c ∈ N t ∧ (c : G) ∈
      Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) ∧
      ∃ Q : Sylow ell (N t),
        let Qa := ((Q : Subgroup (N t)).map (N t).subtype).map (C t).subtype
        Qa = (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype).map
          (MulAut.conj (c : G)).toMonoidHom ∧ F ≤ Qa ∧
        Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (Qa : Set G) ∧
        ((Subgroup.centralizer (Qa : Set G)).subgroupOf (C t) ⊓
          ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
            (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
        ∃ Q0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (Qa : Set G))),
          ((Q0 : Subgroup _).map (CFSG.pPrimeCore 2
            (Subgroup.normalizer (Qa : Set G))).subtype).map
              (Subgroup.normalizer (Qa : Set G)).subtype = Qa := by
  let : Fact ell.Prime := ⟨hell⟩
  let V := Subgroup.closure ({t, s} : Set G)
  let Na := (N t).map (C t).subtype
  let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
  obtain ⟨_, hV2, hVC⟩ := original_involution_pair_properties t s ht hs hsC
  have hVN : V ≤ Subgroup.normalizer (Na : Set G) :=
    actual_centralizer_core_normalized t V hVC
  have hNodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_subtype]
    exact actual_centralizer_core_odd t
  obtain ⟨Pambient, hPambient⟩ := ambient_sylow_from_intrinsic hell (C t) (N t) P
  have hVPambient : V ≤ Subgroup.normalizer
      ((Pambient : Subgroup Na).map Na.subtype : Set G) := by
    rw [hPambient]
    exact hVP
  obtain ⟨c, hc, hFcP⟩ := invariant_pgroup_le_fixed_conjugate_sylow hell V Na F hV2
    hVN hNodd Pambient hVPambient hFN hFp hVF
  rw [hPambient] at hFcP
  let cC : C t := ⟨c, (Subgroup.map_subtype_le (N t)) hc.1⟩
  have hcN : cC ∈ N t := by
    obtain ⟨c0, hc0, heq⟩ := Subgroup.mem_map.mp hc.1
    have hCC : c0 = cC := Subtype.ext heq
    exact hCC ▸ hc0
  let cN : N t := ⟨cC, hcN⟩
  let eN := MulAut.conj cN
  have heN : Function.Surjective eN.toMonoidHom := by
    intro x
    exact ⟨eN.symm x, eN.apply_symm_apply x⟩
  let Q := P.mapSurjective heN
  let Qa := ((Q : Subgroup (N t)).map (N t).subtype).map (C t).subtype
  have hQa : Qa = Pa.map (MulAut.conj c).toMonoidHom := by
    simp only [Qa, Q, Sylow.coe_mapSurjective heN P, Subgroup.map_map, Pa]
    rfl
  have hcV : ∀ v ∈ V, (MulAut.conj c) v = v := by
    intro v hv
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 v hv
    change c * v * c⁻¹ = v
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hVQa : V ≤ Subgroup.normalizer (Qa : Set G) := by
    rw [hQa]
    exact normalized_map_of_fixed (MulAut.conj c) V Pa hcV hVP
  have hQaCover := actual_centralizer_cover_conjugation t cC hcN Pa hcover
  have hQaStationary := stationary_sylow_map_isomorphism hell (MulAut.conj c) Pa
    (stationary_sylow_from_intrinsic_core hell Pa hstationary)
  rw [← hQa] at hQaCover hQaStationary
  have hFQa : F ≤ Qa := by
    rw [hQa]
    exact hFcP
  exact ⟨cC, hcN, hc.2, Q, hQa, hFQa, hVQa, hQaCover,
    stationary_sylow_to_intrinsic_core hell Qa hQaStationary⟩

end ActualSylowTransport

section OriginalGroupTransport

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem original_factorization_transport {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) (H : Subgroup G) :
    ambientOddCore H ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H ↔
      ambientOddCore (H.map e.toMonoidHom) ⊔
        (H.map e.toMonoidHom ⊓ Subgroup.centralizer ({e t} : Set G')) =
          H.map e.toMonoidHom := by
  have hC := PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t
  rw [← ambient_oddCore_map_isomorphism e H, ← hC,
    ← Subgroup.map_inf _ _ _ e.injective, ← Subgroup.map_sup]
  exact ⟨congrArg (Subgroup.map e.toMonoidHom),
    fun h => Subgroup.map_injective (f := e.toMonoidHom) e.injective h⟩

theorem original_subgroup_centralizer_cover_transport [Finite G]
    {G' : Type v} [Group G'] (e : G ≃* G') (t : G) (U : Subgroup G)
    (hcover : ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ((Subgroup.centralizer (U.map e.toMonoidHom : Set G')).subgroupOf (C (e t)) ⊓
      ((CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))).comap (nu (e t))).map
        (nu (e t)) = (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) := by
  have h := PerfectLayerNormalization.isomorphism_transports_original_subgroup_local_cover
    e t (Subgroup.centralizer (U : Set G)) hcover
  rwa [PerfectLayerNormalization.isomorphism_maps_actual_centralizer] at h

theorem actual_stationary_sylow_transport_original_groups [Finite G]
    {G' : Type v} [Group G'] (e : G ≃* G') {ell : ℕ} (hell : ell.Prime)
    (t s : G) (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) :
    ∃ Q : Sylow ell (N (e t)),
      let Qa := ((Q : Subgroup (N (e t))).map (N (e t)).subtype).map (C (e t)).subtype
      Qa = (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype).map
        e.toMonoidHom ∧
      ell ∣ Nat.card (N (e t)) ∧
      Subgroup.closure ({e t, e s} : Set G') ≤ Subgroup.normalizer (Qa : Set G') ∧
      ((Subgroup.centralizer (Qa : Set G')).subgroupOf (C (e t)) ⊓
        ((CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))).comap
          (nu (e t))).map (nu (e t)) =
            (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) ∧
      ∃ Q0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (Qa : Set G'))),
        ((Q0 : Subgroup _).map
          (CFSG.pPrimeCore 2 (Subgroup.normalizer (Qa : Set G'))).subtype).map
            (Subgroup.normalizer (Qa : Set G')).subtype = Qa := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  let : Fact ell.Prime := ⟨hell⟩
  let a := PerfectLayerNormalization.originalOddCoreEquiv e t
  have haSurj : Function.Surjective a.toMonoidHom := by
    intro y
    exact ⟨a.symm y, a.apply_symm_apply y⟩
  let Q := P.mapSurjective (f := a.toMonoidHom) haSurj
  let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
  let Qa := ((Q : Subgroup (N (e t))).map (N (e t)).subtype).map (C (e t)).subtype
  have hcomp : (C (e t)).subtype.comp ((N (e t)).subtype.comp a.toMonoidHom) =
      e.toMonoidHom.comp ((C t).subtype.comp (N t).subtype) := by
    ext x
    change ((a x : C (e t)) : G') = e ((x : C t) : G)
    rw [PerfectLayerNormalization.originalOddCoreEquiv_coe]
    rfl
  have hQa : Qa = Pa.map e.toMonoidHom := by
    simp only [Qa, Pa, Q, Sylow.coe_mapSurjective haSurj P, Subgroup.map_map]
    rw [MonoidHom.comp_assoc, hcomp]
  have hdiv : ell ∣ Nat.card (N (e t)) := by
    rw [← Nat.card_congr a.toEquiv]
    exact hellN
  have hVQa : Subgroup.closure ({e t, e s} : Set G') ≤
      Subgroup.normalizer (Qa : Set G') := by
    rw [PerfectLayerNormalization.isomorphism_maps_original_fourgroup e t s |>.symm,
      hQa, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hVP
  have hcov := original_subgroup_centralizer_cover_transport e t Pa hcover
  rw [← hQa] at hcov
  have hstat := stationary_sylow_map_isomorphism hell e Pa
    (stationary_sylow_from_intrinsic_core hell Pa hstationary)
  rw [← hQa] at hstat
  exact ⟨Q, hQa, hdiv, hVQa, hcov, stationary_sylow_to_intrinsic_core hell Qa hstat⟩

theorem localization_transport_original_groups {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) (V P : Subgroup G) {ell : ℕ}
    (hloc : ∀ U : Subgroup G', U ≠ ⊥ → U ≤ P.map e.toMonoidHom →
      V.map e.toMonoidHom ≤ Subgroup.normalizer (U : Set G') →
      ∀ W : Subgroup G', W ≤ Subgroup.normalizer (U : Set G') → IsPGroup ell W →
        e t ∈ Subgroup.normalizer (W : Set G') →
          W ≤ Subgroup.centralizer ({e t} : Set G')) :
    ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P → V ≤ Subgroup.normalizer (U : Set G) →
      (∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ Subgroup.centralizer ({t} : Set G) ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧
            ∀ w ∈ W, t * w * t⁻¹ = w) ∧
      (∀ W : Subgroup G, W ≤ Subgroup.centralizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ Subgroup.centralizer ({t} : Set G) ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧
            ∀ w ∈ W, t * w * t⁻¹ = w) := by
  intro U hU hUP hVU
  have hUimage : U.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hU ((Subgroup.map_eq_bot_iff_of_injective U e.injective).mp hbot)
  have hVimage := Subgroup.map_mono (f := e.toMonoidHom) hVU
  rw [Subgroup.map_equiv_normalizer_eq] at hVimage
  have hcentralized : ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) →
      IsPGroup ell W → t ∈ Subgroup.normalizer (W : Set G) →
      W ≤ Subgroup.centralizer ({t} : Set G) ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧
        ∀ w ∈ W, t * w * t⁻¹ = w := by
    intro W hWN hWp htW
    have hWimage := Subgroup.map_mono (f := e.toMonoidHom) hWN
    rw [Subgroup.map_equiv_normalizer_eq] at hWimage
    have htimage := Subgroup.mem_map_of_mem e.toMonoidHom htW
    rw [Subgroup.map_equiv_normalizer_eq] at htimage
    have hfixedimage := hloc (U.map e.toMonoidHom) hUimage
      (Subgroup.map_mono hUP) hVimage (W.map e.toMonoidHom) hWimage
      (hWp.map e.toMonoidHom) htimage
    rw [← PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t]
      at hfixedimage
    have hWC := (Subgroup.map_le_map_iff_of_injective e.injective).mp hfixedimage
    exact ⟨hWC, localization_commutator_conclusion t W hWC⟩
  exact ⟨hcentralized, fun W hWC hWp htW =>
    hcentralized W (hWC.trans (Subgroup.centralizer_le_normalizer (U : Set G))) hWp htW⟩

theorem original_inversion_transport {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) (W : Subgroup G) :
    (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ↔
      ∀ w ∈ W.map e.toMonoidHom, e t * w * (e t)⁻¹ = w⁻¹ := by
  constructor
  · intro h w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    change e t * e x * (e t)⁻¹ = (e x)⁻¹
    simpa only [map_mul, map_inv] using congrArg e (h x hx)
  · intro h w hw
    apply e.injective
    simpa only [map_mul, map_inv] using h (e w) (Subgroup.mem_map_of_mem e.toMonoidHom hw)

theorem scalar_dichotomy_transport_original_group {G' : Type v} [Group G']
    (e : G ≃* G') (t : G) (N W : Subgroup G)
    (hscalar :
      (W.map e.toMonoidHom ≤ N.map e.toMonoidHom ∨
        ∀ w ∈ W.map e.toMonoidHom, e t * w * (e t)⁻¹ = w⁻¹) ∧
      ((∀ w ∈ W.map e.toMonoidHom, e t * w * (e t)⁻¹ = w⁻¹) →
        IsMulCommutative (W.map e.toMonoidHom) ∧
          W.map e.toMonoidHom ⊓ C (e t) = ⊥) ∧
      (W.map e.toMonoidHom ≠ ⊥ →
        ¬ (W.map e.toMonoidHom ≤ N.map e.toMonoidHom ∧
          ∀ w ∈ W.map e.toMonoidHom, e t * w * (e t)⁻¹ = w⁻¹))) :
    (W ≤ N ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
      ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
      (W ≠ ⊥ → ¬ (W ≤ N ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) := by
  have hle := Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom)
    (H := W) (K := N) e.injective
  have hinv := original_inversion_transport e t W
  have hC := PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t
  refine ⟨hscalar.1.imp (fun h => hle.mp h) hinv.mpr, ?_, ?_⟩
  · intro h
    obtain ⟨_, hfixed⟩ := hscalar.2.1 (hinv.mp h)
    have hfixedOriginal : W ⊓ C t = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom)
        (W ⊓ C t) e.injective).mp
      rw [Subgroup.map_inf _ _ _ e.injective, hC]
      exact hfixed
    exact ⟨abelian_of_inverted t W h, hfixedOriginal⟩
  · intro hW hboth
    have hWimage : W.map e.toMonoidHom ≠ ⊥ := by
      intro hbot
      exact hW ((Subgroup.map_eq_bot_iff_of_injective W e.injective).mp hbot)
    exact hscalar.2.2 hWimage ⟨hle.mpr hboth.1, hinv.mp hboth.2⟩

end OriginalGroupTransport

section ActualCoreIntersection

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.PerfectLayerNormalization

theorem even_card_of_noncyclic_sylow_two {A : Type v} [Group A] [Finite A]
    (hnc : ∀ P : Sylow 2 A, ¬ IsCyclic P) : Even (Nat.card A) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra heven
  have hodd : Odd (Nat.card A) := Nat.not_even_iff_odd.mp heven
  let P : Sylow 2 A := Classical.choice inferInstance
  rcases P.isPGroup'.card_eq_or_dvd with hcard | hdvd
  · apply hnc P
    exact isCyclic_of_card_le_orderOf (1 : P) (by rw [hcard, orderOf_one])
  · have hdiv : 2 ∣ Nat.card A := hdvd.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup A))
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdiv)

theorem original_covering_centralizer_odd_core [Finite G]
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (H : Subgroup G)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ambientOddCore (H ⊓ C t) = H ⊓ (N t).map (C t).subtype := by
  let B := H.subgroupOf (C t)
  have hLB : CFSG.generalizedFitting (Gamma t) ≤ B.map (kappa t) := by
    intro l hl
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (NZ t) l
    have hq : nu t b ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
      change kappa t b ∈ CFSG.generalizedFitting (Gamma t)
      exact hb ▸ hl
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp (hcover.symm ▸ hq)
    refine Subgroup.mem_map.mpr ⟨x, hx.1, ?_⟩
    change barKappa t (nu t x) = l
    rw [hxq]
    exact hb
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe _).symm.trans ht
  have hcore := original_layer_cover_odd_core_eq_intersection (tInC t) htC
    (even_card_of_noncyclic_sylow_two hnc) hcentral B hLB
  have hcoremap := congrArg (Subgroup.map (C t).subtype) hcore
  have hBC : B.map (C t).subtype = H ⊓ C t := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  let eB : B ≃* ↥(H ⊓ C t) :=
    (B.equivMapOfInjective (C t).subtype (C t).subtype_injective).trans
      (MulEquiv.subgroupCongr hBC)
  have htransport := congrArg (Subgroup.map (H ⊓ C t).subtype) (CFSG.pPrimeCore_map_iso 2 eB)
  rw [Subgroup.map_map] at htransport
  have heB : (H ⊓ C t).subtype.comp eB.toMonoidHom = (C t).subtype.comp B.subtype := rfl
  rw [heB, ← Subgroup.map_map] at htransport
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore, ← htransport, hcoremap,
    Subgroup.map_inf _ _ _ (C t).subtype_injective, hBC, inf_assoc,
    inf_eq_right.mpr (Subgroup.map_subtype_le (N t))]

theorem original_normal_odd_subgroup_fixed_points_le_core [Finite G]
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (H R : Subgroup G) (hRH : R ≤ H) (hRnormal : (R.subgroupOf H).Normal)
    (hRodd : Odd (Nat.card R))
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    R ⊓ C t ≤ (N t).map (C t).subtype := by
  let B := H ⊓ C t
  have hRB : R ⊓ C t ≤ B := inf_le_inf hRH le_rfl
  let : (R.subgroupOf H).Normal := hRnormal
  have hnormal : ((R ⊓ C t).subgroupOf B).Normal :=
    Subgroup.inf_subgroupOf_inf_normal_of_left (C t)
  have hodd : Odd (Nat.card ((R ⊓ C t).subgroupOf B)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRB).toEquiv]
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hcore : (R ⊓ C t).subgroupOf B ≤ CFSG.oddCore B :=
    CFSG.ComponentClassification.OddCore.maximal B _ hnormal hodd
  have hmap := Subgroup.map_mono (f := B.subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hRB] at hmap
  have hBcore := original_covering_centralizer_odd_core t ht hcentral hnc H hcover
  exact hmap.trans (hBcore.le.trans inf_le_right)

theorem original_covered_odd_core_fixed_points_le_core [Finite G]
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (H : Subgroup G)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ambientOddCore H ⊓ C t ≤ (N t).map (C t).subtype := by
  have hnormal : ((ambientOddCore H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le H)).mpr
      (ambientOddCore_normalized H)
  exact original_normal_odd_subgroup_fixed_points_le_core t ht hcentral hnc H
    (ambientOddCore H) (ambientOddCore_le H) hnormal (ambientOddCore_odd H) hcover

theorem actual_scalar_dichotomy_of_original_localization_and_coverage [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hloc : ∀ U : Subgroup G, U ≠ ⊥ →
      U ≤ ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype →
      Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ C t) :
    let Na := (N t).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    (∀ W : Subgroup G, IsPGroup ell W → V ≤ Subgroup.normalizer (W : Set G) →
      W ⊓ C t ≤ Na →
      (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
        ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
        (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹))) ∧
    ∀ H : Subgroup G,
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ∀ W : Subgroup G, W ≤ ambientOddCore H → IsPGroup ell W →
        V ≤ Subgroup.normalizer (W : Set G) →
        (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
          ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
          (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
          (¬ W ≤ C t → IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  intro Na V
  have hscalar := (actual_scalar_dichotomy_of_original_localization hell t s ht hs hsC P
    hellN hVP hloc).1
  refine ⟨hscalar, fun H hcover W hWR hWp hVW => ?_⟩
  have hfixed : W ⊓ C t ≤ Na :=
    (inf_le_inf hWR le_rfl).trans
      (original_covered_odd_core_fixed_points_le_core t ht hcentral hnc H hcover)
  have hW := hscalar W hWp hVW hfixed
  refine ⟨hW.1, hW.2.1, hW.2.2, fun hnot => ?_⟩
  have hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ :=
    hW.1.resolve_left fun hN => hnot (hN.trans (Subgroup.map_subtype_le (N t)))
  exact ⟨(hW.2.1 hinv).1, hinv⟩

theorem original_supplement_ambient_odd_core [Finite G]
    (H B : Subgroup G) (hBH : B ≤ H)
    (hfactor : ambientOddCore H ⊔ B = H) :
    ambientOddCore B = B ⊓ ambientOddCore H := by
  let BH := B.subgroupOf H
  have hfactor' : CFSG.pPrimeCore 2 H ⊔ BH = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_top,
      Subgroup.range_subtype]
    simpa only [ambientOddCore, original_oddCore_eq_twoPrimeCore] using hfactor
  have hcore := odd_core_of_supplement_to_whole_odd_core BH hfactor'
  have hcoremap := congrArg (Subgroup.map H.subtype) hcore
  let eB : BH ≃* B := Subgroup.subgroupOfEquivOfLe hBH
  have htransport := congrArg (Subgroup.map B.subtype) (CFSG.pPrimeCore_map_iso 2 eB)
  rw [Subgroup.map_map] at htransport
  have heB : B.subtype.comp eB.toMonoidHom = H.subtype.comp BH.subtype := rfl
  rw [heB, ← Subgroup.map_map] at htransport
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore, ← htransport, hcoremap,
    Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hBH]
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore]

theorem original_odd_core_fixed_intersection_of_cover_factorization [Finite G]
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (H : Subgroup G)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hfactor : ambientOddCore H ⊔ (H ⊓ C t) = H) :
    ambientOddCore H ⊓ C t = (N t).map (C t).subtype ⊓ H := by
  have h1 := original_covering_centralizer_odd_core t ht hcentral hnc H hcover
  have h2 := original_supplement_ambient_odd_core H (H ⊓ C t) inf_le_left hfactor
  have hR : (H ⊓ C t) ⊓ ambientOddCore H = ambientOddCore H ⊓ C t := by
    rw [inf_right_comm, inf_eq_right.mpr (ambientOddCore_le H), inf_comm]
  exact (hR.symm.trans (h2.symm.trans h1)).trans (inf_comm _ _)

theorem actual_localization_and_scalar_of_local_cover_factorizations [Finite G]
    {ell : ℕ} (hell : ell.Prime) (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
    (hfactor : ∀ H : Subgroup G, Subgroup.closure ({t, s} : Set G) ≤ H →
      ambientOddCore H ≠ ⊥ →
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ambientOddCore H ⊔ (H ⊓ C t) = H) :
    let Na := (N t).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    (∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa → V ≤ Subgroup.normalizer (U : Set G) →
      (∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w) ∧
      (∀ W : Subgroup G, W ≤ Subgroup.centralizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w)) ∧
    (∀ W : Subgroup G, IsPGroup ell W → V ≤ Subgroup.normalizer (W : Set G) →
      W ⊓ C t ≤ Na →
      (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
        ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
        (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹))) ∧
    ∀ H : Subgroup G, V ≤ H → ambientOddCore H ≠ ⊥ →
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ∀ W : Subgroup G, W ≤ ambientOddCore H → IsPGroup ell W →
        V ≤ Subgroup.normalizer (W : Set G) →
        (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
          ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
          (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
          (¬ W ≤ C t → IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  intro Na V Pa
  have htV : t ∈ V := Subgroup.mem_closure_of_mem (Set.mem_insert t _)
  have hnormalizerfactor : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Na →
      V ≤ Subgroup.normalizer (U : Set G) →
      ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ambientOddCore (Subgroup.normalizer (U : Set G)) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ C t) = Subgroup.normalizer (U : Set G) := by
    intro U hU hUN hVU hcovU
    have hUodd : Odd (Nat.card U) := by
      apply Odd.of_dvd_nat _ (Subgroup.card_dvd_of_le hUN)
      rw [Subgroup.card_subtype]
      exact actual_centralizer_core_odd t
    obtain ⟨hVH, -, hR, hcovH⟩ := original_normalizer_cover_inputs (C t) (nu t)
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) V U hU hUodd hVU hcovU
    exact hfactor (Subgroup.normalizer (U : Set G)) hVH hR hcovH
  have hloc := actual_stationary_localization_of_cover_factorizations hell t ht V htV P
    hellN hVP hcover hstationary hnormalizerfactor
  have hcentralization : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) → W ≤ C t :=
    fun U hU hUP hVU W hWN hWp htW => (hloc U hU hUP hVU).1 W hWN hWp htW |>.1
  obtain ⟨hscalar, hcore⟩ := actual_scalar_dichotomy_of_original_localization_and_coverage
    hell t s ht hs hsC hcentral hnc P hellN hVP hcentralization
  exact ⟨hloc, hscalar, fun H _ _ hcovH W hWR hWp hVW =>
    hcore H hcovH W hWR hWp hVW⟩

end ActualCoreIntersection

section OriginalUniversePairSylow

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem original_pair_sylow_presentation_return {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (n : ℕ) (H : Subgroup G) (t s : G)
    (SG' : Sylow 2 G') (fG' : CFSG.Open.SemidihedralGroup n ≃* SG')
    (H' : Subgroup G') (hH : H' = H.map e.toMonoidHom)
    (hodd : Odd H'.index)
    (hSH : (SG' : Subgroup G') ≤ H' ⊓ C (e t))
    (hz : (fG' (CFSG.Semidihedral.z n) : G') = e t)
    (hs : (fG' (CFSG.Semidihedral.s n) : G') = e s) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fG (CFSG.Semidihedral.s n) : G) = s ∧
        ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
        ((fH (CFSG.Semidihedral.s n) : H) : G) = s ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) ∧
          e (fG x : G) = (fG' x : G') := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SG := SG'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let fG := fG'.trans
    ((SG' : Subgroup G').equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
  have hSG : (SG : Subgroup G) = (SG' : Subgroup G').map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective SG'
  have hrepG (x : CFSG.Open.SemidihedralGroup n) :
      e (fG x : G) = (fG' x : G') := e.apply_symm_apply (fG' x)
  have hSGHC : (SG : Subgroup G) ≤ H ⊓ C t := by
    rw [hSG]
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hSH
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    rw [hH, Subgroup.map_inf _ _ _ e.symm.injective,
      Subgroup.map_map, hcomp, Subgroup.map_id,
      PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e.symm (e t),
      e.symm_apply_apply] at h
    exact h
  have hSGH : (SG : Subgroup G) ≤ H := hSGHC.trans inf_le_left
  let SH := SG.subtype hSGH
  have hmap : (SH : Subgroup H).map H.subtype = (SG : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSGH]
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let fH := fG.trans eSH.symm
  have hrepH (x : CFSG.Open.SemidihedralGroup n) :
      (fG x : G) = ((fH x : H) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSH.apply_symm_apply (fG x))
    exact h.symm
  have hzG : (fG (CFSG.Semidihedral.z n) : G) = t :=
    e.injective ((hrepG _).trans hz)
  have hsG : (fG (CFSG.Semidihedral.s n) : G) = s :=
    e.injective ((hrepG _).trans hs)
  have htSG : t ∈ (SG : Subgroup G) := hzG ▸ (fG (CFSG.Semidihedral.z n)).property
  have hsSG : s ∈ (SG : Subgroup G) := hsG ▸ (fG (CFSG.Semidihedral.s n)).property
  have hVSG : Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact htSG
    · exact Set.mem_singleton_iff.mp hx ▸ hsSG
  have hHodd : Odd H.index := by
    rw [hH] at hodd
    have hindex : (H.map e.toMonoidHom).index = H.index := Subgroup.index_map_equiv H e
    rwa [hindex] at hodd
  refine ⟨hHodd, SH, fH, SG, fG, ?_, hVSG, hmap.symm, hzG, hsG,
    (hrepH _).symm.trans hzG, (hrepH _).symm.trans hsG,
    fun x => ⟨hrepH x, hrepG x⟩⟩
  rw [Sylow.coe_subtype]
  exact Subgroup.subgroupOf_mono H hSGHC

theorem actual_covering_subgroup_original_pair_sylow_presentation_all_universes
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fG (CFSG.Semidihedral.s n) : G) = s ∧
        ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
        ((fH (CFSG.Semidihedral.s n) : H) : G) = s ∧
        ((fH (CFSG.Semidihedral.r n) : H) : G) ^ (CFSG.Semidihedral.modulus n / 2) = t ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let fS' : CFSG.Open.SemidihedralGroup n ≃* S' :=
    fS.trans ((S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let H' := H.map e.toMonoidHom
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map
      (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  have hVH' : Subgroup.closure ({e t, e s} : Set G') ≤ H' := by
    rw [← PerfectLayerNormalization.isomorphism_maps_original_fourgroup e t s]
    exact Subgroup.map_mono hVH
  have hsC' : e s ∈ C (e t) := by
    change e s ∈ Subgroup.centralizer ({e t} : Set G')
    rw [← PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hsC
  have hcov' := PerfectLayerNormalization.isomorphism_transports_original_subgroup_local_cover
    e t H hcover
  obtain ⟨hodd, SH', _, SG', fG', hSH'C, _, hmap', hz', hs', _, _, _, _⟩ :=
    actual_covering_subgroup_original_pair_sylow_presentation n hn S' fS'
      (PerfectLayerNormalization.isomorphism_transports_no_index_two e hG) (e t) (e s)
      ((e.orderOf_eq t).trans ht) ((e.orderOf_eq s).trans hs) hsC'
      (fun heq => hts (e.injective heq))
      (PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab) hcentral'
      (PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc)
      p f hp hpodd hf (PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel)
      H' hVH' hcov'
  have hSG'C : (SG' : Subgroup G') ≤ H' ⊓ C (e t) := by
    rw [hmap']
    calc
      (SH' : Subgroup H').map H'.subtype ≤
          ((H' ⊓ C (e t)).subgroupOf H').map H'.subtype := Subgroup.map_mono hSH'C
      _ = H' ⊓ C (e t) := Subgroup.map_subgroupOf_eq_of_le inf_le_left
  obtain ⟨hHodd, SH, fH, SG, fG, hSHC, hVSG, hmap, hz, hs, hzH, hsH, hrep⟩ :=
    original_pair_sylow_presentation_return e n H t s SG' fG' H' rfl hodd hSG'C hz' hs'
  refine ⟨hHodd, SH, fH, SG, fG, hSHC, hVSG, hmap, hz, hs, hzH, hsH, ?_,
    fun x => (hrep x).1⟩
  simpa only [CFSG.Semidihedral.z, CFSG.Semidihedral.half, map_pow, Subgroup.coe_pow,
    CFSG.Semidihedral.modulus_div_two n (by omega)] using hzH

end OriginalUniversePairSylow

section OriginalNormalizerGeometry

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem actual_stationary_subgroup_normalizer_original_cover_geometry
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    {ell : ℕ} (hell : ell.Prime) (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa → V ≤ Subgroup.normalizer (U : Set G) →
      let H := Subgroup.normalizer (U : Set G)
      H < ⊤ ∧ Nat.card H < Nat.card G ∧ V ≤ H ∧ U ≤ ambientOddCore H ∧
        ambientOddCore H ≠ ⊥ ∧
        ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
          ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
            (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
        (H.subgroupOf (C t) ⊓
          ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
            (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
        Odd H.index ∧
        ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
          (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          V ≤ (SG : Subgroup G) ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (fG (CFSG.Semidihedral.z n) : G) = t ∧
          (fG (CFSG.Semidihedral.s n) : G) = s ∧
          ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
          ((fH (CFSG.Semidihedral.s n) : H) : G) = s ∧
          ((fH (CFSG.Semidihedral.r n) : H) : G) ^ (CFSG.Semidihedral.modulus n / 2) = t ∧
          ∀ x, (fG x : G) = ((fH x : H) : G) := by
  intro Pa V U hU hUP hVU H
  have hellodd : Odd ell := (actual_centralizer_core_odd t).of_dvd_nat hellN
  have hPa : IsPGroup ell Pa := (P.isPGroup'.map (N t).subtype).map (C t).subtype
  have hUodd := odd_card_of_pgroup hell hellodd U (hPa.to_le hUP)
  have hcovU := centralizer_cover_descends (C t) (nu t)
    ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) Pa U hUP hcover
  obtain ⟨hH, hcard, hVH, hUcore, hcore, hcovH⟩ :=
    original_normalizer_cover_inputs_with_smaller_order t ht (C t) (nu t)
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) V U hU hUodd hVU hcovU
  obtain ⟨hHodd, SH, fH, SG, fG, hSHC, hVSG, hmap, hzG, hsG, hzH, hsH, hr, hrep⟩ :=
    actual_covering_subgroup_original_pair_sylow_presentation_all_universes n hn S fS
      (CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab) t s ht hs hsC hts
        hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcovH
  exact ⟨hH, hcard, hVH, hUcore, hcore, hcovU, hcovH, hHodd,
    SH, fH, SG, fG, hSHC, hVSG, hmap, hzG, hsG, hzH, hsH, hr, hrep⟩

end OriginalNormalizerGeometry

section OriginalRecognitionRepresentative

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem original_semidihedral_local_recognition_finite_representative
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
 :
    ∃ (G' : Type) (_ : Group G') (_ : Fintype G') (e : G ≃* G')
      (S' : Sylow 2 G') (fS' : CFSG.Open.SemidihedralGroup n ≃* S'),
      IsSimpleGroup G' ∧
      CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G' ∧
      (∃ a b : G', a * b ≠ b * a) ∧ Nat.card G' = Nat.card G ∧
      (S' : Subgroup G') = (S : Subgroup G).map e.toMonoidHom ∧
      (∀ x, (fS' x : G') = e (fS x : G)) ∧
      orderOf (e t) = 2 ∧ orderOf (e s) = 2 ∧ e s ∈ C (e t) ∧ e t ≠ e s ∧
      IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) ∧
      (∃ a b : CFSG.generalizedFitting (Gamma (e t)), a * b ≠ b * a) ∧
      Subgroup.centralizer
        (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ ∧
      (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma (e t))), ¬ IsCyclic P) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma (e t))) .PSL 2 p f := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩, hIH⟩ :=
    PerfectLayerNormalization.original_smaller_simple_recognition_finite_representative hrecognition
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let fS' : CFSG.Open.SemidihedralGroup n ≃* S' :=
    fS.trans ((S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e t
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map
      (PerfectLayerNormalization.originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  have hsC' : e s ∈ C (e t) := by
    change e s ∈ Subgroup.centralizer ({e t} : Set G')
    rw [← PerfectLayerNormalization.isomorphism_maps_original_element_centralizer e t]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hsC
  exact ⟨G', hgroup, hfinite, e, S', fS', e.symm.isSimpleGroup, hIH,
    PerfectLayerNormalization.isomorphism_transports_nonabelian e hGnonab,
    (Nat.card_congr e.toEquiv).symm,
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S, fun _ => rfl,
    (e.orderOf_eq t).trans ht, (e.orderOf_eq s).trans hs, hsC',
    (fun heq => hts (e.injective heq)), d.symm.isSimpleGroup,
    PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab, hcentral',
    PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc,
    PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel⟩

end OriginalRecognitionRepresentative


section FullOriginalStationaryConsequences

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem stationary_localization_and_scalar_all_original_groups
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
 :
    let Na := (N t).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    (∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa → V ≤ Subgroup.normalizer (U : Set G) →
      (∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w) ∧
      (∀ W : Subgroup G, W ≤ Subgroup.centralizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w)) ∧
    (∀ W : Subgroup G, IsPGroup ell W → V ≤ Subgroup.normalizer (W : Set G) →
      W ⊓ C t ≤ Na →
      (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
        ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
        (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹))) ∧
    ∀ H : Subgroup G, V ≤ H → ambientOddCore H ≠ ⊥ →
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ∀ W : Subgroup G, W ≤ ambientOddCore H → IsPGroup ell W →
        V ≤ Subgroup.normalizer (W : Set G) →
        (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
          ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
          (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
          (¬ W ≤ C t → IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
 := by
  have hfactor : ∀ H : Subgroup G, Subgroup.closure ({t, s} : Set G) ≤ H →
      ambientOddCore H ≠ ⊥ →
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ambientOddCore H ⊔ (H ⊓ C t) = H := by
    intro H hVH hR hcov
    have hRintrinsic : CFSG.pPrimeCore 2 H ≠ ⊥ := by
      intro hbot
      apply hR
      simp only [ambientOddCore, original_oddCore_eq_twoPrimeCore, hbot, Subgroup.map_bot]
    have hactual :=
      PerfectLayerNormalization.original_full_layer_cover_forces_core_centralizer_factorization
        hGnonab hrecognition n hn S fS t s ht hs hsC (Ne.symm hts) hnonab hcentral hnc
        p f hp hpodd hf hq hmodel H hVH hRintrinsic hcov
    simpa only [ambientOddCore, original_oddCore_eq_twoPrimeCore] using hactual.1
  exact actual_localization_and_scalar_of_local_cover_factorizations hell t s ht hs hsC
    hcentral hnc P hellN hVP hcover hstationary hfactor

theorem stationary_centralizer_cover_prime_forces_local_invariant_subgroup_centralization
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
 :
    let V := Subgroup.closure ({t, s} : Set G)
    let Pa := ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype
    (∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa → V ≤ Subgroup.normalizer (U : Set G) →
      (∀ W : Subgroup G, W ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w) ∧
      (∀ W : Subgroup G, W ≤ Subgroup.centralizer (U : Set G) → IsPGroup ell W →
        t ∈ Subgroup.normalizer (W : Set G) →
          W ≤ C t ∧ ⁅W, Subgroup.zpowers t⁆ = ⊥ ∧ ∀ w ∈ W, t * w * t⁻¹ = w)) := by
  have h :=
    stationary_localization_and_scalar_all_original_groups hGnonab hrecognition n hn S fS t s
      ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hell P hellN hVP hcover
      hstationary
  exact h.1

theorem stationary_localization_forces_scalar_action_on_odd_subgroups_with_local_fixed_points
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (N t)) (hellN : ell ∣ Nat.card (N t))
    (hVP : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype : Set G))
    (hcover : ((Subgroup.centralizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subgroupOf
        (C t) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype)
 :
    let Na := (N t).map (C t).subtype
    let V := Subgroup.closure ({t, s} : Set G)
    (∀ W : Subgroup G, IsPGroup ell W → V ≤ Subgroup.normalizer (W : Set G) →
      W ⊓ C t ≤ Na →
      (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
        ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
        (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹))) ∧
    ∀ H : Subgroup G, V ≤ H → ambientOddCore H ≠ ⊥ →
      (H.subgroupOf (C t) ⊓
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
      ∀ W : Subgroup G, W ≤ ambientOddCore H → IsPGroup ell W →
        V ≤ Subgroup.normalizer (W : Set G) →
        (W ≤ Na ∨ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
          ((∀ w ∈ W, t * w * t⁻¹ = w⁻¹) → IsMulCommutative W ∧ W ⊓ C t = ⊥) ∧
          (W ≠ ⊥ → ¬ (W ≤ Na ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)) ∧
          (¬ W ≤ C t → IsMulCommutative W ∧ ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  have h :=
    stationary_localization_and_scalar_all_original_groups hGnonab hrecognition n hn S fS t s
      ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hell P hellN hVP hcover
      hstationary
  exact h.2

end FullOriginalStationaryConsequences

end CFSG.Semidihedral.StationaryOddLocalization
