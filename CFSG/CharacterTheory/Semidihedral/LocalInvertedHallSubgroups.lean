module

public import CFSG.CharacterTheory.Semidihedral.OrderedPairLocalTransport
public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControl
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution

public noncomputable section

namespace CFSG.Semidihedral.LocalInvertedHallSubgroups

open scoped Pointwise commutatorElement IsKleinFour
open CFSG.Open CFSG.Semidihedral.Local CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.OrderedPairLocalTransport
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.SignalizerFunctor.Helpers

universe u v

variable {G : Type u} [Group G]

@[expose] def literalConjugationAction (U A : Subgroup G)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) : A →* MulAut U :=
  U.normalizerMonoidHom.comp (Subgroup.inclusion hAU)

theorem literalConjugationAction_apply (U A : Subgroup G)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (a : A) (x : U) :
    (literalConjugationAction U A hAU a x : G) = (a : G) * x * (a : G)⁻¹ := rfl

theorem original_normal_complement_literal_semidirect (N U A : Subgroup G)
    (hUN : U ≤ N) (hAN : A ≤ N) (hUn : (U.subgroupOf N).Normal)
    (hgen : U ⊔ A = N) (hdisj : U ⊓ A = ⊥) :
    ∃ phi : A →* MulAut U,
      (∀ a : A, ∀ x : U, (phi a x : G) = (a : G) * x * (a : G)⁻¹) ∧
      ∃ e : U ⋊[phi] A ≃* N,
        (∀ x : U ⋊[phi] A, (e x : G) = (x.left : G) * x.right) ∧
        (∀ n : N, ∃ x : U, ∃ a : A, (e ⟨x, a⟩ : G) = n) := by
  have hNU : N ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mp hUn
  have hAU := hAN.trans hNU
  let phi := literalConjugationAction U A hAU
  let m : U ⋊[phi] A →* N :=
    (SemidirectProduct.monoidHomSubgroup hAU).codRestrict N
      (fun x => N.mul_mem (hUN x.left.property) (hAN x.right.property))
  have hm : ∀ x : U ⋊[phi] A, (m x : G) = (x.left : G) * x.right := fun _ => rfl
  have hbij : Function.Bijective m := by
    constructor
    · intro x y h
      have hxy := congrArg (fun z : N => (z : G)) h
      have hp : (x.left, x.right) = (y.left, y.right) :=
        Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj) hxy
      exact SemidirectProduct.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    · intro n
      have hn : (n : G) ∈ U ⊔ A := hgen.symm ▸ n.property
      have hn' : (n : G) ∈ (U : Set G) * (A : Set G) := by
        rwa [← Subgroup.coe_mul_of_right_le_normalizer_left U A hAU]
      obtain ⟨x, hx, a, ha, hxa⟩ := Set.mem_mul.mp hn'
      exact ⟨⟨⟨x, hx⟩, ⟨a, ha⟩⟩, Subtype.ext hxa⟩
  let e := MulEquiv.ofBijective m hbij
  refine ⟨phi, literalConjugationAction_apply U A hAU, e, hm, ?_⟩
  intro n
  exact ⟨(e.symm n).left, (e.symm n).right,
    congrArg (fun z : N => (z : G)) (e.apply_symm_apply n)⟩

theorem invariant_ambient_sylow_containing [Finite G] {ell : ℕ} (hell : ell.Prime)
    (V R X : Subgroup G) (hV2 : IsPGroup 2 V) (hRodd : Odd (Nat.card R))
    (hVR : V ≤ Subgroup.normalizer (R : Set G)) (hXR : X ≤ R)
    (hXp : IsPGroup ell X) (hVX : V ≤ Subgroup.normalizer (X : Set G)) :
    ∃ Q : Sylow ell R, X ≤ (Q : Subgroup R).map R.subtype ∧
      V ≤ Subgroup.normalizer ((Q : Subgroup R).map R.subtype : Set G) := by
  let _action := conjugationAction V R hVR
  obtain ⟨Q, hXQ, hQInv⟩ := invariant_sylow_containing 2 ell Nat.prime_two hell
    hV2 hRodd.coprime_two_left (X.subgroupOf R) hXp.comap_subtype
    (normalized_subgroup_invariant_subgroup V R X hVR hVX)
  refine ⟨Q, ?_, invariant_subgroup_map_normalized V R hVR (Q : Subgroup R) ?_⟩
  · have h := Subgroup.map_mono (f := R.subtype) hXQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hXR] at h
  · change ∀ v : V, ∀ x ∈ (Q : Subgroup R), v • x ∈ (Q : Subgroup R)
    intro v x hx
    have h := Subgroup.smul_mem_pointwise_smul x v (Q : Subgroup R) hx
    rwa [← Sylow.pointwise_smul_def, hQInv] at h

theorem ambient_sylow_frattini [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H D : Subgroup G) (hDH : D ≤ H) (hDn : (D.subgroupOf H).Normal)
    (P : Sylow ell D) :
    (H ⊓ Subgroup.normalizer ((P : Subgroup D).map D.subtype : Set G)) ⊔ D = H := by
  let : Fact ell.Prime := ⟨hell⟩
  let D0 := D.subgroupOf H
  let : D0.Normal := hDn
  let e := Subgroup.subgroupOfEquivOfLe hDH
  let P0 := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP0 : ((P0 : Subgroup D0).map D0.subtype).map H.subtype =
      (P : Subgroup D).map D.subtype := by
    rw [Sylow.coe_mapSurjective e.symm.surjective P, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hPH : (P : Subgroup D).map D.subtype ≤ H :=
    (Subgroup.map_subtype_le _).trans hDH
  have hP0' : (P0 : Subgroup D0).map D0.subtype =
      ((P : Subgroup D).map D.subtype).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hPH]
    exact hP0
  have h := congrArg (Subgroup.map H.subtype) P0.normalizer_sup_eq_top
  rw [Subgroup.map_sup, hP0', normalizer_subgroupOf_eq hPH,
    Subgroup.subgroupOf_map_subtype, Subgroup.map_subgroupOf_eq_of_le hDH,
    Subgroup.map_top, Subgroup.range_subtype] at h
  rwa [inf_comm] at h

theorem ambient_sylow_normal_product [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H N D : Subgroup G) (hNH : N ≤ H) (hDH : D ≤ H)
    (hNn : (N.subgroupOf H).Normal) (hgen : N ⊔ D = H)
    (PD : Sylow ell D) (Q : Sylow ell H)
    (hPDQ : (PD : Subgroup D).map D.subtype ≤ (Q : Subgroup H).map H.subtype) :
    let Da := (PD : Subgroup D).map D.subtype
    let Qa := (Q : Subgroup H).map H.subtype
    D ⊓ Qa = Da ∧ Qa = (N ⊓ Qa) ⊔ Da ∧
      (∀ x ∈ Qa, ∃ p ∈ N ⊓ Qa, ∃ d ∈ Da, p * d = x) := by
  let : Fact ell.Prime := ⟨hell⟩
  intro Da Qa
  let N0 := N.subgroupOf H
  let : N0.Normal := hNn
  let q := QuotientGroup.mk' N0
  let qD : D →* H ⧸ N0 := q.comp (Subgroup.inclusion hDH)
  have hfull : N0 ⊔ D.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hDH, hgen, Subgroup.subgroupOf_self]
  have hqD : Function.Surjective qD := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N0 z
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hfull ▸ Subgroup.mem_top x)
    refine ⟨⟨d, hd⟩, ?_⟩
    change q d = q x
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← hnd, map_mul, hqn, one_mul]
  let PDq := PD.mapSurjective hqD
  have hDaH : Da ≤ H := (Subgroup.map_subtype_le _).trans hDH
  have hPDimage : (PDq : Subgroup (H ⧸ N0)) ≤ (Q : Subgroup H).map q := by
    rw [Sylow.coe_mapSurjective hqD PD]
    rintro z ⟨d, hd, rfl⟩
    exact ⟨Subgroup.inclusion hDH d, by
      obtain ⟨x, hx, hxd⟩ := hPDQ (Subgroup.mem_map_of_mem D.subtype hd)
      exact (Subtype.ext hxd : x = Subgroup.inclusion hDH d) ▸ hx, rfl⟩
  have himage : (Q : Subgroup H).map q = (PD : Subgroup D).map qD := by
    exact (PDq.is_maximal' (Q.isPGroup'.map q) hPDimage).trans
      (Sylow.coe_mapSurjective hqD PD)
  have hDinf : D ⊓ Qa = Da := by
    have hle : (PD : Subgroup D) ≤ Qa.subgroupOf D := by
      intro d hd
      exact hPDQ (Subgroup.mem_map_of_mem D.subtype hd)
    have hEq := PD.is_maximal' ((Q.isPGroup'.map H.subtype).comap_subtype) hle
    change Qa.subgroupOf D = (PD : Subgroup D) at hEq
    have h := congrArg (Subgroup.map D.subtype) hEq
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at h
    exact h
  have hfactor : ∀ x ∈ Qa, ∃ p ∈ N ⊓ Qa, ∃ d ∈ Da, p * d = x := by
    intro x hx
    obtain ⟨xH, hxH, rfl⟩ := Subgroup.mem_map.mp hx
    have hxq : q xH ∈ (PD : Subgroup D).map qD :=
      himage ▸ Subgroup.mem_map_of_mem q hxH
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hxq
    have hdQ : (d : G) ∈ Qa := hPDQ (Subgroup.mem_map_of_mem D.subtype hd)
    let dH : H := Subgroup.inclusion hDH d
    have hn : xH * dH⁻¹ ∈ N0 := by
      apply (QuotientGroup.eq_one_iff (xH * dH⁻¹)).mp
      change q (xH * dH⁻¹) = 1
      rw [map_mul, map_inv]
      change q xH * (qD d)⁻¹ = 1
      rw [hdx, mul_inv_cancel]
    refine ⟨(xH : G) * (d : G)⁻¹, ⟨hn, Qa.mul_mem
      (Subgroup.mem_map_of_mem H.subtype hxH) (Qa.inv_mem hdQ)⟩,
      d, Subgroup.mem_map_of_mem D.subtype hd, ?_⟩
    exact inv_mul_cancel_right (xH : G) (d : G)
  refine ⟨hDinf, le_antisymm ?_ (sup_le inf_le_right hPDQ), hfactor⟩
  intro x hx
  obtain ⟨p, hp, d, hd, rfl⟩ := hfactor x hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hd)

theorem normalizer_prime_product_strict [Finite G] {ell : ℕ} (hell : ell.Prime)
    (P D Q : Subgroup G) (hQp : IsPGroup ell Q) (hPQ : P ≤ Q) (hDQ : D ≤ Q)
    (hfactor : ∀ x ∈ Q, ∃ p ∈ P, ∃ d ∈ D, p * d = x)
    (hproper : P ⊓ D < P) :
    P ⊓ D < P ⊓ Subgroup.normalizer (D : Set G) := by
  have hDproper : D < Q := by
    apply lt_of_le_of_ne hDQ
    intro h
    have hPD : P ≤ D := hPQ.trans_eq h.symm
    exact hproper.ne (inf_eq_left.mpr hPD)
  have hstep := (normalizer_step_index hell Q D hQp hDproper).1
  apply lt_of_le_of_ne (inf_le_inf_left P D.le_normalizer)
  intro h
  have hnormalizer : Q ⊓ Subgroup.normalizer (D : Set G) ≤ D := by
    intro x hx
    obtain ⟨p, hp, d, hd, hpd⟩ := hfactor x hx.1
    have hpN : p ∈ Subgroup.normalizer (D : Set G) := by
      have hpx : p = x * d⁻¹ := by rw [← hpd]; group
      rw [hpx]
      exact Subgroup.mul_mem _ hx.2 (Subgroup.inv_mem _ (D.le_normalizer hd))
    have hpD : p ∈ D := (h.symm ▸ (show p ∈ P ⊓ Subgroup.normalizer (D : Set G)
      from ⟨hp, hpN⟩)).2
    rw [← hpd]
    exact D.mul_mem hpD hd
  exact hstep.ne (le_antisymm hstep.le hnormalizer)

theorem factorization_restricts_odd_core_quotient_centrality
    (K R A : Subgroup G) (hRK : R ≤ K) (hRn : (R.subgroupOf K).Normal)
    (hRodd : Odd (Nat.card R)) (hAK : A ≤ K) (t : G) (htA : t ∈ A)
    (hfactor : R ⊔ (K ⊓ Subgroup.centralizer ({t} : Set G)) = K) :
    (QuotientGroup.mk (⟨t, htA⟩ : A) : A ⧸ CFSG.pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := by
  have hRAn : (R.subgroupOf A).Normal := hRn.comap (Subgroup.inclusion hAK)
  have hRAodd : Odd (Nat.card (R.subgroupOf A)) := by
    rw [card_subgroupOf_eq]
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hRAcore : R.subgroupOf A ≤ CFSG.pPrimeCore 2 A := by
    rw [← original_oddCore_eq_twoPrimeCore]
    exact CFSG.ComponentClassification.OddCore.maximal A (R.subgroupOf A) hRAn hRAodd
  let q := QuotientGroup.mk' (CFSG.pPrimeCore 2 A)
  let tA : A := ⟨t, htA⟩
  apply Subgroup.mem_center_iff.mpr
  intro z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 A) z
  have hcomm := kernel_commutators_of_factorization K R hRK hRn t (hAK htA) hfactor
    (w : G) (hAK w.property)
  have hmem : w⁻¹ * (tA * w * tA⁻¹) ∈ CFSG.pPrimeCore 2 A := hRAcore hcomm
  have hfixed : q (tA * w * tA⁻¹) = q w :=
    ((QuotientGroup.eq (s := CFSG.pPrimeCore 2 A)).mpr hmem).symm
  change q w * q tA = q tA * q w
  have h := congrArg (· * q tA) hfixed
  simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using h.symm

theorem ambient_frattini_adjust_preserves_actor [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H D V : Subgroup G) (hDH : D ≤ H) (hDn : (D.subgroupOf H).Normal)
    (hDV : D ≤ Subgroup.centralizer (V : Set G)) (P : Sylow ell D)
    (g : G) (hgH : g ∈ H) :
    ∃ a ∈ H ⊓ Subgroup.normalizer ((P : Subgroup D).map D.subtype : Set G),
      ∀ v ∈ V, a * v * a⁻¹ = g * v * g⁻¹ := by
  let : (D.subgroupOf H).Normal := hDn
  have hfactor := ambient_sylow_frattini hell H D hDH hDn P
  have hfull : ((H ⊓ Subgroup.normalizer
      ((P : Subgroup D).map D.subtype : Set G)).subgroupOf H) ⊔ D.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hDH, hfactor, Subgroup.subgroupOf_self]
  obtain ⟨a, ha, d, hd, had⟩ := Subgroup.mem_sup_of_normal_right.mp
    (hfull ▸ Subgroup.mem_top (⟨g, hgH⟩ : H))
  have had' : (a : G) * d = g := congrArg (fun x : H => (x : G)) had
  refine ⟨a, ha, ?_⟩
  intro v hv
  have hdv : (d : G) * v * (d : G)⁻¹ = v := by
    have hcomm : Commute v (d : G) := (Subgroup.mem_centralizer_iff.mp (hDV hd)) v hv
    exact hcomm.symm.mul_inv_cancel
  calc
    (a : G) * v * (a : G)⁻¹ = a * ((d : G) * v * (d : G)⁻¹) * (a : G)⁻¹ := by rw [hdv]
    _ = ((a : G) * d) * v * ((a : G) * d)⁻¹ := by group
    _ = g * v * g⁻¹ := by rw [had']

theorem normalized_map_of_actor_normalizer (V W : Subgroup G) (g : G)
    (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hVW : V ≤ Subgroup.normalizer (W : Set G)) :
    V ≤ Subgroup.normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hVW
  have hVm : V.map (MulAut.conj g).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgV
  rw [hVm, Subgroup.map_equiv_normalizer_eq] at h
  exact h

theorem invariant_sylow_adjust_preserves_actor [Finite G] {ell : ℕ} (hell : ell.Prime)
    (H R V : Subgroup G) (hRH : R ≤ H) (hRn : (R.subgroupOf H).Normal)
    (hRodd : Odd (Nat.card R)) (hVH : V ≤ H) (hV2 : IsPGroup 2 V)
    (W : Sylow ell R)
    (hVW : V ≤ Subgroup.normalizer ((W : Subgroup R).map R.subtype : Set G))
    (g : G) (hgH : g ∈ H) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ a ∈ H ⊓ Subgroup.normalizer (V : Set G),
      a ∈ Subgroup.normalizer ((W : Subgroup R).map R.subtype : Set G) ∧
      ∀ v ∈ V, a * v * a⁻¹ = g * v * g⁻¹ := by
  let : Fact ell.Prime := ⟨hell⟩
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRn
  have hVR : V ≤ Subgroup.normalizer (R : Set G) := hVH.trans hHR
  let _action := conjugationAction V R hVR
  let eg := R.normalizerMonoidHom ⟨g, hHR hgH⟩
  have heg : Function.Surjective eg.toMonoidHom := fun x =>
    ⟨eg.symm x, eg.apply_symm_apply x⟩
  let Wg := W.mapSurjective (f := eg.toMonoidHom) heg
  have hWg : (Wg : Subgroup R).map R.subtype =
      ((W : Subgroup R).map R.subtype).map (MulAut.conj g).toMonoidHom := by
    change ((W.mapSurjective (f := eg.toMonoidHom) heg : Subgroup R).map
      R.subtype) = _
    rw [Sylow.coe_mapSurjective heg W, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hVWg : V ≤ Subgroup.normalizer ((Wg : Subgroup R).map R.subtype : Set G) := by
    rw [hWg]
    exact normalized_map_of_actor_normalizer V _ g hgV hVW
  obtain ⟨c, hc, hcfixed⟩ := invariant_sylows_conjugate_by_fixed_element
    2 ell Nat.prime_two hell V hV2 R hRodd.coprime_two_left Wg W
    (invariant_subgroup_sylow_fixed V R hVR ell Wg hVWg)
    (invariant_subgroup_sylow_fixed V R hVR ell W hVW)
  have hcV : (c : G) ∈ Subgroup.centralizer (V : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    have hfix := congrArg (fun x : R => (x : G)) (hcfixed (⟨v, hv⟩ : V))
    exact ((Subgroup.mem_centralizer_singleton_iff.mp (conj_fixed_iff v c |>.mp hfix))).symm
  have hcg : (c : G) * g ∈ Subgroup.normalizer
      ((W : Subgroup R).map R.subtype : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have h := congrArg (fun P : Sylow ell R => (P : Subgroup R).map R.subtype) hc
    rw [Sylow.coe_subgroup_smul] at h
    change ((Wg : Subgroup R).map (MulAut.conj c).toMonoidHom).map R.subtype = _ at h
    rw [Subgroup.map_map] at h
    have hcmap : R.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom.comp R.subtype := by ext x; rfl
    rw [hcmap, ← Subgroup.map_map, hWg, Subgroup.map_map] at h
    have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj ((c : G) * g)).toMonoidHom := by
      ext x
      change (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ =
        ((c : G) * g) * x * ((c : G) * g)⁻¹
      group
    rwa [hcomp] at h
  refine ⟨(c : G) * g, ⟨H.mul_mem (hRH c.property) hgH,
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer (V : Set G) hcV) hgV⟩, hcg, ?_⟩
  intro v hv
  have hgv : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
  have hcomm : Commute (g * v * g⁻¹) (c : G) :=
    Subgroup.mem_centralizer_iff.mp hcV _ hgv
  calc
    ((c : G) * g) * v * ((c : G) * g)⁻¹ = c * (g * v * g⁻¹) * (c : G)⁻¹ := by group
    _ = g * v * g⁻¹ := hcomm.symm.mul_inv_cancel

theorem original_pair_centralizer_eq (t s : G) :
    Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) := by
  ext x
  constructor
  · intro hx
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx t (Subgroup.subset_closure (by simp))).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx s (Subgroup.subset_closure (by simp))).symm⟩
  · intro hx
    have hVx : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      apply (Subgroup.closure_le _).mpr
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx.1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hVx hy)

theorem odd_subgroup_le_four_complement (C V D X : Subgroup G)
    [IsKleinFour V] (hVC : V ≤ C) (hDC : D ≤ C) (hDn : (D.subgroupOf C).Normal)
    (hgen : V ⊔ D = C) (hXodd : Odd (Nat.card X)) (hXC : X ≤ C) : X ≤ D := by
  let D0 := D.subgroupOf C
  let : D0.Normal := hDn
  let q := QuotientGroup.mk' D0
  have hfull : V.subgroupOf C ⊔ D0 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hVC hDC, hgen, Subgroup.subgroupOf_self]
  intro x hx
  let xC : C := ⟨x, hXC hx⟩
  obtain ⟨a, ha, d, hd, had⟩ := Subgroup.mem_sup_of_normal_right.mp
    (hfull ▸ Subgroup.mem_top xC)
  have hqd : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
  have hqa : q xC = q a := by rw [← had, map_mul, hqd, mul_one]
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    have h := congrArg (fun z : V => (z : G)) (IsKleinFour.mul_self (⟨a, ha⟩ : V))
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using h
  have hqx2 : q xC ^ 2 = 1 := by rw [hqa, ← map_pow, ha2, map_one]
  have hxc : xC ^ Nat.card X = 1 := by
    apply Subtype.ext
    exact congrArg (fun z : X => (z : G)) (pow_card_eq_one' (x := (⟨x, hx⟩ : X)))
  have hqx : q xC = 1 := (pow_eq_one_iff_of_coprime hXodd.coprime_two_right).mp
    ⟨by rw [← map_pow, hxc, map_one], hqx2⟩
  exact (QuotientGroup.eq_one_iff xC).mp hqx

theorem original_pair_cycle_fixed_free (t s g : G) (ht : orderOf t = 2)
    (hs : orderOf s = 2) (hcomm : Commute t s) (hts : t ≠ s)
    (hgt : g * t * g⁻¹ = t * s) (hgs : g * s * g⁻¹ = t) :
    ∀ x ∈ Subgroup.closure ({t, s} : Set G), x ≠ 1 → g * x * g⁻¹ ≠ x := by
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have ht2 : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  intro x hx hx1
  rcases (CFSG.Semidihedral.TwoCoverOddCore.original_four_group_members
    t s x ht hs hcomm).mp hx with rfl | rfl | rfl | rfl
  · exact (hx1 rfl).elim
  · rw [hgt]
    exact fun h => hs1 (mul_left_cancel (by simpa only [mul_one] using h))
  · rw [hgs]
    exact hts
  · have hgts : g * (t * s) * g⁻¹ = s := by
      change (MulAut.conj g) (t * s) = s
      rw [map_mul]
      change (g * t * g⁻¹) * (g * s * g⁻¹) = s
      rw [hgt, hgs, hcomm.eq, mul_assoc, ht2, mul_one]
    rw [hgts]
    intro h
    exact ht1 (mul_right_cancel (by simpa only [one_mul] using h.symm))

theorem stationary_layer_cover_local_prime_is_centralized_or_inverted
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    {ell : ℕ} (hell : ell.Prime) (hellN : ell ∣ Nat.card (N t))
    (P : Sylow ell (N t)) (hP : OriginalStationaryCoverAt t s ell P) :
    let Pa := originalSylowAmbient t P
    ((∀ x ∈ Pa, s * x * s⁻¹ = x) ∨ (∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹)) ∧
      ((∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹) → IsMulCommutative Pa) := by
  let : Fact ell.Prime := ⟨hell⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect G :=
    CFSG.Semidihedral.CoreFreeDihedral.isPerfect_of_simple_nonabelian hGnonab
  let V := Subgroup.closure ({t, s} : Set G)
  let Na := (N t).map (C t).subtype
  let Po := originalSylowAmbient t P
  let M := Subgroup.normalizer (V : Set G)
  let D := ambientOddCore M
  let CV := Subgroup.centralizer (V : Set G)
  have hcomm : Commute t s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  let : IsKleinFour V :=
    CFSG.Semidihedral.TwoCoverOddCore.original_four_group_isKleinFour t s ht hs hcomm hts
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by
    rw [IsKleinFour.card_four]; norm_num)
  have hVCt : V ≤ C t := (original_involution_pair_properties t s ht hs hsC).2.2
  have hVN : V ≤ Subgroup.normalizer (Na : Set G) :=
    actual_centralizer_core_normalized t V hVCt
  have hNCt : Na ≤ C t := Subgroup.map_subtype_le _
  have hNnormal : (Na.subgroupOf (C t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNCt).mpr
      (actual_centralizer_core_normalized t (C t) le_rfl)
  have hNodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_subtype]
    exact actual_centralizer_core_odd t
  have hellodd : Odd ell := (actual_centralizer_core_odd t).of_dvd_nat hellN
  have hPcover : ((Subgroup.centralizer (Po : Set G)).subgroupOf (C t) ⊓
      originalLayerPreimage t).map (nu t) = originalSection t := by
    rw [original_sylow_centralizer_restriction]
    exact hP.2.2
  have hPstationOdd : OriginalSylowStationarity ell Po := hP.2.1
  have hPstation : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (Po : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (Po : Set G))).subtype).map
          (Subgroup.normalizer (Po : Set G)).subtype = Po := by
    change ∃ P0 : Sylow ell (CFSG.oddCore (Subgroup.normalizer (Po : Set G))), _ at hPstationOdd
    rw [original_oddCore_eq_twoPrimeCore] at hPstationOdd
    exact hPstationOdd
  obtain ⟨SV, hVSV⟩ := hV2.exists_le_sylow
  obtain ⟨-, hZD, -, -, -⟩ := four_and_quaternion_eight_local_normalizer_quotients
    n hn SV (f0.trans (S0.equiv SV)) V hVSV (Or.inl inferInstance)
  have hDCV : D ≤ CV := le_sup_right.trans_eq hZD
  have hDnormalM : (D.subgroupOf M).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le M)).mpr
      (ambientOddCore_normalized M)
  have hDM : D ≤ M := ambientOddCore_le M
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mp hDnormalM
  have hCVMD : CV ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.centralizer_le_normalizer (V : Set G)).trans hMD
  have hDnormalCV : (D.subgroupOf CV).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDCV).mpr hCVMD
  have hVCV : V ≤ CV := fun x hx => Subgroup.mem_centralizer_iff.mpr
    fun y hy => kleinFour_mul_comm V hy hx
  have hVDCV : V ⊔ D = CV := by
    apply le_antisymm (sup_le hVCV hDCV)
    change Subgroup.centralizer (V : Set G) ≤ V ⊔ D
    rw [← hZD]
    exact sup_le_sup (Subgroup.map_subtype_le _) le_rfl
  have hDodd : Odd (Nat.card D) := ambientOddCore_odd M
  have hCVpair : CV = C t ⊓ Subgroup.centralizer ({s} : Set G) :=
    original_pair_centralizer_eq t s
  have hDCt : D ≤ C t := hDCV.trans (by rw [hCVpair]; exact inf_le_left)
  let PD : Sylow ell D := Classical.choice inferInstance
  let Da := (PD : Subgroup D).map D.subtype
  have hDaD : Da ≤ D := Subgroup.map_subtype_le _
  have hVDaC : V ≤ Subgroup.centralizer (Da : Set G) := by
    intro v hv
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hDCV (hDaD hx)) v hv).symm
  have hVDa : V ≤ Subgroup.normalizer (Da : Set G) :=
    hVDaC.trans (Subgroup.centralizer_le_normalizer (Da : Set G))
  let ND := Na ⊔ D
  have hNDC : ND ≤ C t := sup_le hNCt hDCt
  have hNnormalND : (Na.subgroupOf ND).Normal :=
    hNnormal.comap (Subgroup.inclusion hNDC)
  have hNDodd : Odd (Nat.card ND) :=
    odd_card_sup_in_parent (C t) Na D hNCt hDCt hNnormal hNodd hDodd
  have hVND : V ≤ Subgroup.normalizer (ND : Set G) :=
    (le_inf hVN (V.le_normalizer.trans hMD)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Na D)
  obtain ⟨Q, hDaQ, hVQ⟩ := invariant_ambient_sylow_containing hell V ND Da hV2 hNDodd
    hVND (hDaD.trans le_sup_right) (PD.isPGroup'.map D.subtype) hVDa
  let Qa := (Q : Subgroup ND).map ND.subtype
  obtain ⟨Pi, hPi⟩ := ambient_normal_sylow_intersection hell ND Na le_sup_left hNnormalND Q
  let Pa := (Pi : Subgroup Na).map Na.subtype
  have hPiEq : Pa = Na ⊓ Qa := hPi
  have hPaQ : Pa ≤ Qa := by rw [hPiEq]; exact inf_le_right
  have hPaN : Pa ≤ Na := Subgroup.map_subtype_le _
  have hPaCt : Pa ≤ C t := hPaN.trans hNCt
  have hPap : IsPGroup ell Pa := Pi.isPGroup'.map Na.subtype
  have hVPa : V ≤ Subgroup.normalizer (Pa : Set G) := by
    rw [hPiEq]
    exact (le_inf hVN hVQ).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨hDQ, hQprod, hQelements⟩ := ambient_sylow_normal_product hell ND Na D
    le_sup_left le_sup_right hNnormalND rfl PD Q hDaQ
  have hfactorQ : ∀ x ∈ Qa, ∃ a ∈ Pa, ∃ d ∈ Da, a * d = x := by
    rw [hPiEq]
    exact hQelements
  obtain ⟨c, hcN, hcV, Pc, hPcPo, hPaPc, hVPc, hcoverPc, hstationPc⟩ :=
    actual_stationary_covered_sylow_containing hell t s ht hs hsC P hP.1 hPcover hPstation
      Pa hPaN hPap hVPa
  obtain ⟨PcA, hPcA⟩ := ambient_sylow_from_intrinsic hell (C t) (N t) Pc
  have hPiPcA : (Pi : Subgroup Na) ≤ (PcA : Subgroup Na) := by
    intro x hx
    have h := hPaPc (Subgroup.mem_map_of_mem Na.subtype hx)
    rw [← hPcA] at h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    exact Na.subtype_injective hyx ▸ hy
  have hPcPa : originalSylowAmbient t Pc = Pa := by
    change ((Pc : Subgroup (N t)).map (N t).subtype).map (C t).subtype = Pa
    rw [← hPcA, Pi.is_maximal' PcA.isPGroup' hPiPcA]
  have hPaPo : Pa = Po.map (MulAut.conj (c : G)).toMonoidHom := hPcPa.symm.trans hPcPo
  have hloc : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa →
      V ≤ Subgroup.normalizer (U : Set G) →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell X →
        t ∈ Subgroup.normalizer (X : Set G) → X ≤ C t := by
    intro U hU hUP hVU X hXK hXp htX
    have h := stationary_centralizer_cover_prime_forces_local_invariant_subgroup_centralization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq
        hmodel hell Pc hellN hVPc hcoverPc hstationPc
    rw [← hPcPa] at hUP
    exact (h U hU hUP hVU).1 X hXK hXp htX |>.1
  have hfactor : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ Pa →
      V ≤ Subgroup.normalizer (U : Set G) →
      ambientOddCore (Subgroup.normalizer (U : Set G)) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ C t) = Subgroup.normalizer (U : Set G) := by
    intro U hU hUP hVU
    have hcover : ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
        originalLayerPreimage t).map (nu t) = originalSection t := by
      apply centralizer_cover_descends (C t) (nu t) (originalSection t)
        (originalSylowAmbient t Pc) U (hUP.trans_eq hPcPa.symm)
      exact hcoverPc
    have hUodd := odd_card_of_pgroup hell hellodd U (hPap.to_le hUP)
    obtain ⟨hVK, -, hRK, hcovK⟩ := original_normalizer_cover_inputs
      (C t) (nu t) (originalSection t) V U hU hUodd hVU hcover
    have hRintrinsic : CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
      intro hbot
      apply hRK
      simp only [ambientOddCore, original_oddCore_eq_twoPrimeCore, hbot, Subgroup.map_bot]
    have h :=
      PerfectLayerNormalization.original_full_layer_cover_forces_core_centralizer_factorization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts.symm hnonab hcentral hnc p f hp hpodd hf
        hq hmodel (Subgroup.normalizer (U : Set G)) hVK hRintrinsic hcovK
    simpa only [ambientOddCore, original_oddCore_eq_twoPrimeCore] using h.1
  have hPaScalar : (∀ x ∈ Pa, s * x * s⁻¹ = x) ∨ (∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹) := by
    let F := Pa ⊓ Subgroup.centralizer ({s} : Set G)
    have hFodd := odd_card_of_pgroup hell hellodd F (hPap.to_le inf_le_left)
    have hFCV : F ≤ CV := by
      rw [hCVpair]
      exact le_inf (inf_le_left.trans hPaCt) inf_le_right
    have hFD : F ≤ D := odd_subgroup_le_four_complement CV V D F
      hVCV hDCV hDnormalCV hVDCV hFodd hFCV
    have hFPaD : F = Pa ⊓ D := le_antisymm (le_inf inf_le_left hFD) (by
      rw [show F = Pa ⊓ Subgroup.centralizer ({s} : Set G) from rfl]
      exact inf_le_inf_left Pa (hDCV.trans (by rw [hCVpair]; exact inf_le_right)))
    have hDQEq : D ⊓ Qa = Da := hDQ
    have hFPaDa : F = Pa ⊓ Da := by
      rw [hFPaD]
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, hDQEq ▸ (show x ∈ D ⊓ Qa from ⟨hx.2, hPaQ hx.1⟩)⟩
      · intro hx
        exact ⟨hx.1, hDaD hx.2⟩
    have hVF : V ≤ Subgroup.normalizer (F : Set G) := by
      rw [hFPaDa]
      exact (le_inf hVPa hVDa).trans Subgroup.inf_normalizer_le_normalizer_inf
    by_cases hFP : F = Pa
    · exact Or.inl fun x hx => (conj_fixed_iff s x).mpr ((hFP.symm ▸ hx).2)
    by_cases hFbot : F = ⊥
    · exact Or.inr (inverted_of_trivial_fixed_subgroup s hs Pa
        (odd_card_of_pgroup hell hellodd Pa hPap) (hVPa hsV) hFbot)
    exfalso
    let H := Subgroup.normalizer (Da : Set G)
    let A := Subgroup.centralizer (Da : Set G)
    let K := Subgroup.normalizer (F : Set G)
    let P1 := Pa ⊓ H
    let R := ambientOddCore H
    have hFproper : Pa ⊓ Da < Pa := hFPaDa ▸ lt_of_le_of_ne inf_le_left hFP
    have hFP1 : F < P1 := by
      rw [hFPaDa]
      exact normalizer_prime_product_strict hell Pa Da Qa (Q.isPGroup'.map ND.subtype)
        hPaQ hDaQ hfactorQ hFproper
    have hVP1 : V ≤ Subgroup.normalizer (P1 : Set G) :=
      (le_inf hVPa (hVDa.trans H.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hP1p : IsPGroup ell P1 := hPap.to_le inf_le_left
    have hP1odd := odd_card_of_pgroup hell hellodd P1 hP1p
    have hAH : A ≤ H := Subgroup.centralizer_le_normalizer (Da : Set G)
    have hAn : (A.subgroupOf H).Normal := inferInstance
    have hVA : V ≤ A := hVDaC
    have hAK : A ≤ K := (Subgroup.centralizer_le
      (show (F : Set G) ⊆ Da from fun _ hx => (hFPaDa ▸ hx).2)).trans
        (Subgroup.centralizer_le_normalizer (F : Set G))
    have hKfactor := hfactor F hFbot inf_le_left hVF
    have hRKnormal : ((ambientOddCore K).subgroupOf K).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le K)).mpr
        (ambientOddCore_normalized K)
    have htAcentral : (QuotientGroup.mk (⟨t, hVA htV⟩ : A) :
        A ⧸ CFSG.pPrimeCore 2 A) ∈ Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) :=
      factorization_restricts_odd_core_quotient_centrality K (ambientOddCore K) A
        (ambientOddCore_le K) hRKnormal (ambientOddCore_odd K) hAK t (hVA htV) hKfactor
    obtain ⟨g, hgM, hgt, hgs⟩ := original_ordered_pair_normalizer_conjugator
      n hn S0 f0 t s (t * s) ht hs hcomm hts (Or.inr rfl)
    obtain ⟨g1, hg1, hg1V⟩ := ambient_frattini_adjust_preserves_actor hell M D V hDM
      hDnormalM hDCV PD g hgM
    have hg1t : g1 * t * g1⁻¹ = t * s := (hg1V t htV).trans hgt
    have hg1s : g1 * s * g1⁻¹ = t := (hg1V s hsV).trans hgs
    have hg1free := original_pair_cycle_fixed_free t s g1 ht hs hcomm hts hg1t hg1s
    have ht1 : t ≠ 1 := by intro h; simp [h] at ht
    have hcontrol := four_group_cycling_normal_subgroup_controls_invariant_odd_subgroups
      n hn S0 f0 H A V hAH hAn hVA t htV ht1 htAcentral g1 hg1.2 hg1.1 hg1free
    have hP1R : P1 ≤ R := by
      change P1 ≤ (CFSG.oddCore H).map H.subtype
      rw [original_oddCore_eq_twoPrimeCore]
      exact hcontrol.2.2.2.2.2.2.2 P1 inf_le_right hP1odd hVP1
    have hRH : R ≤ H := ambientOddCore_le H
    have hRn : (R.subgroupOf H).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le H)).mpr
        (ambientOddCore_normalized H)
    have hVH : V ≤ H := hVA.trans hAH
    have hVR : V ≤ Subgroup.normalizer (R : Set G) := hVH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRn)
    obtain ⟨W, hP1W, hVW⟩ := invariant_ambient_sylow_containing hell V R P1 hV2
      (ambientOddCore_odd H) hVR hP1R hP1p hVP1
    let Wa := (W : Subgroup R).map R.subtype
    obtain ⟨g2, hg2, hg2W, hg2V⟩ := invariant_sylow_adjust_preserves_actor hell H R V
      hRH hRn (ambientOddCore_odd H) hVH hV2 W hVW g1 hg1.2 hg1.1
    have hg2s : g2 * s * g2⁻¹ = t := (hg2V s hsV).trans hg1s
    have hWnot : ¬ Wa ≤ C t := by
      intro hWt
      have hP1Cs : P1 ≤ Subgroup.centralizer ({s} : Set G) := by
        intro x hx
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply (MulAut.conj g2).injective
        rw [map_mul, map_mul]
        change (g2 * x * g2⁻¹) * (g2 * s * g2⁻¹) =
          (g2 * s * g2⁻¹) * (g2 * x * g2⁻¹)
        rw [hg2s]
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (hWt ((Subgroup.mem_normalizer_iff.mp hg2W x).mp (hP1W hx)))
      have hP1F : P1 ≤ F := le_inf inf_le_left hP1Cs
      exact hFP1.ne (le_antisymm hFP1.le hP1F)
    obtain ⟨x, hxW, hx1, hxinverted, hxcomm, hxnot⟩ := odd_pgroup_inverted_centralizing_witness
      hell hellodd t ht Wa (W.isPGroup'.map R.subtype) (hVW htV) hWnot
    have hFWfixed : F ≤ Wa ⊓ C t := le_inf (hFP1.le.trans hP1W) (inf_le_left.trans hPaCt)
    have hxCF : x ∈ Subgroup.centralizer (F : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hxcomm y (hFWfixed hy)).eq.symm
    let X := Subgroup.zpowers x
    have hXK : X ≤ K := Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer (F : Set G) hxCF)
    have hXW : X ≤ Wa := Subgroup.zpowers_le.mpr hxW
    have htX : t ∈ Subgroup.normalizer (X : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (t * x * t⁻¹) = Subgroup.zpowers x
      rw [hxinverted, Subgroup.zpowers_inv]
    exact hxnot (hloc F hFbot inf_le_left hVF X hXK
      ((W.isPGroup'.map R.subtype).to_le hXW) htX (Subgroup.mem_zpowers x))
  have hcs : (MulAut.conj (c : G)) s = s := by
    have hcc : Commute s (c : G) := Subgroup.mem_centralizer_iff.mp hcV s hsV
    exact hcc.symm.mul_inv_cancel
  constructor
  · rcases hPaScalar with hcentralized | hinverted
    · apply Or.inl
      have hmap : Po.map (MulAut.conj (c : G)).toMonoidHom ≤
          Subgroup.centralizer ({s} : Set G) := by
        rw [← hPaPo]
        exact fun x hx => (conj_fixed_iff s x).mp (hcentralized x hx)
      have h := centralized_of_map_fixed (MulAut.conj (c : G)) s hcs Po hmap
      exact fun x hx => (conj_fixed_iff s x).mpr (h hx)
    · apply Or.inr
      have h := (original_inversion_transport (MulAut.conj (c : G)) s Po).mpr
        (by simpa only [hcs, ← hPaPo] using hinverted)
      exact h
  · exact abelian_of_inverted s Po

theorem original_all_prime_stationary_local_inverted_hall_subgroup
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : CFSG.Semidihedral.PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hprimes : OriginalAllPrimeStationaryCover t s) :
    let Na := (N t).map (C t).subtype
    let A := Na ⊓ Subgroup.centralizer ({s} : Set G)
    Odd (Nat.card Na) ∧ Group.IsSolvable Na ∧
    (∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (N t) →
      ∀ P : Sylow ell (N t), OriginalStationaryCoverAt t s ell P →
      ((∀ x ∈ originalSylowAmbient t P, s * x * s⁻¹ = x) ∨
        (∀ x ∈ originalSylowAmbient t P, s * x * s⁻¹ = x⁻¹)) ∧
      ((∀ x ∈ originalSylowAmbient t P, s * x * s⁻¹ = x⁻¹) →
        IsMulCommutative (originalSylowAmbient t P))) ∧
    Nat.Coprime (Nat.card A) (A.relIndex Na) ∧
    ∃ U : Subgroup G,
      (∀ x : G, x ∈ U ↔ x ∈ Na ∧ s * x * s⁻¹ = x⁻¹) ∧
      (U : Set G) = CFSG.OddInversion.invertedSet Na s ∧
      U = ⁅Na, Subgroup.zpowers s⁆ ∧ U ≤ Na ∧ IsMulCommutative U ∧
      (U.subgroupOf Na).Characteristic ∧
      Nat.Coprime (Nat.card U) (U.relIndex Na) ∧ (U.subgroupOf Na).Normal ∧
      U ⊔ A = Na ∧ U ⊓ A = ⊥ ∧ U ⊓ Subgroup.centralizer ({s} : Set G) = ⊥ ∧
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
          (∀ z : Na, ∃ x : U, ∃ a : A, (e ⟨x, a⟩ : G) = z) := by
  let Na := (N t).map (C t).subtype
  let A := Na ⊓ Subgroup.centralizer ({s} : Set G)
  have hodd : Odd (Nat.card Na) := by
    rw [Subgroup.card_subtype]
    exact actual_centralizer_core_odd t
  have hsolv : Group.IsSolvable Na := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsNa : s ∈ Subgroup.normalizer (Na : Set G) :=
    actual_centralizer_core_normalized t (C t) le_rfl hsC
  have hscalar := fun (ell : ℕ) (hell : ell.Prime) (hellN : ell ∣ Nat.card (N t))
      (P : Sylow ell (N t)) (hP : OriginalStationaryCoverAt t s ell P) =>
    stationary_layer_cover_local_prime_is_centralized_or_inverted hGnonab hrecognition
      n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel
      hell hellN P hP
  have hprime : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card Na →
      ∃ Pa : Subgroup G, Principal.PrimewiseScalar.IsSylowOf Na ell Pa ∧
        (∀ x ∈ Pa, s * x * s⁻¹ ∈ Pa) ∧
        ((∀ x ∈ Pa, s * x * s⁻¹ = x) ∨ (∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹)) := by
    intro ell hell hellNa
    let : Fact ell.Prime := ⟨hell⟩
    have hellN : ell ∣ Nat.card (N t) := by
      simpa only [Na, Subgroup.card_subtype] using hellNa
    obtain ⟨P, hP⟩ := hprimes ell hellN
    obtain ⟨Q, hQ⟩ := ambient_sylow_from_intrinsic hell (C t) (N t) P
    refine ⟨originalSylowAmbient t P, ⟨Q, hQ⟩, ?_, (hscalar ell hell hellN P hP).1⟩
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp
      (hP.1 (Subgroup.subset_closure (Set.mem_insert_of_mem t (Set.mem_singleton s)))) x).mp hx
  have hHall := Principal.PrimewiseScalar.hall_of_scalar Na hsolv hodd hsNa hs hprime
  obtain ⟨U, hUset, hUcomm, hUN, hUab, hUchar, hUHall, hUn, hgen, hdisj,
    hfixed, hcard, hsupport, hunique, hnormalizer⟩ :=
    Principal.PrimewiseScalar.hall_full Na hsolv hodd hsNa hs hHall
  refine ⟨hodd, hsolv, hscalar, hHall, U, ?_, hUset, hUcomm, hUN, hUab, hUchar,
    hUHall, hUn, hgen, hdisj, hfixed, hcard, hsupport, hunique, hnormalizer, ?_, ?_, ?_, ?_⟩
  · intro x
    change x ∈ (U : Set G) ↔ _
    rw [hUset]
    rfl
  · intro hNa
    exact ⟨le_bot_iff.mp (hNa ▸ hUN), le_bot_iff.mp (hNa ▸ (inf_le_left : A ≤ Na))⟩
  · intro hA
    calc U = U ⊔ ⊥ := (sup_bot_eq U).symm
      _ = U ⊔ A := congrArg (fun K : Subgroup G => U ⊔ K) (show A = ⊥ from hA).symm
      _ = Na := hgen
  · intro hU
    calc A = ⊥ ⊔ A := (bot_sup_eq A).symm
      _ = U ⊔ A := congrArg (fun K : Subgroup G => K ⊔ A) hU.symm
      _ = Na := hgen
  · exact original_normal_complement_literal_semidirect Na U A hUN inf_le_left hUn hgen hdisj

end CFSG.Semidihedral.LocalInvertedHallSubgroups
