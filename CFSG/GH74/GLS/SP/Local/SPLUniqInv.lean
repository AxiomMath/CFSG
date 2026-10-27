module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXCtx
public import CFSG.GH74.GLS.SP.Local.SPLTabL2
public import CFSG.GH74.GLS.SP.Local.SPLTabA7
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped MatrixGroups

@[expose] def AtMostOneInvolution (K : Type) [Group K] : Prop :=
  ∀ x y : K, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y

theorem AtMostOneInvolution.of_le {X : Type} [Group X] {A L : Subgroup X} (hAL : A ≤ L)
    (h : AtMostOneInvolution ↥L) : AtMostOneInvolution ↥A := by
  intro x y hx hy hx1 hy1
  have hx' : (⟨(x : X), hAL x.2⟩ : ↥L) * ⟨(x : X), hAL x.2⟩ = 1 :=
    Subtype.ext (by simpa using congrArg (fun u : ↥A => (u : X)) hx)
  have hy' : (⟨(y : X), hAL y.2⟩ : ↥L) * ⟨(y : X), hAL y.2⟩ = 1 :=
    Subtype.ext (by simpa using congrArg (fun u : ↥A => (u : X)) hy)
  have hx1' : (⟨(x : X), hAL x.2⟩ : ↥L) ≠ 1 := fun h' =>
    hx1 (Subtype.ext (by simpa using congrArg (fun u : ↥L => (u : X)) h'))
  have hy1' : (⟨(y : X), hAL y.2⟩ : ↥L) ≠ 1 := fun h' =>
    hy1 (Subtype.ext (by simpa using congrArg (fun u : ↥L => (u : X)) h'))
  exact Subtype.ext (by simpa using congrArg (fun u : ↥L => (u : X)) (h _ _ hx' hy' hx1' hy1'))

theorem atMostOneInvolution_of_hasSL2Model {K : Type} [Group K] (h : HasSL2Model K Odd) :
    AtMostOneInvolution K := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
  let e' : K ≃* SL(2, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  intro x y hx hy hx1 hy1
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  rw [CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e'] at hxo hyo
  exact hxo.trans hyo.symm

theorem atMostOneInvolution_of_isDoubleCoverOfAlt {K : Type} [Group K] [Finite K]
    (h : IsDoubleCoverOfAlt K 7) : AtMostOneInvolution K := by
  obtain ⟨π, hπ⟩ := CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt (H := K) (n := 7)
    ⟨h.1, inferInstance, h.2.1, h.2.2⟩
  have hker : ∀ x : K, x * x = 1 → x ∈ π.ker := by
    intro x hx
    by_contra hxk
    have hπx : π x ≠ 1 := hxk
    have hsq : ((π x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, pow_two, hx, map_one]
      rfl
    have hne : ((π x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ≠ 1 := fun h' =>
      hπx (Subtype.ext h')
    have hs := Equiv.Perm.mem_alternatingGroup.mp (π x).2
    have hct : ((π x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
      rcases IVK.A7.involution_cycleType _ hsq hne with h' | h' | h'
      · exfalso
        rw [Equiv.Perm.sign_of_cycleType, h'] at hs
        exact absurd hs (by decide)
      · exact h'
      · exfalso
        rw [Equiv.Perm.sign_of_cycleType, h'] at hs
        exact absurd hs (by decide)
    have h4 := hπ.orderOf_eq_four_of_cycleType_two_two (by norm_num) hct
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
    rw [h4] at h2
    exact absurd h2 (by decide)
  intro x y hx hy hx1 hy1
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp hπ.card_ker
  have hxc : (⟨x, hker x hx⟩ : π.ker) = c := hc _ (fun h' => hx1 (congrArg Subtype.val h'))
  have hyc : (⟨y, hker y hy⟩ : π.ker) = c := hc _ (fun h' => hy1 (congrArg Subtype.val h'))
  exact congrArg Subtype.val (hxc.trans hyc.symm)

theorem not_atMostOneInvolution_of_isL2 {A : Type} [Group A] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hA : IVK.IsL2 A (fun r => r = q)) : ¬ AtMostOneInvolution A := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hA
  have hFq' : Nat.card F = q := hFq
  have hF : IVK.L2Field F := ⟨by rw [hFq']; exact hq, by omega⟩
  intro hU
  have hev : Even (Nat.card A) := IVK.Proofs2.even_card_of_l2 hF e
  have : Finite A := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (even_iff_two_dvd.mp hev)
  have hu2 : u * u = 1 := by
    rw [← pow_two, ← hu]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  have hcen : u ∈ center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g * u * g⁻¹ = u := by
      refine hU _ _ ?_ hu2 ?_ hu1
      · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      · intro h
        apply hu1
        calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
    calc g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [hg]
  let e' : A ≃* CFSG.GorensteinWalter.PSL2 F := e.trans (IVK.L2.equivPSL F)
  have hc2 : e' u ∈ center (CFSG.GorensteinWalter.PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen g']
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot F, Subgroup.mem_bot] at hc2
  exact hu1 (e'.injective (hc2.trans (map_one e').symm))

section CentralQuotient

variable {K : Type} [Group K]

@[expose] noncomputable def centerQuotAut (σ : MulAut K) : MulAut (K ⧸ center K) :=
  QuotientGroup.congr (center K) (center K) σ (Subgroup.map_center_eq σ)

theorem centerQuotAut_mk (σ : MulAut K) (x : K) :
    centerQuotAut σ (x : K ⧸ center K) = ((σ x : K) : K ⧸ center K) := rfl

theorem centerQuotAut_sq (σ : MulAut K) (hσ : σ ^ 2 = 1) : centerQuotAut σ ^ 2 = 1 := by
  have h : ∀ x : K, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut K => f x) hσ
    simpa [pow_two] using this
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
  rw [centerQuotAut_mk, centerQuotAut_mk, h]

@[expose] def twistHom (σ : MulAut K) {H : Type} [Group H] (ι : H →* K)
    (hH : ∀ x : H, (ι x)⁻¹ * σ (ι x) ∈ center K) : H →* center K where
  toFun x := ⟨(ι x)⁻¹ * σ (ι x), hH x⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    have hc := Subgroup.mem_center_iff.mp (hH x) (ι y)⁻¹
    show (ι (x * y))⁻¹ * σ (ι (x * y)) = ((ι x)⁻¹ * σ (ι x)) * ((ι y)⁻¹ * σ (ι y))
    rw [map_mul, map_mul]
    calc (ι x * ι y)⁻¹ * (σ (ι x) * σ (ι y)) = (ι y)⁻¹ * ((ι x)⁻¹ * σ (ι x)) * σ (ι y) := by group
      _ = ((ι x)⁻¹ * σ (ι x)) * (ι y)⁻¹ * σ (ι y) := by rw [hc]
      _ = ((ι x)⁻¹ * σ (ι x)) * ((ι y)⁻¹ * σ (ι y)) := by group

theorem eq_one_of_centerQuotAut_eq_one [Group.IsPerfect K] {σ : MulAut K}
    (h : centerQuotAut σ = 1) : σ = 1 := by
  have hZ : ∀ x : K, ((MonoidHom.id K) x)⁻¹ * σ ((MonoidHom.id K) x) ∈ center K := fun x => by
    have h1 : centerQuotAut σ (x : K ⧸ center K) = (x : K ⧸ center K) := by
      rw [h]
      rfl
    exact QuotientGroup.eq.mp h1.symm
  have hle := Abelianization.commutator_subset_ker (twistHom σ (MonoidHom.id K) hZ)
  rw [Group.IsPerfect.commutator_eq_top] at hle
  ext x
  have hx : x ∈ (twistHom σ (MonoidHom.id K) hZ).ker := hle (Subgroup.mem_top x)
  have h2 : x⁻¹ * σ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact (inv_mul_eq_one.mp h2).symm

theorem centerQuotAut_ne_one [Group.IsPerfect K] {σ : MulAut K} (hσ : σ ≠ 1) :
    centerQuotAut σ ≠ 1 := fun h => hσ (eq_one_of_centerQuotAut_eq_one h)

theorem card_fixedSubgroup_centerQuot_le [Finite K] (σ : MulAut K) :
    Nat.card ↥(fixedSubgroup (K ⧸ center K) (centerQuotAut σ)) ≤
      Nat.card ↥(fixedSubgroup K σ) := by
  set Z : Subgroup K := center K with hZdef
  set Cb : Subgroup (K ⧸ Z) := fixedSubgroup (K ⧸ Z) (centerQuotAut σ) with hCb
  set C : Subgroup K := fixedSubgroup K σ with hC
  let N : Subgroup K := Cb.comap (QuotientGroup.mk' Z)
  have hNZ : ∀ x : N, ((N.subtype x))⁻¹ * σ (N.subtype x) ∈ center K := fun x =>
    QuotientGroup.eq.mp (x.2 : centerQuotAut σ ((x : K) : K ⧸ Z) = ((x : K) : K ⧸ Z)).symm
  let ψ : N →* center K := twistHom σ N.subtype hNZ
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card N := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.ker ≤ Nat.card C := by
    have hfix : ∀ x : ψ.ker, σ ((x : N) : K) = ((x : N) : K) := fun x => by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact (inv_mul_eq_one.mp h).symm
    refine Nat.card_le_card_of_injective (fun x : ψ.ker => (⟨((x : N) : K), hfix x⟩ : C)) ?_
    intro x y hxy
    have h : ((x : N) : K) = ((y : N) : K) := congrArg (fun c : C => (c : K)) hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Nat.card ψ.range ≤ Nat.card (center K) := Subgroup.card_le_card_group _
  have h4 : Nat.card N = Nat.card Cb * Nat.card Z := by
    have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
    have hidx : N.index = Cb.index := Subgroup.index_comap_of_surjective Cb hsurj
    have e1 := Subgroup.card_mul_index N
    have e2 := Subgroup.card_mul_index Cb
    have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hpos : 0 < Cb.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have : Nat.card N * Cb.index = (Nat.card Cb * Nat.card Z) * Cb.index := by
      calc Nat.card N * Cb.index = Nat.card K := by rw [← hidx]; exact e1
        _ = Nat.card (K ⧸ Z) * Nat.card Z := e3
        _ = (Nat.card Cb * Cb.index) * Nat.card Z := by rw [e2]
        _ = (Nat.card Cb * Nat.card Z) * Cb.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h5 : Nat.card Cb * Nat.card Z ≤ Nat.card C * Nat.card Z := by
    rw [← h4, ← h1]
    exact Nat.mul_le_mul h2 h3
  exact Nat.le_of_mul_le_mul_right h5 hZpos

end CentralQuotient

theorem not_isPerfect_sl2_of_card_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ¬ Group.IsPerfect SL(2, F) := by
  intro hperf
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  have hperf3 : Group.IsPerfect SL(2, ZMod 3) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hp : IsPGroup 2 CFSG.ClassicalInvolution.sl2ThreeQ :=
    IsPGroup.of_card (n := 3) (by rw [CFSG.ClassicalInvolution.natCard_sl2ThreeQ]; norm_num)
  have : Group.IsNilpotent CFSG.ClassicalInvolution.sl2ThreeQ := hp.isNilpotent
  have := CFSG.ClassicalInvolution.sl2ThreeQ_normal
  have hsolvQ : Group.IsSolvable (SL(2, ZMod 3) ⧸ CFSG.ClassicalInvolution.sl2ThreeQ) := by
    have hc : Nat.card (SL(2, ZMod 3) ⧸ CFSG.ClassicalInvolution.sl2ThreeQ) = 3 := by
      have := CFSG.ClassicalInvolution.sl2ThreeQ_index
      rw [Subgroup.index] at this
      exact this
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : IsCyclic (SL(2, ZMod 3) ⧸ CFSG.ClassicalInvolution.sl2ThreeQ) :=
      isCyclic_of_prime_card hc
    infer_instance
  have hsolv : Group.IsSolvable SL(2, ZMod 3) :=
    Group.isSolvable_of_subgroup_quotient CFSG.ClassicalInvolution.sl2ThreeQ
  have : Nontrivial SL(2, ZMod 3) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [CFSG.ClassicalInvolution.natCard_sl2Three]; norm_num)
  exact Group.IsPerfect.not_isSolvable SL(2, ZMod 3) hsolv

theorem exists_quotCenter_equiv_L2 {K : Type} [Group K] (hK : IsQuasisimple K)
    (h : HasSL2Model K Odd) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), IVK.L2Field F ∧
      Nonempty (K ⧸ center K ≃* IVK.L2 F) := by
  obtain ⟨F, hF, hFin, hodd, ⟨e⟩⟩ := h
  have h3 : 3 < Nat.card F := by
    by_contra hle
    push Not at hle
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    have h3' : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hperfK : Group.IsPerfect K := hK.1
    let e' : K ≃* SL(2, F) :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
    exact not_isPerfect_sl2_of_card_three h3'
      (Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective)
  refine ⟨F, hF, hFin, ⟨hodd, h3⟩, ⟨QuotientGroup.congr (center K)
    ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) e ?_⟩⟩
  rw [Subgroup.map_center_eq e]
  exact (CFSG.Semidihedral.ProjectiveSL2Cover.statedScalarKernel_eq_center F 2).symm

theorem atMostOneInvolution_of_model {K : Type} [Group K] [Finite K]
    (h : HasSL2Model K Odd ∨ IsDoubleCoverOfAlt K 7) : AtMostOneInvolution K :=
  h.elim atMostOneInvolution_of_hasSL2Model atMostOneInvolution_of_isDoubleCoverOfAlt

theorem stableUniqueInvolution : StableUniqueInvolution := by
  intro X _ _ z t A T₁ L hX hL _ hmodel
  obtain ⟨q, hq, h5, hA⟩ := hX.A_L2
  exact not_atMostOneInvolution_of_isL2 hq h5 hA
    ((atMostOneInvolution_of_model hmodel).of_le hL.A_le)

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {G : Type*} [Group G] {a : G} (ha : a * a = 1)
    {y : G} (hy : y ∈ zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact ha
  have hk : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h]
    simp
  · right
    rw [hk, h]
    simp

theorem mem_sup_zpowers_cases {X : Type} [Group X] {z t : X} (hz : z * z = 1) (ht : t * t = 1)
    (hc : ∀ x : X, x * t = t * x) {x : X} (hx : x ∈ zpowers z ⊔ zpowers t) :
    x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  have hN : (zpowers t).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hg : g * t ^ k = t ^ k * g := (Commute.zpow_right (hc g) k).eq
    rw [hg, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hz hy with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self ht hw with rfl | rfl <;> simp

theorem otherUniqueInvolution : OtherUniqueInvolution := by
  intro X _ _ z t A T₁ K hX hK htK hKq hmodel
  have hU : AtMostOneInvolution ↥K := atMostOneInvolution_of_model hmodel
  have hzK : z ∉ K := by
    intro hz
    have h1 : (⟨z, hz⟩ : ↥K) = ⟨t, htK⟩ := hU _ _ (Subtype.ext hX.z_sq) (Subtype.ext hX.t_sq)
      (fun h => hX.z_ne_one (congrArg (fun u : ↥K => (u : X)) h))
      (fun h => hX.t_ne_one (congrArg (fun u : ↥K => (u : X)) h))
    exact hX.zt_ne (congrArg (fun u : ↥K => (u : X)) h1)
  let σ : MulAut ↥K :=
    { toFun := fun x => ⟨z * x * z⁻¹, hK.stable x x.2⟩
      invFun := fun x => ⟨z * x * z⁻¹, hK.stable x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show z * (z * (x : X) * z⁻¹) * z⁻¹ = x
        calc z * (z * (x : X) * z⁻¹) * z⁻¹ = (z * z) * (x : X) * (z * z)⁻¹ := by group
          _ = x := by rw [hX.z_sq]; group)
      right_inv := fun x => Subtype.ext (by
        show z * (z * (x : X) * z⁻¹) * z⁻¹ = x
        calc z * (z * (x : X) * z⁻¹) * z⁻¹ = (z * z) * (x : X) * (z * z)⁻¹ := by group
          _ = x := by rw [hX.z_sq]; group)
      map_mul' := fun x y => Subtype.ext (by
        show z * ((x : X) * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹)
        group) }
  have hσapp : ∀ x : ↥K, ((σ x : ↥K) : X) = z * x * z⁻¹ := fun x => rfl
  have hσfix : ∀ x : ↥K, σ x = x ↔ z * (x : X) = x * z := fun x => by
    rw [Subtype.ext_iff, hσapp, mul_inv_eq_iff_eq_mul]
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rw [hσapp, hσapp]
    calc z * (z * (x : X) * z⁻¹) * z⁻¹ = (z * z) * (x : X) * (z * z)⁻¹ := by group
      _ = x := by rw [hX.z_sq]; group
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨x, hxK, hx⟩ := hK.moves
    apply hx
    exact (hσfix ⟨x, hxK⟩).mp (by rw [h]; rfl)
  have hCle : fixedSubgroup ↥K σ ≤ zpowers (⟨t, htK⟩ : ↥K) := by
    intro x hx
    have hzx : z * (x : X) = x * z := (hσfix x).mp hx
    have hmem := hX.cen_A (x : X) hzx (fun a ha => hK.comm_A x x.2 a ha)
    rcases mem_sup_zpowers_cases hX.z_sq hX.t_sq hX.t_central hmem with h | h | h | h
    · have : x = 1 := Subtype.ext h
      rw [this]
      exact one_mem _
    · exact absurd (h ▸ x.2) hzK
    · have : x = ⟨t, htK⟩ := Subtype.ext h
      rw [this]
      exact mem_zpowers _
    · refine absurd ?_ hzK
      have h1 : z = (x : X) * t := by
        rw [h, mul_assoc, hX.t_sq, mul_one]
      rw [h1]
      exact K.mul_mem x.2 htK
  have hCcard : Nat.card ↥(fixedSubgroup ↥K σ) ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hCle
    rw [Nat.card_zpowers, Subgroup.orderOf_mk,
      orderOf_eq_prime (by rw [pow_two]; exact hX.t_sq) hX.t_ne_one] at h1
    exact h1
  have hperf : Group.IsPerfect ↥K := hKq.1
  have hbar2 := centerQuotAut_sq σ hσ2
  have hbar1 := centerQuotAut_ne_one hσ1
  have hle := card_fixedSubgroup_centerQuot_le σ
  have h4 : 4 ≤ Nat.card ↥(fixedSubgroup (↥K ⧸ center ↥K) (centerQuotAut σ)) := by
    rcases hmodel with hsl | hdc
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_quotCenter_equiv_L2 hKq hsl
      exact tabL2Card F hF (↥K ⧸ center ↥K) ⟨e⟩ (centerQuotAut σ) hbar2 hbar1
    · exact tabA7Card (↥K ⧸ center ↥K) hdc.2.2 (centerQuotAut σ) hbar2 hbar1
  omega

end CFSG.GH74.GLS.SP.Local
