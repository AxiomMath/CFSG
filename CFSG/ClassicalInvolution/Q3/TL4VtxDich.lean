module

public import CFSG.ClassicalInvolution.Q3.TL4VtxOrb
public import CFSG.ClassicalInvolution.Q3.TL4OddSecE2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

section Class

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem le_center_of_normal_of_cls (hd : TightDatum R S t) (hc : TightCls Y R S t)
    {N : Subgroup Y} (hNn : N.Normal) (htN : t ∉ N) : N ≤ Subgroup.center Y := by
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hd.sylow_core.2.1
  have hSN : S₀ ⊓ N = ⊥ := by
    by_contra hne
    exact htN (Subgroup.mem_inf.mp (hd.mem_of_ne_bot (inf_le_left.trans hd.S₀_le)
      (hS₀2.to_le inf_le_left) hne)).2
  have h1 := comm613Gen_normal hd.hypOmegaGen hd.S₀_mem_RSet hNn hSN
  have h2 : oddCoreOf N = ⊥ := by
    rw [AscThmA.oddCoreOf_eq_inf, show classicalInvolutionOddCore Y = ⊥ from hc.2.2, inf_bot_eq]
  rw [h2, le_bot_iff] at h1
  have hSC : S₀ ≤ Subgroup.centralizer (N : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have htop : Subgroup.centralizer (N : Set Y) = ⊤ := hd.eq_top_of_conj hc.2.1 fun y x hx => by
    rw [mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : y⁻¹ * p * y ∈ N := by simpa using hNn.conj_mem p hp y⁻¹
    have := Subgroup.mem_centralizer_iff.mp (hSC hx) _ hp'
    calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [this]
      _ = x * p := by group
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (N : Set Y) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm

theorem isPGroup_two_of_le_center (hO : classicalInvolutionOddCore Y = ⊥) {N : Subgroup Y}
    (hN : N ≤ Subgroup.center Y) : IsPGroup 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set y : Y := (g : Y) ^ 2 ^ k with hy
  have hyZ : y ∈ Subgroup.center Y := Subgroup.pow_mem _ (hN g.2) _
  have hZle : Subgroup.zpowers y ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr hyZ
  have hnorm : (Subgroup.zpowers y).Normal := ⟨fun a ha b => by
    have hab := Subgroup.mem_center_iff.mp (hZle ha) b
    rw [hab, mul_assoc, mul_inv_cancel, mul_one]
    exact ha⟩
  have hord : orderOf y = m := by
    have h1 : orderOf (g : Y) = 2 ^ k * m := by rw [Subgroup.orderOf_coe]; exact hkm
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (h1 ▸ dvd_mul_right _ _), h1,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hcard : Odd (Nat.card ↥(Subgroup.zpowers y)) := by rw [Nat.card_zpowers, hord]; exact hm
  have hle : Subgroup.zpowers y ≤ classicalInvolutionOddCore Y := le_sSup ⟨hnorm, hcard⟩
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hord
  exact ⟨k, by rw [hkm, ← hord, mul_one]⟩

theorem component_eq_of_le {A C : Subgroup Y} (hA : IsComponent A) (hC : IsComponent C)
    (hle : A ≤ C) : A = C := by
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := exists_ne_of_isComponent hA
  exact hab (comm_of_ne hA hC hne ha (hle hb))

theorem component_unique_of_cls (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) {A B : Subgroup Y} (hA : IsComponent A) (hB : IsComponent B) :
    A = B := by
  rcases tightDichotomy_of hd hc with h | hq | ⟨L, hL, -, hlay, -⟩
  · exact absurd h hE2
  · have hFn := genFittingFStar_normal Y
    have hF : IsComponent (genFittingFStar Y) := by
      refine (CFSG.isComponent_iff_open _).mpr ⟨le_top, IsSubnormal.step le_top ?_
        (IsSubnormal.refl _), hq⟩
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr fun g _ =>
        Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)
    have hle : ∀ {D : Subgroup Y}, IsComponent D → D ≤ genFittingFStar Y := fun hD => by
      have h1 := CFSG.LocalCores.component_le_layer hD
      rw [← genFittingLayer_eq_layer] at h1
      exact h1.trans le_sup_right
    rw [component_eq_of_le hA hF (hle hA), component_eq_of_le hB hF (hle hB)]
  · rw [component_eq_of_le hA hL (hlay ▸ CFSG.LocalCores.component_le_layer hA),
      component_eq_of_le hB hL (hlay ▸ CFSG.LocalCores.component_le_layer hB)]

end Class

section Orbit

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem nonempty_sylow_equiv (h : TypeRFam 3 Φ) {K : Subgroup Q} (hK : K ∈ Φ)
    (S : Sylow 2 ↥K) : Nonempty (↥(S : Subgroup K) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := h.quat K hK _ (isSylow2In_map_subtype K S)
  exact ⟨((S : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans e⟩

theorem tightDatum_of_mem (h : TypeRFam 3 Φ) {K : Subgroup Q} (hK : K ∈ Φ) {z : Q}
    (hz : IsUniqueInvolution K z) (S : Sylow 2 ↥K) : TightDatum K S z where
  quat := ⟨3, le_rfl, nonempty_sylow_equiv h hK S⟩
  mem := T3.mem_of_isPGroup hz (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet h.hyp
      (mem_RSet_of_isSylow2In hK (isSylow2In_map_subtype K S))))
  order := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  cent := h.le_centralizer hK hz
  normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (h.le_centralizer hK hz)).mpr
    (h.tight K hK z hz)
  twoGroup := h.twoGroup K hK

theorem tightCls_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) :
    ∃ S' : Sylow 2 ↥(K.subgroupOf (orbGrp Φ K)),
      TightDatum (K.subgroupOf (orbGrp Φ K)) S' ⟨z, le_orbGrp K hz.mem⟩ ∧
        TightCls ↥(orbGrp Φ K) (K.subgroupOf (orbGrp Φ K)) S' ⟨z, le_orbGrp K hz.mem⟩ := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  have hd := tightDatum_of_mem h hK hz S
  have hcl := h.hyp.conjInvariant
  have hKX : K ≤ orbGrp Φ K := le_orbGrp K
  obtain ⟨S', hd', ⟨e⟩⟩ := hd.restrict (H := orbGrp Φ K) ((Subgroup.map_subtype_le _).trans hKX)
  refine ⟨S', hd', ⟨e.trans (nonempty_sylow_equiv h hK S).some⟩, ?_, ?_⟩
  · have hcore : tightCore (K.subgroupOf (orbGrp Φ K)) = K.subgroupOf (orbGrp Φ K) := by
      rw [tightCore_subgroupOf ((tightCore_le K).trans hKX)]
      congr 1
      exact h.closure_twoElts hK
    show (⨆ g : ↥(orbGrp Φ K), conjSub g (tightCore (K.subgroupOf (orbGrp Φ K)))) = ⊤
    rw [hcore]
    apply Subgroup.map_injective (orbGrp Φ K).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ g : ↥(orbGrp Φ K), (conjSub g (K.subgroupOf (orbGrp Φ K))).map
        (orbGrp Φ K).subtype = conjSub (g : Q) K := by
      intro g
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact conjSub_le_orbGrp K ⟨g, orbGrp_le hcl hK g.2⟩
    simp_rw [e2]
    exact (orbGrp_eq_iSup hcl hK (commute_conj_of_not_conj h4 h hO hn hK)).symm
  · exact oddCore_eq_bot_of_isSubnormal (isSubnormal_orbGrp hcl hK) hO

theorem not_tightInO2_orbGrp (hcl : ConjInvariant Φ) {K : Subgroup Q} (hK : K ∈ Φ) {z : Q}
    (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) :
    ¬ TightInO2 (⟨z, le_orbGrp K hz.mem⟩ : ↥(orbGrp Φ K)) := by
  rintro ⟨P, hPn, hP2, hzP⟩
  obtain ⟨y, hy, hne⟩ := hm
  have hLX := le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y, hy, hne⟩
  have hc := commute_of_mem_normal_isPGroup (CFSG.LocalCores.component_overgroup hL hLX) hPn
    hP2 hzP ⟨y, hLX hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
  exact hne (congrArg Subtype.val hc)

theorem moves_atMostOne (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L₁ L₂ : Subgroup Q}
    (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) (hm₁ : ∃ y ∈ L₁, z * y ≠ y * z)
    (hm₂ : ∃ y ∈ L₂, z * y ≠ y * z) : L₁ = L₂ := by
  have hcl := h.hyp.conjInvariant
  have hle : ∀ {L : Subgroup Q}, IsComponent L → (∃ y ∈ L, z * y ≠ y * z) →
      L ≤ orbGrp Φ K :=
    fun hL ⟨y, hy, hne⟩ => le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y, hy, hne⟩
  obtain ⟨S', hd', hc'⟩ := tightCls_orbGrp h4 h hO hn hK hz
  have e := component_unique_of_cls hd' hc' (not_tightInO2_orbGrp hcl hK hz hL₁ hm₁)
    (CFSG.LocalCores.component_overgroup hL₁ (hle hL₁ hm₁))
    (CFSG.LocalCores.component_overgroup hL₂ (hle hL₂ hm₂))
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr (hle hL₁ hm₁),
    inf_eq_left.mpr (hle hL₂ hm₂)] at e

theorem normal_subgroupOf_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) : (L.subgroupOf (orbGrp Φ K)).Normal := by
  have hcl := h.hyp.conjInvariant
  obtain ⟨y, hy, hne⟩ := hm
  have hLX := le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y, hy, hne⟩
  obtain ⟨S', hd', hc'⟩ := tightCls_orbGrp h4 h hO hn hK hz
  have hcomp := CFSG.LocalCores.component_overgroup hL hLX
  refine ⟨fun a ha g => ?_⟩
  have h1 : conjSub g (L.subgroupOf (orbGrp Φ K)) = L.subgroupOf (orbGrp Φ K) :=
    component_unique_of_cls hd' hc' (not_tightInO2_orbGrp hcl hK hz hL ⟨y, hy, hne⟩)
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hcomp) hcomp
  rw [← h1]
  exact conj_mem_conjSub ha

theorem orbGrp_le_normalizer (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) : orbGrp Φ K ≤ Subgroup.normalizer (L : Set Q) := by
  obtain ⟨y, hy, hne⟩ := hm
  have hLX := le_orbGrp_of_moves h.hyp.conjInvariant hK hL ⟨z, hz.mem, y, hy, hne⟩
  have hN := normal_subgroupOf_orbGrp h4 h hO hn hK hz hL ⟨y, hy, hne⟩
  intro x hx
  refine (mem_normalizer_subgroupOf_iff (y := ⟨x, hx⟩) hLX).mpr ?_
  exact Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)

theorem centralizer_subgroupOf_le_center (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) :
    Subgroup.centralizer ((L.subgroupOf (orbGrp Φ K) : Subgroup ↥(orbGrp Φ K)) :
      Set ↥(orbGrp Φ K)) ≤ Subgroup.center ↥(orbGrp Φ K) := by
  obtain ⟨S', hd', hc'⟩ := tightCls_orbGrp h4 h hO hn hK hz
  have hN := normal_subgroupOf_orbGrp h4 h hO hn hK hz hL hm
  refine le_center_of_normal_of_cls hd' hc' inferInstance fun hzC => ?_
  obtain ⟨y, hy, hne⟩ := hm
  have hLX := le_orbGrp_of_moves h.hyp.conjInvariant hK hL ⟨z, hz.mem, y, hy, hne⟩
  exact hne (congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hzC ⟨y, hLX hy⟩ (Subgroup.mem_subgroupOf.mpr hy))).symm

theorem isPGroup_centralizer_subgroupOf (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z) {L : Subgroup Q} (hL : IsComponent L)
    (hm : ∃ y ∈ L, z * y ≠ y * z) :
    IsPGroup 2 ↥(Subgroup.centralizer ((L.subgroupOf (orbGrp Φ K) : Subgroup ↥(orbGrp Φ K)) :
      Set ↥(orbGrp Φ K))) :=
  isPGroup_two_of_le_center
    (oddCore_eq_bot_of_isSubnormal (isSubnormal_orbGrp h.hyp.conjInvariant hK) hO)
    (centralizer_subgroupOf_le_center h4 h hO hn hK hz hL hm)

end Orbit

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
