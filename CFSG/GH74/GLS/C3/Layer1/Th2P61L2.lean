module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61Obs
public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy
open scoped commutatorElement

section Local

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem pPrimeCoreOf_outer_involution_eq_bot
    (hF : L2Field F) (e : K ≃* L2 F) (H : Subgroup (MulAut K)) (hH : innAut K ≤ H)
    {y : MulAut K} (hy2 : y * y = 1) (hy : y ∉ innDiagSub e) :
    pPrimeCoreOf 2 (H ⊓ centralizer ({y} : Set (MulAut K))) = ⊥ := by
  have hy1 : y ≠ 1 := fun h => hy (h ▸ (innDiagSub e).one_mem)
  have hproj : fieldProj e y ≠ 1 := fun h => hy ((mem_innDiagSub_iff e y).mpr h)
  have hord : orderOf (thetaAut e y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord
    (by rw [← fieldProj_apply]; exact hproj)
  set σ := (thetaAut e y).right with hσ
  have hΘφ : thetaAut e (fieldAutHom e σ) = SemidirectProduct.inr σ := thetaAut_fieldAutHom e σ
  set a : MulAut K := innDiagHom e C with ha
  have hΘa : thetaAut e a = SemidirectProduct.inl C := thetaAut_innDiagHom e C
  have hconj : a⁻¹ * y * a = fieldAutHom e σ := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, hΘa, hΘφ]
    exact hC
  have hσ2 : orderOf σ = 2 := by
    have hσ' : σ = fieldProj e y := rfl
    rw [hσ']
    refine orderOf_eq_prime ?_ hproj
    rw [← map_pow, pow_two, hy2, map_one]
  have hy' : y = a * fieldAutHom e σ * a⁻¹ := by rw [← hconj]; group
  have hH' : innAut K ≤ Th2.cj a⁻¹ H := by
    intro z hz
    rw [Th2.mem_cj_iff, inv_inv]
    apply hH
    obtain ⟨k, rfl⟩ := hz
    refine ⟨a k, ?_⟩
    exact (CFSG.GH74.GLS.Prop27.mul_conj_mul_inv a k).symm
  have h0 := pPrimeCoreOf_fieldInvolution_eq_bot hF e (Th2.cj a⁻¹ H) hH' σ hσ2
  have hkey : H ⊓ centralizer ({y} : Set (MulAut K)) =
      Th2.cj a (Th2.cj a⁻¹ H ⊓ centralizer ({fieldAutHom e σ} : Set (MulAut K))) := by
    unfold Th2.cj
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective]
    have h1 : (Th2.cj a⁻¹ H).map (MulAut.conj a).toMonoidHom = H := Th2.cj_inv_cj a H
    have h2 : (centralizer ({fieldAutHom e σ} : Set (MulAut K))).map (MulAut.conj a).toMonoidHom =
        centralizer ({y} : Set (MulAut K)) := by
      have := Th2.cj_centralizer_singleton a (fieldAutHom e σ)
      rw [← hy'] at this
      exact this
    rw [h1, h2]
  rw [hkey, Th2.pPrimeCoreOf_cj, h0]
  exact Subgroup.map_bot _

omit [Finite K] in
theorem centralizer_four_innDiagSub
    (hF : L2Field F) (e : K ≃* L2 F) (U : Subgroup (MulAut K))
    (hUD : U ≤ innDiagSub e) (h4 : IsFourSubgroup U) :
    centralizer (U : Set (MulAut K)) ⊓ innDiagSub e = U := by
  have hodd := isOddPrimePower_of_L2Field hF
  obtain ⟨hcomm, -⟩ := isFourSubgroup_props h4
  let ι : ↥(innDiagSub e) ≃* PGL2 F := innDiagEquiv e
  let V : Subgroup (PGL2 F) := (U.subgroupOf (innDiagSub e)).map ι.toMonoidHom
  let ψ : ↥V ≃* ↥U :=
    (Subgroup.equivMapOfInjective (U.subgroupOf (innDiagSub e)) ι.toMonoidHom ι.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hUD)
  have hV : IsKleinFour V :=
    { card_four := (Nat.card_congr ψ.toEquiv).trans h4.2
      exponent_two := (Monoid.exponent_eq_of_mulEquiv ψ).trans (exponent_of_isFourSubgroup h4) }
  have hcent := pgl2_kleinFour_centralizer_eq_self F hodd V hV
  ext g
  constructor
  · rintro ⟨hgC, hgD⟩
    have hmem : ι ⟨g, hgD⟩ ∈ Subgroup.centralizer (V : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hgC (u : MulAut K) hu
    rw [hcent] at hmem
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hmem
    have : u = ⟨g, hgD⟩ := ι.injective hue
    have hu' : (u : MulAut K) ∈ U := hu
    rw [this] at hu'
    exact hu'
  · intro hgU
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, hUD hgU⟩
    intro y hy
    exact hcomm y hy g hgU

omit [Finite K] in
theorem centralizer_four_comm
    (hF : L2Field F) (e : K ≃* L2 F) {U : Subgroup (MulAut K)}
    (hUD : U ≤ innDiagSub e) (h4 : IsFourSubgroup U) {x y : MulAut K}
    (hx : ∀ u ∈ U, x * u = u * x) (hy : ∀ u ∈ U, y * u = u * y) : x * y = y * x := by
  have hcyc : IsCyclic (F ≃+* F) :=
    ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  set C : Subgroup (MulAut K) := centralizer (U : Set (MulAut K)) with hC
  let θ : ↥C →* (F ≃+* F) := (fieldProj e).comp C.subtype
  have hker : θ.ker ≤ center ↥C := by
    intro c hc
    have hc1 : fieldProj e (c : MulAut K) = 1 := hc
    have hcD : (c : MulAut K) ∈ innDiagSub e := (mem_innDiagSub_iff e _).2 hc1
    have hcU : (c : MulAut K) ∈ U := by
      rw [← centralizer_four_innDiagSub hF e U hUD h4]
      exact ⟨c.2, hcD⟩
    rw [Subgroup.mem_center_iff]
    intro c'
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 c'.2 _ hcU).symm
  have hxC : x ∈ C := Subgroup.mem_centralizer_iff.2 fun u hu => (hx u hu).symm
  have hyC : y ∈ C := Subgroup.mem_centralizer_iff.2 fun u hu => (hy u hu).symm
  have := (θ.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm ⟨x, hxC⟩ ⟨y, hyC⟩
  exact congrArg Subtype.val this

end Local

section Global

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem innAut_le_range_barAct (J : Subgroup G) : innAut (kBar J) ≤ (barAct J).range := by
  rintro _ ⟨kb, rfl⟩
  induction kb using QuotientGroup.induction_on with | H k => ?_
  exact ⟨⟨(k : G), Subgroup.le_normalizer k.2⟩, barAct_of_mem k.2⟩

theorem obs_innDiag
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : kBar J ≃* L2 F) {d : G} (hd : d ∈ D) : barAct J ⟨d, h.D_norm d hd⟩ ∈ innDiagSub e := by
  classical
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  by_contra hnot
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ρ : ↥M →* MulAut (kBar J) := barAct J with hρ
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hnot
    have : (⟨1, h.D_norm 1 hd⟩ : ↥M) = 1 := rfl
    rw [this, map_one]
    exact (innDiagSub e).one_mem
  set Z : Subgroup (MulAut (kBar J)) := ρ.range with hZ
  have hInn : innAut (kBar J) ≤ Z := innAut_le_range_barAct J
  let φ : ↥M →* ↥Z := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  obtain ⟨x, hxX, hxmove⟩ := h.X_move
  have hxN : x ∈ M := h.X_norm x hxX
  have hdM : d ∈ M := h.D_norm d hd
  have hd2 : d * d = 1 := hBsq d (h.D_le hd)
  have hmem := map_mem_involutionOddCore φ hφ hdM hd2 hxN (h.mem_core hB hxX hd hd1)
  have hy2 : ρ ⟨d, hdM⟩ * ρ ⟨d, hdM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, hdM⟩ : ↥M) * ⟨d, hdM⟩ = 1 := Subtype.ext hd2
    rw [this, map_one]
  have hbot : involutionOddCore (φ ⟨d, hdM⟩) = ⊥ := by
    refine involutionOddCore_eq_bot_of_pPrimeCoreOf Z (φ ⟨d, hdM⟩) ?_
    exact pPrimeCoreOf_outer_involution_eq_bot hF e Z hInn (y := ρ ⟨d, hdM⟩) hy2 hnot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hxmove ((barAct_eq_one_iff _).1 (congrArg Subtype.val hmem))

omit [Finite G] in
theorem card_map_barAct {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D) :
    Nat.card ((D.subgroupOf (normalizer (J : Set G))).map (barAct J)) = Nat.card D := by
  set M : Subgroup G := normalizer (J : Set G) with hM
  have hDM : D ≤ M := fun d hd => h.D_norm d hd
  have hbij : Function.Bijective ((barAct J).subgroupMap (D.subgroupOf M)) := by
    refine ⟨?_, (barAct J).subgroupMap_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro m hm
    have h1 : barAct J (m : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    have hmD : ((m : ↥M) : G) ∈ D := Subgroup.mem_subgroupOf.mp m.2
    by_contra hne
    have hm1 : ((m : ↥M) : G) ≠ 1 := by
      intro h1'
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact h1'
    exact h.D_faith _ hmD hm1 ((barAct_eq_one_iff _).1 h1)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv

theorem obs_L2_four
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : kBar J ≃* L2 F) :
    IsFourSubgroup ((D.subgroupOf (normalizer (J : Set G))).map (barAct J)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  set U : Subgroup (MulAut (kBar J)) := (D.subgroupOf M).map (barAct J) with hU
  have hUD : U ≤ innDiagSub e := by
    rintro _ ⟨m, hm, rfl⟩
    exact obs_innDiag h hB hF e (Subgroup.mem_subgroupOf.mp hm)
  have hUsq : ∀ x ∈ U, x * x = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hBsq m (h.D_le (Subgroup.mem_subgroupOf.mp hm)))
    rw [this, map_one]
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (h.D_le (Subgroup.mem_subgroupOf.mp hm)) _ (h.D_le (Subgroup.mem_subgroupOf.mp hn))
  have hUel : CFSG.IsElementaryAbelian 2 ↥U := isElementaryAbelian_two_of_sq U hUsq
  have hU2 : IsPGroup 2 ↥U := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨T', hT'⟩ := hU2.exists_le_sylow
  have hle : Nat.card ↥U ≤ 4 := card_le_four_of_le_inf e hF T' U hT' hUD hUc hUsq
  have hge : 4 ≤ Nat.card ↥U := by
    rw [hU, card_map_barAct h]
    exact h.D_card
  exact ⟨hUel, le_antisymm hle hge⟩

theorem obs_L2_not_B
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G))
    {F : Type} [Field F] [Finite F] (hF : L2Field F) (e : kBar J ≃* L2 F) : False := by
  classical
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  obtain ⟨y, β, hy, hβ, hx, -, hnc⟩ := h.exists_noncomm hB hBN
  have hxX : ⁅y, β⁆ ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ :=
    Subgroup.commutator_mem_commutator hy hβ
  have hU := obs_L2_four h hB hF e
  have hUD : (D.subgroupOf M).map (barAct J) ≤ innDiagSub e := by
    rintro _ ⟨m, hm, rfl⟩
    exact obs_innDiag h hB hF e (Subgroup.mem_subgroupOf.mp hm)
  apply hnc
  refine centralizer_four_comm hF e hUD hU ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ hβ _ (h.D_le hmD)
  · rintro _ ⟨m, hm, rfl⟩
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact h.comm_D hB hxX hmD

end Global


end CFSG.GH74.GLS.Th2.Obs
