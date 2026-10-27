module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthImage
public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthBig
public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthFrame
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

section Lift

variable {K Γ : Type*} [Group K] [Group Γ] (θ : K →* Γ)

theorem eq_of_map_eq_of_cubes (hker : θ.ker ≤ Subgroup.center K)
    (hker2 : ∀ c ∈ θ.ker, c * c = 1) {L L' : Subgroup K}
    (hL : ∀ a ∈ L, ∃ u₁ ∈ L, ∃ u₂ ∈ L, ∃ u₃ ∈ L, u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧
      a = u₁ * u₂ * u₃)
    (hL' : ∀ a ∈ L', ∃ u₁ ∈ L', ∃ u₂ ∈ L', ∃ u₃ ∈ L', u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧
      a = u₁ * u₂ * u₃)
    (h : L.map θ = L'.map θ) : L = L' := by
  have key : ∀ {L L' : Subgroup K}, L.map θ ≤ L'.map θ →
      ∀ u ∈ L, u ^ 3 = 1 → u ∈ L' := by
    intro L L' hle u hu hu3
    obtain ⟨u', hu', hθ⟩ := hle (Subgroup.mem_map_of_mem θ hu)
    have hc : u'⁻¹ * u ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
    set c := u'⁻¹ * u with hcdef
    have hcc : c * c = 1 := hker2 c hc
    have hcz : ∀ w : K, w * c = c * w := fun w => Subgroup.mem_center_iff.mp (hker hc) w
    have hu_eq : u = u' * c := by rw [hcdef]; group
    have h3 : u ^ 3 = u' ^ 3 * c := by
      rw [hu_eq, Commute.mul_pow (show Commute u' c from hcz u') 3, pow_three c, hcc, mul_one]
    have hcinv : c = (u' ^ 3)⁻¹ := by
      rw [h3] at hu3
      exact eq_inv_of_mul_eq_one_right hu3
    rw [hu_eq, hcinv]
    exact L'.mul_mem hu' (L'.inv_mem (L'.pow_mem hu' 3))
  have hgen : ∀ {L L' : Subgroup K}, (∀ a ∈ L, ∃ u₁ ∈ L, ∃ u₂ ∈ L, ∃ u₃ ∈ L, u₁ ^ 3 = 1 ∧
      u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧ a = u₁ * u₂ * u₃) → L.map θ ≤ L'.map θ → L ≤ L' := by
    intro L L' hL hle a ha
    obtain ⟨u₁, h₁, u₂, h₂, u₃, h₃, e₁, e₂, e₃, rfl⟩ := hL a ha
    exact L'.mul_mem (L'.mul_mem (key hle u₁ h₁ e₁) (key hle u₂ h₂ e₂)) (key hle u₃ h₃ e₃)
  exact le_antisymm (hgen hL h.le) (hgen hL' h.ge)

end Lift

section Main

open CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

private theorem natCard_galoisField_three' : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem exists_frame_map_eq_of_isClassicalMember3 (hQ : (polarBilin Q).Nondegenerate)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) (hz : spinAction Q z ≠ 1) :
    ∃ fr : Frame Q, L.map (spinAction Q) = fr.La.range := by
  have hF : Nat.card (GaloisField 3 1) = 3 := natCard_galoisField_three'
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hF]; decide
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  set θ := spinAction Q with hθ
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hO
  let e : SL(2, ZMod 3) ≃* L := eL.symm
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hLC : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  obtain ⟨x₀, hx₀⟩ := e.surjective ⟨z, h.mem⟩
  have hx₀z : ((e x₀ : L) : spinGroup Q) = z := congrArg Subtype.val hx₀
  have hx₀sq : x₀ ^ 2 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hx₀z, pow_two, hzz, map_one]
    rfl
  have hx₀neg : x₀ = -1 := by
    rcases eq_neg_one_of_sq_eq_one x₀ hx₀sq with h1 | h1
    · exact absurd (by rw [← hx₀z, h1, map_one]; rfl) h.ne_one
    · exact h1
  have hez : ((e (-1) : L) : spinGroup Q) = z := by rw [← hx₀neg]; exact hx₀z
  let φ : SL(2, ZMod 3) →* (V ≃ₗ[GaloisField 3 1] V) := (θ.comp L.subtype).comp e.toMonoidHom
  have hφ : ∀ g, φ g = θ ((e g : L) : spinGroup Q) := fun g => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : ((e g : L) : spinGroup Q) ∈ θ.ker := hg
    have hsq := hker2 _ hg'
    have hg2 : g ^ 2 = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow, pow_two, hsq, map_one]
      rfl
    rcases eq_neg_one_of_sq_eq_one g hg2 with h1 | h1
    · exact h1
    · exfalso
      apply hz
      rw [← hez, ← hφ]
      rw [h1] at hg
      exact hg
  have hrangeL : φ.range = L.map θ := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, (e g).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, hg⟩ := e.surjective ⟨x, hx⟩
      exact ⟨g, by rw [hφ, hg]⟩
  have hrangeO : θ.range ≤ O := by
    rw [hrange]
    exact Subgroup.commutator_le_self O
  set i := θ z with hi_def
  have hiO : i ∈ O := hrangeO ⟨z, rfl⟩
  have hii : i * i = 1 := by rw [hi_def, ← map_mul, hzz, map_one]
  have hi2 : orderOf i = 2 := orderOf_eq_prime (by rw [pow_two]; exact hii) hz
  have hV : minusSp i ≠ ⊥ := by
    intro hbot
    refine hz (LinearEquiv.ext fun x => ?_)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule (GaloisField 3 1) V) := hbot ▸ hv
      exact (Submodule.mem_bot _).mp this
    rw [hv0, add_zero]
    exact mem_plusSp.mp hu
  have hφO : ∀ g, φ g ∈ O := fun g => hrangeO ⟨_, rfl⟩
  have hφc : ∀ g, φ g * i = i * φ g := fun g => by
    rw [hφ, hi_def, ← map_mul, ← map_mul, hLC _ (e g).2]
  have hφi : φ (-1) = i := by rw [hφ, hez]
  set T := (Subgroup.centralizer ({z} : Set (spinGroup Q))).map θ with hT
  have hsub : IsSubnormal φ.range T := by
    rw [hrangeL]
    exact isSubnormal_map θ h.subnormal
  have hTC : T ≤ O ⊓ Subgroup.centralizer ({i} : Set (V ≃ₗ[GaloisField 3 1] V)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hrangeO ⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [hi_def, ← map_mul, ← map_mul, hy']
  have hT3 : ∀ g ∈ O, g * i = i * g → g ^ 3 = 1 → g ∈ T := fun g hgO hgc hg3 =>
    mem_map_centralizer_of_pow_three hQnd θ hker hker2 hrange hgO hg3 hgc
  have hTE : T ≤ elementaryGroup Q := by
    rintro _ ⟨y, -, rfl⟩
    exact hE (hrange ▸ ⟨y, rfl⟩)
  have hnM := range_le_nM_of_isSubnormal hF hQ hiO hii hV φ hφinj hφO hφc hφi hsub hTC hT3 hTE
  have hφn : ∀ g, φ g ∈ nM Q i := fun g => hnM ⟨g, rfl⟩
  have hdet : LinearEquiv.det i = 1 := by
    have hmem : i ∈ θ.range := ⟨z, rfl⟩
    rw [hrange] at hmem
    exact det_eq_one_of_mem_commutator hmem
  have hW : PolarNondegOn Q (minusSp i) := polarNondegOn_minusSp h2 hQ hiO hii
  have hQ' : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp i)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have heven : Even (Module.finrank (GaloisField 3 1) (minusSp i)) :=
    even_finrank_minusSp h2 hii hdet
  obtain ⟨l, hlen, hlorth, hlne, hlspan, hldisc⟩ :=
    exists_orthogonal_list_restrict Q (minusSp i) hQ''
  obtain ⟨c, hc, hzz'⟩ := spinLift_sq_and_norm hQnd hiO hii rfl hlorth (hlen ▸ heven) hlspan hlne
  have hz2' : (z : CliffordAlgebra Q) * z = 1 := by
    have := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hzz
    simpa using this
  have hsign : ((-1 : GaloisField 3 1) ^ l.length.choose 2) = 1 := by
    apply algebraMap_injective' Q
    rw [← hzz', hz2', map_one]
  have hchoose : Even (l.length.choose 2) :=
    (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp hsign
  have h4a : 4 ∣ Module.finrank (GaloisField 3 1) (minusSp i) := by
    rw [← hlen]
    exact four_dvd_of_even_of_even_choose (hlen ▸ heven) hchoose
  have ha0 : Module.finrank (GaloisField 3 1) (minusSp i) ≠ 0 := fun h0 =>
    hV (Submodule.finrank_eq_zero.mp h0)
  have hcase : Module.finrank (GaloisField 3 1) (minusSp i) = 4 ∨
      8 ≤ Module.finrank (GaloisField 3 1) (minusSp i) := by
    obtain ⟨k, hk⟩ := h4a
    omega
  rcases hcase with hdim | hdim
  swap
  · exact (false_of_finrank_minus_ge_eight3 hF hQ hiO hii hdim φ hφinj hφn hsub hT3).elim
  ·
    have hiso : ¬ (Q.restrict (minusSp i)).Anisotropic := by
      rw [QuadraticMap.not_anisotropic_iff_exists]
      obtain ⟨v, hv0, hvQ⟩ :=
        exists_isotropic_of_finrank_ge_three hodd (Q.restrict (minusSp i)) hQ' (by omega)
      exact ⟨v, hv0, hvQ⟩
    have hP0 : (l.map Q).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      exact zero_ne_one hc
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_mul] at hc
      exact zero_ne_one hc
    have hdisc : TauCeti.RegularFormClass.discr
        (TauCeti.formClass (Q.restrict (minusSp i)) hQ'') = 0 := by
      rw [hldisc (Units.mk0 _ hP0) rfl, TauCeti.squareClass_eq_zero_iff]
      refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), Units.ext ?_⟩
      simp only [Units.val_mk0, Units.val_mul]
      field_simp
      linear_combination hc
    obtain ⟨ψ'⟩ := hQ''.equivalent_hyperbolicPlane_prod_self hdim hdisc hiso
    obtain ⟨fr, hfr⟩ := Frame4.exists_frame_of_isometryEquiv (minusSp i) ψ'
    have hfri : fr.La (-1) = i := La_neg_one_eq_of_span_eq h2 hii hiO fr hfr
    have hperp : fr.perp = plusSp i :=
      le_antisymm (perp_le_plusSp h2 hii hiO fr hfr) (plusSp_le_perp h2 hiO fr hfr)
    have hφfix : ∀ g, ∀ x ∈ fr.perp, φ g x = x := fun g x hx => by
      rw [hperp] at hx
      exact (hφn g).2.2 x hx
    have hφc' : ∀ g, φ g * fr.La (-1) = fr.La (-1) * φ g := fun g => by
      rw [hfri]
      exact hφc g
    have hT3' : ∀ g ∈ O, g * fr.La (-1) = fr.La (-1) * g → g ^ 3 = 1 → g ∈ T := by
      rw [hfri]
      exact hT3
    rcases eq_La_range_or_eq_swap3 fr hF φ hφinj hφO hφc' hφfix hsub hT3' with hA | hA
    · exact ⟨fr, hrangeL ▸ hA⟩
    · exact ⟨fr.swap, hrangeL ▸ hA⟩

omit [FiniteDimensional (GaloisField 3 1) V] in
theorem spinAction_ne_one_of_isClassicalMember3 (hK : CFSG.Open.IsQuasisimple (spinGroup Q))
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) : spinAction Q z ≠ 1 := by
  intro hz
  have hzc : z ∈ Subgroup.center (spinGroup Q) := hker (MonoidHom.mem_ker.mpr hz)
  have hcent : Subgroup.centralizer ({z} : Set (spinGroup Q)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.mp hzc g
  have hsubtop : IsSubnormal L ⊤ := hcent ▸ h.subnormal
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hK L hsubtop with
    hle | htop
  · exact h.not_le_center hle
  · obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hO
    have : Group.IsSolvable L :=
      haveI := isSolvable_sl2Three
      Group.isSolvable_of_surjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    let e' : L ≃* spinGroup Q := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    exact false_of_isQuasisimple_of_isSolvable hK
      (Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective)

theorem exists_cubes_of_range {G : Type*} [Group G] (hF : Nat.card (GaloisField 3 1) = 3)
    (ψ : SL(2, GaloisField 3 1) →* G) {a : G} (ha : a ∈ ψ.range) :
    ∃ u₁ ∈ ψ.range, ∃ u₂ ∈ ψ.range, ∃ u₃ ∈ ψ.range, u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧
      a = u₁ * u₂ * u₃ := by
  obtain ⟨e₃⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨a, b, c, ha, hb, hc, hg⟩ := sl2Three_exists_cubes (e₃ g)
  have hg' : g = e₃.symm a * e₃.symm b * e₃.symm c := by
    rw [← map_mul, ← map_mul, ← hg, MulEquiv.symm_apply_apply]
  have hcube : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → ψ (e₃.symm x) ^ 3 = 1 := fun x hx => by
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  refine ⟨ψ (e₃.symm a), ⟨_, rfl⟩, ψ (e₃.symm b), ⟨_, rfl⟩, ψ (e₃.symm c), ⟨_, rfl⟩,
    hcube a ha, hcube b hb, hcube c hc, ?_⟩
  rw [hg', map_mul, map_mul]

theorem exists_conj_longSL2_of_isClassicalMember3 (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q)
    (hK : CFSG.Open.IsQuasisimple (spinGroup Q)) {m : ℕ} (F₀ : HypFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool)
    (hperp : 2 ≤ Module.finrank (GaloisField 3 1) (F₀.toFrame hij s t).perp)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ x : spinGroup Q, L = (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom := by
  have hF : Nat.card (GaloisField 3 1) = 3 := natCard_galoisField_three'
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hF]; decide
  have : Invertible (2 : GaloisField 3 1) :=
    invertibleOfNonzero (three_eq_zero_two_ne_zero_of_card_eq_three hF).2
  set fr₀ := F₀.toFrame hij s t with hfr₀
  have : Nontrivial V := ⟨⟨fr₀.e₁, 0, fr₀.P.e_ne_zero⟩⟩
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1 := by
    intro c hc
    rcases (mem_ker_spinAction_iff Q hQnd c).mp hc with rfl | rfl
    · exact one_mul 1
    · apply Subtype.ext
      simp
  have hz := spinAction_ne_one_of_isClassicalMember3 hK hker h hO
  obtain ⟨fr, hfr⟩ := exists_frame_map_eq_of_isClassicalMember3 hQ hker hker2 hrange hE h hO hz
  obtain ⟨x, hx⟩ := exists_spin_conj hodd hQ fr₀ fr hperp
  refine ⟨x, ?_⟩
  obtain ⟨e⟩ := h.nonempty_equiv_sl2 hO
  have hLcubes : ∀ a ∈ L, ∃ u₁ ∈ L, ∃ u₂ ∈ L, ∃ u₃ ∈ L, u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧
      a = u₁ * u₂ * u₃ := fun a ha => exists_cubes_of_mulEquiv e.symm ha
  have hinj : Function.Injective (F₀.longSL2 hij s t) := by
    intro g g' hgg
    apply (fr₀.La_injective)
    rw [← DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) g,
      ← DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) g']
    exact congrArg (spinAction Q) hgg
  let ψ : SL(2, GaloisField 3 1) →* spinGroup Q :=
    (MulAut.conj x).toMonoidHom.comp (F₀.longSL2 hij s t)
  have hrangeψ : (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom = ψ.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have hmapR : ((F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom).map (spinAction Q) =
      fr.La.range := by
    rw [map_conj_map, map_longSL2_range, La_range_eq_map_conj hx]
  exact eq_of_map_eq_of_cubes (spinAction Q) hker hker2 hLcubes
    (by rw [hrangeψ]; exact fun a ha => exists_cubes_of_range hF ψ ha) (hfr.trans hmapR.symm)

end Main

end CFSG.ClassicalInvolution.Q3
