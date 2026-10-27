module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcGFE
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

variable {τ : Tag}

theorem fix_of_fixed_normal_simple {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    {i : MulAut S} {R : Subgroup (MulAut S)} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    {J : Subgroup S} (hJfix : ∀ j ∈ J, i j = j)
    (hJn : ∀ s : S, i s = s → ∀ j ∈ J, s * j * s⁻¹ ∈ J) (hJs : IsSimpleGroup J)
    (hJna : ∃ a b : J, a * b ≠ b * a) {r : MulAut S} (hr : r ∈ R) {j : S} (hj : j ∈ J) :
    r j = j := by
  have hperf : _root_.commutator J = ⊤ := commutator_eq_top_of_simple' hJna
  have hJT : J ≤ oddFixed i := by
    refine (le_oddClosure_of_perfect le_rfl hperf).trans (closure_mono ?_)
    rintro g ⟨hgJ, hgo⟩
    exact ⟨hJfix g hgJ, hgo⟩
  have hTfix : ∀ t ∈ oddFixed i, i t = t := by
    have hle : oddFixed i ≤ i.toMonoidHom.eqLocus (MonoidHom.id S) := by
      rw [oddFixed, closure_le]
      rintro s ⟨hs, -⟩
      exact hs
    exact fun t ht => hle ht
  have hcomp : GorensteinWalter.IsComponentOf J (oddFixed i) := by
    refine ⟨hJT, ?_, gw_isQuasisimple_of_simple hJna⟩
    have hn : (J.subgroupOf (oddFixed i)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hJT]
      intro j t hj ht
      exact hJn t (hTfix t ht) j hj
    exact hn.isSubnormal
  exact fix_of_isComponentOf hRi hRc hZ hRodd hr hcomp hj

theorem odd_card_of_ringChar_ne_two {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hcard]
  exact (hp.eq_two_or_odd'.resolve_left hF).pow

theorem ringChar_subfield_ne_two' {K : Type} [Field K] (hK : ringChar K ≠ 2) (S : Subfield K) :
    ringChar S ≠ 2 := by
  intro h
  have h0 : ((2 : ℕ) : S) = 0 := by
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  apply Ring.two_ne_zero hK
  have := congrArg S.subtype h0
  rw [map_natCast, map_zero] at this
  exact_mod_cast this

theorem outerCoreTrivAt_entrywise_field_E
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (δ : K ≃+* K) (hδ2 : δ ^ 2 = 1) {β : MulAut (adjointGroup τ K)}
    (hβ : ∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K))
    (hβ2 : β ^ 2 = 1) : OuterCoreTrivAt β := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hZ : center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (fixSubfield δ) := Subtype.finite
  obtain ⟨-, -, -, hJΓ, -, hJn, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K δ
  have hfixΓ : ∀ s : adjointGroup τ K, β s = s ↔ (s : ModGL τ K) ∈ entrywiseFixedGroup τ δ := by
    intro s
    constructor
    · intro hs
      refine mem_inf.2 ⟨s.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (s : ModGL τ K) = s
      rw [← hβ, hs]
    · intro hs
      apply Subtype.ext
      rw [hβ]
      exact (mem_inf.1 hs).2
  have hJC : fixedFieldImage τ δ ≤ adjointGroup τ K := fun x hx => (fixedFieldImage_le hx).1
  obtain ⟨hJs0, hJna0, -⟩ :=
    odd_pinned_Chevalley_p_components τ (fixSubfield δ) (ringChar_fixSubfield_ne_two hK2 δ)
  have eJ : (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K) ≃*
      adjointGroup τ (fixSubfield δ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv δ).symm
  have hJs : IsSimpleGroup ((fixedFieldImage τ δ).subgroupOf (adjointGroup τ K)) :=
    (MulEquiv.isSimpleGroup_congr eJ).2 hJs0
  have hJna : ∃ x y : (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hJna0
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (eJ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hJfix : ∀ j ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K), β j = j :=
    fun j hj => (hfixΓ j).2 (hJΓ hj)
  have hJnorm : ∀ s : adjointGroup τ K, β s = s →
      ∀ j ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K),
        s * j * s⁻¹ ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K) := by
    intro s hs j hj
    have hsΓ := (hfixΓ s).1 hs
    have h1 := hJn.conj_mem (⟨j, hJΓ hj⟩ : entrywiseFixedGroup τ δ) hj ⟨s, hsΓ⟩
    exact h1
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form τ hτ K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  intro R hRodd hRi hRc r hr
  have hrJ : ∀ j ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K), r j = j :=
    fun j hj => fix_of_fixed_normal_simple hZ hRodd hRi hRc hJfix hJnorm hJs hJna hr hj
  have hro : Odd (orderOf r) := odd_orderOf_of_mem hRodd hr
  obtain ⟨g, a, φ, ε, hgaφ⟩ := hNF r
  have hε : (ε : ℕ) = 0 := by
    rcases hτ with rfl | rfl | rfl
    · have h1 : Θ r ^ orderOf r = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [hΘ r g a φ ε hgaφ] at h1
      have h2 := congrArg Prod.snd h1
      rw [Prod.pow_snd, Prod.snd_one, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
      have hε2 : (ε : ℕ) < 2 := ε.isLt
      by_contra hne
      have hε1 : (ε : ℕ) = 1 := by omega
      rw [hε1, Nat.cast_one, mul_one] at h2
      have h3 : ((orderOf r : ℕ) : ZMod 2) = 0 := h2
      exact (Nat.not_even_iff_odd.2 hro) (ZMod.natCast_eq_zero_iff_even.1 h3)
    · exact Nat.lt_one_iff.1 ε.isLt
    · exact Nat.lt_one_iff.1 ε.isLt
  have hQ : exactQ τ K (ε : ℕ) = 1 := by
    rw [hε]
    rcases hτ with rfl | rfl | rfl
    · exact pow_zero _
    · rfl
    · rfl
  obtain ⟨x, hx⟩ : ∃ x : ModGL τ K, x = (g : ModGL τ K) * rootDiagUnit τ a := ⟨_, rfl⟩
  have hr' : ∀ h : adjointGroup τ K, (r h : ModGL τ K) =
      x * Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * x⁻¹ := fun h => by
    rw [hgaφ h, hQ, hx]
    group
  set K₁ : Subfield K := fixSubfield φ ⊓ fixSubfield δ with hK₁def
  have : Finite K₁ := Subtype.finite
  have hK₁ : Odd (Nat.card K₁) :=
    odd_card_of_ringChar_ne_two (ringChar_subfield_ne_two' hK2 K₁)
  have hK₁δ : K₁ ≤ fixSubfield δ := inf_le_right
  have hφK₁ : φ.toRingHom.comp K₁.subtype = K₁.subtype :=
    RingHom.ext fun c => (mem_fixSubfield φ).1 ((show K₁ ≤ fixSubfield φ from inf_le_left) c.2)
  have hJ₁ : ∀ g₁ ∈ adjointGroup τ K₁, baseChangeGL K₁.subtype g₁ ∈ fixedFieldImage τ δ := by
    intro g₁ hg₁
    refine ⟨baseChangeGL (Subfield.inclusion hK₁δ) g₁, baseChangeGL_mem_adjointGroup _ hg₁, ?_⟩
    rw [baseChangeGL_baseChangeGL]
    rfl
  have hxJ₁ : ∀ g₁ ∈ adjointGroup τ K₁,
      x * baseChangeGL K₁.subtype g₁ = baseChangeGL K₁.subtype g₁ * x := by
    intro g₁ hg₁
    have hjC : baseChangeGL K₁.subtype g₁ ∈ adjointGroup τ K := hJC (hJ₁ g₁ hg₁)
    have h1 := hrJ ⟨_, hjC⟩ (hJ₁ g₁ hg₁)
    have h2 := hr' ⟨_, hjC⟩
    rw [h1] at h2
    change baseChangeGL K₁.subtype g₁ = x * Units.map (entrywiseHom φ.toRingHom)
      (baseChangeGL K₁.subtype g₁) * x⁻¹ at h2
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hφK₁] at h2
    calc x * baseChangeGL K₁.subtype g₁ =
        (x * baseChangeGL K₁.subtype g₁ * x⁻¹) * x := by group
      _ = baseChangeGL K₁.subtype g₁ * x := by rw [← h2]
  set L := AlgebraicClosure K
  set ι := algebraMap K L with hι
  obtain ⟨-, -, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ K₁ hK₁ L (ι.comp K₁.subtype)
  have hzG : baseChangeGL ι x ∈ adjointGroup τ L := by
    rw [hx, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup ι g.2)
      (exceptional_Lang_adjoint_diagonal_lift τ L _).1
  have hz1 : baseChangeGL ι x = 1 := by
    refine hfaith _ hzG ?_
    rintro _ ⟨g₁, hg₁, rfl⟩
    rw [← baseChangeGL_baseChangeGL, ← map_mul, ← map_mul, hxJ₁ g₁ hg₁]
  have hx1 : x = 1 := baseChangeGL_injective ι (by rw [hz1, map_one])
  have hφK₀ : ∀ c, δ c = c → φ c = c := by
    intro c hc
    set i₀ : Fin τ.rank := ⟨0, τ.rank_pos⟩
    have hxJ : (xUnit τ K i₀ c : ModGL τ K) ∈ fixedFieldImage τ δ := by
      refine ⟨xUnit τ (fixSubfield δ) i₀ ⟨c, hc⟩, xUnit_mem_adjointGroup _ _, ?_⟩
      rw [baseChangeGL_xUnit]
      rfl
    have h1 := hrJ (adjX τ K i₀ c) hxJ
    have h2 := hr' (adjX τ K i₀ c)
    rw [h1, hx1, one_mul, inv_one, mul_one] at h2
    change xUnit τ K i₀ c = Units.map (entrywiseHom φ.toRingHom) (xUnit τ K i₀ c) at h2
    rw [units_map_entrywiseHom_xUnit] at h2
    have h3 : adjX τ K i₀ (φ c) = adjX τ K i₀ c := Subtype.ext h2.symm
    exact adjX_injective i₀ h3
  have hφz : φ ∈ zpowers δ := UnbalancedCatalog.mem_zpowers_of_fixed hφK₀
  have hid : ∀ y : ModGL τ K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) y = y :=
    fun y => Units.ext (entrywise_id _)
  rcases eq_one_or_eq_of_mem_zpowers_of_sq hδ2 hφz with rfl | rfl
  · refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hr', hx1, hid]
    simp
  · have hrβ : r = β := MulEquiv.ext fun h => Subtype.ext (by rw [hr', hx1, hβ]; simp)
    rw [hrβ] at hro ⊢
    exact eq_one_of_odd_of_mem_zpowers hβ2 (mem_zpowers β) hro

theorem outerCoreAt_quadratic_field_E
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hψ' : ψ * α * ψ⁻¹ = β := MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (hβ u).symm)
  have hβ2 : β ^ 2 = 1 := by
    rw [← hψ', sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα,
      mul_one, mul_inv_cancel]
  have hδ2 : δ ^ 2 = 1 := pow_eq_one_of_apply_eq_pow δ hKe hδ
  exact outerCoreAt_of_conj hψ'
    (outerCoreTrivAt_entrywise_field_E hτ hK δ hδ2 hβ hβ2).outerCoreAt

theorem outerCoreAt_E7_of_innerDiag
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) (hinn : InnerDiagCoreInput .E7)
    (α : MulAut (adjointGroup .E7 K)) (hα : orderOf α = 2) : OuterCoreAt α := by
  have hα2 : α ^ 2 = 1 := sq_eq_one_of_orderOf hα
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by norm_num)
  rcases odd_E7_involution_inner_or_quadratic hK hα2 with ⟨g, a, hαg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · exact hinn K hK α hα2 hα1 g a hαg
  · exact outerCoreAt_quadratic_field_E (Or.inr (Or.inl rfl)) hK hq he hKe δ hδ hαg hα2

theorem oddLieCoreFamilyInput_E7
    (hinn : InnerDiagCoreInput .E7) : OddLieCoreFamilyInput .E7 := by
  refine oddLieCoreFamilyInput_of_outerCoreAt fun S _ _ _ _ n p f hp hp2 _ hm i hi => ?_
  refine outerCoreAt_of_lieModel_untwisted .E7 hm (fun G _ hG => hG.2) ⟨by decide, by decide,
    by decide⟩ (fun K _ _ hK β hβ => ?_) i hi
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact outerCoreAt_E7_of_innerDiag hodd hinn β hβ

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
