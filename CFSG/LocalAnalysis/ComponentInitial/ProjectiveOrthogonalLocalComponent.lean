module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentPaired
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentUnitary
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open TauCeti.QuadraticMap (orthogonalGroup)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def orthSigns (Q : QuadraticForm K V) : Subgroup (orthogonalGroup Q) where
  carrier := {g | (∀ v, (g : V ≃ₗ[K] V) v = v) ∨ ∀ v, (g : V ≃ₗ[K] V) v = -v}
  one_mem' := Or.inl fun _ => rfl
  mul_mem' := by
    rintro g g' (hg | hg) (hg' | hg')
    · exact Or.inl fun v => show (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) v) = v by rw [hg', hg]
    · exact Or.inr fun v => show (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) v) = -v by rw [hg', hg]
    · exact Or.inr fun v => show (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) v) = -v by rw [hg', hg]
    · exact Or.inl fun v => show (g : V ≃ₗ[K] V) ((g' : V ≃ₗ[K] V) v) = v by
        rw [hg', hg, neg_neg]
  inv_mem' := by
    rintro g (hg | hg)
    · exact Or.inl fun v => show (g : V ≃ₗ[K] V).symm v = v by
        rw [LinearEquiv.symm_apply_eq, hg]
    · exact Or.inr fun v => show (g : V ≃ₗ[K] V).symm v = -v by
        rw [LinearEquiv.symm_apply_eq, hg, neg_neg]

theorem mem_orthSigns {g : orthogonalGroup Q} :
    g ∈ orthSigns Q ↔ (∀ v, (g : V ≃ₗ[K] V) v = v) ∨ ∀ v, (g : V ≃ₗ[K] V) v = -v :=
  Iff.rfl

theorem orthSigns_le_center (Q : QuadraticForm K V) :
    orthSigns Q ≤ Subgroup.center (orthogonalGroup Q) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  change (g : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) v) = (z : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v)
  rcases hz with hz | hz
  · rw [hz, hz]
  · rw [hz, hz, map_neg]

instance orthSigns_normal (Q : QuadraticForm K V) : (orthSigns Q).Normal :=
  ⟨fun z hz g => by
    have h1 := Subgroup.mem_center_iff.mp (orthSigns_le_center Q hz) g
    rw [h1, mul_inv_cancel_right]
    exact hz⟩

theorem eq_one_of_mem_orthSigns (h2 : (2 : K) ≠ 0) {g : orthogonalGroup Q} (hg : g ∈ orthSigns Q)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hfix : ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) : g = 1 := by
  rcases mem_orthSigns.mp hg with h1 | h1
  · exact Subtype.ext (LinearEquiv.ext h1)
  · exfalso
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have h3 := hfix w hwW
    rw [h1] at h3
    have h4 : (2 : K) • w = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      exact neg_add_cancel w
    exact hw0 ((smul_eq_zero.mp h4).resolve_left h2)

theorem exists_ne_zero_of_nondegenerate (hQ : Q.polarBilin.Nondegenerate) [Nontrivial V] :
    ∃ v, Q v ≠ 0 := by
  by_contra! h0
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hQ.1 x fun y => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h0, h0, h0, sub_zero, sub_zero])

theorem lift_involution (hQ : Q.polarBilin.Nondegenerate) [Nontrivial V] {T : orthogonalGroup Q}
    (hT : orderOf (QuotientGroup.mk' (orthSigns Q) T) = 2) :
    (∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1) ∧
      ((∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = v) ∨
        ∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = -v) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · have hTv : ∀ v, (T : V ≃ₗ[K] V) v = c • v := fun v => by
      rw [← LinearEquiv.coe_toLinearMap, hc, LinearMap.smul_apply, Module.End.one_apply]
    obtain ⟨v, hv⟩ := exists_ne_zero_of_nondegenerate hQ
    have h1 : Q ((T : V ≃ₗ[K] V) v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp T.2 v
    rw [hTv, QuadraticMap.map_smul, smul_eq_mul] at h1
    have hc2 : c * c = 1 := by
      have h3 : (c * c - 1) * Q v = 0 := by linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hv)
    have hTZ : T ∈ orthSigns Q := by
      rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
      · exact Or.inl fun v => by rw [hTv, one_smul]
      · exact Or.inr fun v => by rw [hTv, neg_one_smul]
    have h4 : QuotientGroup.mk' (orthSigns Q) T = 1 := (QuotientGroup.eq_one_iff T).mpr hTZ
    rw [h4, orderOf_one] at hT
    exact absurd hT (by norm_num)
  · have h1 : QuotientGroup.mk' (orthSigns Q) (T * T) = 1 := by
      rw [map_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff (T * T)).mp h1

theorem sq_eq_one_of_isComponent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] (hd : 5 ≤ finrank K V)
    (hQ : Q.polarBilin.Nondegenerate) {T : orthogonalGroup Q}
    (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hTsq : (∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = v) ∨
      ∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = -v)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (orthogonalGroup Q)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (orthogonalGroup Q)) : Set (orthogonalGroup Q)))
    (hRp : ⁅R, R⁆ = R) (hR1 : R ≠ ⊥) : ∀ v, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) = v := by
  rcases hTsq with h1 | h1
  · exact h1
  · exfalso
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    · obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact one_ne_zero (neg_eq_zero.mp hl.symm)
      exact hR1 (paired_case hℓ hℓ2 hf hK hd hQ hTns h1 (Units.mk0 l hl0) hl hL hR hRp)
    · push Not at hsq
      exact hR1 (unitary_case hℓ hℓ2 hf hK hd hQ hTns h1 hsq hL hR hRp)

theorem negativeSquareKernel_neg_one (A : V ≃ₗ[K] V) :
    negativeSquareKernel A (-1) = positiveSquareKernel A 1 := by
  have h1 : (-1 : K)⁻¹ • A.toLinearMap + 1 = -((1 : K)⁻¹ • A.toLinearMap - 1) := by
    rw [inv_neg, inv_one, neg_smul, neg_sub, neg_add_eq_sub]
  rw [negativeSquareKernel, positiveSquareKernel, h1, LinearMap.ker_neg]

theorem positiveSquareKernel_neg_one (A : V ≃ₗ[K] V) :
    positiveSquareKernel A (-1) = negativeSquareKernel A 1 := by
  have h1 : (-1 : K)⁻¹ • A.toLinearMap - 1 = -((1 : K)⁻¹ • A.toLinearMap + 1) := by
    rw [inv_neg, inv_one, neg_smul, neg_add']
  rw [negativeSquareKernel, positiveSquareKernel, h1, LinearMap.ker_neg]

theorem positiveSquareKernel_one (A : V ≃ₗ[K] V) :
    positiveSquareKernel A 1 = LinearMap.ker (A.toLinearMap - 1) := by
  rw [positiveSquareKernel, inv_one, one_smul]

theorem negativeSquareKernel_one (A : V ≃ₗ[K] V) :
    negativeSquareKernel A 1 = LinearMap.ker (A.toLinearMap + 1) := by
  rw [negativeSquareKernel, inv_one, one_smul]

theorem exists_fixing_sign {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] (hn : 2 ≤ finrank K V)
    (hQ : Q.polarBilin.Nondegenerate) {T : orthogonalGroup Q}
    (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hTT : ∀ x, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) x) = x)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L) :
    ∃ b : Kˣ, ((b : K) = 1 ∨ (b : K) = -1) ∧ negativeSquareKernel (T : V ≃ₗ[K] V) b ≠ ⊥ ∧
      ∀ x ∈ L, ∀ w ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b,
        ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w = w := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f hℓ hℓ2 hf
      hK hn Q hQ (T : V ≃ₗ[K] V) 1 1 (fun x => by rw [Units.val_one, one_smul]; exact hTT x)
      (fun x y => by rw [Units.val_one, one_mul]; exact polarBilin_map_of_mem T.2 x y) hTns
  obtain ⟨-, hP0, hN0, hpos, -⟩ := hsq 1 (by rw [Units.val_one, one_pow])
  obtain ⟨-, -, -, e, he1, he2, -⟩ := hpos (by rw [Units.val_one, div_one])
  have : Finite V := Module.finite_of_finite K
  have : Finite (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V)
      ((1 : Kˣ) : K)).subtype)) :=
    Finite.of_injective (fun g x => (g : positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K) ≃ₗ[K]
      positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) x)
      fun g g' hgg' => Subtype.ext (LinearEquiv.ext (congrFun hgg'))
  have : Finite (orthogonalGroup (Q.comp (negativeSquareKernel (T : V ≃ₗ[K] V)
      ((1 : Kˣ) : K)).subtype)) :=
    Finite.of_injective (fun g x => (g : negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K) ≃ₗ[K]
      negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) x)
      fun g g' hgg' => Subtype.ext (LinearEquiv.ext (congrFun hgg'))
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup.centralizer {T} ≃*
      (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)).subtype) ×
        orthogonalGroup (Q.comp (negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)).subtype)),
      E' = (MulEquiv.subgroupCongr (centralizer_eq_orthogonalOperatorCentralizer T)).trans e :=
    ⟨_, rfl⟩
  rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent E' hL) with
    h2 | h1
  · refine ⟨1, Or.inl rfl, hN0, fun x hx w hw => ?_⟩
    have h3 := h2 _ (Subgroup.mem_map_of_mem E'.toMonoidHom hx)
    have h4 : (((((E' x).2 : orthogonalGroup (Q.comp (negativeSquareKernel (T : V ≃ₗ[K] V)
        ((1 : Kˣ) : K)).subtype)) : negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K) ≃ₗ[K]
          negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) ⟨w, hw⟩ :
            negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) : V) =
        ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w := by
      rw [hE']
      exact he2 _ ⟨w, hw⟩
    rw [← h4]
    change (((((E'.toMonoidHom x).2 : orthogonalGroup (Q.comp (negativeSquareKernel
      (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)).subtype)) : negativeSquareKernel (T : V ≃ₗ[K] V)
        ((1 : Kˣ) : K) ≃ₗ[K] negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) ⟨w, hw⟩ :
          negativeSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) : V) = w
    rw [h3]
    rfl
  · refine ⟨-1, Or.inr (by rw [Units.val_neg, Units.val_one]), by
      rw [Units.val_neg, Units.val_one, negativeSquareKernel_neg_one]
      rw [Units.val_one] at hP0
      exact hP0, fun x hx w hw => ?_⟩
    have hw' : w ∈ positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K) := by
      rw [Units.val_neg, Units.val_one, negativeSquareKernel_neg_one] at hw
      rw [Units.val_one]
      exact hw
    have h3 := h1 _ (Subgroup.mem_map_of_mem E'.toMonoidHom hx)
    have h4 : (((((E' x).1 : orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V)
        ((1 : Kˣ) : K)).subtype)) : positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K) ≃ₗ[K]
          positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) ⟨w, hw'⟩ :
            positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) : V) =
        ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w := by
      rw [hE']
      exact he1 _ ⟨w, hw'⟩
    rw [← h4]
    change (((((E'.toMonoidHom x).1 : orthogonalGroup (Q.comp (positiveSquareKernel
      (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)).subtype)) : positiveSquareKernel (T : V ≃ₗ[K] V)
        ((1 : Kˣ) : K) ≃ₗ[K] positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) ⟨w, hw'⟩ :
          positiveSquareKernel (T : V ≃ₗ[K] V) ((1 : Kˣ) : K)) : V) = w
    rw [h3]
    rfl

theorem exists_elemAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] {L : Subgroup H}
    {B₀ : Subgroup G} (e : L ≃* B₀)
    (hE : ∃ E : Subgroup G, E ≤ B₀ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4) :
    ∃ E : Subgroup H, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E, hEB, hEab, hEc⟩ := hE
  have : IsMulCommutative E := hEab.1
  let φ : B₀ →* H := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hcomm : IsMulCommutative (E.subgroupOf B₀) := ⟨⟨fun x y => Subtype.ext (Subtype.ext
    (congrArg (Subtype.val : E → G)
      ((isMulCommutative_iff.mp this) ⟨((x : B₀) : G), x.2⟩ ⟨((y : B₀) : G), y.2⟩)))⟩⟩
  refine ⟨(E.subgroupOf B₀).map φ, ?_, ⟨Subgroup.map_isMulCommutative _ φ, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : x ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hEab.2 _ hx)
    rw [← map_pow, h1, map_one]
  · rw [Subgroup.card_map_of_injective hφ, ← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv

theorem eigenspace_fixed_space_aux {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] (hd : 5 ≤ finrank K V)
    (hQ : Q.polarBilin.Nondegenerate) {T : orthogonalGroup Q}
    (hu : orderOf (QuotientGroup.mk' (orthSigns Q) T) = 2)
    {B₀ : Subgroup (Subgroup.centralizer {(QuotientGroup.mk' (orthSigns Q)) T})}
    (hE : ∃ E : Subgroup (Subgroup.centralizer {(QuotientGroup.mk' (orthSigns Q)) T}),
      E ≤ B₀ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    (hLB : L.map (centralizerProj (orthSigns Q) T) = B₀)
    {Bhat : Subgroup (orthogonalGroup Q)} (hPL : Bhat = L.map (Subgroup.centralizer {T}).subtype)
    {Rhat : Subgroup (orthogonalGroup Q)}
    (hRcent : Rhat ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (orthogonalGroup Q)) : Set (orthogonalGroup Q)))
    (hRperf : ⁅Rhat, Rhat⁆ = Rhat) (hR1 : Rhat ≠ ⊥) :
    T * T = 1 ∧
      LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) ≠ ⊥ ∧
      LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ≠ ⊥ ∧
      (∀ v ∈ LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1),
        ∀ w ∈ LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1), Q.polarBilin v w = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin
        (LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1))).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin
        (LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1))).Nondegenerate ∧
      ∃ A W : Submodule K V,
        (A = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) ∧
            W = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ∨
          A = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ∧
            W = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1)) ∧
        (∀ g ∈ Bhat, ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) ∧
        (∃ C : Subgroup (orthogonalGroup (Q.comp A.subtype)), CFSG.IsComponent C ∧
          ∀ c, c ∈ C ↔ ∃ g ∈ Bhat, ∀ a : A, (((c : A ≃ₗ[K] A) a : A) : V) = (g : V ≃ₗ[K] V) a) ∧
        (∃ e : Bhat ≃* B₀, ∀ g,
          ((e g : Subgroup.centralizer {(QuotientGroup.mk' (orthSigns Q)) T}) :
            orthogonalGroup Q ⧸ orthSigns Q) =
            QuotientGroup.mk' (orthSigns Q) (g : orthogonalGroup Q)) ∧
        3 ≤ finrank K A ∧
        {v : V | ∀ g ∈ Bhat, (g : V ≃ₗ[K] V) v = v} = W ∧
        ∀ g ∈ Rhat, ∀ a ∈ A, (g : V ≃ₗ[K] V) a = a := by
  subst hPL
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hk : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  obtain ⟨hTns, hTsq⟩ := lift_involution hQ hu
  have hTT := sq_eq_one_of_isComponent hℓ hℓ2 hf hK hd hQ hTns hTsq hL hRcent hRperf hR1
  obtain ⟨b, hb1, hN0, hfixN⟩ := exists_fixing_sign hℓ hℓ2 hf hK (by omega) hQ hTns hTT hL
  have hb2 : (b : K) ^ 2 = 1 := by
    rcases hb1 with h | h <;> rw [h] <;> norm_num
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_of_inf_eq_one hLB fun x hx hxZ =>
    Subtype.ext (eq_one_of_mem_orthSigns h2 hxZ hN0 (hfixN x hx))
  have hEL := exists_elemAbelian_of_mulEquiv
    ((L.equivMapOfInjective _ Subtype.val_injective).trans e₀) hE
  obtain ⟨hP, hN, -, horth, hndP, hndN, ⟨C, hC, hCmem⟩, h3, hfixL, hRfix⟩ :=
    split_case hℓ hℓ2 hf hK (by omega) hQ hTns hTT b hb2 rfl rfl hL hfixN hEL
  have hW : ∀ g ∈ L.map (Subgroup.centralizer {T}).subtype,
      ∀ w ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b, (g : V ≃ₗ[K] V) w = w := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    exact hfixN x hx w hw
  have hCmem' : ∀ c, c ∈ C ↔ ∃ g ∈ L.map (Subgroup.centralizer {T}).subtype,
      ∀ a : positiveSquareKernel (T : V ≃ₗ[K] V) b,
        (((c : positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
          positiveSquareKernel (T : V ≃ₗ[K] V) b) a : _) : V) = (g : V ≃ₗ[K] V) a := by
    intro c
    rw [hCmem]
    constructor
    · rintro ⟨x, hx, hxc⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hxc⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxc⟩
      exact ⟨x, hx, hxc⟩
  have hfix' : {v : V | ∀ g ∈ L.map (Subgroup.centralizer {T}).subtype,
      (g : V ≃ₗ[K] V) v = v} = negativeSquareKernel (T : V ≃ₗ[K] V) b := by
    rw [← hfixL]
    ext v
    constructor
    · intro hv x hx
      exact hv _ ⟨x, hx, rfl⟩
    · rintro hv _ ⟨x, hx, rfl⟩
      exact hv x hx
  have hTT' : T * T = 1 := Subtype.ext (LinearEquiv.ext hTT)
  rcases hb1 with hb | hb
  · have hPk : positiveSquareKernel (T : V ≃ₗ[K] V) b =
        LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) := by
      rw [hb, positiveSquareKernel_one]
    have hNk : negativeSquareKernel (T : V ≃ₗ[K] V) b =
        LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) := by
      rw [hb, negativeSquareKernel_one]
    refine ⟨hTT', hPk ▸ hP, hNk ▸ hN, ?_, hPk ▸ hndP, hNk ▸ hndN, _, _, Or.inl ⟨hPk, hNk⟩, hW,
      ⟨C, hC, hCmem'⟩, ⟨e₀, he₀⟩, h3, hfix', hRfix _ hRcent hRperf⟩
    rw [← hPk, ← hNk]
    exact horth
  · have hPk : positiveSquareKernel (T : V ≃ₗ[K] V) b =
        LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) := by
      rw [hb, positiveSquareKernel_neg_one, negativeSquareKernel_one]
    have hNk : negativeSquareKernel (T : V ≃ₗ[K] V) b =
        LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) := by
      rw [hb, negativeSquareKernel_neg_one, positiveSquareKernel_one]
    refine ⟨hTT', hNk ▸ hN, hPk ▸ hP, fun v hv w hw => ?_, hNk ▸ hndN, hPk ▸ hndP, _, _,
      Or.inr ⟨hPk, hNk⟩, hW, ⟨C, hC, hCmem'⟩, ⟨e₀, he₀⟩, h3, hfix', hRfix _ hRcent hRperf⟩
    rw [← hNk] at hv
    rw [← hPk] at hw
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
    exact horth w hw v hv

theorem odd_projective_orthogonal_local_component_eigenspace_fixed_space {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) [FiniteDimensional K V]
    (hd : 5 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    {u : orthogonalGroup Q ⧸ orthSigns Q} (hu : orderOf u = 2) {T : orthogonalGroup Q}
    (hTu : QuotientGroup.mk' (orthSigns Q) T = u)
    {B₀ : Subgroup (Subgroup.centralizer {u})} (hB₀ : CFSG.IsComponent B₀)
    (hE : ∃ E : Subgroup (Subgroup.centralizer {u}), E ≤ B₀ ∧
      CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4)
    {R : Subgroup (orthogonalGroup Q ⧸ orthSigns Q)}
    (hRB : R ≤ Subgroup.centralizer ((B₀.map (Subgroup.centralizer {u}).subtype :
      Subgroup (orthogonalGroup Q ⧸ orthSigns Q)) : Set (orthogonalGroup Q ⧸ orthSigns Q)))
    (hR : R ≠ ⊥) (hRp : ⁅R, R⁆ = R) :
    T * T = 1 ∧
      LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) ≠ ⊥ ∧
      LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ≠ ⊥ ∧
      (∀ v ∈ LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1),
        ∀ w ∈ LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1), Q.polarBilin v w = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin
        (LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1))).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin
        (LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1))).Nondegenerate ∧
      ∃ A W : Submodule K V,
        (A = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1) ∧
            W = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ∨
          A = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap + 1) ∧
            W = LinearMap.ker ((T : V ≃ₗ[K] V).toLinearMap - 1)) ∧
        (∀ g ∈ ⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (orthSigns Q)),
          (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (orthSigns Q))⁆,
          ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) ∧
        (∃ C : Subgroup (orthogonalGroup (Q.comp A.subtype)), CFSG.IsComponent C ∧
          ∀ c, c ∈ C ↔ ∃ g ∈ ⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap
              (QuotientGroup.mk' (orthSigns Q)),
            (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (orthSigns Q))⁆,
            ∀ a : A, (((c : A ≃ₗ[K] A) a : A) : V) = (g : V ≃ₗ[K] V) a) ∧
        (∃ e : (⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (orthSigns Q)),
          (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (orthSigns Q))⁆ :
            Subgroup (orthogonalGroup Q)) ≃* B₀,
          ∀ g, ((e g : Subgroup.centralizer {u}) : orthogonalGroup Q ⧸ orthSigns Q) =
            QuotientGroup.mk' (orthSigns Q) (g : orthogonalGroup Q)) ∧
        3 ≤ finrank K A ∧
        {v : V | ∀ g ∈ ⁅(B₀.map (Subgroup.centralizer {u}).subtype).comap
            (QuotientGroup.mk' (orthSigns Q)),
          (B₀.map (Subgroup.centralizer {u}).subtype).comap (QuotientGroup.mk' (orthSigns Q))⁆,
          (g : V ≃ₗ[K] V) v = v} = W ∧
        ∀ g ∈ ⁅R.comap (QuotientGroup.mk' (orthSigns Q)),
            R.comap (QuotientGroup.mk' (orthSigns Q))⁆,
          ∀ a ∈ A, (g : V ≃ₗ[K] V) a = a := by
  subst hTu
  obtain ⟨hLc, hLB, hPL, hRperf, -, hRhat, hRcent⟩ := lift_component (orthSigns_le_center Q)
    (ProjectiveSymplectic.commutator_le_range_centralizerProj (orthSigns_le_center Q) T) hB₀ hRB hR
    hRp
  exact eigenspace_fixed_space_aux hp hp2 hf hK hd hQ hu hE hLc hLB hPL hRcent hRperf hRhat

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal
