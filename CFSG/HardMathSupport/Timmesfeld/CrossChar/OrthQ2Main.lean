module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Fix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Six
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpFamily
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOFix

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

section Linear

omit [Finite K] [FiniteDimensional K V] in
theorem exists_isometry_of_inducedBySemilinear (hK : Nat.card K = 2)
    {α : MulAut (ProjOrthDerived Q)} (hα : KCOrthogonalAut.InducedBySemilinear Q α) :
    ∃ G : V ≃ₗ[K] V, G ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ∀ y : orthDerived Q, ∃ hy : G * (y : V ≃ₗ[K] V) * G⁻¹ ∈ orthDerived Q,
        α (QuotientGroup.mk y) = QuotientGroup.mk ⟨_, hy⟩ := by
  obtain ⟨σ, F, hF, μ, hμ, hQF, hind⟩ := hα
  have hσ : σ = RingEquiv.refl K := KCSpFull.ringEquiv_eq_refl_of_card_two hK σ
  subst hσ
  have hμ1 : μ = 1 := (eq_zero_or_one_of_card hK μ).resolve_left hμ
  subst hμ1
  let G : V ≃ₗ[K] V :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun c v => by simpa using hF c v
      invFun := F.symm
      left_inv := F.left_inv
      right_inv := F.right_inv }
  have hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q (F v) = Q v
    simpa using hQF v
  refine ⟨G, hGO, fun y => ⟨conj_mem_orthDerived hGO y.2, hind y _ fun v => rfl⟩⟩

omit [Finite K] [FiniteDimensional K V] in
theorem scalars_subgroupOf_eq_bot (hK : Nat.card K = 2) :
    (scalars K V).subgroupOf (orthDerived Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hgΩ⟩ hg
  obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hg)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext v
  change g v = v
  rcases eq_zero_or_one_of_card hK c with rfl | rfl
  · have h1 : g v = g 0 := by rw [hc, zero_smul, map_zero]
    have h2 : v = 0 := g.injective h1
    rw [h2, map_zero]
  · rw [hc, one_smul]

omit [Finite K] [FiniteDimensional K V] in
theorem mk_injective_of_card_two (hK : Nat.card K = 2) :
    Function.Injective (QuotientGroup.mk : orthDerived Q → ProjOrthDerived Q) := by
  have h := scalars_subgroupOf_eq_bot (Q := Q) hK
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact h)
  exact hinj

theorem conj_injective_of_center_bot' {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← h]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have := congrArg (fun φ : MulAut G => φ y) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc y * x = x * y * x⁻¹ * x := by rw [this]
    _ = x * y := by group

end Linear

section Main

theorem localDeltaIn_eq_bot_orth_two (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h12 : 12 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) {H : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : innerAut (ProjOrthDerived Q) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : CharP K 2 := charP_two_of_card hK
  have : Finite V := Module.finite_of_finite K
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  obtain ⟨-, -, -, hsimple, hnonab, -, hodd, -, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_bot' hcenter
  have hmk := mk_injective_of_card_two (Q := Q) hK
  set ι : orthDerived Q →* MulAut (ProjOrthDerived Q) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).comp
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) with hιdef
  have hι : Function.Injective ι := hinj.comp hmk
  have hιapp : ∀ y : orthDerived Q, ι y = MulAut.conj (QuotientGroup.mk y : ProjOrthDerived Q) :=
    fun y => rfl
  have hHι : ∀ y, ι y ∈ H := fun y => hH ⟨_, rfl⟩
  have hnexcV : ¬ SmallFixedException Q := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  have hGof : ∀ α : MulAut (ProjOrthDerived Q), ∃ (G : V ≃ₗ[K] V)
      (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q), ∀ y : orthDerived Q,
        α (QuotientGroup.mk y) = QuotientGroup.mk
          (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q) := by
    intro α
    obtain ⟨G, hGO, hG⟩ := exists_isometry_of_inducedBySemilinear hK (hsemi α)
    refine ⟨G, hGO, fun y => ?_⟩
    obtain ⟨_, h⟩ := hG y
    exact h
  have hG1 : ∀ G : V ≃ₗ[K] V, G ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ y : orthDerived Q, G * (y : V ≃ₗ[K] V) * G⁻¹ = y) → G = 1 := by
    intro G hGO hGy
    refine CFSG.StandardType.LayerCores.OrthRegular.eq_one_of_commute_orthDerived hQ (by omega)
      hnexcV hGO fun y hy => ?_
    have := hGy ⟨y, hy⟩
    calc G * y = G * y * G⁻¹ * G := by group
      _ = y * G := by rw [this]
  have hconj3 : ∀ (α : MulAut (ProjOrthDerived Q)) (G : V ≃ₗ[K] V)
      (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q),
      (∀ y : orthDerived Q, α (QuotientGroup.mk y) = QuotientGroup.mk
        (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q)) →
      α = 1 → ∀ y : orthDerived Q, G * (y : V ≃ₗ[K] V) * G⁻¹ = y := by
    intro α G hGO hα h1 y
    have h2 := hα y
    rw [h1, MulAut.one_apply] at h2
    exact (congrArg Subtype.val (hmk h2)).symm
  have hDι : D ≤ ι.range := by
    intro d hd
    obtain ⟨G, hGO, hGd⟩ := hGof d
    have hG3O : G ^ 3 ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem hGO 3
    have hd3 : ∀ y : orthDerived Q, (d ^ 3) (QuotientGroup.mk y) = QuotientGroup.mk
        (⟨G ^ 3 * (y : V ≃ₗ[K] V) * (G ^ 3)⁻¹, conj_mem_orthDerived hG3O y.2⟩ :
          orthDerived Q) := by
      intro y
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hGd, hGd, hGd]
      congr 1
    have hG3 : G ^ 3 = 1 := hG1 _ hG3O (hconj3 _ _ hG3O hd3 (hD.2 d hd))
    have hGodd : Odd (orderOf G) :=
      Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hG3)
    have hGΩ : G ∈ orthDerived Q := hodd G hGO hGodd
    refine ⟨⟨G, hGΩ⟩, ?_⟩
    ext t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    rw [hιapp, MulAut.conj_apply, hGd y, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl
  set Dh : Subgroup (orthDerived Q) := D.comap ι with hDh
  have hmemDh : ∀ x, x ∈ Dh ↔ ι x ∈ D := fun x => Iff.rfl
  have hDhcard : Nat.card Dh = 27 := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hDι, hcard]
    norm_num
  have hDh3 : ∀ x ∈ Dh, x ^ 3 = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hD.2 _ ((hmemDh x).1 hx)
  have hDhcomm : ∀ x ∈ Dh, ∀ y ∈ Dh, x * y = y * x := fun x hx y hy => by
    apply hι
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, (hmemDh x).1 hx⟩ ⟨_, (hmemDh y).1 hy⟩)
  let _ : CommGroup Dh := { (inferInstance : Group Dh) with
    mul_comm := fun a b => Subtype.ext (hDhcomm a a.2 b b.2) }
  obtain ⟨e⟩ := exists_mulEquiv_z3 (G := Dh) (fun g => Subtype.ext (hDh3 g g.2))
    (by rw [hDhcard])
  set xh : Z3 → orthDerived Q := fun z => ((e.symm (Multiplicative.ofAdd z) : Dh) : orthDerived Q)
    with hxh
  have hxhD : ∀ z, xh z ∈ Dh := fun z => (e.symm (Multiplicative.ofAdd z)).2
  let ρ : Multiplicative Z3 →* Module.End K V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((orthDerived Q).subtype.comp (Dh.subtype.comp e.symm.toMonoidHom))
  have hact : ∀ z v, act ρ z v = (xh z : V ≃ₗ[K] V) v := fun z v => rfl
  have hfaith : ∀ z, act ρ z = 1 → z = 0 := by
    intro z hz
    have h1 : (xh z : V ≃ₗ[K] V) = 1 := LinearEquiv.ext fun v => by
      rw [← hact, hz]
      rfl
    have h2 : e.symm (Multiplicative.ofAdd z) = 1 := Subtype.ext (Subtype.ext h1)
    have h3 : Multiplicative.ofAdd z = 1 := by simpa using h2
    exact h3
  have hxhO : ∀ z, (xh z : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun z => orthDerived_le_orthogonalGroup Q (xh z).2
  have hisoB : ∀ z u v, QuadraticMap.polarBilin Q (act ρ z u) (act ρ z v) =
      QuadraticMap.polarBilin Q u v := fun z u v => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, hact, hact]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hxhO z) u v
  have hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})) := fun φ hφ =>
    even_finrank_fixOf_N (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB hφ
  have hp1 : ∀ z : Z3, z ≠ 0 → Even (finrank K (fixOf ρ {z})) := fun z hz =>
    even_finrank_fixOf_single (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB hz
  have hcov := cover_six ρ hfaith hpN hp1 h12
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨G, hGO, hGg⟩ := hGof g
  have hGcomm : ∀ z, G * (xh z : V ≃ₗ[K] V) = (xh z : V ≃ₗ[K] V) * G := by
    intro z
    have hc := commute_of_mem_localDeltaIn hg ((hmemDh (xh z)).1 (hxhD z))
    have h1 : MulAut.conj (g (QuotientGroup.mk (xh z))) =
        MulAut.conj (QuotientGroup.mk (xh z) : ProjOrthDerived Q) := by
      rw [← mul_conj_mul_inv, ← hιapp, hc, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := hinj h1
    rw [hGg] at h2
    have h3 : G * (xh z : V ≃ₗ[K] V) * G⁻¹ = xh z := congrArg Subtype.val (hmk h2)
    calc G * (xh z : V ≃ₗ[K] V) = G * (xh z : V ≃ₗ[K] V) * G⁻¹ * G := by group
      _ = (xh z : V ≃ₗ[K] V) * G := by rw [h3]
  have hfixV : ∀ z, GoodSix ρ z → ∀ v ∈ fixOf ρ {z}, G v = v := by
    intro z hz v hv
    obtain ⟨hz0, h6, y, u, hu, hyu⟩ := hz
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hx1 : xh z ≠ 1 := by
      intro h1
      apply hz0
      have h2 : e.symm (Multiplicative.ofAdd z) = 1 := Subtype.ext h1
      have h3 : Multiplicative.ofAdd z = 1 := by simpa using h2
      exact h3
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 hx1
    have hfix : ∀ w, w ∈ fixedSpace (xh z : V ≃ₗ[K] V) ↔ w ∈ fixOf ρ {z} := by
      intro w
      rw [mem_fixedSpace, mem_fixOf]
      constructor
      · intro hw x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hact]
        exact hw
      · intro hw
        rw [← hact]
        exact hw z rfl
    have h6' : 6 ≤ finrank K (fixedSpace (xh z : V ≃ₗ[K] V)) := by
      have : fixedSpace (xh z : V ≃ₗ[K] V) = fixOf ρ {z} := Submodule.ext hfix
      rw [this]
      exact h6
    have hx := oddOrderIsometry_of_orthDerived hp hpl hQ (xh z) hxo
    have hyM : (xh y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (xh z : V ≃ₗ[K] V) := by
      rw [mem_isometryCentralizer]
      refine ⟨fun w => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).1 (hxhO y) w,
        fun w => ?_⟩
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V) w)
        (hDhcomm _ (hxhD y) _ (hxhD z))
      simpa using this
    have hy3 : (xh y : V ≃ₗ[K] V) ^ 3 = 1 := by
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V)) (hDh3 _ (hxhD y))
      simpa using this
    obtain ⟨w, hw, hw3, hw1⟩ := orth_exists_supported_of_moves hx hyM hy3 ((hfix u).2 hu)
      (by rw [← hact]; exact hyu)
    have hF := orth2_fixedComponentImage_le_fixSub hK hQ hT hinj (H := H) (E := D) hH hg (xh z)
      hxo ((hmemDh _).1 (hxhD z)) hw hw3 hw1 h6'
    have hcommF : ∀ f ∈ supportedFixedDerived Q (xh z : V ≃ₗ[K] V), G * f = f * G := by
      intro f hf
      have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
      have hmem : (QuotientGroup.mk (⟨f, hfΩ⟩ : orthDerived Q) : ProjOrthDerived Q) ∈
          fixedComponentImage Q (xh z : V ≃ₗ[K] V) :=
        ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
      have h1 := mem_fixSub.1 (hF hmem)
      rw [hGg] at h1
      have h2 : G * f * G⁻¹ = f := congrArg Subtype.val (hmk h1)
      calc G * f = G * f * G⁻¹ * G := by group
        _ = f * G := by rw [h2]
    exact orth2_fixes_fixedSpace hK hQ hx h6' hGO (hGcomm z) hcommF v ((hfix v).2 hv)
  have hall : ∀ v, G v = v := fun v => by
    have : v ∈ ⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x} := hcov Submodule.mem_top
    have hle : (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ≤
        LinearMap.eqLocus (G : V →ₗ[K] V) LinearMap.id :=
      iSup₂_le fun x hx w hw => hfixV x hx w hw
    exact hle this
  have hG : G = 1 := LinearEquiv.ext hall
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [hGg y, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change G * (y : V ≃ₗ[K] V) * G⁻¹ = y
  rw [hG, one_mul, inv_one, mul_one]

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
