module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Cover8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

section Helpers

omit [Finite K] [FiniteDimensional K V] in
theorem orth2_conj_pow {α : MulAut (ProjOrthDerived Q)} {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hα : ∀ y : orthDerived Q, α (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q))
    (n : ℕ) (y : orthDerived Q) : (α ^ n) (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G ^ n * (y : V ≃ₗ[K] V) * (G ^ n)⁻¹,
        conj_mem_orthDerived (pow_mem hGO n) y.2⟩ : orthDerived Q) := by
  induction n generalizing y with
  | zero =>
    rw [pow_zero, MulAut.one_apply]
    congr 1
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih y, hα]
    congr 1
    apply Subtype.ext
    show G * (G ^ n * (y : V ≃ₗ[K] V) * (G ^ n)⁻¹) * G⁻¹ =
      G ^ (n + 1) * (y : V ≃ₗ[K] V) * (G ^ (n + 1))⁻¹
    group

omit [Finite K] [FiniteDimensional K V] in
theorem orth2_conj_eq_of_eq_one (hK : Nat.card K = 2) {α : MulAut (ProjOrthDerived Q)}
    {G : V ≃ₗ[K] V} (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hα : ∀ y : orthDerived Q, α (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q))
    (h1 : α = 1) (y : orthDerived Q) : G * (y : V ≃ₗ[K] V) * G⁻¹ = y := by
  have h2 := hα y
  rw [h1, MulAut.one_apply] at h2
  exact (congrArg Subtype.val (mk_injective_of_card_two hK h2)).symm

theorem orth2_isometry_eq_one (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGy : ∀ y : orthDerived Q, G * (y : V ≃ₗ[K] V) * G⁻¹ = y) : G = 1 := by
  have : CharP K 2 := charP_two_of_card hK
  have hnexcV : ¬ SmallFixedException Q := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  refine CFSG.StandardType.LayerCores.OrthRegular.eq_one_of_commute_orthDerived hQ (by omega)
    hnexcV hGO fun y hy => ?_
  have := hGy ⟨y, hy⟩
  calc G * y = G * y * G⁻¹ * G := by group
    _ = y * G := by rw [this]

theorem orth2_mem_innerAut_of_pow_three (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h5 : 5 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α)
    {d : MulAut (ProjOrthDerived Q)} (hd : d ^ 3 = 1) : d ∈ innerAut (ProjOrthDerived Q) := by
  have : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, -, -, -, -, -, hodd, -, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨G, hGO, hG⟩ := exists_isometry_of_inducedBySemilinear hK (hsemi d)
  have hGd : ∀ y : orthDerived Q, d (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q) := fun y => by
    obtain ⟨_, h⟩ := hG y
    exact h
  have hG3 : G ^ 3 = 1 := orth2_isometry_eq_one hK hQ h5 (pow_mem hGO 3)
    (orth2_conj_eq_of_eq_one hK (pow_mem hGO 3) (orth2_conj_pow hGO hGd 3) hd)
  have hGodd : Odd (orderOf G) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hG3)
  have hGΩ : G ∈ orthDerived Q := hodd G hGO hGodd
  refine ⟨QuotientGroup.mk ⟨G, hGΩ⟩, ?_⟩
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [MulAut.conj_apply, hGd y, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

end Helpers

theorem orth2_eq_one_of_isometry_eight (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) (hDinn : D ≤ innerAut (ProjOrthDerived Q))
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H D) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGg : ∀ y : orthDerived Q, g (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q)) :
    g = 1 := by
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
  have hDι : D ≤ ι.range := by
    intro d hd
    obtain ⟨t, ht⟩ := hDinn hd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨y, ht⟩
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
  have hp0 : Even (finrank K (fixOf ρ Set.univ)) := by
    have hodd : Odd (Nat.card (⊤ : AddSubgroup Z3)) := by
      rw [AddSubgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
        Fintype.card_fin]
      decide
    have h := even_finrank_fixOf (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB ⊤
      hodd
    rwa [AddSubgroup.coe_top] at h
  have hcov := cover_eight ρ hfaith hpN hp0 h8
  have hxh1 : ∀ z : Z3, z ≠ 0 → xh z ≠ 1 := by
    intro z hz0 h1
    apply hz0
    have h2 : e.symm (Multiplicative.ofAdd z) = 1 := Subtype.ext h1
    have h3 : Multiplicative.ofAdd z = 1 := by simpa using h2
    exact h3
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
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
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
  have hz₁ : (![1, 0, 0] : Z3) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  have hgk : Nat.Coprime 3 (orderOf g) := by
    refine coprime_orderOf_of_mem_localDeltaIn hp hg ((hmemDh _).1 (hxhD ![1, 0, 0])) ?_
    intro h1
    exact hxh1 _ hz₁ (hι (h1.trans (map_one ι).symm))
  have hGk : G ^ orderOf g = 1 :=
    orth2_isometry_eq_one hK hQ (by omega) (pow_mem hGO _)
      (orth2_conj_eq_of_eq_one hK (pow_mem hGO _) (orth2_conj_pow hGO hGg _)
        (pow_orderOf_eq_one g))
  have hfixU : ∀ z, GoodU ρ z → ∀ v ∈ LinearMap.ker (eCyc ρ z), G v = v := by
    intro z hz v hv
    obtain ⟨hz0, h8z⟩ := hz
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hE : eCyc ρ z = (xh z : V ≃ₗ[K] V).toLinearMap ^ 2 +
        (xh z : V ≃ₗ[K] V).toLinearMap + 1 := by
      ext w
      simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, act_add,
        Module.End.mul_apply, hact, pow_two, LinearEquiv.coe_coe]
      abel
    have hker : LinearMap.ker (eCyc ρ z) =
        primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K) := by
      rw [primaryComponent, aeval_cyc3, hE]
    have hrk := LinearMap.finrank_range_add_finrank_ker (eCyc ρ z)
    rw [range_eCyc ρ z] at hrk
    have h8' : 8 ≤ finrank K (primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K)) := by
      rw [← hker]
      omega
    exact orth2_fixes_unitary hQ hT hK hinj hH hg (xh z) hxo ((hmemDh _).1 (hxhD z)) h8' hGO
      (hGcomm z) hmk hGg hgk hGk v (hker ▸ hv)
  have hall : ∀ v, G v = v := fun v => by
    have hv : v ∈ (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ⊔
        ⨆ x ∈ {x | GoodU ρ x}, LinearMap.ker (eCyc ρ x) := hcov Submodule.mem_top
    have hle1 : (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ≤
        LinearMap.eqLocus (G : V →ₗ[K] V) LinearMap.id :=
      iSup₂_le fun x hx w hw => hfixV x hx w hw
    have hle2 : (⨆ x ∈ {x | GoodU ρ x}, LinearMap.ker (eCyc ρ x)) ≤
        LinearMap.eqLocus (G : V →ₗ[K] V) LinearMap.id :=
      iSup₂_le fun x hx w hw => hfixU x hx w hw
    exact sup_le hle1 hle2 hv
  have hG : G = 1 := LinearEquiv.ext hall
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [hGg y, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change G * (y : V ≃ₗ[K] V) * G⁻¹ = y
  rw [hG, one_mul, inv_one, mul_one]


theorem localDeltaIn_eq_bot_orth_two_eight (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : 8 ≤ finrank K V)
    (hsemi : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) {H : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : innerAut (ProjOrthDerived Q) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨G, hGO, hG⟩ := exists_isometry_of_inducedBySemilinear hK (hsemi g)
  refine orth2_eq_one_of_isometry_eight hK hQ hT h8 hD hcard
    (fun d hd => orth2_mem_innerAut_of_pow_three hK hQ hT (by omega) hsemi (hD.2 d hd)) hH hg hGO
    fun y => ?_
  obtain ⟨_, h⟩ := hG y
  exact h

end CFSG.HardMathSupport.Timmesfeld.CrossChar
