module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Orbit
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Perm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

@[expose] noncomputable def actHom (K : Type) [Group K] [Finite K] :
    K →* Equiv.Perm (ComponentIndex K) :=
  MulAction.toPermHom K (ComponentIndex K)

theorem mem_ker_actHom {g : K} : g ∈ (actHom K).ker ↔ ∀ C : ComponentIndex K, g • C = C := by
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  rfl

theorem ker_actHom_le_normalizer (C : ComponentIndex K) :
    (actHom K).ker ≤ normalizer (C.1 : Set K) := fun g hg =>
  (smul_eq_self_iff g C).1 (mem_ker_actHom.1 hg C)

namespace Red

theorem eq_one_of_mem_centralizer_layer (R : Red n p K P z D) {x : K}
    (hx : x ∈ centralizer (layer K : Set K)) : x = 1 := by
  haveI := R.fact
  have hF : fittingSubgroup K = ⊥ := by rw [Fitting_eq_pcore K p R.core, R.pc]
  have hgf : generalizedFitting K = layer K := by
    rw [generalizedFitting.eq_sup, hF, bot_sup_eq]
  have hle := centralizer_generalizedFitting_le K
  rw [hgf] at hle
  have hxL : x ∈ layer K := hle hx
  refine eq_one_of_π_eq_one (hZ := R.hZ) hxL fun C => ?_
  rw [π_eq_one_iff (hZ := R.hZ) C hxL, mem_centralizer_iff]
  intro g hg
  exact mem_centralizer_iff.1 hx g (component_le_layer C.2 hg)

theorem mem_layer_of_inner (R : Red n p K P z D) {y : K}
    (hy : ∀ C : ComponentIndex K, ∃ c : C.1, ∀ c' ∈ C.1, y * c' * y⁻¹ = c * c' * (c : K)⁻¹) :
    y ∈ layer K := by
  choose c hc using hy
  set ℓ : layer K := layerMulOnto K c with hℓ
  have hπ : ∀ C : ComponentIndex K, π R.hZ C (ℓ : K) ℓ.2 = c C := by
    intro C
    have := coord_layerMulOnto (hZ := R.hZ) C c
    exact congrArg Subtype.val this
  have hcen : (ℓ : K)⁻¹ * y ∈ centralizer (layer K : Set K) := by
    refine mem_centralizer_layer_of_forall _ fun C c' hc' => ?_
    have h1 : (ℓ : K) * c' * (ℓ : K)⁻¹ = c C * c' * (c C : K)⁻¹ := by
      rw [conj_eq_π (hZ := R.hZ) C ℓ.2 hc', hπ C]
    have h2 : y * c' * y⁻¹ = (ℓ : K) * c' * (ℓ : K)⁻¹ := by rw [h1]; exact hc C c' hc'
    calc (ℓ : K)⁻¹ * y * c' = (ℓ : K)⁻¹ * (y * c' * y⁻¹) * y := by group
      _ = (ℓ : K)⁻¹ * ((ℓ : K) * c' * (ℓ : K)⁻¹) * y := by rw [h2]
      _ = c' * ((ℓ : K)⁻¹ * y) := by group
  have h1 : (ℓ : K)⁻¹ * y = 1 := R.eq_one_of_mem_centralizer_layer hcen
  have : y = ℓ := by
    calc y = (ℓ : K) * ((ℓ : K)⁻¹ * y) := by group
      _ = ℓ := by rw [h1, mul_one]
  rw [this]
  exact ℓ.2

end Red

@[expose] noncomputable def outHom (C : ComponentIndex K) : (actHom K).ker →* Outer C.1 :=
  (QuotientGroup.mk' (inner C.1)).comp
    (C.1.normalizerMonoidHom.comp (Subgroup.inclusion (ker_actHom_le_normalizer C)))

@[expose] noncomputable def ωHom (K : Type) [Group K] [Finite K] :
    (actHom K).ker →* (∀ C : ComponentIndex K, Outer C.1) :=
  MonoidHom.pi fun C => outHom C

namespace Red

theorem ker_ωHom_le_layer (R : Red n p K P z D) (y : (actHom K).ker)
    (hy : y ∈ (ωHom K).ker) : (y : K) ∈ layer K := by
  refine R.mem_layer_of_inner fun C => ?_
  have h1 : outHom C y = 1 := congrFun (MonoidHom.mem_ker.1 hy) C
  have h2 : (C.1.normalizerMonoidHom (Subgroup.inclusion (ker_actHom_le_normalizer C) y)) ∈
      inner C.1 := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, fun c' hc' => ?_⟩
  have h3 := congrArg (fun a : MulAut C.1 => ((a ⟨c', hc'⟩ : C.1) : K)) hc
  simpa [MulAut.conj_apply] using h3.symm

theorem commute_zc_of_commute (R : Red n p K P z D) (C : ComponentIndex K) {u : K}
    (hu : u ∈ layer K) (huz : z * u = u * z) : Commute (π R.hZ C u hu) (R.zc C) := by
  have h1 : π R.hZ C (z * u * z⁻¹) (conj_mem_layer z hu) =
      R.zc C * π R.hZ C u hu * (R.zc C)⁻¹ := by
    rw [π_mul C (mul_mem R.hzL hu) (inv_mem R.hzL), π_mul C R.hzL hu, π_inv C R.hzL]
    rfl
  have h2 : z * u * z⁻¹ = u := by rw [huz]; group
  have h3 : π R.hZ C (z * u * z⁻¹) (conj_mem_layer z hu) = π R.hZ C u hu := π_congr C h2 _ _
  rw [h3] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm

theorem commute_of_pElement (R : Red n p K P z D) {w : K} (hw : w ∈ D)
    (hall : ∀ C : ComponentIndex K, w • C ≠ C) {u v : K} (hu : u ∈ layer K) (hv : v ∈ layer K)
    (huz : z * u = u * z) (hvz : z * v = v * z) {k : ℕ} (huk : u ^ (p ^ k) = 1) :
    u * v = v * u := by
  refine commute_of_π (hZ := R.hZ) hu hv fun C => ?_
  have hk : π R.hZ C u hu ^ (p ^ k) = 1 := by
    rw [← π_pow C hu (p ^ k)]
    have : π R.hZ C (u ^ (p ^ k)) (pow_mem hu _) = π R.hZ C 1 (one_mem _) :=
      π_congr C huk _ _
    rw [this, π_one]
  have hmem : π R.hZ C u hu ∈ zpowers (R.zc C) :=
    R.pElement_mem_zpowers_zc hw (hall C) (π_mem C u hu) (R.commute_zc_of_commute C hu huz).eq hk
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hmem
  rw [← hm]
  exact (R.commute_zc_of_commute C hv hvz).symm.zpow_left m

theorem false_of_section_ker (R : Red n p K P z D)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1)) {w : K} (hw : w ∈ D)
    (hall : ∀ C : ComponentIndex K, w • C ≠ C) {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (hdvd : p ∣ Nat.card S) (V : Subgroup K)
    (hVY : V ≤ (actHom K).ker) (hVz : V ≤ centralizer ({z} : Set K)) (g : V →* S)
    (hg : Function.Surjective g) : False := by
  haveI := R.fact
  set Y := (actHom K).ker with hY
  let e : V.subgroupOf Y ≃* V := Subgroup.subgroupOfEquivOfLe hVY
  let g₁ : V.subgroupOf Y →* S := g.comp e.toMonoidHom
  have hg₁ : Function.Surjective g₁ := hg.comp e.surjective
  rcases simple_quotient_cases (ωHom K) (V.subgroupOf Y) g₁ hg₁ with
    ⟨V', g', hV'U, hV'ker, hg'⟩ | ⟨V', g', hg'⟩
  · let V'' : Subgroup K := V'.map Y.subtype
    have hV'' : ∀ x ∈ V'', x ∈ layer K ∧ z * x = x * z := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨R.ker_ωHom_le_layer y (hV'ker hy), ?_⟩
      have hyV : (y : K) ∈ V := Subgroup.mem_subgroupOf.1 (hV'U hy)
      exact (mem_centralizer_singleton_iff.1 (hVz hyV)).symm
    let f₂ : V'' →* S :=
      g'.comp (V'.equivMapOfInjective Y.subtype Y.subtype_injective).symm.toMonoidHom
    have hf₂ : Function.Surjective f₂ := hg'.comp (MulEquiv.surjective _)
    have hcent : ∀ x : V'', (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ center V'' := by
      rintro x ⟨k, hk⟩
      rw [mem_center_iff]
      intro v
      apply Subtype.ext
      have h1 := R.commute_of_pElement hw hall (hV'' x x.2).1 (hV'' v v.2).1 (hV'' x x.2).2
        (hV'' v v.2).2 (k := k) (congrArg Subtype.val hk)
      exact h1.symm
    exact false_of_central_pElements R.prime hnab hdvd hcent f₂ hf₂
  · haveI : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1) := hOut
    haveI : Group.IsSolvable (∀ C : ComponentIndex K, Outer C.1) := isSolvable_pi_of_finite
    haveI : Group.IsSolvable V' := inferInstance
    haveI : Group.IsSolvable S := Group.isSolvable_of_surjective hg'
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := S)).2 inferInstance a b)

end Red

theorem involvedInSymm_of_card {Ω : Type*} [Fintype Ω] (hΩ : Fintype.card Ω = p) {S : Type*}
    [Group S] (V : Subgroup (Equiv.Perm Ω)) (g : V →* S) (hg : Function.Surjective g) :
    InvolvedInSymm p S := by
  let ψ : Equiv.Perm Ω ≃* Equiv.Perm (Fin p) := (Fintype.equivFinOfCardEq hΩ).permCongrHom
  let e : V ≃* V.map ψ.toMonoidHom := V.equivMapOfInjective ψ.toMonoidHom ψ.injective
  exact ⟨V.map ψ.toMonoidHom, g.comp e.symm.toMonoidHom, hg.comp e.symm.surjective⟩

namespace Red

theorem involvedInSymm_of_section (R : Red n p K P z D)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1)) {w : K} (hw : w ∈ D)
    (hall : ∀ C : ComponentIndex K, w • C ≠ C) (hcard : Fintype.card (ComponentIndex K) = p)
    {S : Type} [Group S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    (hdvd : p ∣ Nat.card S) (U : Subgroup K) (hUz : U ≤ centralizer ({z} : Set K)) (f : U →* S)
    (hf : Function.Surjective f) : InvolvedInSymm p S := by
  rcases simple_quotient_cases (actHom K) U f hf with ⟨V, g, hVU, hVker, hg⟩ | ⟨V, g, hg⟩
  · exact (R.false_of_section_ker hOut hw hall hnab hdvd V hVker (hVU.trans hUz) g hg).elim
  · exact involvedInSymm_of_card hcard V g hg

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
