module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4TPLevelS
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem l154d4tp_exists_unit_sq_ne_one (L : Type*) [Field L] [Infinite L] :
    ∃ u : Lˣ, u ^ 2 ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
  have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · simp [sub_eq_zero.1 h]
  · simp [eq_neg_of_add_eq_zero_left h]

theorem l154d4tp_twoPart_card_of_odd_factor {M : Type*} [Group M] {G C T : Subgroup M} [Finite G]
    (hCG : C ≤ G) (hTG : T ≤ G) (hnormC : ∀ y ∈ G, ∀ x ∈ C, y * x * y⁻¹ ∈ C)
    (hTodd : Odd (Nat.card T)) (hdec : ∀ y ∈ G, ∃ t ∈ T, ∃ x ∈ C, y = t * x) :
    twoPart (Nat.card G) = twoPart (Nat.card C) := by
  haveI : Finite T := Finite.of_injective (Subgroup.inclusion hTG)
    (Subgroup.inclusion_injective hTG)
  haveI hnorm : (C.subgroupOf G).Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hnormC y.1 y.2 x.1 hx⟩
  let φ : ↥T →* ↥G ⧸ C.subgroupOf G :=
    (QuotientGroup.mk' (C.subgroupOf G)).comp (Subgroup.inclusion hTG)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨t, ht, x, hx, hyt⟩ := hdec y y.2
      refine ⟨⟨t, ht⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hTG ⟨t, ht⟩) : ↥G ⧸ C.subgroupOf G) = _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h : (((Subgroup.inclusion hTG ⟨t, ht⟩)⁻¹ * y : ↥G) : M) = x := by simp [hyt]
      rw [h]
      exact hx
  have hodd : Odd (Nat.card (↥G ⧸ C.subgroupOf G)) :=
    Odd.of_dvd_nat hTodd (Subgroup.card_dvd_of_surjective hφ)
  have hcardG : Nat.card G = Nat.card (↥G ⧸ C.subgroupOf G) * Nat.card (C.subgroupOf G) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hC' : Nat.card (C.subgroupOf G) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCG).toEquiv
  haveI : Finite C := Finite.of_injective (Subgroup.inclusion hCG)
    (Subgroup.inclusion_injective hCG)
  rw [hcardG, hC', l154d4tp_twoPart_mul_odd hodd Nat.card_pos.ne']

section Torus

variable
  {τ : Tag} {L : Type} [Field L]

theorem l154d4tp_frobGL_torus (σ : L ≃+* L) {q : ℕ} (hσ : ∀ c, σ c = c ^ q) {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) : frobGL σ t = t ^ q := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  change Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = _
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_rootDiagUnit]
  have h1 : (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) = a ^ q := by
    funext i
    apply Units.ext
    simp [hσ]
  rw [h1]
  exact map_pow (rootDiagUnitHom τ L) a q

end Torus

section Fix

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

@[expose] noncomputable def l154d4tpFix (σ : L ≃+* L) (Ψ : Set (Fin τ.rank → ℤ)) :
    Subgroup (ModGL τ L) :=
  rootSpan τ L Ψ ⊓ (frobGL σ).eqLocus (MonoidHom.id _)

theorem l154d4tp_unionRootSpan_singleton (i : KernelComponent χ) :
    unionRootSpan L χ ({i} : Set (KernelComponent χ)) = rootSpan τ L (componentRoots χ i) := by
  change rootSpan τ L (unionRoots χ ({i} : Set (KernelComponent χ))) = _
  rw [unionRoots_singleton]

theorem mem_l154d4tpFix {σ : L ≃+* L} {Ψ : Set (Fin τ.rank → ℤ)} {x : ModGL τ L} :
    x ∈ l154d4tpFix σ Ψ ↔ x ∈ rootSpan τ L Ψ ∧ frobGL σ x = x := Iff.rfl

variable (σ : L ≃+* L) (i : KernelComponent χ)

theorem l154d4tp_CQ_le_rootSpan : CQ σ i ≤ rootSpan τ L (componentRoots χ i) := by
  unfold CQ
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, c, hc, rfl⟩
  rw [unionRoots_singleton] at hγ
  exact pinnedX_mem_rootSpan hγ c

theorem l154d4tp_frobGL_eq_self_of_mem_CQ {x : ModGL τ L} (hx : x ∈ CQ σ i) : frobGL σ x = x := by
  have : CQ σ i ≤ (frobGL σ).eqLocus (MonoidHom.id _) := by
    unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    show frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ c
    rw [frobGL_pinnedX, hc]
  exact this hx

theorem l154d4tp_fix_decomp (hs : ∃ s : Lˣ, s ^ 2 ≠ 1) {y : ModGL τ L}
    (hy : y ∈ l154d4tpFix σ (componentRoots χ i)) :
    ∃ t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)), frobGL σ t = t ∧
      ∃ x ∈ CQ σ i, y = t * x := by
  have hyS : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    have := (mem_l154d4tpFix.1 hy).1
    rwa [← l154d4tp_unionRootSpan_singleton] at this
  obtain ⟨t, ht, x, hx, hyt, hφ⟩ := exists_decomp (σ := σ) (c := 1) hyS (one_mem _)
    (by rw [one_mul]; exact (mem_l154d4tpFix.1 hy).2)
  exact ⟨t, ht, by simpa using hφ, x, hx, hyt⟩

theorem l154d4tp_odd_card_fixTorus {e : ℕ} (he : 1 ≤ e) (hσ : ∀ c, σ c = c ^ (2 ^ e))
    [Finite ↥(unionTorus L χ ({i} : Set (KernelComponent χ)) ⊓
      (frobGL σ).eqLocus (MonoidHom.id _))] :
    Odd (Nat.card ↥(unionTorus L χ ({i} : Set (KernelComponent χ)) ⊓
      (frobGL σ).eqLocus (MonoidHom.id _))) := by
  refine l154d4tp_odd_card_of_forall_pow (m := 2 ^ e - 1) ?_ fun t => ?_
  · exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  · have h1 : frobGL σ (t : ModGL τ L) = (t : ModGL τ L) := t.2.2
    have h2 : frobGL σ (t : ModGL τ L) = (t : ModGL τ L) ^ (2 ^ e) :=
      l154d4tp_frobGL_torus σ hσ (unionTorus_le_torusGroup t.2.1)
    rw [h1] at h2
    apply Subtype.ext
    have h3 : (t : ModGL τ L) ^ (2 ^ e - 1) * (t : ModGL τ L) = (t : ModGL τ L) := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
      exact h2.symm
    have h4 : (t : ModGL τ L) ^ (2 ^ e - 1) = 1 := mul_eq_right.1 h3
    simpa using h4

theorem l154d4tp_CQ_conj_mem (hs : ∃ s : Lˣ, s ^ 2 ≠ 1) {y : ModGL τ L}
    (hy : y ∈ l154d4tpFix σ (componentRoots χ i)) {x : ModGL τ L} (hx : x ∈ CQ σ i) :
    y * x * y⁻¹ ∈ CQ σ i := by
  obtain ⟨t, ht, htf, x₀, hx₀, hyt⟩ := l154d4tp_fix_decomp σ i hs hy
  have hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)),
      a * (1 : ModGL τ L) = 1 * a := fun a _ => by simp
  have hn := (torus_normalizes_CQ (σ := σ) ht hc (by rw [one_mul]; exact htf)).1
  have hxx : x₀ * x * x₀⁻¹ ∈ CQ σ i := mul_mem (mul_mem hx₀ hx) (inv_mem hx₀)
  rw [hyt]
  have e : t * x₀ * x * (t * x₀)⁻¹ = t * (x₀ * x * x₀⁻¹) * t⁻¹ := by group
  rw [e]
  exact hn _ hxx

section FixCard

variable [CharP L 2]

theorem l154d4tp_fix_twoPart {e : ℕ} (he : 1 ≤ e) (hσ : ∀ c, σ c = c ^ (2 ^ e))
    (hs : ∃ s : Lˣ, s ^ 2 ≠ 1) [Finite ↥(l154d4tpFix σ (componentRoots χ i))] :
    twoPart (Nat.card ↥(l154d4tpFix σ (componentRoots χ i))) =
      2 ^ (e * (posRoots (componentRoots χ i)).ncard) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := 2)
      (n := e) (by omega) σ hσ
  haveI := hfinK
  have hCG : CQ σ i ≤ l154d4tpFix σ (componentRoots χ i) := fun x hx =>
    ⟨l154d4tp_CQ_le_rootSpan σ i hx, l154d4tp_frobGL_eq_self_of_mem_CQ σ i hx⟩
  haveI : Finite ↥(CQ σ i) := Finite.of_injective (Subgroup.inclusion hCG)
    (Subgroup.inclusion_injective hCG)
  have hCcard : Nat.card (CQ σ i) = Nat.card (componentRootSpan (fixSubfield σ) χ i) := by
    rw [CQ_eq_map i σ]
    exact Nat.card_congr ((componentRootSpan (fixSubfield σ) χ i).equivMapOfInjective _
      (baseChangeGL_injective _)).toEquiv.symm
  have hC2 : twoPart (Nat.card (CQ σ i)) = 2 ^ (e * (posRoots (componentRoots χ i)).ncard) := by
    rw [hCcard]
    exact l154d4tp_twoPart_card_componentRootSpan (K := fixSubfield σ) i he hKcard
  have hTG : unionTorus L χ ({i} : Set (KernelComponent χ)) ⊓
      (frobGL σ).eqLocus (MonoidHom.id _) ≤ l154d4tpFix σ (componentRoots χ i) := fun t ht =>
    ⟨by
      rw [← l154d4tp_unionRootSpan_singleton]
      exact unionTorus_le_unionRootSpan ht.1, ht.2⟩
  haveI : Finite ↥(unionTorus L χ ({i} : Set (KernelComponent χ)) ⊓
      (frobGL σ).eqLocus (MonoidHom.id _)) :=
    Finite.of_injective (Subgroup.inclusion hTG) (Subgroup.inclusion_injective hTG)
  rw [l154d4tp_twoPart_card_of_odd_factor hCG hTG
    (fun y hy x hx => l154d4tp_CQ_conj_mem σ i hs hy hx) (l154d4tp_odd_card_fixTorus σ i he hσ)
    (fun y hy => by
      obtain ⟨t, ht, htf, x, hx, hyt⟩ := l154d4tp_fix_decomp σ i hs hy
      exact ⟨t, ⟨ht, htf⟩, x, hx, hyt⟩)]
  exact hC2

end FixCard

end Fix

section Layer

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}

theorem l154d4tp_layer_twoPart (S₀ : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT₀ : rootDiagUnit τ a ∈ S₀.D.torus) (i : KernelComponent (rootCharHom a)) {e : ℕ}
    (he : 1 ≤ e) (hq : S₀.D.q = 2 ^ e)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S₀.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i) (S₀.ρ : (Fin τ.rank → ℤ) → _)) :
    twoPart (Nat.card ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model)) =
      2 ^ (e * (posRoots (componentRoots (rootCharHom a) i)).ncard) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hΨr : IsRootComponent Ψ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun β hβ => hΨr.isRoot β hβ
  have horb : componentOrbitLength S₀.ρ Ψ = 1 := componentOrbitLength_eq_one hfin hρ
  have hinner' : twistInner Ψ ((S₀.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
    rw [Function.iterate_one]
    exact hinner
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S₀ hT₀ i one_pos hinner'
  rw [pow_one, hq] at hσ
  have hlayer : rootSpan τ L Ψ ⊓ S₀.D.model =
      (l154d4tpFix σ Ψ).map (MulAut.conj z).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨hxS, hxM⟩
      have hg : z⁻¹ * x * z ∈ rootSpan τ L Ψ := by
        refine (hnorm i (z⁻¹ * x * z)).2 ?_
        have e : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [e]
        exact hxS
      refine ⟨z⁻¹ * x * z, ⟨hg, ?_⟩, by simp [MulAut.conj_apply]; group⟩
      have h1 := hz (z⁻¹ * x * z) hg
      have e : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
      rw [e] at h1
      have h2 : S₀.D.step x = x := hxM.2
      change frobGL σ (z⁻¹ * x * z) = z⁻¹ * x * z
      have h3 : z * frobGL σ (z⁻¹ * x * z) * z⁻¹ = x := by
        rw [← h1]
        exact h2
      calc frobGL σ (z⁻¹ * x * z) = z⁻¹ * (z * frobGL σ (z⁻¹ * x * z) * z⁻¹) * z := by group
        _ = z⁻¹ * x * z := by rw [h3]
    · rintro ⟨g, ⟨hgS, hgf⟩, rfl⟩
      have hxS : z * g * z⁻¹ ∈ rootSpan τ L Ψ := (hnorm i g).1 hgS
      refine ⟨hxS, rootSpan_le_adjointGroup L Ψ hxS, ?_⟩
      have h1 := hz g hgS
      change S₀.D.step (z * g * z⁻¹) = z * g * z⁻¹
      have hgf' : frobGL σ g = g := hgf
      rw [show S₀.D.step (z * g * z⁻¹) = iterHom S₀.D.step 1 (z * g * z⁻¹) from rfl, h1, hgf']
  have hfinH : Finite ↥(rootSpan τ L Ψ ⊓ S₀.D.model) := by
    haveI := S₀.finite
    exact Finite.of_injective (Subgroup.inclusion (inf_le_right :
      rootSpan τ L Ψ ⊓ S₀.D.model ≤ S₀.D.model)) (Subgroup.inclusion_injective _)
  have hcongr : Nat.card ↥(rootSpan τ L Ψ ⊓ S₀.D.model) = Nat.card ↥(l154d4tpFix σ Ψ) := by
    rw [hlayer]
    exact Nat.card_congr ((l154d4tpFix σ Ψ).equivMapOfInjective (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective).toEquiv.symm
  haveI : Finite ↥(l154d4tpFix σ Ψ) := by
    have h : Finite ↥((l154d4tpFix σ Ψ).map (MulAut.conj z).toMonoidHom) := hlayer ▸ hfinH
    exact Finite.of_equiv _ ((l154d4tpFix σ Ψ).equivMapOfInjective (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective).toEquiv.symm
  rw [hcongr]
  exact l154d4tp_fix_twoPart σ i he hσ (l154d4tp_exists_unit_sq_ne_one L)

end Layer

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
