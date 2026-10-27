module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ10

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

theorem endo_eq_id_of_central {G : Type*} [Group G] (hP : Group.IsPerfect G) (φ : G →* G)
    (h : ∀ g, g⁻¹ * φ g ∈ Subgroup.center G) (g : G) : φ g = g := by
  let f : G →* Subgroup.center G :=
    { toFun := fun g => ⟨g⁻¹ * φ g, h g⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have h2 := Subgroup.mem_center_iff.mp (h a) b⁻¹
        calc b⁻¹ * a⁻¹ * (φ a * φ b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by group
          _ = (a⁻¹ * φ a) * b⁻¹ * φ b := by rw [h2]
          _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by group }
  have hf : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp hP] at hf
  have h3 := hf (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at h3
  have h4 : g⁻¹ * φ g = 1 := congrArg Subtype.val h3
  rw [inv_mul_eq_one] at h4
  exact h4.symm

section Others

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem components_commute [Finite V] {G L C : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : IsComponentIn L G) (hC : IsComponentIn C G) (hCL : C ≠ L) :
    ∀ c ∈ C, ∀ l ∈ L, c * l = l * c := by
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  rcases CFSG.LocalCores.distinct_components_commute hC.2 hL.2 with h | h
  · exfalso
    apply hCL
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hC.1, inf_eq_left.2 hL.1] at this
  · intro c hc l hl
    have h1 : ⁅(⟨c, hC.1 hc⟩ : ↥G), (⟨l, hL.1 hl⟩ : ↥G)⁆ ∈
        ⁅C.subgroupOf G, L.subgroupOf G⁆ := Subgroup.commutator_mem_commutator hc hl
    rw [h, Subgroup.mem_bot] at h1
    have h2 : ⁅c, l⁆ = 1 := congrArg Subtype.val h1
    exact (commutatorElement_eq_one_iff_commute.1 h2)

theorem component_fixes_I [Finite V] {G L A C : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : IsComponentIn L G) (hC : IsComponentIn C G) (hCL : C ≠ L) {I : Submodule (ZMod 2) V}
    (hsec : ComponentSection L A I) (hIL : commGL L ⊤ = I) :
    ∀ c ∈ C, ∀ i ∈ I, c i = i := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hcomm := components_commute hL hC hCL
  have hcomm' : ∀ c ∈ C, ∀ l ∈ L, ∀ v, c (l v) = l (c v) := by
    intro c hc l hl v
    have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ v) (hcomm c hc l hl)
    simpa using this
  have hCq : CFSG.IsQuasisimple ↥C :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC.1) hC.2.1
  have hI := isInvariant_sup_subgroup hsec.inv_L hsec.inv_A
  have hCI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) C I := by
    intro c hc u hu
    have hle : commGL L ⊤ ≤ (commGL L ⊤).comap (c : V →ₗ[ZMod 2] V) := by
      rw [commSub_le_iff]
      intro l hl v _
      show c (l v - v) ∈ commGL L ⊤
      rw [map_sub, hcomm' c hc l hl v]
      exact mem_commSub_of hl Submodule.mem_top
    rw [← hIL] at hu ⊢
    exact hle hu
  let resC : ↥C →* (↥I ≃ₗ[ZMod 2] ↥I) := resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) C I hCI
  have hfixIn : ∀ x : ↥C, ∀ z ∈ fixIn L I, resC x z ∈ fixIn L I := by
    intro x z hz l hl
    show l ((resC x z : ↥I) : V) = ((resC x z : ↥I) : V)
    rw [resSub_apply]
    show l ((x : V ≃ₗ[ZMod 2] V) (z : V)) = (x : V ≃ₗ[ZMod 2] V) (z : V)
    rw [← hcomm' x x.2 l hl, show l (z : V) = z from hz l hl]
  let φ : ↥C →* ((↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)) :=
    quotHom resC (fixIn L I) hfixIn
  obtain ⟨hnt, hirrAct⟩ := lbar_irreducible hsec.A_norm hI hsec.irr
  have : Finite (↥I ⧸ fixIn L I) := inferInstance
  obtain ⟨F, _, _, _, _, _, hF1, -⟩ :=
    finite_irreducible_endomorphism_field_density.{v, 0, 0} (Lbar L A I hsec.A_norm hI) hirrAct
  have hscal : ∀ c : ↥C, ∃ a : F, ∀ w, φ c w = a • w := by
    intro c
    refine (hF1 ((φ c : (↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)) :
      Module.End (ZMod 2) (↥I ⧸ fixIn L I))).1 (fun h hh w => ?_)
    obtain ⟨l, rfl⟩ := hh
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    show φ c (actOn L A I hsec.A_norm hI L le_sup_left l (Submodule.Quotient.mk u)) =
      actOn L A I hsec.A_norm hI L le_sup_left l (φ c (Submodule.Quotient.mk u))
    rw [actOn_L_mk, quotHom_mk, quotHom_mk, actOn_L_mk]
    congr 1
    apply Subtype.ext
    rw [resSub_apply, resSub_apply, resSub_apply, resSub_apply]
    exact hcomm' c c.2 l l.2 _
  have hcommφ : ∀ x y : ↥C, φ x * φ y = φ y * φ x := by
    intro x y
    obtain ⟨a, ha⟩ := hscal x
    obtain ⟨b, hb⟩ := hscal y
    apply LinearEquiv.ext
    intro w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb w, ha (b • w), ha w, hb (a • w),
      smul_smul, smul_smul, mul_comm]
  have hker : commutator ↥C ≤ φ.ker := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (hcommφ x y)
  rw [Group.isPerfect_def.1 hCq.1] at hker
  intro c hc i hi
  have hz : ∀ u : ↥I, ∀ l ∈ L, l (c (u : V) - (u : V)) = c (u : V) - (u : V) := by
    intro u l hl
    have h1 : φ ⟨c, hc⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
    have h2 : φ ⟨c, hc⟩ (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := by
      rw [h1]; rfl
    rw [quotHom_mk] at h2
    have h3 := (Submodule.Quotient.eq (fixIn L I)).1 h2
    have h4 := h3 l hl
    have e : (((resC ⟨c, hc⟩ u - u : ↥I)) : V) = c (u : V) - u := by
      rw [Submodule.coe_sub]
      rfl
    have h4' : l (((resC ⟨c, hc⟩ u - u : ↥I)) : V) = ((resC ⟨c, hc⟩ u - u : ↥I) : V) := h4
    rw [e] at h4'
    exact h4'
  let D : V →ₗ[ZMod 2] V := (c : V →ₗ[ZMod 2] V) - LinearMap.id
  have hkerD : commGL L I ≤ LinearMap.ker D := by
    rw [commSub_le_iff]
    intro l hl u hu
    show D (l u - u) = 0
    have h1 := hcomm' c hc l hl u
    have h2 := hz ⟨u, hu⟩ l hl
    have key : c (l u - u) - (l u - u) = 0 := by
      rw [map_sub, h1]
      have h3 : l (c u) - l u = c u - u := by rw [← map_sub]; exact h2
      calc l (c u) - c u - (l u - u) = (l (c u) - l u) - (c u - u) := by abel
        _ = 0 := by rw [h3]; exact sub_self _
    simpa [D] using key
  have hi' : i ∈ commGL L I := by rw [hsec.comm]; exact hi
  have := hkerD hi'
  rw [LinearMap.mem_ker] at this
  simp only [D, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] at this
  exact sub_eq_zero.1 this

theorem component_commutes_A [Finite V] (hQ : QuadBestOffendersNormalize (ZMod 2) V)
    {G A C : Subgroup (V ≃ₗ[ZMod 2] V)} (hC : IsComponentIn C G) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    {I : Submodule (ZMod 2) V} (hinvA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A I)
    (hVsplit : I ⊔ fixGL A = ⊤) (hfix : ∀ c ∈ C, ∀ i ∈ I, c i = i) :
    ∀ c ∈ C, ∀ a ∈ A, c * a = a * c := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hCq : CFSG.IsQuasisimple ↥C :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC.1) hC.2.1
  have hnorm : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C := by
    intro a ha c hc
    have h := (minimal_best_offenders_normalize_components hQ
      (hAG.trans Subgroup.le_normalizer) hAel hAne hoff hstrict).2 C hC a ha
    have h2 : a * c * a⁻¹ ∈ CFSG.Quasithin.B6.conjSub a C :=
      CFSG.Quasithin.B6.mem_conjSub.2 (by rw [show a⁻¹ * (a * c * a⁻¹) * a = c by group]; exact hc)
    rwa [h] at h2
  have hAtriv : A ≤ trivMod I := by
    intro x hx w
    have hw' : w ∈ I ⊔ fixGL A := by rw [hVsplit]; trivial
    obtain ⟨i, hi, c', hc', rfl⟩ := Submodule.mem_sup.1 hw'
    have h8 : x c' = c' := hc' x hx
    rw [map_add, h8]
    have : x i + c' - (i + c') = x i - i := by abel
    rw [this]
    exact I.sub_mem (hinvA x hx i hi) hi
  let U : Subgroup (V ≃ₗ[ZMod 2] V) := trivMod I ⊓ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) I
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    trivMod_commute (fun z hz => hx.2 z hz) (fun z hz => hy.2 z hz) hx.1 hy.1
  have hgen : ∀ c ∈ C, ∀ a ∈ A, ⁅c, a⁆ ∈ U := by
    intro c hc a ha
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact (trivMod I).mul_mem (conj_mem_trivMod (fun z hz => by rw [hfix c hc z hz]; exact hz)
        (hAtriv ha)) ((trivMod I).inv_mem (hAtriv ha))
    · intro i hi
      have h1 : a⁻¹ i ∈ I := hinvA a⁻¹ (A.inv_mem ha) i hi
      have h2 : c⁻¹ (a⁻¹ i) = a⁻¹ i := hfix c⁻¹ (C.inv_mem hc) _ h1
      show (c * a * c⁻¹ * a⁻¹) i = i
      simp only [LinearEquiv.mul_apply]
      rw [h2, gl_apply_inv_apply, hfix c hc i hi]
  have hKC : ⁅C, A⁆ ≤ C := by
    refine Subgroup.commutator_le.2 fun c hc a ha => ?_
    have : ⁅c, a⁆ = c * (a * c⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact C.mul_mem hc (hnorm a ha c⁻¹ (C.inv_mem hc))
  have hKU : ⁅C, A⁆ ≤ U := Subgroup.commutator_le.2 hgen
  have hKnormal : ∀ x ∈ C, ∀ k ∈ ⁅C, A⁆, x * k * x⁻¹ ∈ ⁅C, A⁆ := by
    intro x hx k hk
    rw [Subgroup.commutator_def] at hk
    induction hk using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, a, ha, rfl⟩ := hy
      have e : x * ⁅c, a⁆ * x⁻¹ = ⁅x * c, a⁆ * ⁅x, a⁆⁻¹ := by
        rw [commutatorElement_mul_left_eq_conj_mul]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (C.mul_mem hx hc) ha)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx ha))
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hN : ((⁅C, A⁆ : Subgroup (V ≃ₗ[ZMod 2] V)).subgroupOf C).Normal :=
    ⟨fun n hn g => hKnormal g g.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hCq hN with hN1 | hN2
  · exfalso
    have hCK : ∀ c ∈ C, c ∈ ⁅C, A⁆ := fun c hc => by
      have : (⟨c, hc⟩ : ↥C) ∈ (⁅C, A⁆ : Subgroup (V ≃ₗ[ZMod 2] V)).subgroupOf C := by
        rw [hN1]; trivial
      exact this
    have hCab : ∀ x y : ↥C, x * y = y * x := fun x y =>
      Subtype.ext (hUcomm _ (hKU (hCK _ x.2)) _ (hKU (hCK _ y.2)))
    have hP := Group.isPerfect_def.1 hCq.1
    have hbot : commutator ↥C ≤ ⊥ := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_commute.2 (hCab x y)
    rw [hP] at hbot
    have := CFSG.LocalCores.isQuasisimple_nontrivial hCq
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥C)
    exact hx (Subgroup.mem_bot.1 (hbot (Subgroup.mem_top x)))
  · intro c hc a ha
    let φ : ↥C →* ↥C :=
      { toFun := fun x => ⟨a * x * a⁻¹, hnorm a ha x x.2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intro x y; apply Subtype.ext; simp [mul_assoc] }
    have h := endo_eq_id_of_central hCq.1 φ (fun g => by
      refine hN2 ?_
      show ((g⁻¹ * φ g : ↥C) : V ≃ₗ[ZMod 2] V) ∈ ⁅C, A⁆
      have e : ((g⁻¹ * φ g : ↥C) : V ≃ₗ[ZMod 2] V) = ⁅(g : V ≃ₗ[ZMod 2] V)⁻¹, a⁆ := by
        show (g : V ≃ₗ[ZMod 2] V)⁻¹ * (a * (g : V ≃ₗ[ZMod 2] V) * a⁻¹) = _
        rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (C.inv_mem g.2) ha) ⟨c, hc⟩
    have h2 : a * c * a⁻¹ = c := congrArg Subtype.val h
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm

theorem minimal_even_SL2_component_offender
    [Finite V]
    {G L A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : IsComponentIn L G) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hcomm : ⁅L, A⁆ ≠ ⊥) :
    ComponentOffenderOutput L A n α (commGL L ⊤) ∧
      ∀ C : Subgroup (V ≃ₗ[ZMod 2] V), IsComponentIn C G → C ≠ L →
        (∀ c ∈ C, ∀ i ∈ commGL L ⊤, c i = i) ∧ ∀ c ∈ C, ∀ a ∈ A, c * a = a * c := by
  have hQ : QuadBestOffendersNormalize (ZMod 2) V := quadBestOffendersNormalize
  obtain ⟨I, hsec, hIL, hVsplit, hout⟩ :=
    component_offender_output hQ hL hn hF α hAG hAel hAne hoff hstrict hcomm
  subst hIL
  refine ⟨hout, fun C hC hCL => ?_⟩
  have hfix := component_fixes_I hL hC hCL hsec rfl
  exact ⟨hfix, component_commutes_A hQ hC hAG hAel hAne hoff hstrict hsec.inv_A hVsplit hfix⟩

end Others

end CFSG.QuasithinUnique.Setup.Lift
