module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLCaseA
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLConfig
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Submodule CFSG.LocalAnalysis.ComponentInitial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

@[expose] def NoDihedralPair (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) : Prop :=
  ∀ (φ ψ : Dual (ZMod 2) V) (a b : V), a ≠ 0 → ψ ≠ 0 → InG G φ a → InG G ψ b → φ b = 1 →
    ψ a = 0 → False

@[expose] def centres (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) : Set V :=
  {a | a ≠ 0 ∧ ∃ φ : Dual (ZMod 2) V, φ ≠ 0 ∧ InG G φ a}

theorem apply_eq_apply (hno : NoDihedralPair G) {φ ψ : Dual (ZMod 2) V} {a b : V} (ha : a ≠ 0)
    (hb : b ≠ 0) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (hφa : InG G φ a) (hψb : InG G ψ b) : φ b = ψ a := by
  rcases zmod2_eq_zero_or_one (φ b) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (ψ a) with h2 | h2
  · rw [h1, h2]
  · exact (hno ψ φ b a hb hφ hψb hφa h2 h1).elim
  · exact (hno φ ψ a b ha hψ hφa hψb h1 h2).elim
  · rw [h1, h2]

theorem map_mem_centres {a : V} (ha : a ∈ centres G)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ∈ G) :
    (g : V →ₗ[ZMod 2] V) a ∈ centres G := by
  obtain ⟨ha0, φ, hφ, hφa⟩ := ha
  have hinv : ∀ v, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) v) = v := fun v => by
    change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
    rw [inv_mul_cancel]
    rfl
  refine ⟨fun h => ha0 ?_, φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    V →ₗ[ZMod 2] V), fun h => hφ ?_, hφa.conj hg⟩
  · rw [← hinv a, h, map_zero]
  · ext v
    have := LinearMap.congr_fun h ((g : V →ₗ[ZMod 2] V) v)
    rwa [LinearMap.comp_apply, hinv, LinearMap.zero_apply] at this

theorem span_centres_eq_top (hirr : IsIrreducibleOn G) (hne : (centres G).Nonempty) :
    span (ZMod 2) (centres G) = ⊤ := by
  have hinv : IsGInvariant G (span (ZMod 2) (centres G)) := by
    intro g hg w hw
    induction hw using Submodule.span_induction with
    | mem a ha => exact subset_span (map_mem_centres ha hg)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact smul_mem _ c hx
  rcases hirr _ hinv with h | h
  · obtain ⟨a, ha⟩ := hne
    have : a ∈ span (ZMod 2) (centres G) := subset_span ha
    rw [h, mem_bot] at this
    exact absurd this ha.1
  · exact h

theorem exists_symplectic_form [FiniteDimensional (ZMod 2) V] (hgen : GenByTransvections G)
    (hirr : IsIrreducibleOn G) (hno : NoDihedralPair G) (hne : (centres G).Nonempty) :
    ∃ f : LinearMap.BilinForm (ZMod 2) V, (∀ v, f v v = 0) ∧ (∀ u v, f u v = f v u) ∧
      (∀ u, (∀ v, f u v = 0) → u = 0) ∧
      (∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = f a) ∧
      ∀ a ∈ centres G, InG G (f a) a := by
  classical
  have hspan := span_centres_eq_top hirr hne
  choose φ hφ0 hφ using fun a : centres G => a.2.2
  have hsymm : ∀ a b : centres G, φ a (b : V) = φ b (a : V) := fun a b =>
    apply_eq_apply hno a.2.1 b.2.1 (hφ0 a) (hφ0 b) (hφ a) (hφ b)
  obtain ⟨t, hts, htspan, hli⟩ := exists_linearIndependent (ZMod 2) (centres G)
  have htop : ⊤ ≤ span (ZMod 2) (Set.range ((↑) : t → V)) := by
    rw [Subtype.range_coe, htspan, hspan]
  let B := Basis.mk hli htop
  let F : V →ₗ[ZMod 2] Dual (ZMod 2) V := B.constr (ZMod 2) fun i => φ ⟨i.1, hts i.2⟩
  have h1 : ∀ c (hc : c ∈ centres G) (v : V), F v c = φ ⟨c, hc⟩ v := by
    intro c hc v
    have : (Module.Dual.eval (ZMod 2) V c) ∘ₗ F = φ ⟨c, hc⟩ := by
      refine B.ext fun i => ?_
      rw [LinearMap.comp_apply, Module.Dual.eval_apply, Basis.constr_basis, Basis.mk_apply]
      exact hsymm ⟨i.1, hts i.2⟩ ⟨c, hc⟩
    exact LinearMap.congr_fun this v
  have h2 : ∀ a (ha : a ∈ centres G), F a = φ ⟨a, ha⟩ := fun a ha =>
    LinearMap.ext_on hspan fun c hc => by
      rw [h1 c hc]
      exact hsymm ⟨c, hc⟩ ⟨a, ha⟩
  have hcomm : ∀ u v, F u v = F v u := by
    intro u v
    have : F u = F.flip u := LinearMap.ext_on hspan fun c hc => by
      rw [LinearMap.flip_apply, h2 c hc, h1 c hc]
    exact LinearMap.congr_fun this v
  have halt : ∀ v, F v v = 0 := by
    intro v
    have hv : v ∈ span (ZMod 2) (centres G) := hspan ▸ mem_top
    induction hv using Submodule.span_induction with
    | mem a ha =>
      rw [h2 a ha]
      exact (hφ ⟨a, ha⟩).apply_eq_zero
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero, hcomm y x]
      exact zmod2_scalar_add_self _
    | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hF4 : ∀ (ψ : Dual (ZMod 2) V) (a : V), a ≠ 0 → ψ ≠ 0 → InG G ψ a → ψ = F a := by
    intro ψ a ha hψ hψa
    refine LinearMap.ext_on hspan fun c hc => ?_
    rw [h1 c hc]
    exact apply_eq_apply hno ha hc.1 hψ (hφ0 ⟨c, hc⟩) hψa (hφ ⟨c, hc⟩)
  have hnd : ∀ u, (∀ v, F u v = 0) → u = 0 := by
    have hR : IsGInvariant G (LinearMap.ker F) := by
      by_contra hR
      obtain ⟨χ, e, hχ, he, hχe, -, w, hw, hχw⟩ := exists_moving_transvection hgen hR
      have hw' : F w = 0 := hw
      rw [hF4 χ e he hχ hχe, hcomm, hw', LinearMap.zero_apply] at hχw
      exact zero_ne_one hχw
    rcases hirr _ hR with h | h
    · intro u hu
      have : u ∈ LinearMap.ker F := LinearMap.ext hu
      rwa [h, mem_bot] at this
    · exfalso
      obtain ⟨a, ha⟩ := hne
      have : F a = 0 := (h ▸ mem_top : a ∈ LinearMap.ker F)
      rw [h2 a ha] at this
      exact hφ0 ⟨a, ha⟩ this
  refine ⟨F, halt, hcomm, hnd, hF4, fun a ha => ?_⟩
  rw [h2 a ha]
  exact hφ ⟨a, ha⟩

section Form

variable {f : LinearMap.BilinForm (ZMod 2) V}

theorem tv_mem_bilinIsometryGroup (hcomm : ∀ u v, f u v = f v u) {a : V} (h : f a a = 0) :
    tv (f a) a h ∈ bilinIsometryGroup f := by
  intro x y
  have hxa : f x a = f a x := hcomm x a
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxa, h]
  generalize f x y = γ
  generalize f a x = α
  generalize f a y = β
  revert α β γ
  decide

variable (hF4 : ∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = f a)
include hF4

theorem le_bilinIsometryGroup (hgen : GenByTransvections G) (hcomm : ∀ u v, f u v = f v u) :
    G ≤ bilinIsometryGroup f := by
  obtain ⟨S, hS, rfl⟩ := hgen
  rw [Subgroup.closure_le]
  intro t ht
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
  obtain rfl := hF4 φ a ha hφ ⟨h, Subgroup.subset_closure ht⟩
  exact tv_mem_bilinIsometryGroup hcomm h

theorem isGInvariant_of_forall (hgen : GenByTransvections G) {W : Submodule (ZMod 2) V}
    (h : ∀ d ∈ centres G, ∀ w ∈ W, f d w = 1 → d ∈ W) : IsGInvariant G W := by
  by_contra hW
  obtain ⟨χ, e, hχ, he, hχe, heW, w, hw, hχw⟩ := exists_moving_transvection hgen hW
  have hχF := hF4 χ e he hχ hχe
  rw [hχF] at hχw
  exact heW (h e ⟨he, χ, hχ, hχe⟩ w hw hχw)

theorem eq_closure_tv (hgen : GenByTransvections G) (halt : ∀ v, f v v = 0)
    (hF5 : ∀ a ∈ centres G, InG G (f a) a) :
    G = Subgroup.closure {t | ∃ d ∈ centres G, t = tv (f d) d (halt d)} := by
  apply le_antisymm
  · obtain ⟨S, hS, hG⟩ := hgen
    have hle : S ⊆ {t | ∃ d ∈ centres G, t = tv (f d) d (halt d)} := by
      intro t ht
      obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
      have hφa : InG G φ a := ⟨h, hG ▸ Subgroup.subset_closure ht⟩
      obtain rfl := hF4 φ a ha hφ hφa
      exact ⟨a, ⟨ha, f a, hφ, hφa⟩, rfl⟩
    calc G = Subgroup.closure S := hG
      _ ≤ _ := Subgroup.closure_mono hle
  · rw [Subgroup.closure_le]
    rintro t ⟨d, hd, rfl⟩
    exact (hF5 d hd).2

end Form

theorem exists_preConfig [FiniteDimensional (ZMod 2) V] (hgen : GenByTransvections G)
    (hirr : IsIrreducibleOn G) (hno : NoDihedralPair G) (hne : (centres G).Nonempty) :
    ∃ P : PreConfig V, P.D = centres G ∧
      (∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = P.b a) ∧
      ∀ a ∈ centres G, InG G (P.b a) a := by
  obtain ⟨f, halt, hcomm, hnd, hF4, hF5⟩ := exists_symplectic_form hgen hirr hno hne
  have hvanish : ∀ (ℓ : Set V) (d : V), (∀ p ∈ ℓ, f d p = 0) →
      ∀ x ∈ span (ZMod 2) ℓ, f d x = 0 := by
    intro ℓ d h x hx
    induction hx using Submodule.span_induction with
    | mem p hp => exact h p hp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  refine ⟨
    { b := f
      D := centres G
      self_eq_zero := halt
      comm := hcomm
      nondeg := hnd
      zero_notMem := fun h => h.1 rfl
      span_eq := span_centres_eq_top hirr hne
      add_mem := ?_
      eq_of_closed := ?_ }, rfl, hF4, hF5⟩
  · intro u hu v hv huv
    have h := (hF5 u hu).conj_tv (hF5 v hv)
    rw [huv, one_smul, hcomm v u, huv, one_smul] at h
    refine ⟨fun h0 => ?_, f u + f v, fun h0 => ?_, h⟩
    · have huv' : u = v := by
        have := congrArg (· + v) h0
        simpa [add_assoc, zmod2_add_self] using this
      rw [huv', halt] at huv
      exact zero_ne_one huv
    · have := LinearMap.congr_fun h0 u
      rw [LinearMap.add_apply, halt, zero_add, hcomm, huv, LinearMap.zero_apply] at this
      exact one_ne_zero this
  · intro ℓ hℓD hne' hcl
    have hcl' : ∀ d ∈ centres G, ∀ p ∈ ℓ, f d p = 1 → p + d ∈ ℓ := fun d hd p hp hdp => by
      have := hcl d hd p hp
      rwa [hcomm, hdp, one_smul] at this
    have hinv : IsGInvariant G (span (ZMod 2) ℓ) :=
      isGInvariant_of_forall hF4 hgen fun d hd w hw hdw => by
        obtain ⟨p, hp, hdp⟩ : ∃ p ∈ ℓ, f d p = 1 := by
          by_contra hno'
          have := hvanish ℓ d (fun p hp => (zmod2_eq_zero_or_one _).resolve_right
            fun h => hno' ⟨p, hp, h⟩) w hw
          rw [this] at hdw
          exact zero_ne_one hdw
        have hpd := hcl' d hd p hp hdp
        rw [show d = (p + d) + p by rw [add_comm p d, add_assoc, zmod2_add_self, add_zero]]
        exact add_mem (subset_span hpd) (subset_span hp)
    have htop : span (ZMod 2) ℓ = ⊤ := by
      refine (hirr _ hinv).resolve_left fun h => ?_
      obtain ⟨p, hp⟩ := hne'
      have : p ∈ span (ZMod 2) ℓ := subset_span hp
      rw [h, mem_bot] at this
      exact (hℓD hp).1 this
    refine le_antisymm hℓD fun d hd => ?_
    obtain ⟨p, hp, hdp⟩ : ∃ p ∈ ℓ, f d p = 1 := by
      by_contra hno'
      refine hd.1 (hnd d fun v => ?_)
      exact hvanish ℓ d (fun p hp => (zmod2_eq_zero_or_one _).resolve_right
        fun h => hno' ⟨p, hp, h⟩) v (htop ▸ mem_top)
    have hpd := hcl' d hd p hp hdp
    have hpdp := hcl' p (hℓD hp) (p + d) hpd (by
      rw [map_add, halt, zero_add, hcomm, hdp])
    rwa [add_comm p d, add_assoc, zmod2_add_self, add_zero] at hpdp

end CFSG.ComponentClassification.OutcomeLocal
