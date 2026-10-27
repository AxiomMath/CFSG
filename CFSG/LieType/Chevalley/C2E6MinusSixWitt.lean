module

public import CFSG.LieType.Chevalley.C2E6MinusSixForm

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem zmod_two_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 :=
  (zmod_two_eq_zero_or_one c).resolve_left h

structure Frame where
  e : X
  e₂ : X
  f : X
  f₂ : X
  u₀ : X
  u₁ : X
  Q_e : Q e = 0
  Q_e₂ : Q e₂ = 0
  Q_f : Q f = 0
  Q_f₂ : Q f₂ = 0
  Q_u₀ : Q u₀ = 1
  Q_u₁ : Q u₁ = 1
  e_e₂ : polarQ e e₂ = 0
  e_f : polarQ e f = 1
  e_f₂ : polarQ e f₂ = 0
  e_u₀ : polarQ e u₀ = 0
  e_u₁ : polarQ e u₁ = 0
  e₂_f : polarQ e₂ f = 0
  e₂_f₂ : polarQ e₂ f₂ = 1
  e₂_u₀ : polarQ e₂ u₀ = 0
  e₂_u₁ : polarQ e₂ u₁ = 0
  f_f₂ : polarQ f f₂ = 0
  f_u₀ : polarQ f u₀ = 0
  f_u₁ : polarQ f u₁ = 0
  f₂_u₀ : polarQ f₂ u₀ = 0
  f₂_u₁ : polarQ f₂ u₁ = 0
  u₀_u₁ : polarQ u₀ u₁ = 1

namespace Frame

variable (F : Frame)

@[expose] def toLin : X →ₗ[ZMod 2] X :=
  Fintype.linearCombination (ZMod 2) ![F.e, F.e₂, F.f, F.f₂, F.u₀, F.u₁]

theorem toLin_apply (x : X) :
    F.toLin x = x 0 • F.e + x 1 • F.e₂ + x 2 • F.f + x 3 • F.f₂ + x 4 • F.u₀ + x 5 • F.u₁ := by
  rw [toLin, Fintype.linearCombination_apply, Fin.sum_univ_six]
  rfl

theorem Q_toLin (x : X) : Q (F.toLin x) = Q x := by
  rw [toLin_apply]
  simp only [Q_add, Q_smul, polarQ_add_left, polarQ_smul_left, polarQ_smul_right, F.Q_e, F.Q_e₂,
    F.Q_f, F.Q_f₂, F.Q_u₀, F.Q_u₁, F.e_e₂, F.e_f, F.e_f₂, F.e_u₀, F.e_u₁, F.e₂_f, F.e₂_f₂,
    F.e₂_u₀, F.e₂_u₁, F.f_f₂, F.f_u₀, F.f_u₁, F.f₂_u₀, F.f₂_u₁, F.u₀_u₁]
  rw [Q_apply]
  ring

theorem polarQ_toLin (x y : X) : polarQ (F.toLin x) (F.toLin y) = polarQ x y := by
  have h := Q_add (F.toLin x) (F.toLin y)
  rw [← map_add, F.Q_toLin, F.Q_toLin, F.Q_toLin, Q_add] at h
  exact (add_left_cancel h).symm

theorem toLin_injective : Function.Injective F.toLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine polarQ_nondeg x fun y => ?_
  rw [← F.polarQ_toLin, hx]
  simp [polarQ]

@[expose] def iso : QuadraticMap.IsometryEquiv Q Q :=
  ⟨LinearEquiv.ofInjectiveEndo F.toLin F.toLin_injective, F.Q_toLin⟩

theorem iso_apply (x : X) : F.iso x = F.toLin x := rfl

theorem iso_single (k : Fin 6) :
    F.iso (Pi.single k 1) = ![F.e, F.e₂, F.f, F.f₂, F.u₀, F.u₁] k := by
  rw [iso_apply, toLin, Fintype.linearCombination_apply_single, one_smul]

theorem iso_e₁ : F.iso e₁ = F.e := F.iso_single 0

theorem iso_e₂ : F.iso C2E6Overlap.e₂ = F.e₂ := F.iso_single 1

theorem iso_f₁ : F.iso f₁ = F.f := F.iso_single 2

theorem iso_f₂ : F.iso C2E6Overlap.f₂ = F.f₂ := F.iso_single 3

end Frame

theorem exists_partner {L : Submodule (ZMod 2) X} (hL2 : finrank (ZMod 2) L = 2) {e f : X}
    (he : e ∈ L) (he0 : e ≠ 0) (hef : polarQ e f = 1) :
    ∃ e₂ ∈ L, e₂ ≠ 0 ∧ e₂ ≠ e ∧ polarQ e₂ f = 0 := by
  have hlt : (ZMod 2) ∙ e < L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem e L).mpr he) fun h => ?_
    have := finrank_span_singleton (K := ZMod 2) he0
    rw [h, hL2] at this
    omega
  obtain ⟨a, ha, hae⟩ := IsConcreteLE.exists_of_lt hlt
  have ha0 : a ≠ 0 := fun h => hae (h ▸ Submodule.zero_mem _)
  have hane : a ≠ e := fun h => hae (by rw [h]; exact Submodule.mem_span_singleton_self e)
  rcases zmod_two_eq_zero_or_one (polarQ a f) with h | h
  · exact ⟨a, ha, ha0, hane, h⟩
  · refine ⟨a + e, L.add_mem ha he, fun h0 => hane ?_, fun h1 => ha0 ?_, ?_⟩
    · rw [← add_right_cancel_iff (a := e), h0, add_self_zmod_two]
    · rw [← add_right_cancel_iff (a := e), h1, zero_add]
    · rw [polarQ_add_left, h, hef]
      rfl

@[expose] def pairMap (e e₂ f f₂ : X) : X →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun x := ![polarQ x e, polarQ x e₂, polarQ x f, polarQ x f₂]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [polarQ_add_left]
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [polarQ_smul_left]

theorem pairMap_apply (e e₂ f f₂ x : X) :
    pairMap e e₂ f f₂ x = ![polarQ x e, polarQ x e₂, polarQ x f, polarQ x f₂] := rfl

theorem finrank_ker_pairMap {e e₂ f f₂ : X} (h1 : polarQ e e₂ = 0) (h2 : polarQ e f = 1)
    (h3 : polarQ e f₂ = 0) (h4 : polarQ e₂ f = 0) (h5 : polarQ e₂ f₂ = 1)
    (h6 : polarQ f f₂ = 0) : finrank (ZMod 2) (LinearMap.ker (pairMap e e₂ f f₂)) = 2 := by
  have hsurj : Function.Surjective (pairMap e e₂ f f₂) := by
    intro t
    refine ⟨t 0 • f + t 1 • f₂ + t 2 • e + t 3 • e₂, ?_⟩
    have c1 := polarQ_comm e f
    have c2 := polarQ_comm e₂ f₂
    have c3 := polarQ_comm e₂ f
    have c4 := polarQ_comm e f₂
    have c5 := polarQ_comm e e₂
    have c6 := polarQ_comm f f₂
    funext i
    fin_cases i <;>
      simp [pairMap_apply, polarQ_add_left, polarQ_smul_left, polarQ_self, h1, h2, h3, h4, h5,
        h6, ← c1, ← c2, ← c3, ← c4, ← c5, ← c6]
  have h := LinearMap.finrank_range_add_finrank_ker (pairMap e e₂ f f₂)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  omega

theorem exists_frame {p L p' L' : Submodule (ZMod 2) X} (hL : IsTotallySingular L)
    (hL' : IsTotallySingular L') (hp : finrank (ZMod 2) p = 1) (hL2 : finrank (ZMod 2) L = 2)
    (hpL : p ≤ L) (hp' : finrank (ZMod 2) p' = 1) (hL2' : finrank (ZMod 2) L' = 2)
    (hpL' : p' ≤ L') (hLL : L ⊓ L' = ⊥)
    (hB : ∀ x ∈ p, ∀ y ∈ p', x ≠ 0 → y ≠ 0 → QuadraticMap.polar Q x y ≠ 0) :
    ∃ F : Frame, p = (ZMod 2) ∙ F.e ∧ L = Submodule.span (ZMod 2) {F.e, F.e₂} ∧
      p' = (ZMod 2) ∙ F.f ∧ L' = Submodule.span (ZMod 2) {F.f, F.f₂} := by
  have hpne : p ≠ ⊥ := by
    rintro rfl
    simp at hp
  have hpne' : p' ≠ ⊥ := by
    rintro rfl
    simp at hp'
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne'
  have hef : polarQ e f = 1 := by
    have := hB e he f hf he0 hf0
    rw [polar_Q] at this
    exact zmod_two_eq_one_of_ne_zero this
  have heL := hpL he
  have hfL' := hpL' hf
  obtain ⟨e₂, he₂, he₂0, he₂e, he₂f⟩ := exists_partner hL2 heL he0 hef
  obtain ⟨f₂, hf₂, hf₂0, hf₂f, hf₂e⟩ :=
    exists_partner hL2' hfL' hf0 ((polarQ_comm f e).trans hef)
  have hee₂ := polarQ_eq_zero_of_isTotallySingular hL heL he₂
  have hff₂ := polarQ_eq_zero_of_isTotallySingular hL' hfL' hf₂
  have hef₂ : polarQ e f₂ = 0 := (polarQ_comm e f₂).trans hf₂e
  have hL'eq : L' = Submodule.span (ZMod 2) {f, f₂} :=
    eq_span_pair_of_finrank_eq_two hL2' hfL' hf₂ hf0 hf₂0 (Ne.symm hf₂f)
  have hLeq : L = Submodule.span (ZMod 2) {e, e₂} :=
    eq_span_pair_of_finrank_eq_two hL2 heL he₂ he0 he₂0 (Ne.symm he₂e)
  have he₂f₂ : polarQ e₂ f₂ = 1 := by
    refine zmod_two_eq_one_of_ne_zero fun h => he₂0 ?_
    have hmem : e₂ ∈ L' := by
      rw [hL'eq]
      exact mem_span_of_orthogonal hf0 hf₂0 (Ne.symm hf₂f) (hL' f hfL') (hL' f₂ hf₂)
        (hL e₂ he₂) hff₂ ((polarQ_comm f e₂).trans he₂f) ((polarQ_comm f₂ e₂).trans h)
    have : e₂ ∈ L ⊓ L' := ⟨he₂, hmem⟩
    rwa [hLL, Submodule.mem_bot] at this
  set K := LinearMap.ker (pairMap e e₂ f f₂)
  have hK := finrank_ker_pairMap hee₂ hef hef₂ he₂f he₂f₂ hff₂
  have hmemK : ∀ {u : X}, u ∈ K → polarQ u e = 0 ∧ polarQ u e₂ = 0 ∧ polarQ u f = 0 ∧
      polarQ u f₂ = 0 := by
    intro u hu
    have h := congrFun (LinearMap.mem_ker.mp hu)
    exact ⟨h 0, h 1, h 2, h 3⟩
  have hQK : ∀ {u : X}, u ∈ K → u ≠ 0 → Q u = 1 := by
    intro u hu hu0
    obtain ⟨h1, h2, h3, h4⟩ := hmemK hu
    refine zmod_two_eq_one_of_ne_zero fun hQ => ?_
    have hspan := mem_span_of_orthogonal he0 he₂0 (Ne.symm he₂e) (hL e heL) (hL e₂ he₂) hQ hee₂
      ((polarQ_comm e u).trans h1) ((polarQ_comm e₂ u).trans h2)
    rcases mem_span_pair_zmod_two.mp hspan with rfl | rfl | rfl | rfl
    · exact hu0 rfl
    · rw [hef] at h3
      exact absurd h3 (by decide)
    · rw [he₂f₂] at h4
      exact absurd h4 (by decide)
    · rw [polarQ_add_left, hef, he₂f] at h3
      exact absurd h3 (by decide)
  obtain ⟨u₀, hu₀, u₁, hu₁, hu₀0, hu₁0, hu₀₁⟩ := exists_pair_of_finrank_eq_two hK
  have hQu₀ := hQK hu₀ hu₀0
  have hQu₁ := hQK hu₁ hu₁0
  have hQu : Q (u₀ + u₁) = 1 := hQK (K.add_mem hu₀ hu₁) fun h => hu₀₁ (by
    rw [← add_right_cancel_iff (a := u₁), h, add_self_zmod_two])
  have hpol : polarQ u₀ u₁ = 1 := by
    have h := Q_add u₀ u₁
    rw [hQu, hQu₀, hQu₁] at h
    revert h
    generalize polarQ u₀ u₁ = c
    revert c
    decide
  obtain ⟨a1, a2, a3, a4⟩ := hmemK hu₀
  obtain ⟨b1, b2, b3, b4⟩ := hmemK hu₁
  refine ⟨⟨e, e₂, f, f₂, u₀, u₁, hL e heL, hL e₂ he₂, hL' f hfL', hL' f₂ hf₂, hQu₀, hQu₁, hee₂,
    hef, hef₂, (polarQ_comm e u₀).trans a1, (polarQ_comm e u₁).trans b1, he₂f, he₂f₂,
    (polarQ_comm e₂ u₀).trans a2, (polarQ_comm e₂ u₁).trans b2, hff₂,
    (polarQ_comm f u₀).trans a3, (polarQ_comm f u₁).trans b3, (polarQ_comm f₂ u₀).trans a4,
    (polarQ_comm f₂ u₁).trans b4, hpol⟩, eq_span_singleton_of_mem_of_finrank_eq_one hp he he0,
    hLeq, eq_span_singleton_of_mem_of_finrank_eq_one hp' hf hf0, hL'eq⟩

theorem exists_isometry_of_opposite {p L p' L' : Submodule (ZMod 2) X}
    (hL : IsTotallySingular L) (hL' : IsTotallySingular L') (hp : finrank (ZMod 2) p = 1)
    (hL2 : finrank (ZMod 2) L = 2) (hpL : p ≤ L) (hp' : finrank (ZMod 2) p' = 1)
    (hL2' : finrank (ZMod 2) L' = 2) (hpL' : p' ≤ L') (hLL : L ⊓ L' = ⊥)
    (hB : ∀ x ∈ p, ∀ y ∈ p', x ≠ 0 → y ≠ 0 → QuadraticMap.polar Q x y ≠ 0) :
    ∃ φ : QuadraticMap.IsometryEquiv Q Q,
      ((ZMod 2) ∙ e₁).map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) = p ∧
      (Submodule.span (ZMod 2) {e₁, C2E6Overlap.e₂}).map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) = L ∧
      ((ZMod 2) ∙ f₁).map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) = p' ∧
      (Submodule.span (ZMod 2) {f₁, C2E6Overlap.f₂}).map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) =
        L' := by
  obtain ⟨F, rfl, rfl, rfl, rfl⟩ := exists_frame hL hL' hp hL2 hpL hp' hL2' hpL' hLL hB
  refine ⟨F.iso, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_span, Set.image_singleton]
    change (ZMod 2) ∙ F.iso e₁ = _
    rw [F.iso_e₁]
  · rw [Submodule.map_span, Set.image_pair]
    change Submodule.span (ZMod 2) {F.iso e₁, F.iso C2E6Overlap.e₂} = _
    rw [F.iso_e₁, F.iso_e₂]
  · rw [Submodule.map_span, Set.image_singleton]
    change (ZMod 2) ∙ F.iso f₁ = _
    rw [F.iso_f₁]
  · rw [Submodule.map_span, Set.image_pair]
    change Submodule.span (ZMod 2) {F.iso f₁, F.iso C2E6Overlap.f₂} = _
    rw [F.iso_f₁, F.iso_f₂]

end CFSG.LieType.Chevalley.C2E6Overlap
