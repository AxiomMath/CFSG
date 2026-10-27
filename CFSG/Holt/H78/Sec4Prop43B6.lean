module

public import CFSG.Holt.H78.Sec4Prop43B5

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section HalfConj

variable {X Y : Type*}

theorem half_props_permCongr (ψ : X ≃ Y) {x₀ : X} {H : Set X} {s r : Equiv.Perm X}
    (hsγ : s x₀ = x₀) (hsw : ∀ x, x ≠ x₀ → (s x ∈ H ↔ x ∉ H)) (hrγ : r x₀ = x₀)
    (hrH : ∀ x, r x ∈ H ↔ x ∈ H) (hrfree : ∀ x, x ≠ x₀ → r x ≠ x) (hs2 : s * s = 1)
    (hr2 : r * r = 1) (hsr : s * r = r * s) :
    ψ.permCongr s (ψ x₀) = ψ x₀ ∧
      (∀ y, y ≠ ψ x₀ → (ψ.permCongr s y ∈ ψ '' H ↔ y ∉ ψ '' H)) ∧
      ψ.permCongr r (ψ x₀) = ψ x₀ ∧ (∀ y, ψ.permCongr r y ∈ ψ '' H ↔ y ∈ ψ '' H) ∧
      (∀ y, y ≠ ψ x₀ → ψ.permCongr r y ≠ y) ∧ ψ.permCongr s * ψ.permCongr s = 1 ∧
      ψ.permCongr r * ψ.permCongr r = 1 ∧
      ψ.permCongr s * ψ.permCongr r = ψ.permCongr r * ψ.permCongr s := by
  have hmem : ∀ y, y ∈ ψ '' H ↔ ψ.symm y ∈ H := fun y => by
    rw [Equiv.image_eq_preimage_symm]
    rfl
  have hne : ∀ y, y ≠ ψ x₀ → ψ.symm y ≠ x₀ := fun y hy h => hy (by rw [← h, ψ.apply_symm_apply])
  have hmul : ∀ a b : Equiv.Perm X, ψ.permCongr a * ψ.permCongr b = ψ.permCongr (a * b) :=
    fun a b => Equiv.ext fun y => by simp [Equiv.permCongr_apply]
  refine ⟨by simp [Equiv.permCongr_apply, hsγ], fun y hy => ?_,
    by simp [Equiv.permCongr_apply, hrγ],
    fun y => ?_, fun y hy h => ?_, ?_, ?_, ?_⟩
  · rw [hmem, hmem, Equiv.permCongr_apply, ψ.symm_apply_apply]
    exact hsw _ (hne y hy)
  · rw [hmem, hmem, Equiv.permCongr_apply, ψ.symm_apply_apply]
    exact hrH _
  · rw [Equiv.permCongr_apply] at h
    exact hrfree _ (hne y hy) (by rw [← ψ.apply_eq_iff_eq, ψ.apply_symm_apply]; exact h) |>.elim
  · rw [hmul, hs2]
    exact Equiv.ext fun y => by simp [Equiv.permCongr_apply]
  · rw [hmul, hr2]
    exact Equiv.ext fun y => by simp [Equiv.permCongr_apply]
  · rw [hmul, hmul, hsr]

end HalfConj

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_twoPointNormalizer_of_mapsDir {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {j : C.D.ι} (h : C.MapsDir g j j) : g ∈ twoPointNormalizer G Ω α β (C.D.L j) := by
  obtain ⟨σ, hσ⟩ := C.D.conj_L (twoPointElt hg)
  have hσM : ∀ k, C.MapsDir g k (σ k) := fun k δ₁ δ₂ δ₁' δ₂' e₁ e₂ => by
    rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg • δ₁),
      (Subtype.ext e₂ : δ₂' = twoPointElt hg • δ₂)]
    exact C.D.coord_smul_eq_iff_of_conj C.oddCore_eq_bot hσ k δ₁ δ₂
  have hj : j = σ j := MapsDir.eq_of_forall C hg hσM h
  exact (mem_twoPointNormalizer_iff_of_mem hg).mpr (C.D.mem_normalizer_L_of_conj hσ hj.symm)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_mul {g h : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hh : h ∈ stabilizer G ({α, β} : Set Ω)) {j k l : C.D.ι} (hjk : C.MapsDir g j k)
    (hkl : C.MapsDir h k l) (c : C.D.Ψc j) :
    C.transport (mul_mem hh hg) (MapsDir.mul C hg hjk hkl) c =
      C.transport hh hkl (C.transport hg hjk c) := by
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ j = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ₁ := twoPointElt hg • δ
  set δ₂ := twoPointElt hh • δ₁
  rw [← hδ, ← C.coord_smul_eq_transport hg hjk (δ := δ) (δ' := δ₁) rfl,
    ← C.coord_smul_eq_transport hh hkl (δ := δ₁) (δ' := δ₂) rfl,
    ← C.coord_smul_eq_transport (mul_mem hh hg) (MapsDir.mul C hg hjk hkl) (δ := δ) (δ' := δ₂)
      (by change h • g • (δ : Ω) = (h * g) • (δ : Ω); rw [mul_smul])]

@[expose] noncomputable def normElt (j : C.D.ι) :
    ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j)) →*
      Subgroup.normalizer (C.D.L j : Set (twoPointSection G Ω α β)) :=
  (((twoPointHom G Ω α β).comp (Subgroup.inclusion
    (inf_le_left.trans C.calG_le_stabilizer_pair))).codRestrict (twoPointSection G Ω α β)
      fun _ => twoPointHom_mem_twoPointSection _).codRestrict _ fun g =>
    (mem_twoPointNormalizer_iff_of_mem _).mp (Subgroup.mem_inf.mp g.2).2

@[expose] noncomputable def normHom (j : C.D.ι) :
    ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j)) →* Equiv.Perm (C.D.Ψc j) :=
  (C.D.nRho j).comp (C.normElt j)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_smul_eq_normHom {j : C.D.ι} (g : ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j)))
    {δ δ' : holtDelta G Ω α β} (h : (δ' : Ω) = (g : G) • (δ : Ω)) :
    C.D.coord δ' j = C.normHom j g (C.D.coord δ j) := by
  have hδ' : δ' = (C.normElt j g : twoPointSection G Ω α β) • δ := Subtype.ext h
  rw [normHom, MonoidHom.comp_apply, C.D.nRho_coord, hδ']

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_eq_normHom {j : C.D.ι}
    (g : ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j))) (hjj : C.MapsDir g j j) :
    C.transport (C.calG_le_stabilizer_pair (Subgroup.mem_inf.mp g.2).1) hjj = C.normHom j g := by
  refine Equiv.ext fun c => ?_
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ j = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ' := twoPointElt (C.calG_le_stabilizer_pair (Subgroup.mem_inf.mp g.2).1) • δ
  rw [← hδ, ← C.coord_smul_eq_transport _ hjj (δ := δ) (δ' := δ') rfl,
    ← C.coord_smul_eq_normHom g (δ := δ) (δ' := δ') rfl]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem kerC_le_calG_inf (j : C.D.ι) :
    C.kerC j ≤ C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j) := fun _ hq =>
  Subgroup.mem_inf.mpr ⟨C.kerC_le_calG j hq, (mem_twoPointNormalizer_iff_of_mem
    (C.kerC_le_stabilizer_pair j hq)).mpr (C.twoPointElt_mem_normalizer_of_mem_kerC hq j)⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem kerCHom_eq_normHom {j : C.D.ι} (q : C.kerC j) :
    C.kerCHom j q = C.normHom j ⟨q, C.kerC_le_calG_inf j q.2⟩ := by
  refine Equiv.ext fun c => ?_
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ j = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ' := twoPointElt (C.kerC_le_stabilizer_pair j q.2) • δ
  rw [← hδ, ← C.coord_smul_eq_kerCHom q (δ' := δ') rfl,
    ← C.coord_smul_eq_normHom ⟨q, C.kerC_le_calG_inf j q.2⟩ (δ' := δ') rfl]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mapsDir_of_mem_kerC {j : C.D.ι} (q : C.kerC j) : C.MapsDir q j j := by
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  rw [C.coord_smul_eq_kerCHom q e₁, C.coord_smul_eq_kerCHom q e₂]
  exact (C.kerCHom j q).injective.eq_iff

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_eq_kerCHom {j : C.D.ι} (q : C.kerC j) :
    C.transport (C.kerC_le_stabilizer_pair j q.2) (C.mapsDir_of_mem_kerC q) = C.kerCHom j q := by
  refine Equiv.ext fun c => ?_
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ j = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
  set δ' := twoPointElt (C.kerC_le_stabilizer_pair j q.2) • δ
  rw [← hδ, ← C.coord_smul_eq_transport _ (C.mapsDir_of_mem_kerC q) (δ := δ) (δ' := δ') rfl,
    ← C.coord_smul_eq_kerCHom q (δ' := δ') rfl]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_symm {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k : C.D.ι}
    (h : C.MapsDir g j k) : (C.transport hg h).symm = C.transport (inv_mem hg) h.inv :=
  Equiv.ext fun _ => rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem transport_half_compat {j₀ : C.D.ι} {H : Set (C.D.Ψc j₀)}
    (hinv : ∀ g : ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j₀)), (g : G) ∈ C.calP →
      (∀ x, C.normHom j₀ g x ∈ H ↔ x ∈ H) ∨
        (∀ x, x ≠ C.D.coord C.γ j₀ → (C.normHom j₀ g x ∈ H ↔ x ∉ H)))
    {p₁ p₂ : G} (hp₁ : p₁ ∈ C.calP) (hp₂ : p₂ ∈ C.calP) {j k : C.D.ι}
    (h₁ : C.MapsDir p₁ j₀ j) (h₂ : C.MapsDir p₂ j₀ k) {p : G} (hp : p ∈ C.calP)
    (hpjk : C.MapsDir p j k) :
    (∀ c, C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hpjk c ∈
        C.transport (C.mem_stabilizer_pair_of_mem_calP hp₂) h₂ '' H ↔
      c ∈ C.transport (C.mem_stabilizer_pair_of_mem_calP hp₁) h₁ '' H) ∨
    (∀ c, c ≠ C.D.coord C.γ j →
      (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hpjk c ∈
        C.transport (C.mem_stabilizer_pair_of_mem_calP hp₂) h₂ '' H ↔
      c ∉ C.transport (C.mem_stabilizer_pair_of_mem_calP hp₁) h₁ '' H)) := by
  have hS₁ := C.mem_stabilizer_pair_of_mem_calP hp₁
  have hS₂ := C.mem_stabilizer_pair_of_mem_calP hp₂
  have hSp := C.mem_stabilizer_pair_of_mem_calP hp
  set φ₁ := C.transport hS₁ h₁
  set φ₂ := C.transport hS₂ h₂
  set T := C.transport hSp hpjk
  have hg1 : C.MapsDir (p * p₁) j₀ k := MapsDir.mul C hS₁ h₁ hpjk
  have hg : C.MapsDir (p₂⁻¹ * (p * p₁)) j₀ j₀ := MapsDir.mul C (mul_mem hSp hS₁) hg1 h₂.inv
  have hgP : p₂⁻¹ * (p * p₁) ∈ C.calP :=
    C.calP.mul_mem (C.calP.inv_mem hp₂) (C.calP.mul_mem hp hp₁)
  have hgS : p₂⁻¹ * (p * p₁) ∈ stabilizer G ({α, β} : Set Ω) :=
    C.mem_stabilizer_pair_of_mem_calP hgP
  have hgN : p₂⁻¹ * (p * p₁) ∈ C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j₀) :=
    Subgroup.mem_inf.mpr ⟨C.calP_le_calG hgP, C.mem_twoPointNormalizer_of_mapsDir hgS hg⟩
  have hT : ∀ y, C.normHom j₀ ⟨_, hgN⟩ y = φ₂.symm (T (φ₁ y)) := by
    intro y
    rw [← C.transport_eq_normHom ⟨_, hgN⟩ hg, C.transport_symm hS₂ h₂]
    rw [show C.transport (C.calG_le_stabilizer_pair (Subgroup.mem_inf.mp hgN).1) hg y =
      C.transport (mul_mem (inv_mem hS₂) (mul_mem hSp hS₁)) (MapsDir.mul C (mul_mem hSp hS₁) hg1
        h₂.inv) y from rfl]
    rw [C.transport_mul (mul_mem hSp hS₁) (inv_mem hS₂) hg1 h₂.inv,
      C.transport_mul hS₁ hSp h₁ hpjk]
  have hmem : ∀ (φ : C.D.Ψc j₀ ≃ C.D.Ψc k) (x : C.D.Ψc k), x ∈ φ '' H ↔ φ.symm x ∈ H :=
    fun φ x => by rw [Equiv.image_eq_preimage_symm]; rfl
  have hmem₁ : ∀ x, x ∈ φ₁ '' H ↔ φ₁.symm x ∈ H := fun x => by
    rw [Equiv.image_eq_preimage_symm]; rfl
  have hφ₁γ : φ₁ (C.D.coord C.γ j₀) = C.D.coord C.γ j := C.transport_γ hS₁ h₁
    (C.smul_γ_of_mem_calP hp₁)
  rcases hinv ⟨_, hgN⟩ hgP with h | h
  · left
    intro c
    have := h (φ₁.symm c)
    rw [hT, Equiv.apply_symm_apply] at this
    rw [hmem, hmem₁]
    exact this
  · right
    intro c hc
    have hc' : φ₁.symm c ≠ C.D.coord C.γ j₀ := fun h' =>
      hc (by rw [← Equiv.apply_symm_apply φ₁ c, h', hφ₁γ])
    have := h (φ₁.symm c) hc'
    rw [hT, Equiv.apply_symm_apply] at this
    rw [hmem, hmem₁]
    exact this

theorem fix_of_half (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    {j : C.D.ι} (h4 : Fintype.card (C.D.Ψc j) % 4 = 1) {H : Set (C.D.Ψc j)}
    (hγ : C.D.coord C.γ j ∉ H) (hHne : H.Nonempty)
    (hQ : ∀ q : C.kerC j, (q : G) ∈ C.calP → (∀ x, C.kerCHom j q x ∈ H ↔ x ∈ H) ∨
      (∀ x, x ≠ C.D.coord C.γ j → (C.kerCHom j q x ∈ H ↔ x ∉ H)))
    {s₀ r₀ : Equiv.Perm (C.D.Ψc j)} (hs₀ : s₀ ∈ C.Qimg j) (hr₀ : r₀ ∈ C.Qimg j)
    (hs₀γ : s₀ (C.D.coord C.γ j) = C.D.coord C.γ j)
    (hs₀sw : ∀ x, x ≠ C.D.coord C.γ j → (s₀ x ∈ H ↔ x ∉ H))
    (hr₀γ : r₀ (C.D.coord C.γ j) = C.D.coord C.γ j) (hr₀H : ∀ x, r₀ x ∈ H ↔ x ∈ H)
    (hr₀free : ∀ x, x ≠ C.D.coord C.γ j → r₀ x ≠ x) (hs₀2 : s₀ * s₀ = 1) (hr₀2 : r₀ * r₀ = 1)
    (hsr₀ : s₀ * r₀ = r₀ * s₀) :
    ∃ s' : C.kerC j, (s' : G) ∈ C.calP ∧ C.kerCHom j s' = s₀ ∧
      ∀ ω ∈ fixSet Ω (C.halfStab j H), ∀ q ∈ C.calP ⊓ C.kerC j, q • ω = ω := by
  obtain ⟨s', hs'P, hs'⟩ := C.exists_of_mem_Qimg hs₀
  obtain ⟨r', hr'P, hr'⟩ := C.exists_of_mem_Qimg hr₀
  have hcompl : ∀ (π : Equiv.Perm (C.D.Ψc j)), π (C.D.coord C.γ j) = C.D.coord C.γ j →
      ∀ x, x ≠ C.D.coord C.γ j → π x ≠ C.D.coord C.γ j := fun π hπ x hx h =>
    hx (π.injective (h.trans hπ.symm))
  have hsR : (s' : G) ∉ C.halfStab j H := by
    rintro ⟨-, h, hH⟩
    obtain ⟨x, hx⟩ := hHne
    have h1 := (hH x).mpr hx
    rw [show (⟨(s' : G), h⟩ : C.kerC j) = s' from rfl, hs'] at h1
    exact ((hs₀sw x (fun h' => hγ (h' ▸ hx))).mp h1) hx
  have hrR : (r' : G) ∈ C.halfStab j H := ⟨hr'P, r'.2, fun x => by
    rw [show (⟨(r' : G), r'.2⟩ : C.kerC j) = r' from rfl, hr']
    exact hr₀H x⟩
  have hswapH : ∀ (π : Equiv.Perm (C.D.Ψc j)), π (C.D.coord C.γ j) = C.D.coord C.γ j →
      (∀ x, x ≠ C.D.coord C.γ j → (π x ∈ H ↔ x ∉ H)) → ∀ x, s₀ (π x) ∈ H ↔ x ∈ H := by
    intro π hπγ hπ x
    by_cases hx : x = C.D.coord C.γ j
    · rw [hx, hπγ, hs₀γ]
    · rw [hs₀sw (π x) (hcompl π hπγ x hx), hπ x hx, not_not]
  have hQR : ∀ q ∈ C.calP ⊓ C.kerC j, q ∈ C.halfStab j H ∨ (s' : G) * q ∈ C.halfStab j H := by
    intro q hq
    obtain ⟨hqP, hqK⟩ := Subgroup.mem_inf.mp hq
    rcases hQ ⟨q, hqK⟩ hqP with h | h
    · exact Or.inl ⟨hqP, hqK, h⟩
    · refine Or.inr ⟨C.calP.mul_mem hs'P hqP, (C.kerC j).mul_mem s'.2 hqK, fun x => ?_⟩
      rw [show (⟨(s' : G) * q, (C.kerC j).mul_mem s'.2 hqK⟩ : C.kerC j) =
        s' * ⟨q, hqK⟩ from rfl, map_mul, Equiv.Perm.mul_apply, hs']
      exact hswapH _ (C.kerCHom_apply_γ _) h x
  have hsfree : ∀ c, c ≠ C.D.coord C.γ j → C.kerCHom j s' c ≠ c := by
    intro c hc h
    rw [hs'] at h
    have h1 := hs₀sw c hc
    rw [h] at h1
    exact (iff_not_self h1).elim
  have hrfree : ∀ c, c ≠ C.D.coord C.γ j → C.kerCHom j r' c ≠ c := by
    intro c hc
    rw [hr']
    exact hr₀free c hc
  have hsrfree : ∀ c, c ≠ C.D.coord C.γ j → C.kerCHom j (s' * r') c ≠ c := by
    intro c hc h
    rw [map_mul, Equiv.Perm.mul_apply, hs', hr'] at h
    have h1 := hs₀sw (r₀ c) (hcompl r₀ hr₀γ c hc)
    rw [h, hr₀H] at h1
    exact (iff_not_self h1).elim
  have hfixR := C.smul_eq_of_lemma44 hS hαβ hT hP h4 (C.halfStab_le j H) hs'P hsR hrR hQR
    (by rw [hs']; exact hs₀2) (by rw [hr']; exact hr₀2) (by rw [hs', hr']; exact hsr₀) hsfree
    hrfree hsrfree
  refine ⟨s', hs'P, hs', fun ω hω q hq => ?_⟩
  rcases hQR q hq with h | h
  · exact hω q h
  · have h1 := hω _ h
    rw [mul_smul] at h1
    exact smul_left_cancel _ (h1.trans (hfixR ω hω).symm)

theorem false_of_half_ne (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (htrans : ∀ j k, j ≠ C.i₁ → k ≠ C.i₁ → ∃ p ∈ C.calP, C.MapsDir p j k) {j₀ : C.D.ι}
    (hj₀ : j₀ ≠ C.i₁) {b : ℕ} (hb : 3 ≤ b) (hcard : Fintype.card (C.D.Ψc j₀) = 2 ^ b + 1) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardΛ : Nat.card ↥(({C.D.coord C.γ j₀} : Set (C.D.Ψc j₀))ᶜ) = 2 ^ b := by
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp [hcard]
  have hV := C.fusionIsSylowIn_Qimg_inf hS hP j₀
  rw [← fixingSubgroup_singleton_perm] at hV
  set N₀ := C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j₀) with hN₀
  set QP : Subgroup (Equiv.Perm (C.D.Ψc j₀)) :=
    ((C.calP ⊓ twoPointNormalizer G Ω α β (C.D.L j₀)).subgroupOf N₀).map (C.normHom j₀)
    with hQPdef
  have hQP : IsPGroup 2 QP :=
    (((C.sylow.2.1.to_le (inf_le_left.trans inf_le_left)).comap_of_injective N₀.subtype
      N₀.subtype_injective).to_le le_rfl).map _
  have hVQP : C.Qimg j₀ ⊓ alternatingGroup (C.D.Ψc j₀) ≤ QP := by
    intro u hu
    obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hu).1
    refine ⟨⟨q, C.kerC_le_calG_inf j₀ q.2⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨hqP, (Subgroup.mem_inf.mp (C.kerC_le_calG_inf j₀ q.2)).2⟩), ?_⟩
    exact (C.kerCHom_eq_normHom q).symm
  have hγfix : ∀ g : N₀, C.normHom j₀ g (C.D.coord C.γ j₀) = C.D.coord C.γ j₀ := fun g =>
    (C.coord_smul_eq_normHom g (δ := C.γ) (δ' := C.γ)
      (C.calG_le_stabilizer_γ (Subgroup.mem_inf.mp g.2).1).symm).symm
  have hQPΛ : QP ≤ fixingSubgroup (Equiv.Perm (C.D.Ψc j₀)) {C.D.coord C.γ j₀} := by
    rintro _ ⟨g, -, rfl⟩
    rw [fixingSubgroup_singleton_perm]
    exact hγfix g
  obtain ⟨H, hHΛ, hHcard, hinvQ, ⟨s, hsV, hs2, hssw, r, hrV, hr2, hrH, hrfree, hsr⟩,
    hsweep⟩ := exists_half_system_strong (by omega) hcardΛ hV hQP hVQP hQPΛ
  have hmemΛ : ∀ x : C.D.Ψc j₀, x ∈ ({C.D.coord C.γ j₀} : Set (C.D.Ψc j₀))ᶜ ↔
      x ≠ C.D.coord C.γ j₀ := fun x => by simp
  have hinv : ∀ g : N₀, (g : G) ∈ C.calP → (∀ x, C.normHom j₀ g x ∈ H ↔ x ∈ H) ∨
      (∀ x, x ≠ C.D.coord C.γ j₀ → (C.normHom j₀ g x ∈ H ↔ x ∉ H)) := by
    intro g hgP
    rcases hinvQ _ ⟨g, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨hgP, (Subgroup.mem_inf.mp g.2).2⟩), rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx => h x ((hmemΛ x).mpr hx)
  have hch : ∀ j, j ≠ C.i₁ → ∃ p ∈ C.calP, C.MapsDir p j₀ j := fun j hj => htrans j₀ j hj₀ hj
  choose pj hpjP hpjM using hch
  set φ : ∀ j, j ≠ C.i₁ → (C.D.Ψc j₀ ≃ C.D.Ψc j) := fun j hj =>
    C.transport (C.mem_stabilizer_pair_of_mem_calP (hpjP j hj)) (hpjM j hj) with hφdef
  set Hj : ∀ j, Set (C.D.Ψc j) := fun j => if hj : j = C.i₁ then ∅ else φ j hj '' H with hHjdef
  have hHj : ∀ j (hj : j ≠ C.i₁), Hj j = φ j hj '' H := fun j hj => by simp [hHjdef, hj]
  have hφγ : ∀ j (hj : j ≠ C.i₁), φ j hj (C.D.coord C.γ j₀) = C.D.coord C.γ j := fun j hj =>
    C.transport_γ _ _ (C.smul_γ_of_mem_calP (hpjP j hj))
  have hγH : C.D.coord C.γ j₀ ∉ H := fun h => (hmemΛ _).mp (hHΛ h) rfl
  have hγHj : ∀ j (hj : j ≠ C.i₁), C.D.coord C.γ j ∉ Hj j := fun j hj h => by
    rw [hHj j hj, ← hφγ j hj] at h
    exact hγH ((φ j hj).injective.mem_set_image.mp h)
  have hcompat : ∀ p (hp : p ∈ C.calP) j k (hj : j ≠ C.i₁) (hk : k ≠ C.i₁)
      (hpjk : C.MapsDir p j k),
      (∀ c, C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hpjk c ∈ Hj k ↔ c ∈ Hj j) ∨
      (∀ c, c ≠ C.D.coord C.γ j →
        (C.transport (C.mem_stabilizer_pair_of_mem_calP hp) hpjk c ∈ Hj k ↔ c ∉ Hj j)) := by
    intro p hp j k hj hk hpjk
    rw [hHj j hj, hHj k hk]
    exact C.transport_half_compat hinv (hpjP j hj) (hpjP k hk) (hpjM j hj) (hpjM k hk) hp hpjk
  have hsγ : s (C.D.coord C.γ j₀) = C.D.coord C.γ j₀ := by
    have := hV.1 hsV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  have hrγ : r (C.D.coord C.γ j₀) = C.D.coord C.γ j₀ := by
    have := hV.1 hrV
    rw [fixingSubgroup_singleton_perm] at this
    exact this.2
  have hHne : H.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    rw [← Nat.card_coe_set_eq]
    have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcoordj : ∀ j (hj : j ≠ C.i₁), ∃ s' : C.kerC j, (s' : G) ∈ C.calP ∧
      C.kerCHom j s' (C.D.coord C.γ j) = C.D.coord C.γ j ∧
      (∀ x, x ≠ C.D.coord C.γ j → (C.kerCHom j s' x ∈ Hj j ↔ x ∉ Hj j)) ∧
      ∀ ω ∈ fixSet Ω (C.halfStab j (Hj j)), ∀ q ∈ C.calP ⊓ C.kerC j, q • ω = ω := by
    intro j hj
    have hcardj : Fintype.card (C.D.Ψc j) = 2 ^ b + 1 :=
      (C.card_Ψc_eq_of_mapsDir (hpjP j hj) (hpjM j hj)).symm.trans hcard
    have h4 : Fintype.card (C.D.Ψc j) % 4 = 1 := by
      rw [hcardj, show b = 2 + (b - 2) by omega, pow_add]
      simp [Nat.add_mod]
    obtain ⟨h1, h2, h3, h4', h5, h6, h7, h8⟩ := half_props_permCongr (φ j hj) hsγ
      (fun x hx => hssw x ((hmemΛ x).mpr hx)) hrγ hrH (fun x hx => hrfree x ((hmemΛ x).mpr hx))
      (by rw [← sq]; exact hs2) (by rw [← sq]; exact hr2) hsr
    simp only [hφγ j hj, ← hHj j hj] at h1 h2 h3 h4' h5
    have hQ : ∀ q : C.kerC j, (q : G) ∈ C.calP → (∀ x, C.kerCHom j q x ∈ Hj j ↔ x ∈ Hj j) ∨
        (∀ x, x ≠ C.D.coord C.γ j → (C.kerCHom j q x ∈ Hj j ↔ x ∉ Hj j)) := by
      intro q hqP
      have := hcompat q hqP j j hj hj (C.mapsDir_of_mem_kerC q)
      rwa [show C.transport (C.mem_stabilizer_pair_of_mem_calP hqP) (C.mapsDir_of_mem_kerC q) =
        C.kerCHom j q from C.transport_eq_kerCHom q] at this
    obtain ⟨s', hs'P, hs', hfix⟩ := C.fix_of_half hS hαβ hT hP h4 (hγHj j hj)
      (by rw [hHj j hj]; exact hHne.image _) hQ
      (C.permCongr_mem_Qimg (hpjP j hj) (hpjM j hj) (Subgroup.mem_inf.mp hsV).1)
      (C.permCongr_mem_Qimg (hpjP j hj) (hpjM j hj) (Subgroup.mem_inf.mp hrV).1)
      h1 h2 h3 h4' h5 h6 h7 h8
    exact ⟨s', hs'P, by rw [hs']; exact h1, fun x hx => by rw [hs']; exact h2 x hx, hfix⟩
  choose sj hsjP hsjγ hsjsw hsjfix using hcoordj
  set Λc : ∀ j, Set (C.D.Ψc j) := Function.update (fun j => insert (C.D.coord C.γ j) (Hj j))
    C.i₁ Set.univ with hΛc
  have hΛ₁ : Λc C.i₁ = Set.univ := Function.update_self _ _ _
  have hΛj : ∀ j, j ≠ C.i₁ → Λc j = insert (C.D.coord C.γ j) (Hj j) := fun j hj =>
    Function.update_of_ne hj _ _
  have hcardH : H.ncard = 2 ^ (b - 1) := by
    rw [← Nat.card_coe_set_eq]
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hcardHj : ∀ j (hj : j ≠ C.i₁), (Hj j).ncard = 2 ^ (b - 1) := fun j hj => by
    rw [hHj j hj, Set.ncard_image_of_injective _ (φ j hj).injective, hcardH]
  have hsize : ∀ j, (Λc j).ncard = 1 ∨ 5 ≤ (Λc j).ncard := by
    intro j
    right
    by_cases hj : j = C.i₁
    · subst hj
      rw [hΛ₁, C.ncard_univ_Ψc]
      exact C.D.five_le_card _
    · rw [hΛj j hj, Set.ncard_insert_of_notMem (hγHj j hj) (Set.toFinite _), hcardHj j hj]
      have : 2 ^ 2 ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hsweep' := hsweep hb
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ j, C.D.coord δ j ∈ Λc j) → ∃ v ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ j, C.D.coord δ' j ∈ Λc j) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ := by
    intro δ hδ
    push Not at hδ
    obtain ⟨j, hj⟩ := hδ
    have hj1 : j ≠ C.i₁ := by
      rintro rfl
      rw [hΛ₁] at hj
      exact hj (Set.mem_univ _)
    rw [hΛj j hj1] at hj
    set c₀ := (φ j hj1).symm (C.D.coord δ j)
    have hc₀ : c₀ ∉ fixSet (C.D.Ψc j₀)
        (C.Qimg j₀ ⊓ alternatingGroup (C.D.Ψc j₀) ⊓ fixingSubgroup (Perm (C.D.Ψc j₀)) H) := by
      rw [hsweep']
      rintro (h | h)
      · apply hj
        left
        rw [← hφγ j hj1, ← Set.mem_singleton_iff.mp h, Equiv.apply_symm_apply]
      · apply hj
        right
        rw [hHj j hj1]
        exact ⟨c₀, h, Equiv.apply_symm_apply _ _⟩
    simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hc₀
    obtain ⟨w, hw, hmv⟩ := hc₀
    obtain ⟨hwV, hwH⟩ := Subgroup.mem_inf.mp hw
    have hwγ : w (C.D.coord C.γ j₀) = C.D.coord C.γ j₀ := by
      have := hV.1 hwV
      rw [fixingSubgroup_singleton_perm] at this
      exact this.2
    refine C.exists_mem_calP_of_mem_Qimg_fix (C.permCongr_mem_Qimg (hpjP j hj1) (hpjM j hj1)
      (Subgroup.mem_inf.mp hwV).1) (Λc := Λc) ?_ ?_
    · intro c hc
      rw [hΛj j hj1] at hc
      change (φ j hj1) (w ((φ j hj1).symm c)) = c
      rcases hc with rfl | hc
      · rw [← hφγ j hj1, Equiv.symm_apply_apply, hwγ]
      · rw [hHj j hj1] at hc
        obtain ⟨x, hx, rfl⟩ := hc
        have hwx : w x = x := (mem_fixingSubgroup_iff _).mp hwH x hx
        rw [Equiv.symm_apply_apply, hwx]
    · change (φ j hj1) (w c₀) ≠ C.D.coord δ j
      intro h
      apply hmv
      change w c₀ = c₀
      rw [← (φ j hj1).apply_eq_iff_eq, h, Equiv.apply_symm_apply]
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ j, C.D.coord δ j ∈ Λc j := by
    obtain ⟨c₀, hc₀Λ, hc₀H⟩ : ∃ c₀, c₀ ∈ ({C.D.coord C.γ j₀} : Set (C.D.Ψc j₀))ᶜ ∧
        c₀ ∉ Hj j₀ := by
      by_contra h
      push Not at h
      have h1 := Set.ncard_le_ncard (fun x hx => h x hx) (Set.toFinite (Hj j₀))
      rw [← Nat.card_coe_set_eq, hcardΛ, hcardHj j₀ hj₀] at h1
      have : 2 ^ b = 2 * 2 ^ (b - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
      omega
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) j₀ c₀), fun h => ?_⟩
    have := h j₀
    rw [hΛj j₀ hj₀, C.coord_coordEquiv_symm, Function.update_self] at this
    rcases this with h' | h'
    · exact (hmemΛ c₀).mp hc₀Λ h'
    · exact hc₀H h'
  have h₁ : 5 ≤ (Λc C.i₁).ncard := by
    rw [hΛ₁, C.ncard_univ_Ψc]
    exact C.D.five_le_card _
  have hj' : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard := ⟨j₀, hj₀, (hsize j₀).resolve_left (by
    rw [hΛj j₀ hj₀, Set.ncard_insert_of_notMem (hγHj j₀ hj₀) (Set.toFinite _), hcardHj j₀ hj₀]
    have : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
    omega)⟩
  have h4' := C.four_le_card_fixSet_calP_inf_stabilizer hS hαβ Λc hmove hne hsize h₁ hj'
  obtain ⟨b', hb', hb't⟩ := C.exists_mem_fixSet_notMem_triple hαβ h4'
  have hQjb : ∀ j (hj : j ≠ C.i₁), ∀ q ∈ C.calP ⊓ C.kerC j, q • b' = b' := by
    intro j hj
    refine hsjfix j hj b' fun g hg => hb' g ?_
    obtain ⟨hgP, hgK, hgH⟩ := hg
    refine Subgroup.mem_inf.mpr ⟨hgP, C.mem_stabilizer_boxSet (C.kerC_le_stabilizer_pair j hgK)
      fun δ δ' e => ?_⟩
    have hco : ∀ k, k ≠ j → C.D.coord δ' k = C.D.coord δ k := fun k hk =>
      C.coord_smul_of_mem_kerC hgK e hk
    have hcj : C.D.coord δ' j = C.kerCHom j ⟨g, hgK⟩ (C.D.coord δ j) :=
      C.coord_smul_eq_kerCHom ⟨g, hgK⟩ e
    refine forall_congr' fun k => ?_
    by_cases hkj : k = j
    · subst hkj
      rw [hcj, hΛj k hj]
      by_cases hc : C.D.coord δ k = C.D.coord C.γ k
      · rw [hc, C.kerCHom_apply_γ]
      · have hne' : C.kerCHom k ⟨g, hgK⟩ (C.D.coord δ k) ≠ C.D.coord C.γ k := fun h =>
          hc ((C.kerCHom k ⟨g, hgK⟩).injective (h.trans (C.kerCHom_apply_γ _).symm))
        simp only [Set.mem_insert_iff, hc, hne', false_or, hgH]
    · rw [hco k hkj]
  have hinto : ∀ p ∈ C.calP, (∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ j, C.D.coord δ j ∈ Λc j) → ∀ j, C.D.coord δ' j ∈ Λc j) →
        p ∈ C.calP ⊓ stabilizer G (C.boxSet Λc) := by
    intro p hp hpi
    have hpS := C.mem_stabilizer_pair_of_mem_calP hp
    refine Subgroup.mem_inf.mpr ⟨hp, C.mem_stabilizer_boxSet hpS fun δ δ' e =>
      ⟨fun h' => ?_, hpi δ δ' e⟩⟩
    let f : {x : holtDelta G Ω α β // ∀ j, C.D.coord x j ∈ Λc j} →
        {x : holtDelta G Ω α β // ∀ j, C.D.coord x j ∈ Λc j} :=
      fun x => ⟨twoPointElt hpS • x.1, hpi x.1 _ rfl x.2⟩
    have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext
      (smul_left_cancel p (congrArg (fun z => ((z.1 : holtDelta G Ω α β) : Ω)) h)))
    obtain ⟨⟨δ₀, h₀⟩, hδ₀⟩ := (Finite.injective_iff_surjective.mp hf) ⟨δ', h'⟩
    have h1 : (δ₀ : Ω) = δ := smul_left_cancel p
      ((congrArg (fun z => ((z.1 : holtDelta G Ω α β) : Ω)) hδ₀).trans e)
    rw [← (Subtype.ext h1 : δ₀ = δ)]
    exact h₀
  set good : G → C.D.ι → Prop := fun p k => ∀ δ δ' : holtDelta G Ω α β,
    (δ' : Ω) = p • (δ : Ω) → (∀ j, C.D.coord δ j ∈ Λc j) → C.D.coord δ' k ∈ Λc k with hgood
  set bad : G → Finset C.D.ι := fun p => Finset.univ.filter fun k => ¬ good p k with hbad
  have hgood₁ : ∀ p, good p C.i₁ := fun p δ δ' _ _ => by rw [hΛ₁]; exact Set.mem_univ _
  have hstep : ∀ p ∈ C.calP, ∀ k (hk : k ∈ bad p) (hk1 : k ≠ C.i₁),
      bad ((sj k hk1 : G) * p) ⊆ (bad p).erase k := by
    intro p hp k hk hk1
    set q := sj k hk1
    have hpS := C.mem_stabilizer_pair_of_mem_calP hp
    obtain ⟨σ, hσ⟩ := C.exists_mapsDir hpS
    have hm : C.MapsDir p (σ.symm k) k := by
      have := hσ (σ.symm k)
      rwa [Equiv.apply_symm_apply] at this
    have hm1 : σ.symm k ≠ C.i₁ := fun h => hk1 ((C.eq_i₁_iff_of_mapsDir hp hm).mp h)
    set T := C.transport hpS hm
    have hTγ : T (C.D.coord C.γ (σ.symm k)) = C.D.coord C.γ k :=
      C.transport_γ hpS hm (C.smul_γ_of_mem_calP hp)
    have hswap : ∀ c, c ≠ C.D.coord C.γ (σ.symm k) → (T c ∈ Hj k ↔ c ∉ Hj (σ.symm k)) := by
      rcases hcompat p hp _ k hm1 hk1 hm with h | h
      · exfalso
        refine (Finset.mem_filter.mp hk).2 fun δ δ' e hδ => ?_
        rw [hΛj k hk1, C.coord_smul_eq_transport hpS hm e]
        have h1 := hδ (σ.symm k)
        rw [hΛj _ hm1] at h1
        rcases h1 with h1 | h1
        · rw [h1, hTγ]
          exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ((h _).mpr h1)
      · exact h
    have hgoodk : good ((q : G) * p) k := by
      intro δ δ'' e hδ
      set δ' := twoPointElt hpS • δ
      have e' : (δ'' : Ω) = (q : G) • (δ' : Ω) := by rw [e, mul_smul]; rfl
      rw [C.coord_smul_eq_kerCHom q e', C.coord_smul_eq_transport hpS hm (δ' := δ') rfl,
        hΛj k hk1]
      have h1 := hδ (σ.symm k)
      rw [hΛj _ hm1] at h1
      rcases h1 with h1 | h1
      · rw [h1, hTγ, hsjγ k hk1]
        exact Set.mem_insert _ _
      · have hc : C.D.coord δ (σ.symm k) ≠ C.D.coord C.γ (σ.symm k) := fun h =>
          hγHj _ hm1 (h ▸ h1)
        have hTc : T (C.D.coord δ (σ.symm k)) ≠ C.D.coord C.γ k := fun h =>
          hc (T.injective (h.trans hTγ.symm))
        refine Set.mem_insert_of_mem _ ((hsjsw k hk1 _ hTc).mpr ?_)
        exact (hswap _ hc).not.mpr (not_not.mpr h1)
    intro k' hk'
    have hk'bad := (Finset.mem_filter.mp hk').2
    refine Finset.mem_erase.mpr ⟨fun hkk => hk'bad (hkk ▸ hgoodk), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun hgp => hk'bad ?_⟩⟩
    intro δ δ'' e hδ
    by_cases hkk : k' = k
    · subst hkk
      exact hgoodk δ δ'' e hδ
    · set δ' := twoPointElt hpS • δ
      have e' : (δ'' : Ω) = (q : G) • (δ' : Ω) := by rw [e, mul_smul]; rfl
      rw [C.coord_smul_of_mem_kerC q.2 e' hkk]
      exact hgp δ δ' rfl hδ
  have hmain : ∀ n, ∀ p ∈ C.calP, (bad p).card ≤ n → p • b' = b' := by
    intro n
    induction n with
    | zero =>
      intro p hp hcard0
      have hempty : bad p = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard0)
      refine hb' p (hinto p hp fun δ δ' e hδ k => ?_)
      by_contra hk
      have : k ∈ bad p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hg => hk (hg δ δ' e hδ)⟩
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    | succ n ih =>
      intro p hp hcardn
      by_cases hempty : bad p = ∅
      · exact ih p hp (by rw [hempty]; exact Nat.zero_le _)
      · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hk1 : k ≠ C.i₁ := fun h => (Finset.mem_filter.mp hk).2 (h ▸ hgood₁ p)
        have hqp : (sj k hk1 : G) * p ∈ C.calP := C.calP.mul_mem (hsjP k hk1) hp
        have hc := Finset.card_le_card (hstep p hp k hk hk1)
        rw [Finset.card_erase_of_mem hk] at hc
        have h1 := ih _ hqp (by omega)
        have hq : (sj k hk1 : G) • b' = b' :=
          hQjb k hk1 _ (Subgroup.mem_inf.mpr ⟨hsjP k hk1, (sj k hk1).2⟩)
        rw [mul_smul] at h1
        exact smul_left_cancel _ (h1.trans hq.symm)
  have hbP : b' ∈ fixSet Ω C.calP := fun p hp => hmain _ p hp le_rfl
  exact C.false_of_mem_fixSet_calP hαβ hbP hb't

end AltConfig

end CFSG.Holt.H78
