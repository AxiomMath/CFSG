module

public import CFSG.GF2Type.Smith1979.W4C2Model
public import CFSG.LargeExtraspecial.Types
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

theorem isTypeA_of_conj {h ℓ : Vm ≃ₗ[ZMod 2] Vm} (hh : ∀ v, q0 (h v) = q0 v)
    (H : IsTypeA q0 (h * ℓ * h⁻¹) 2) : IsTypeA q0 ℓ 2 := by
  obtain ⟨hiso, hne, hsq, hdim, hsing⟩ := H
  refine ⟨fun v => ?_, fun h1 => hne (by rw [h1]; group), ?_, ?_, fun x hx => ?_⟩
  · have e1 : (h * ℓ * h⁻¹) (h v) = h (ℓ v) := by
      simp [LinearEquiv.mul_apply]
    have := hiso (h v)
    rw [e1, hh, hh] at this
    exact this
  · have e : h * (ℓ * ℓ) * h⁻¹ = 1 := by
      rw [← hsq]; group
    calc ℓ * ℓ = h⁻¹ * (h * (ℓ * ℓ) * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group
  · exact (finrank_commSpace_conj h ℓ).symm.trans hdim
  · have hx' : h x ∈ commSpace (h * ℓ * h⁻¹) := by
      rw [commSpace_conj]
      exact Submodule.mem_map_of_mem hx
    have := hsing _ hx'
    rwa [hh] at this

structure Hyp (b : Vm) (L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)) (D : Submodule (ZMod 2) Vm) :
    Prop where
  b0 : b ≠ 0
  bq : q0 b = 0
  LH : L ≤ Hm
  Lc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a
  Ls : ∀ a ∈ L, a * a = 1
  L8 : 8 ≤ Nat.card L
  Lb : ∀ ℓ ∈ L, ℓ b = b
  Ln : ∀ m ∈ Hm, m b = b → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L
  bD : b ∈ D
  LD : ∀ ℓ ∈ L, ∀ v, polar q0 b v = 0 → ℓ v - v ∈ D
  card : Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) = 2 ^ 8
  faith : finrank (ZMod 2) D = 4 → ∀ ℓ ∈ L, (∀ v ∈ D, ℓ v = v) → ℓ = 1

@[expose] def conjSub (h : Vm ≃ₗ[ZMod 2] Vm) (L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)) :
    Subgroup (Vm ≃ₗ[ZMod 2] Vm) :=
  L.map (MulAut.conj h).toMonoidHom

theorem mem_conjSub {h x : Vm ≃ₗ[ZMod 2] Vm} {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)} :
    x ∈ conjSub h L ↔ h⁻¹ * x * h ∈ L := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem card_conjSub (h : Vm ≃ₗ[ZMod 2] Vm) (L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)) :
    Nat.card (conjSub h L) = Nat.card L :=
  Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem polar_comp {h : Vm ≃ₗ[ZMod 2] Vm} (hh : ∀ v, q0 (h v) = q0 v) (x y : Vm) :
    polar q0 (h x) (h y) = polar q0 x y := by
  unfold polar
  rw [← map_add, hh, hh, hh]

theorem apply_inv_apply' (h : Vm ≃ₗ[ZMod 2] Vm) (v : Vm) : h (h⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

theorem inv_apply_apply' (h : Vm ≃ₗ[ZMod 2] Vm) (v : Vm) : h⁻¹ (h v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem mul_apply_conj (h x : Vm ≃ₗ[ZMod 2] Vm) (v : Vm) :
    h ((h⁻¹ * x * h) v) = x (h v) := by
  simp only [LinearEquiv.mul_apply, apply_inv_apply']

theorem Hyp.conj {b : Vm} {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)} {D : Submodule (ZMod 2) Vm}
    (H : Hyp b L D) {h : Vm ≃ₗ[ZMod 2] Vm} (hh : h ∈ Hm) :
    Hyp (h b) (conjSub h L) (D.map (h : Vm →ₗ[ZMod 2] Vm)) := by
  have hq : ∀ v, q0 (h v) = q0 v := (mem_Hm_iff.mp hh).1
  have hHm : ∀ x, h⁻¹ * x * h ∈ Hm → x ∈ Hm := fun x hx => by
    have := Hm.mul_mem (Hm.mul_mem hh hx) (Hm.inv_mem hh)
    simpa [mul_assoc] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply H.b0
    exact h.injective (by rw [h0, map_zero])
  · rw [hq]; exact H.bq
  · intro x hx
    exact hHm x (H.LH (mem_conjSub.mp hx))
  · intro x hx x' hx'
    have a1 := mem_conjSub.mp hx
    have a2 := mem_conjSub.mp hx'
    have := H.Lc _ a1 _ a2
    calc x * x' = h * ((h⁻¹ * x * h) * (h⁻¹ * x' * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x' * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
      _ = x' * x := by group
  · intro x hx
    have a1 := mem_conjSub.mp hx
    have := H.Ls _ a1
    calc x * x = h * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [card_conjSub]; exact H.L8
  · intro x hx
    have a1 := H.Lb _ (mem_conjSub.mp hx)
    have : x (h b) = h ((h⁻¹ * x * h) b) := (mul_apply_conj h x b).symm
    rw [this, a1]
  · intro m hm hmb x hx
    rw [mem_conjSub]
    have hm0 : h⁻¹ * m * h ∈ Hm := Hm.mul_mem (Hm.mul_mem (Hm.inv_mem hh) hm) hh
    have hm0b : (h⁻¹ * m * h) b = b := by
      have : (h⁻¹ * m * h) b = h⁻¹ (m (h b)) := by simp [LinearEquiv.mul_apply]
      rw [this, hmb]; simp
    have := H.Ln _ hm0 hm0b _ (mem_conjSub.mp hx)
    convert this using 1
    group
  · exact Submodule.mem_map_of_mem H.bD
  · intro x hx v hv
    have a1 := mem_conjSub.mp hx
    have hu : polar q0 b (h⁻¹ v) = 0 := by
      rw [← polar_comp hq, apply_inv_apply']
      exact hv
    have hD := H.LD _ a1 _ hu
    refine ⟨(h⁻¹ * x * h) (h⁻¹ v) - h⁻¹ v, hD, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub]
    rw [mul_apply_conj, apply_inv_apply']
  · rw [LinearEquiv.finrank_map_eq, card_conjSub]
    exact H.card
  · intro h4 x hx hfix
    rw [LinearEquiv.finrank_map_eq] at h4
    have a1 := mem_conjSub.mp hx
    have := H.faith h4 _ a1 (fun u hu => by
      have e := hfix (h u) (Submodule.mem_map_of_mem hu)
      have : h ((h⁻¹ * x * h) u) = h u := by rw [mul_apply_conj]; exact e
      exact h.injective this)
    calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem coset_mem {G : Type*} [Group G] (C : Finset G) (hC16 : C.card ≤ 16) (L : Subgroup G)
    (hL8 : 8 ≤ Nat.card L) (hLC : ∀ x ∈ L, x ∈ C) (hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hsq : ∀ x ∈ C, x * x = 1)
    {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) (hcL : c ∉ L) (hc'L : c' ∉ L) : c' * c ∈ L := by
  classical
  set LF : Finset G := C.filter (· ∈ L) with hLF
  have hLFsub : LF ⊆ C := Finset.filter_subset _ _
  have hLFcard : LF.card = Nat.card L := by
    have h1 : (L : Set G) = ↑LF := by
      ext x
      simp only [SetLike.mem_coe, hLF, Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun hx => ⟨hLC x hx, hx⟩, fun hx => hx.2⟩
    rw [← Set.ncard_coe_finset, ← h1]
    rfl
  set img : Finset G := LF.image (c * ·) with himg
  have himgcard : img.card = LF.card :=
    Finset.card_image_of_injective _ (mul_right_injective c)
  have hsub : img ⊆ C \ LF := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzC : z ∈ C := hLFsub hz
    have hzL : z ∈ L := (Finset.mem_filter.mp hz).2
    refine Finset.mem_sdiff.mpr ⟨hmul c hc z hzC, fun hcz => hcL ?_⟩
    have hczL : c * z ∈ L := (Finset.mem_filter.mp hcz).2
    simpa using L.mul_mem hczL (L.inv_mem hzL)
  have hsdcard : (C \ LF).card = C.card - LF.card := Finset.card_sdiff_of_subset hLFsub
  have hle : LF.card ≤ (C \ LF).card := by rw [← himgcard]; exact Finset.card_le_card hsub
  have hLF8 : 8 ≤ LF.card := by rw [hLFcard]; exact hL8
  have hLF8' : LF.card = 8 := by omega
  have heq : img = C \ LF :=
    Finset.eq_of_subset_of_card_le hsub (by rw [himgcard]; omega)
  have hc'mem : c' ∈ C \ LF :=
    Finset.mem_sdiff.mpr ⟨hc', fun h => hc'L (Finset.mem_filter.mp h).2⟩
  rw [← heq] at hc'mem
  obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp hc'mem
  have hzC : z ∈ C := hLFsub hz
  have hzL : z ∈ L := (Finset.mem_filter.mp hz).2
  have : c' * c = z := by
    rw [← hzc, mul_assoc, ← hcomm c hc z hzC, ← mul_assoc, hsq c hc, one_mul]
  rw [this]
  exact hzL

theorem dim_contradiction {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)} {D : Submodule (ZMod 2) Vm}
    (hL8 : 8 ≤ Nat.card L) (hcard : Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) = 2 ^ 8)
    (hfaith : finrank (ZMod 2) D = 4 → ∀ ℓ ∈ L, (∀ v ∈ D, ℓ v = v) → ℓ = 1)
    (w : Fin 4 → Vm) (hw : LinearIndependent (ZMod 2) w) (hwD : ∀ i, w i ∈ D)
    {k : Vm ≃ₗ[ZMod 2] Vm} (hkL : k ∈ L) (hk1 : k ≠ 1) (hkfix : ∀ i, k (w i) = w i) : False := by
  have h4 : 4 ≤ finrank (ZMod 2) D := by
    have hind : LinearIndependent (ZMod 2) (fun i => (⟨w i, hwD i⟩ : D)) :=
      LinearIndependent.of_comp D.subtype hw
    simpa using hind.fintype_card_le_finrank
  have hd : finrank (ZMod 2) D = 4 := by
    by_contra hne
    have h5 : 6 ≤ finrank (ZMod 2) D + 1 := by omega
    have h6 : 2 ^ 6 ≤ 2 ^ (finrank (ZMod 2) D + 1) := Nat.pow_le_pow_right (by norm_num) h5
    have h7 : 8 * 2 ^ 6 ≤ Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) := Nat.mul_le_mul hL8 h6
    rw [hcard] at h7
    norm_num at h7
  have hspan : Submodule.span (ZMod 2) (Set.range w) = D := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact hwD i
    · rw [finrank_span_eq_card hw, hd]
      simp
  have hfix : ∀ v ∈ D, k v = v := by
    intro v hv
    rw [← hspan] at hv
    have hle : Submodule.span (ZMod 2) (Set.range w) ≤
        LinearMap.ker ((k : Vm →ₗ[ZMod 2] Vm) - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hkfix]
    have := hle hv
    simpa [sub_eq_zero] using this
  exact hk1 (hfaith hd k hkL hfix)

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
