module

public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Transvection

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic
open scoped IsMulCommutative

variable {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def weakZClosure (E : Subgroup G) (S : Set (Subgroup G)) (a : G) : Subgroup G :=
  Subgroup.closure (wzSet {K | K ∈ S ∧ a ∈ axisSub E K})

private theorem zmod2_cases' (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

section Frame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem weakPairingAdj_iff [Finite G] (Fr : WeakPreFrame F Ω E S) {K L : Subgroup G}
    (hL : L ∈ S) {z : G} (hz : IsCentralInvolution L z) :
    WeakPairingAdj E K L ↔ z ∉ axisSub E K := by
  constructor
  · rintro ⟨z', hz', h⟩
    rwa [Fr.eq_of_central hL hz hz']
  · exact fun h => ⟨z, hz, h⟩

theorem weak_isMulCommutative (Fr : WeakPreFrame F Ω E S) : IsMulCommutative ↥E :=
  ⟨⟨fun x y => Subtype.ext (Fr.comm x.2 y.2)⟩⟩

theorem axisChar_mul_of_weak (Fr : WeakPreFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    axisChar E K (x * y) = axisChar E K x + axisChar E K y := by
  have hKs := Fr.weakInSigma hK
  by_cases h1 : x ∈ axisSub E K <;> by_cases h2 : y ∈ axisSub E K
  · have h3 : x * y ∈ axisSub E K := (axisSub E K).mul_mem h1 h2
    rw [axisChar_of_mem h3, axisChar_of_mem h1, axisChar_of_mem h2]
    rfl
  · have h3 : x * y ∉ axisSub E K := fun h => h2 (by
      have := (axisSub E K).mul_mem ((axisSub E K).inv_mem h1) h
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_mem h1, axisChar_of_not_mem h2]
    simp
  · have h3 : x * y ∉ axisSub E K := fun h => h1 (by
      have := (axisSub E K).mul_mem h ((axisSub E K).inv_mem h2)
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_not_mem h1, axisChar_of_mem h2]
    simp
  · have h3 : x * y ∈ axisSub E K := hKs.mul_mem_axis Fr.elem hx hy h1 h2
    rw [axisChar_of_mem h3, axisChar_of_not_mem h1, axisChar_of_not_mem h2]
    decide

theorem axisChar_conjSub_weak [Finite G] (Fr : WeakPreFrame F Ω E S) {K L : Subgroup G}
    (hK : K ∈ S) (hL : L ∈ S) {zK : G} (hzK : IsCentralInvolution K zK) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) {e : G} (he : e ∈ E) :
    axisChar E (conjSub w L) e = axisChar E L e + axisChar E L zK * axisChar E K e := by
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  have hzKE : zK ∈ E := Fr.mem_of_central hK hzK
  have hKs := Fr.weakInSigma hK
  have key : e ∈ axisSub E (conjSub w L) ↔ w⁻¹ * e * w ∈ axisSub E L := by
    rw [axisSub_conjSub hwN L, mem_conjSub_iff]
  have h1 : axisChar E (conjSub w L) e = axisChar E L (w⁻¹ * e * w) := by
    by_cases h : w⁻¹ * e * w ∈ axisSub E L
    · rw [axisChar_of_mem h, axisChar_of_mem (key.mpr h)]
    · rw [axisChar_of_not_mem h, axisChar_of_not_mem (fun h' => h (key.mp h'))]
  rw [h1]
  by_cases he' : e ∈ axisSub E K
  · have h2 : w⁻¹ * e * w = e := by
      have := InSigma.conj_eq_of_mem_axis (K.inv_mem (normPart_le_left K E hw)) he'
      simpa using this
    rw [h2, axisChar_of_mem he', mul_zero, add_zero]
  · have h2 : w⁻¹ * e * w = e * zK := by
      rw [hKs.conj_inv_eq Fr.elem Fr.odd hzK hw hw' he]
      exact hKs.conj_eq_mul_of_not_mem_axis Fr.elem Fr.odd hzK hw hw' he he'
    rw [h2, axisChar_mul_of_weak Fr hL he hzKE, axisChar_of_not_mem he', mul_one]

section Construction

variable (Fr : WeakToralFrame F Ω E S)

private noncomputable def weakZg (K : ↥S) : G :=
  Classical.choose (Fr.exists_central K.2)

private theorem isCentral_weakZg (K : ↥S) : IsCentralInvolution (K : Subgroup G) (weakZg Fr K) :=
  (Classical.choose_spec (Fr.exists_central K.2)).1

private theorem weakZg_mem (K : ↥S) : weakZg Fr K ∈ E :=
  (Classical.choose_spec (Fr.exists_central K.2)).2

private noncomputable def weakZ (K : ↥S) : Additive ↥E :=
  Additive.ofMul ⟨weakZg Fr K, weakZg_mem Fr K⟩

private noncomputable def weakChi [IsMulCommutative ↥E] [Module (ZMod 2) (Additive ↥E)]
    (K : ↥S) : Module.Dual (ZMod 2) (Additive ↥E) where
  toFun x := axisChar E K ((Additive.toMul x : ↥E) : G)
  map_add' x y :=
    axisChar_mul_of_weak Fr.toWeakPreFrame K.2 (Additive.toMul x).2 (Additive.toMul y).2
  map_smul' c x := by
    rcases zmod2_cases' c with rfl | rfl
    · rw [zero_smul]
      change axisChar E K ((1 : ↥E) : G) = _
      rw [Subgroup.coe_one, axisChar_of_mem (axisSub E K).one_mem]
      simp
    · rw [one_smul]
      simp

variable [IsMulCommutative ↥E] [Module (ZMod 2) (Additive ↥E)]

private theorem weakChi_apply (K : ↥S) (e : ↥E) :
    weakChi Fr K (Additive.ofMul e) = axisChar E K (e : G) := rfl

private theorem weakChi_weakZ (K L : ↥S) :
    weakChi Fr K (weakZ Fr L) = axisChar E K (weakZg Fr L) := rfl

private theorem weak_symm [Finite G] (K L : ↥S) :
    weakChi Fr K (weakZ Fr L) = weakChi Fr L (weakZ Fr K) := by
  rw [weakChi_weakZ, weakChi_weakZ]
  by_cases h : weakZg Fr L ∈ axisSub E K
  · rw [axisChar_of_mem h]
    symm
    rw [axisChar_eq_zero_iff]
    by_contra h'
    have h1 : WeakPairingAdj E L K :=
      (weakPairingAdj_iff Fr.toWeakPreFrame K.2 (isCentral_weakZg Fr K)).mpr h'
    have h2 := Fr.sym L L.2 K K.2 h1
    exact ((weakPairingAdj_iff Fr.toWeakPreFrame L.2 (isCentral_weakZg Fr L)).mp h2) h
  · have h1 : WeakPairingAdj E K L :=
      (weakPairingAdj_iff Fr.toWeakPreFrame L.2 (isCentral_weakZg Fr L)).mpr h
    have h2 := Fr.sym K K.2 L L.2 h1
    have h3 := (weakPairingAdj_iff Fr.toWeakPreFrame K.2 (isCentral_weakZg Fr K)).mp h2
    rw [axisChar_of_not_mem h, axisChar_of_not_mem h3]

private theorem weak_conn [Finite G] (K L : ↥S) :
    Relation.ReflTransGen (fun K' L' : ↥S => weakChi Fr K' (weakZ Fr L') = 1) K L := by
  refine Relation.ReflTransGen.mono (fun K' L' h => ?_) K L (Fr.conn K L)
  rw [weakChi_weakZ]
  exact axisChar_of_not_mem
    ((weakPairingAdj_iff Fr.toWeakPreFrame L'.2 (isCentral_weakZg Fr L')).mp h)

private theorem weak_closed [Finite G] (K L : ↥S) :
    ∃ M : ↥S, weakZ Fr M = weakZ Fr L + weakChi Fr K (weakZ Fr L) • weakZ Fr K ∧
      weakChi Fr M = weakChi Fr L + weakChi Fr L (weakZ Fr K) • weakChi Fr K := by
  obtain ⟨w, hw, hw'⟩ := (Fr.weakInSigma K.2).exists_mem_normPart_not_mem_centPart Fr.elem
    Fr.odd Fr.five
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  obtain ⟨M, hM⟩ : ∃ M : ↥S, (M : Subgroup G) = conjSub w L :=
    ⟨⟨conjSub w L, Fr.conj_mem hwN L.2⟩, rfl⟩
  have hzM : weakZg Fr M = w * weakZg Fr L * w⁻¹ := by
    have h := (isCentral_weakZg Fr L).conj w
    rw [← hM] at h
    exact Fr.eq_of_central M.2 (isCentral_weakZg Fr M) h
  refine ⟨M, ?_, ?_⟩
  · by_cases h : weakZg Fr L ∈ axisSub E K
    · have h1 : weakZg Fr M = weakZg Fr L := by
        rw [hzM]
        exact InSigma.conj_eq_of_mem_axis (E := E) (K := (K : Subgroup G))
          (normPart_le_left (K : Subgroup G) E hw) h
      rw [weakChi_weakZ, axisChar_of_mem h, zero_smul, add_zero]
      exact congrArg Additive.ofMul (Subtype.ext h1)
    · have h1 : weakZg Fr M = weakZg Fr L * weakZg Fr K := by
        rw [hzM]
        exact (Fr.weakInSigma K.2).conj_eq_mul_of_not_mem_axis Fr.elem Fr.odd
          (isCentral_weakZg Fr K) hw hw' (weakZg_mem Fr L) h
      rw [weakChi_weakZ, axisChar_of_not_mem h, one_smul]
      exact congrArg Additive.ofMul (Subtype.ext h1)
  · refine LinearMap.ext fun x => ?_
    obtain ⟨e, rfl⟩ := Additive.ofMul.surjective x
    rw [LinearMap.add_apply, LinearMap.smul_apply, weakChi_apply, weakChi_apply,
      weakChi_apply, weakChi_weakZ, smul_eq_mul, hM]
    exact axisChar_conjSub_weak Fr.toWeakPreFrame K.2 L.2 (isCentral_weakZg Fr K) hw hw' e.2

private theorem weak_span [Finite G] :
    Submodule.span (ZMod 2) (Set.range (weakZ Fr)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨e, rfl⟩ := Additive.ofMul.surjective v
  have he : (e : G) ∈ Subgroup.closure (wzSet S) := by
    rw [Fr.gen]
    exact e.2
  have key : ∀ x ∈ Subgroup.closure (wzSet S), ∃ hxE : x ∈ E,
      Additive.ofMul (⟨x, hxE⟩ : ↥E) ∈ Submodule.span (ZMod 2) (Set.range (weakZ Fr)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨K, hK, hKx⟩ := hx
      have hxE : x ∈ E := Fr.mem_of_central hK hKx
      refine ⟨hxE, Submodule.subset_span ⟨⟨K, hK⟩, ?_⟩⟩
      exact congrArg Additive.ofMul
        (Subtype.ext (Fr.eq_of_central hK (isCentral_weakZg Fr ⟨K, hK⟩) hKx))
    | one => exact ⟨E.one_mem, Submodule.zero_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxE, hx'⟩ := hx
      obtain ⟨hyE, hy'⟩ := hy
      exact ⟨E.mul_mem hxE hyE, Submodule.add_mem _ hx' hy'⟩
    | inv x _ hx =>
      obtain ⟨hxE, hx'⟩ := hx
      have h : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Fr.elem x hxE)
      have h' : (⟨x⁻¹, E.inv_mem hxE⟩ : ↥E) = ⟨x, hxE⟩ := Subtype.ext h
      exact ⟨E.inv_mem hxE, by rw [h']; exact hx'⟩
  obtain ⟨_, h⟩ := key (e : G) he
  exact h

private noncomputable def weakRootFamily [Finite G] : RootFamily ↥S (Additive ↥E) where
  z := weakZ Fr
  χ := weakChi Fr
  symm := weak_symm Fr
  closed := weak_closed Fr
  conn := weak_conn Fr
  span_eq := weak_span Fr

private theorem weak_R_le [Finite G] {a : G} (ha : a ∈ E) {v : Additive ↥E}
    (hv : v ∈ (weakRootFamily Fr).R (Additive.ofMul (⟨a, ha⟩ : ↥E))) :
    ((Additive.toMul v : ↥E) : G) ∈ weakZClosure E S a := by
  refine Submodule.span_induction
    (p := fun v _ => ((Additive.toMul v : ↥E) : G) ∈ weakZClosure E S a) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨K, hK, rfl⟩
    have h0 : axisChar E K a = 0 := hK
    have haK : a ∈ axisSub E K := axisChar_eq_zero_iff.mp h0
    exact Subgroup.subset_closure ⟨K, ⟨K.2, haK⟩, isCentral_weakZg Fr K⟩
  · exact (weakZClosure E S a).one_mem
  · intro x y _ _ hx hy
    exact (weakZClosure E S a).mul_mem hx hy
  · intro c x _ hx
    rcases zmod2_cases' c with rfl | rfl
    · rw [zero_smul]
      exact (weakZClosure E S a).one_mem
    · rw [one_smul]
      exact hx

end Construction

theorem mem_or_mem_or_mul_mem_weakZClosure [Finite G] (Fr : WeakToralFrame F Ω E S)
    {a x y : G} (ha : a ∈ E) (hx : x ∈ E) (hy : y ∈ E) :
    x ∈ weakZClosure E S a ∨ y ∈ weakZClosure E S a ∨ x * y ∈ weakZClosure E S a := by
  have := Fr.finite
  have := weak_isMulCommutative Fr.toWeakPreFrame
  let _ : Module (ZMod 2) (Additive ↥E) := AddCommGroup.zmodModule (fun v => by
    obtain ⟨e, rfl⟩ := Additive.ofMul.surjective v
    rw [← ofMul_pow]
    have h : e ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using Fr.elem e e.2)
    rw [h]
    rfl)
  have h := (weakRootFamily Fr).mem_or_mem_or_add_mem
    (Additive.ofMul (⟨a, ha⟩ : ↥E)) (Additive.ofMul (⟨x, hx⟩ : ↥E)) (Additive.ofMul (⟨y, hy⟩ : ↥E))
  rcases h with h | h | h
  · exact Or.inl (weak_R_le Fr ha h)
  · exact Or.inr (Or.inl (weak_R_le Fr ha h))
  · exact Or.inr (Or.inr (weak_R_le Fr ha h))

theorem weakZClosure_le [Finite G] (Fr : WeakToralFrame F Ω E S) (a : G) :
    weakZClosure E S a ≤ E := by
  refine (Subgroup.closure_le E).mpr ?_
  rintro z ⟨K, ⟨hK, -⟩, hz⟩
  exact Fr.mem_of_central hK hz

theorem relIndex_weakZClosure_le_two [Finite G] (Fr : WeakToralFrame F Ω E S) {a : G}
    (ha : a ∈ E) : (weakZClosure E S a).relIndex E ≤ 2 := by
  by_cases hall : ∀ x ∈ E, x ∈ weakZClosure E S a
  · rw [Subgroup.relIndex_eq_one.mpr hall]
    norm_num
  · push Not at hall
    obtain ⟨x₀, hx₀, hx₀H⟩ := hall
    have h2 : (weakZClosure E S a).relIndex E = 2 := by
      rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
      refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
      have hb : (b : G) ∈ E := b.2
      by_cases hbH : (b : G) ∈ weakZClosure E S a
      · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr hbH, fun h => hx₀H ?_⟩
        have h' : (b : G) * x₀ ∈ weakZClosure E S a := Subgroup.mem_subgroupOf.mp h
        have := (weakZClosure E S a).mul_mem ((weakZClosure E S a).inv_mem hbH) h'
        simpa using this
      · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr ?_,
          fun h => hbH (Subgroup.mem_subgroupOf.mp h)⟩
        rcases mem_or_mem_or_mul_mem_weakZClosure Fr ha hb hx₀ with h | h | h
        · exact absurd h hbH
        · exact absurd h hx₀H
        · exact h
    rw [h2]

end Frame

end CFSG.ClassicalInvolution.Balance
