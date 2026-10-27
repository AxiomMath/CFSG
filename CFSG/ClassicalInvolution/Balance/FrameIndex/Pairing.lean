module

public import CFSG.ClassicalInvolution.Balance.FrameIndex.RootFamily
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic
open scoped IsMulCommutative

variable {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def PairingAdj (E K L : Subgroup G) : Prop :=
  ∃ z, IsUniqueInvolution L z ∧ z ∉ axisSub E K

@[expose] def zClosure (E : Subgroup G) (S : Set (Subgroup G)) (a : G) : Subgroup G :=
  Subgroup.closure (zSet {K | K ∈ S ∧ a ∈ axisSub E K})

@[expose] def PairingSymmetric (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K ∈ S, ∀ L ∈ S, PairingAdj E K L → PairingAdj E L K

@[expose] def PairingConnected (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K L : ↥S, Relation.ReflTransGen (fun K' L' : ↥S => PairingAdj E K' L') K L

open scoped Classical in
@[expose] noncomputable def axisChar (E K : Subgroup G) (e : G) : ZMod 2 :=
  if e ∈ axisSub E K then 0 else 1

theorem axisChar_of_mem {E K : Subgroup G} {e : G} (h : e ∈ axisSub E K) : axisChar E K e = 0 := by
  simp [axisChar, h]

theorem axisChar_of_not_mem {E K : Subgroup G} {e : G} (h : e ∉ axisSub E K) :
    axisChar E K e = 1 := by
  simp [axisChar, h]

theorem axisChar_eq_zero_iff {E K : Subgroup G} {e : G} : axisChar E K e = 0 ↔ e ∈ axisSub E K := by
  by_cases h : e ∈ axisSub E K
  · simp [axisChar_of_mem h, h]
  · rw [axisChar_of_not_mem h]
    simp [h]

theorem axisChar_cases (E K : Subgroup G) (e : G) : axisChar E K e = 0 ∨ axisChar E K e = 1 := by
  by_cases h : e ∈ axisSub E K
  · exact Or.inl (axisChar_of_mem h)
  · exact Or.inr (axisChar_of_not_mem h)

private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem pairingAdj_iff {E K L : Subgroup G} {z : G} (hz : IsUniqueInvolution L z) :
    PairingAdj E K L ↔ z ∉ axisSub E K := by
  constructor
  · rintro ⟨z', hz', h⟩
    rwa [hz.eq hz']
  · exact fun h => ⟨z, hz, h⟩

section Frame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem frame_comm (Fr : ToralFrame F Ω E S) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h1 := Fr.elem (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Fr.elem x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (Fr.elem y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

theorem frame_isMulCommutative (Fr : ToralFrame F Ω E S) : IsMulCommutative ↥E :=
  ⟨⟨fun x y => Subtype.ext (frame_comm Fr x.2 y.2)⟩⟩

theorem axisChar_mul_of_frame (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) :
    axisChar E K (x * y) = axisChar E K x + axisChar E K y := by
  obtain ⟨a, haE, haN, hsplit⟩ := (Fr.inSigma hK).exists_split
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
  · have hxa : x * a ∈ axisSub E K := (hsplit x hx).resolve_left h1
    have hya : y * a ∈ axisSub E K := (hsplit y hy).resolve_left h2
    have h3 : x * y ∈ axisSub E K := by
      have h4 := (axisSub E K).mul_mem hxa hya
      have e1 : x * a * (y * a) = x * y := by
        calc x * a * (y * a) = x * (a * y) * a := by group
          _ = x * (y * a) * a := by rw [frame_comm Fr haE hy]
          _ = x * y * (a * a) := by group
          _ = x * y := by rw [Fr.elem a haE, mul_one]
      rwa [e1] at h4
    rw [axisChar_of_mem h3, axisChar_of_not_mem h1, axisChar_of_not_mem h2]
    decide


theorem frame_conj_inv_of_not_mem_axis (Fr : ToralFrame F Ω E S) {K : Subgroup G}
    (hK : K ∈ S) {zK : G} (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K E)
    (hw' : w ∉ centPart K E) {e : G} (he : e ∈ E) (hn : e ∉ axisSub E K) :
    w⁻¹ * e * w = e * zK := by
  have := Fr.finite
  have h1 : w * e * w⁻¹ = e * zK :=
    (Fr.inSigma hK).conj_eq_mul_of_not_mem_axis Fr.odd hzK hw hw' he hn
  have h2 : w * w = zK := (Fr.inSigma hK).sq_eq_of_mem Fr.odd hzK hw hw'
  have h4 : w⁻¹ * zK * w = zK := by
    rw [← h2]
    group
  have h5 : w⁻¹ * (e * zK) * w = e := by
    rw [← h1]
    group
  have h6 : w⁻¹ * (e * zK) * w = (w⁻¹ * e * w) * (w⁻¹ * zK * w) := by group
  rw [h6, h4] at h5
  calc w⁻¹ * e * w = (w⁻¹ * e * w) * (zK * zK) := by rw [hzK.sq, mul_one]
    _ = ((w⁻¹ * e * w) * zK) * zK := (mul_assoc _ _ _).symm
    _ = e * zK := by rw [h5]

theorem axisChar_conjSub (Fr : ToralFrame F Ω E S) {K L : Subgroup G} (hK : K ∈ S)
    (hL : L ∈ S) {zK : G} (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K E)
    (hw' : w ∉ centPart K E) {e : G} (he : e ∈ E) :
    axisChar E (conjSub w L) e = axisChar E L e + axisChar E L zK * axisChar E K e := by
  have := Fr.finite
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  have hzKE : zK ∈ E := Fr.mem_of_isUniqueInvolution hK hzK
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
  · rw [frame_conj_inv_of_not_mem_axis Fr hK hzK hw hw' he he',
      axisChar_mul_of_frame Fr hL he hzKE, axisChar_of_not_mem he', mul_one]


section Construction

variable (Fr : ToralFrame F Ω E S)

private noncomputable def frameZg (K : ↥S) : G :=
  Classical.choose (Fr.exists_isUniqueInvolution K.2)

private theorem isUniqueInvolution_frameZg (K : ↥S) :
    IsUniqueInvolution (K : Subgroup G) (frameZg Fr K) :=
  Classical.choose_spec (Fr.exists_isUniqueInvolution K.2)

private theorem frameZg_mem (K : ↥S) : frameZg Fr K ∈ E :=
  Fr.mem_of_isUniqueInvolution K.2 (isUniqueInvolution_frameZg Fr K)

private noncomputable def frameZ (K : ↥S) : Additive ↥E :=
  Additive.ofMul ⟨frameZg Fr K, frameZg_mem Fr K⟩

private noncomputable def frameChi [IsMulCommutative ↥E] [Module (ZMod 2) (Additive ↥E)]
    (K : ↥S) : Module.Dual (ZMod 2) (Additive ↥E) where
  toFun x := axisChar E K ((Additive.toMul x : ↥E) : G)
  map_add' x y := axisChar_mul_of_frame Fr K.2 (Additive.toMul x).2 (Additive.toMul y).2
  map_smul' c x := by
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      change axisChar E K ((1 : ↥E) : G) = _
      rw [Subgroup.coe_one, axisChar_of_mem (axisSub E K).one_mem]
      simp
    · rw [one_smul]
      simp

variable [IsMulCommutative ↥E] [Module (ZMod 2) (Additive ↥E)]

private theorem frameChi_apply (K : ↥S) (e : ↥E) :
    frameChi Fr K (Additive.ofMul e) = axisChar E K (e : G) := rfl

private theorem frameChi_frameZ (K L : ↥S) :
    frameChi Fr K (frameZ Fr L) = axisChar E K (frameZg Fr L) := rfl

private theorem frame_symm (hsym : PairingSymmetric E S) (K L : ↥S) :
    frameChi Fr K (frameZ Fr L) = frameChi Fr L (frameZ Fr K) := by
  rw [frameChi_frameZ, frameChi_frameZ]
  by_cases h : frameZg Fr L ∈ axisSub E K
  · rw [axisChar_of_mem h]
    symm
    rw [axisChar_eq_zero_iff]
    by_contra h'
    have h1 : PairingAdj E L K := (pairingAdj_iff (isUniqueInvolution_frameZg Fr K)).mpr h'
    have h2 := hsym L L.2 K K.2 h1
    exact ((pairingAdj_iff (isUniqueInvolution_frameZg Fr L)).mp h2) h
  · have h1 : PairingAdj E K L := (pairingAdj_iff (isUniqueInvolution_frameZg Fr L)).mpr h
    have h2 := hsym K K.2 L L.2 h1
    have h3 := (pairingAdj_iff (isUniqueInvolution_frameZg Fr K)).mp h2
    rw [axisChar_of_not_mem h, axisChar_of_not_mem h3]

private theorem frame_conn (hconn : PairingConnected E S) (K L : ↥S) :
    Relation.ReflTransGen (fun K' L' : ↥S => frameChi Fr K' (frameZ Fr L') = 1) K L := by
  refine Relation.ReflTransGen.mono (fun K' L' h => ?_) K L (hconn K L)
  rw [frameChi_frameZ]
  exact axisChar_of_not_mem ((pairingAdj_iff (isUniqueInvolution_frameZg Fr L')).mp h)

private theorem frame_closed [Finite F] (K L : ↥S) :
    ∃ M : ↥S, frameZ Fr M = frameZ Fr L + frameChi Fr K (frameZ Fr L) • frameZ Fr K ∧
      frameChi Fr M = frameChi Fr L + frameChi Fr L (frameZ Fr K) • frameChi Fr K := by
  obtain ⟨w, hw, hw'⟩ := (Fr.inSigma K.2).exists_mem_normPart_not_mem_centPart Fr.odd Fr.five
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  obtain ⟨M, hM⟩ : ∃ M : ↥S, (M : Subgroup G) = conjSub w L :=
    ⟨⟨conjSub w L, Fr.conj_mem hwN L.2⟩, rfl⟩
  have hzM : frameZg Fr M = w * frameZg Fr L * w⁻¹ := by
    have h := (isUniqueInvolution_frameZg Fr L).conj w
    rw [← hM] at h
    exact (isUniqueInvolution_frameZg Fr M).eq h
  refine ⟨M, ?_, ?_⟩
  · by_cases h : frameZg Fr L ∈ axisSub E K
    · have h1 : frameZg Fr M = frameZg Fr L := by
        rw [hzM]
        exact InSigma.conj_eq_of_mem_axis (E := E) (K := (K : Subgroup G))
          (normPart_le_left (K : Subgroup G) E hw) h
      rw [frameChi_frameZ, axisChar_of_mem h, zero_smul, add_zero]
      exact congrArg Additive.ofMul (Subtype.ext h1)
    · have h1 : frameZg Fr M = frameZg Fr L * frameZg Fr K := by
        rw [hzM]
        exact (Fr.inSigma K.2).conj_eq_mul_of_not_mem_axis Fr.odd
          (isUniqueInvolution_frameZg Fr K) hw hw' (frameZg_mem Fr L) h
      rw [frameChi_frameZ, axisChar_of_not_mem h, one_smul]
      exact congrArg Additive.ofMul (Subtype.ext h1)
  · refine LinearMap.ext fun x => ?_
    obtain ⟨e, rfl⟩ := Additive.ofMul.surjective x
    rw [LinearMap.add_apply, LinearMap.smul_apply, frameChi_apply, frameChi_apply,
      frameChi_apply, frameChi_frameZ, smul_eq_mul, hM]
    exact axisChar_conjSub Fr K.2 L.2 (isUniqueInvolution_frameZg Fr K) hw hw' e.2

private theorem frame_span :
    Submodule.span (ZMod 2) (Set.range (frameZ Fr)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨e, rfl⟩ := Additive.ofMul.surjective v
  have he : (e : G) ∈ Subgroup.closure (zSet S) := by
    rw [Fr.gen]
    exact e.2
  have key : ∀ x ∈ Subgroup.closure (zSet S), ∃ hxE : x ∈ E,
      Additive.ofMul (⟨x, hxE⟩ : ↥E) ∈ Submodule.span (ZMod 2) (Set.range (frameZ Fr)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨K, hK, hKx⟩ := hx
      have hxE : x ∈ E := Fr.mem_of_isUniqueInvolution hK hKx
      refine ⟨hxE, Submodule.subset_span ⟨⟨K, hK⟩, ?_⟩⟩
      exact congrArg Additive.ofMul (Subtype.ext ((isUniqueInvolution_frameZg Fr ⟨K, hK⟩).eq hKx))
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

private noncomputable def frameRootFamily [Finite F] (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) : RootFamily ↥S (Additive ↥E) where
  z := frameZ Fr
  χ := frameChi Fr
  symm := frame_symm Fr hsym
  closed := frame_closed Fr
  conn := frame_conn Fr hconn
  span_eq := frame_span Fr

private theorem frame_R_le [Finite F] (hsym : PairingSymmetric E S) (hconn : PairingConnected E S)
    {a : G} (ha : a ∈ E) {v : Additive ↥E}
    (hv : v ∈ (frameRootFamily Fr hsym hconn).R (Additive.ofMul (⟨a, ha⟩ : ↥E))) :
    ((Additive.toMul v : ↥E) : G) ∈ zClosure E S a := by
  refine Submodule.span_induction (p := fun v _ => ((Additive.toMul v : ↥E) : G) ∈ zClosure E S a)
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨K, hK, rfl⟩
    have h0 : axisChar E K a = 0 := hK
    have haK : a ∈ axisSub E K := axisChar_eq_zero_iff.mp h0
    exact Subgroup.subset_closure ⟨K, ⟨K.2, haK⟩, isUniqueInvolution_frameZg Fr K⟩
  · exact (zClosure E S a).one_mem
  · intro x y _ _ hx hy
    exact (zClosure E S a).mul_mem hx hy
  · intro c x _ hx
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact (zClosure E S a).one_mem
    · rw [one_smul]
      exact hx

end Construction

theorem mem_or_mem_or_mul_mem_zClosure (Fr : ToralFrame F Ω E S) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) {a x y : G} (ha : a ∈ E) (hx : x ∈ E) (hy : y ∈ E) :
    x ∈ zClosure E S a ∨ y ∈ zClosure E S a ∨ x * y ∈ zClosure E S a := by
  have := Fr.finite
  have := frame_isMulCommutative Fr
  let _ : Module (ZMod 2) (Additive ↥E) := AddCommGroup.zmodModule (fun v => by
    obtain ⟨e, rfl⟩ := Additive.ofMul.surjective v
    rw [← ofMul_pow]
    have h : e ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using Fr.elem e e.2)
    rw [h]
    rfl)
  have h := (frameRootFamily Fr hsym hconn).mem_or_mem_or_add_mem
    (Additive.ofMul (⟨a, ha⟩ : ↥E)) (Additive.ofMul (⟨x, hx⟩ : ↥E)) (Additive.ofMul (⟨y, hy⟩ : ↥E))
  rcases h with h | h | h
  · exact Or.inl (frame_R_le Fr hsym hconn ha h)
  · exact Or.inr (Or.inl (frame_R_le Fr hsym hconn ha h))
  · exact Or.inr (Or.inr (frame_R_le Fr hsym hconn ha h))

theorem zClosure_le (Fr : ToralFrame F Ω E S) (a : G) : zClosure E S a ≤ E := by
  refine (Subgroup.closure_le E).mpr ?_
  rintro z ⟨K, ⟨hK, -⟩, hz⟩
  exact Fr.mem_of_isUniqueInvolution hK hz

theorem relIndex_zClosure_le_two (Fr : ToralFrame F Ω E S) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) {a : G} (ha : a ∈ E) : (zClosure E S a).relIndex E ≤ 2 := by
  by_cases hall : ∀ x ∈ E, x ∈ zClosure E S a
  · rw [Subgroup.relIndex_eq_one.mpr hall]
    norm_num
  · push Not at hall
    obtain ⟨x₀, hx₀, hx₀H⟩ := hall
    have h2 : (zClosure E S a).relIndex E = 2 := by
      rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
      refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
      have hb : (b : G) ∈ E := b.2
      by_cases hbH : (b : G) ∈ zClosure E S a
      · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr hbH, fun h => hx₀H ?_⟩
        have h' : (b : G) * x₀ ∈ zClosure E S a := Subgroup.mem_subgroupOf.mp h
        have := (zClosure E S a).mul_mem ((zClosure E S a).inv_mem hbH) h'
        simpa using this
      · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr ?_, fun h => hbH (Subgroup.mem_subgroupOf.mp h)⟩
        rcases mem_or_mem_or_mul_mem_zClosure Fr hsym hconn ha hb hx₀ with h | h | h
        · exact absurd h hbH
        · exact absurd h hx₀H
        · exact h
    rw [h2]

end Frame

end CFSG.ClassicalInvolution.Balance
