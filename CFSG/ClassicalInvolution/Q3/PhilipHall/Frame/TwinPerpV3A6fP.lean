module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem iSup₂_induction {Y : Type} [Group Y] {s : Set (Subgroup Y)} {motive : Y → Prop} {x : Y}
    (hx : x ∈ ⨆ J ∈ s, J) (mem : ∀ J ∈ s, ∀ x ∈ J, motive x) (one : motive 1)
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  refine Subgroup.iSup_induction (C := motive) (fun J : Subgroup Y => ⨆ _ : J ∈ s, J) hx ?_ one mul
  intro J z hz
  refine Subgroup.iSup_induction (C := motive) (fun _ : J ∈ s => J) hz ?_ one mul
  intro hJ z' hz'
  exact mem J hJ z' hz'

theorem mul4_swap {Y : Type} [Group Y] {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Y} (c21 : a₂ * b₁ = b₁ * a₂)
    (c31 : a₃ * b₁ = b₁ * a₃) (c41 : a₄ * b₁ = b₁ * a₄) (c32 : a₃ * b₂ = b₂ * a₃)
    (c42 : a₄ * b₂ = b₂ * a₄) (c43 : a₄ * b₃ = b₃ * a₄) :
    a₁ * a₂ * a₃ * a₄ * (b₁ * b₂ * b₃ * b₄) = a₁ * b₁ * (a₂ * b₂) * (a₃ * b₃) * (a₄ * b₄) := by
  have s21 : ∀ z, a₂ * (b₁ * z) = b₁ * (a₂ * z) := fun z => by rw [← mul_assoc, c21, mul_assoc]
  have s31 : ∀ z, a₃ * (b₁ * z) = b₁ * (a₃ * z) := fun z => by rw [← mul_assoc, c31, mul_assoc]
  have s41 : ∀ z, a₄ * (b₁ * z) = b₁ * (a₄ * z) := fun z => by rw [← mul_assoc, c41, mul_assoc]
  have s32 : ∀ z, a₃ * (b₂ * z) = b₂ * (a₃ * z) := fun z => by rw [← mul_assoc, c32, mul_assoc]
  have s42 : ∀ z, a₄ * (b₂ * z) = b₂ * (a₄ * z) := fun z => by rw [← mul_assoc, c42, mul_assoc]
  have s43 : ∀ z, a₄ * (b₃ * z) = b₃ * (a₄ * z) := fun z => by rw [← mul_assoc, c43, mul_assoc]
  simp only [mul_assoc]
  rw [s41, s31, s21, s42, s32, s43]

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem mem_ae6Vc_iff {J : Subgroup Y} :
    J ∈ ae6Vc Ω[R] t ↔ J = K ∨ J = K' ∨ J = K₃ ∨ J = K₄ := by
  constructor
  · intro hJ
    exact twinSet_four C.H.ex.1 C.H.ex.2.1 J ⟨hJ.1, t, C.H.ex.1.datum.hz, hJ.2⟩
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨C.H.ex.1.datum.mem, C.H.ex.1.datum.hz⟩
    · exact ⟨C.H.ex.1.datum.hK'.1, C.uniq C.hK't⟩
    · exact ⟨C.H.ex.1.datum.hK₃.1, C.uniq C.hK₃t⟩
    · exact ⟨C.H.ex.2.1.1.1, C.uniq C.hK₄t⟩

include C in
theorem ae6Vc_subset_twinSet : ae6Vc Ω[R] t ⊆ twinSet Ω[R] K :=
  fun _ hJ => ⟨hJ.1, t, C.H.ex.1.datum.hz, hJ.2⟩

include C in
theorem ae6P_eq_twinJoin : ae6P Ω[R] t = TwinSecXg.twinJoin Ω[R] K := by
  have hset : ae6Vc Ω[R] t = twinSet Ω[R] K := by
    ext J
    exact ⟨fun hJ => ae6Vc_subset_twinSet C hJ, fun hJ => ⟨hJ.1, C.uniq hJ⟩⟩
  unfold ae6P TwinSecXg.twinJoin
  rw [hset]

include C in
theorem ae6P_comm_t {p : Y} (hp : p ∈ ae6P Ω[R] t) : p * t = t * p := by
  have := TwinSecXg.twinJoin_le_centralizer (Ω := Ω[R]) C.H.ex.1.datum.hz
  rw [← ae6P_eq_twinJoin C] at this
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hp)

include C in
theorem isPGroup_ae6P : IsPGroup 2 ↥(ae6P Ω[R] t) := by
  rw [ae6P_eq_twinJoin C]
  exact TwinSecXg.twinJoin_isPGroup (CoreData.of_S C.H.ex.1.perp.core).hyp C.H.ex.2.2.2.1
    C.H.ex.1.datum.hz

include C in
theorem exists_prod4 {p : Y} (hp : p ∈ ae6P Ω[R] t) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K', ∃ k₃ ∈ K₃, ∃ k₄ ∈ K₄, p = k₁ * k₂ * k₃ * k₄ := by
  obtain ⟨hne12, hne13, hne14, hne23, hne24, hne34⟩ := C.twins_ne
  have c21 : ∀ a ∈ K', ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK't C.hKt hne12.symm a ha b hb
  have c31 : ∀ a ∈ K₃, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₃t C.hKt hne13.symm a ha b hb
  have c41 : ∀ a ∈ K₄, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₄t C.hKt hne14.symm a ha b hb
  have c32 : ∀ a ∈ K₃, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₃t C.hK't hne23.symm a ha b hb
  have c42 : ∀ a ∈ K₄, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₄t C.hK't hne24.symm a ha b hb
  have c43 : ∀ a ∈ K₄, ∀ b ∈ K₃, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₄t C.hK₃t hne34.symm a ha b hb
  refine iSup₂_induction (s := ae6Vc Ω[R] t)
    (motive := fun p => ∃ k₁ ∈ K, ∃ k₂ ∈ K', ∃ k₃ ∈ K₃, ∃ k₄ ∈ K₄, p = k₁ * k₂ * k₃ * k₄) hp ?_ ?_ ?_
  · intro J hJ z hz
    rcases (mem_ae6Vc_iff C).mp hJ with rfl | rfl | rfl | rfl
    · exact ⟨z, hz, 1, K'.one_mem, 1, K₃.one_mem, 1, K₄.one_mem, by simp⟩
    · exact ⟨1, K.one_mem, z, hz, 1, K₃.one_mem, 1, K₄.one_mem, by simp⟩
    · exact ⟨1, K.one_mem, 1, K'.one_mem, z, hz, 1, K₄.one_mem, by simp⟩
    · exact ⟨1, K.one_mem, 1, K'.one_mem, 1, K₃.one_mem, z, hz, by simp⟩
  · exact ⟨1, K.one_mem, 1, K'.one_mem, 1, K₃.one_mem, 1, K₄.one_mem, by simp⟩
  · rintro x z ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, a₄, ha₄, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, b₄, hb₄, rfl⟩
    exact ⟨a₁ * b₁, K.mul_mem ha₁ hb₁, a₂ * b₂, K'.mul_mem ha₂ hb₂, a₃ * b₃, K₃.mul_mem ha₃ hb₃,
      a₄ * b₄, K₄.mul_mem ha₄ hb₄,
      mul4_swap (c21 _ ha₂ _ hb₁) (c31 _ ha₃ _ hb₁) (c41 _ ha₄ _ hb₁) (c32 _ ha₃ _ hb₂)
        (c42 _ ha₄ _ hb₂) (c43 _ ha₄ _ hb₃)⟩

include C in
theorem comm_twin_ae6P {J : Subgroup Y} (hJ : J ∈ ae6Vc Ω[R] t) {q p : Y} (hq : q ∈ J)
    (hp : p ∈ ae6P Ω[R] t) : q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t := by
  have hJt : J ∈ twinSet Ω[R] K := ae6Vc_subset_twinSet C hJ
  have hq8 := C.twin_q8 hJt
  have htt : t * t = 1 := C.H.ex.1.datum.hz.sq
  have key : p ∈ ae6P Ω[R] t ∧ (q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t) := by
    refine iSup₂_induction (s := ae6Vc Ω[R] t)
      (motive := fun p => p ∈ ae6P Ω[R] t ∧ (q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t)) hp ?_ ?_ ?_
    · intro J' hJ' z hz
      have hzP : z ∈ ae6P Ω[R] t := A6Hx.le_ae6P hJ'.1 hJ'.2 hz
      refine ⟨hzP, ?_⟩
      by_cases hJJ : J' = J
      · subst hJJ
        by_cases hc : q * z = z * q
        · left
          calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [hc]
            _ = z := by group
        · right
          have h1 := hq8.comm_eq q hq z hz hc
          calc q * z * q⁻¹ = (q * z * q⁻¹ * z⁻¹) * z := by group
            _ = t * z := by rw [h1]
            _ = z * t := (ae6P_comm_t C hzP).symm
      · left
        have hJ't : J' ∈ twinSet Ω[R] K := ae6Vc_subset_twinSet C hJ'
        have h1 := C.twin_comm hJt hJ't (Ne.symm hJJ) q hq z hz
        calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [h1]
          _ = z := by group
    · exact ⟨(ae6P Ω[R] t).one_mem, Or.inl (by group)⟩
    · rintro x z ⟨hxP, hx⟩ ⟨hzP, hz⟩
      refine ⟨(ae6P Ω[R] t).mul_mem hxP hzP, ?_⟩
      have e : q * (x * z) * q⁻¹ = (q * x * q⁻¹) * (q * z * q⁻¹) := by group
      have htz : t * z = z * t := (ae6P_comm_t C hzP).symm
      rcases hx with hx | hx <;> rcases hz with hz | hz
      · rw [e, hx, hz]
        left
        rfl
      · rw [e, hx, hz]
        right
        exact (mul_assoc x z t).symm
      · rw [e, hx, hz]
        right
        rw [mul_assoc, htz, ← mul_assoc]
      · rw [e, hx, hz]
        left
        rw [mul_assoc, ← mul_assoc t z t, htz, mul_assoc z t t, htt, mul_one]
  exact key.2

include C in
theorem comm_ae6P {q p : Y} (hq : q ∈ ae6P Ω[R] t) (hp : p ∈ ae6P Ω[R] t) :
    q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t := by
  have key : q ∈ ae6P Ω[R] t ∧ ∀ p ∈ ae6P Ω[R] t, (q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t) := by
    refine iSup₂_induction (s := ae6Vc Ω[R] t)
      (motive := fun q => q ∈ ae6P Ω[R] t ∧
        ∀ p ∈ ae6P Ω[R] t, (q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * t)) hq ?_ ?_ ?_
    · intro J hJ z hz
      exact ⟨A6Hx.le_ae6P hJ.1 hJ.2 hz, fun p hp => comm_twin_ae6P C hJ hz hp⟩
    · exact ⟨(ae6P Ω[R] t).one_mem, fun p _ => Or.inl (by group)⟩
    · rintro x z ⟨hxP, hx⟩ ⟨hzP, hz⟩
      refine ⟨(ae6P Ω[R] t).mul_mem hxP hzP, fun p hp => ?_⟩
      have e : x * z * p * (x * z)⁻¹ = x * (z * p * z⁻¹) * x⁻¹ := by group
      have hxt : x * t * x⁻¹ = t := by
        rw [ae6P_comm_t C hxP, mul_inv_cancel_right]
      rcases hz p hp with h | h
      · rw [e, h]
        exact hx p hp
      · rw [e, h]
        have e2 : x * (p * t) * x⁻¹ = (x * p * x⁻¹) * (x * t * x⁻¹) := by group
        rw [e2, hxt]
        rcases hx p hp with h' | h'
        · right
          rw [h']
        · left
          rw [h', mul_assoc, C.H.ex.1.datum.hz.sq, mul_one]
  exact key.2 p hp

theorem move_of_comp {J : Subgroup Y} {t k r : Y} (hq8 : WF.Q8Facts J t) (hk : k ∈ J) (hk1 : k ≠ 1)
    (hkt : k ≠ t) (hr : ∀ j ∈ J, j * r = r * j) (htr : t * r = r * t) :
    ∃ j ∈ J, j * (k * r) * j⁻¹ = (k * r) * t := by
  obtain ⟨m, hm, hkm⟩ := hq8.exists_noncomm k hk hk1 hkt
  refine ⟨m, hm, ?_⟩
  have hmk : m * k ≠ k * m := fun h => hkm h.symm
  have h1 := hq8.comm_eq m hm k hk hmk
  have h2 : m * k * m⁻¹ = k * t := by
    calc m * k * m⁻¹ = (m * k * m⁻¹ * k⁻¹) * k := by group
      _ = t * k := by rw [h1]
      _ = k * t := hq8.z_central k hk
  have h3 : m * r * m⁻¹ = r := by
    rw [hr m hm, mul_inv_cancel_right]
  calc m * (k * r) * m⁻¹ = (m * k * m⁻¹) * (m * r * m⁻¹) := by group
    _ = (k * t) * r := by rw [h2, h3]
    _ = k * r * t := by rw [mul_assoc, htr, ← mul_assoc]

theorem swap_mul {a b : Y} (h : a * b = b * a) (z : Y) : a * (b * z) = b * (a * z) := by
  rw [← mul_assoc, h, mul_assoc]

include C in
theorem exists_move_ae6P {e : Y} (he : e ∈ ae6P Ω[R] t) (h1 : e ≠ 1) (ht : e ≠ t) :
    ∃ j ∈ ae6P Ω[R] t, j * e * j⁻¹ = e * t := by
  have htt : t * t = 1 := C.H.ex.1.datum.hz.sq
  obtain ⟨hne12, hne13, hne14, hne23, hne24, hne34⟩ := C.twins_ne
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, k₄, hk₄, rfl⟩ := exists_prod4 C he
  have hKP : K ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.mem C.H.ex.1.datum.hz
  have hK'P : K' ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.hK'.1 (C.uniq C.hK't)
  have hK₃P : K₃ ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.1.datum.hK₃.1 (C.uniq C.hK₃t)
  have hK₄P : K₄ ≤ ae6P Ω[R] t := A6Hx.le_ae6P C.H.ex.2.1.1.1 (C.uniq C.hK₄t)
  have c12 : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK't hne12 a ha b hb
  have c13 : ∀ a ∈ K, ∀ b ∈ K₃, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK₃t hne13 a ha b hb
  have c14 : ∀ a ∈ K, ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hKt C.hK₄t hne14 a ha b hb
  have c23 : ∀ a ∈ K', ∀ b ∈ K₃, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK't C.hK₃t hne23 a ha b hb
  have c24 : ∀ a ∈ K', ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK't C.hK₄t hne24 a ha b hb
  have c34 : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a := fun a ha b hb =>
    C.twin_comm C.hK₃t C.hK₄t hne34 a ha b hb
  have ct : ∀ z ∈ ae6P Ω[R] t, t * z = z * t := fun z hz => (ae6P_comm_t C hz).symm
  have q1 := C.twin_q8 C.hKt
  have q2 := C.twin_q8 C.hK't
  have q3 := C.twin_q8 C.hK₃t
  have q4 := C.twin_q8 C.hK₄t
  have cp3 : ∀ {j a b c : Y}, j * a = a * j → j * b = b * j → j * c = c * j →
      j * (a * b * c) = (a * b * c) * j := fun {j a b c} ha hb hc =>
    (((show Commute j a from ha).mul_right (show Commute j b from hb)).mul_right
      (show Commute j c from hc)).eq
  have htk₁ : t * k₁ = k₁ * t := ct k₁ (hKP hk₁)
  have htk₂ : t * k₂ = k₂ * t := ct k₂ (hK'P hk₂)
  have htk₃ : t * k₃ = k₃ * t := ct k₃ (hK₃P hk₃)
  have htk₄ : t * k₄ = k₄ * t := ct k₄ (hK₄P hk₄)
  by_cases n1 : k₁ ≠ 1 ∧ k₁ ≠ t
  · obtain ⟨j, hj, hjk⟩ := move_of_comp q1 hk₁ n1.1 n1.2 (r := k₂ * k₃ * k₄)
      (fun j hj => cp3 (c12 j hj k₂ hk₂) (c13 j hj k₃ hk₃) (c14 j hj k₄ hk₄))
      (cp3 htk₂ htk₃ htk₄)
    refine ⟨j, hKP hj, ?_⟩
    have e : k₁ * k₂ * k₃ * k₄ = k₁ * (k₂ * k₃ * k₄) := by simp only [mul_assoc]
    rw [e]
    exact hjk
  by_cases n2 : k₂ ≠ 1 ∧ k₂ ≠ t
  · obtain ⟨j, hj, hjk⟩ := move_of_comp q2 hk₂ n2.1 n2.2 (r := k₁ * k₃ * k₄)
      (fun j hj => cp3 (c12 k₁ hk₁ j hj).symm (c23 j hj k₃ hk₃) (c24 j hj k₄ hk₄))
      (cp3 htk₁ htk₃ htk₄)
    refine ⟨j, hK'P hj, ?_⟩
    have e : k₁ * k₂ * k₃ * k₄ = k₂ * (k₁ * k₃ * k₄) := by
      rw [c12 k₁ hk₁ k₂ hk₂]
      simp only [mul_assoc]
    rw [e]
    exact hjk
  by_cases n3 : k₃ ≠ 1 ∧ k₃ ≠ t
  · obtain ⟨j, hj, hjk⟩ := move_of_comp q3 hk₃ n3.1 n3.2 (r := k₁ * k₂ * k₄)
      (fun j hj => cp3 (c13 k₁ hk₁ j hj).symm (c23 k₂ hk₂ j hj).symm (c34 j hj k₄ hk₄))
      (cp3 htk₁ htk₂ htk₄)
    refine ⟨j, hK₃P hj, ?_⟩
    have e : k₁ * k₂ * k₃ * k₄ = k₃ * (k₁ * k₂ * k₄) := by
      simp only [mul_assoc]
      rw [swap_mul (c13 k₁ hk₁ k₃ hk₃).symm (k₂ * k₄), swap_mul (c23 k₂ hk₂ k₃ hk₃).symm k₄]
    rw [e]
    exact hjk
  by_cases n4 : k₄ ≠ 1 ∧ k₄ ≠ t
  · obtain ⟨j, hj, hjk⟩ := move_of_comp q4 hk₄ n4.1 n4.2 (r := k₁ * k₂ * k₃)
      (fun j hj => cp3 (c14 k₁ hk₁ j hj).symm (c24 k₂ hk₂ j hj).symm (c34 k₃ hk₃ j hj).symm)
      (cp3 htk₁ htk₂ htk₃)
    refine ⟨j, hK₄P hj, ?_⟩
    have e : k₁ * k₂ * k₃ * k₄ = k₄ * (k₁ * k₂ * k₃) := by
      simp only [mul_assoc]
      rw [swap_mul (c14 k₁ hk₁ k₄ hk₄).symm (k₂ * k₃), swap_mul (c24 k₂ hk₂ k₄ hk₄).symm k₃,
        (c34 k₃ hk₃ k₄ hk₄).symm]
    rw [e]
    exact hjk
  exfalso
  have cen : ∀ k : Y, ¬ (k ≠ 1 ∧ k ≠ t) → (k = 1 ∨ k = t) := fun k h => by tauto
  have mulZ : ∀ a b : Y, (a = 1 ∨ a = t) → (b = 1 ∨ b = t) → (a * b = 1 ∨ a * b = t) := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact htt
  rcases mulZ _ _ (mulZ _ _ (mulZ _ _ (cen _ n1) (cen _ n2)) (cen _ n3)) (cen _ n4) with h | h
  · exact h1 h
  · exact ht h

include C in
theorem comm_ae6P_conj (g : Y) {q p : Y} (hq : q ∈ ae6P Ω[R] (g * t * g⁻¹))
    (hp : p ∈ ae6P Ω[R] (g * t * g⁻¹)) :
    q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p * (g * t * g⁻¹) := by
  have hinv := conjInvariant_conjClass (tightCore R)
  rw [← A6Hx.ae6P_conj hinv g t] at hq hp
  have hq' : g⁻¹ * q * g ∈ ae6P Ω[R] t := mem_conjSub_iff.mp hq
  have hp' : g⁻¹ * p * g ∈ ae6P Ω[R] t := mem_conjSub_iff.mp hp
  have e : q * p * q⁻¹ = g * ((g⁻¹ * q * g) * (g⁻¹ * p * g) * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
  rcases comm_ae6P C hq' hp' with h | h
  · left
    rw [e, h]
    group
  · right
    rw [e, h]
    group

include C in
theorem exists_move_ae6P_conj (g : Y) {e : Y} (he : e ∈ ae6P Ω[R] (g * t * g⁻¹)) (h1 : e ≠ 1)
    (hc : e ≠ g * t * g⁻¹) :
    ∃ j ∈ ae6P Ω[R] (g * t * g⁻¹), j * e * j⁻¹ = e * (g * t * g⁻¹) := by
  have hinv := conjInvariant_conjClass (tightCore R)
  have he0 := he
  rw [← A6Hx.ae6P_conj hinv g t] at he0
  have he' : g⁻¹ * e * g ∈ ae6P Ω[R] t := mem_conjSub_iff.mp he0
  have h1' : g⁻¹ * e * g ≠ 1 := fun h => h1 (by
    have : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hc' : g⁻¹ * e * g ≠ t := fun h => hc (by
    have : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    rw [this, h])
  obtain ⟨j', hj', hjj⟩ := exists_move_ae6P C he' h1' hc'
  refine ⟨g * j' * g⁻¹, ?_, ?_⟩
  · rw [← A6Hx.ae6P_conj hinv g t]
    exact conj_mem_conjSub hj'
  · have e1 : g * j' * g⁻¹ * e * (g * j' * g⁻¹)⁻¹ = g * (j' * (g⁻¹ * e * g) * j'⁻¹) * g⁻¹ := by group
    rw [e1, hjj]
    group

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
