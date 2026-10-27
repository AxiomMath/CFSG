module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Fuse

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sl2_order4_conj : ∀ x y : SL(2, ZMod 3), x ^ 2 ≠ 1 → x ^ 4 = 1 → y ^ 2 ≠ 1 → y ^ 4 = 1 →
    ∃ m : SL(2, ZMod 3), m * x * m⁻¹ = y := by
  decide +kernel

variable {Y : Type} [Group Y]

theorem exists_conj_order4 {M : Subgroup Y} (e : M ≃* SL(2, ZMod 3)) {x y : Y} (hx : x ∈ M)
    (hy : y ∈ M) (hx2 : x ^ 2 ≠ 1) (hx4 : x ^ 4 = 1) (hy2 : y ^ 2 ≠ 1) (hy4 : y ^ 4 = 1) :
    ∃ m ∈ M, m * x * m⁻¹ = y := by
  have key : ∀ w : Y, ∀ hw : w ∈ M, ∀ k : ℕ, e ⟨w, hw⟩ ^ k = 1 ↔ w ^ k = 1 := by
    intro w hw k
    rw [← map_pow, MulEquiv.map_eq_one_iff]
    constructor
    · intro h; simpa using congrArg Subtype.val h
    · intro h; exact Subtype.ext (by simpa using h)
  obtain ⟨m', hm'⟩ := sl2_order4_conj (e ⟨x, hx⟩) (e ⟨y, hy⟩) (fun h => hx2 ((key x hx 2).mp h))
    ((key x hx 4).mpr hx4)
    (fun h => hy2 ((key y hy 2).mp h)) ((key y hy 4).mpr hy4)
  refine ⟨(e.symm m' : Y), (e.symm m').2, ?_⟩
  have := congrArg (fun s => (e.symm s : Y)) hm'
  simpa using this

theorem fusion_core {K K'' M M'' : Subgroup Y} {z u : Y} (hz : IsUniqueInvolution K z)
    (hz'' : IsUniqueInvolution K'' z) (hK4 : ∀ x ∈ K, x ^ 4 = 1) (hK4'' : ∀ x ∈ K'', x ^ 4 = 1)
    (hKM : K ≤ M) (hKM'' : K'' ≤ M'') (eM : M ≃* SL(2, ZMod 3)) (eM'' : M'' ≃* SL(2, ZMod 3))
    (hcomm : ∀ m ∈ M, ∀ n ∈ M'', m * n = n * m) (hu : u ∈ K ⊔ K'') (hu1 : u ≠ 1)
    (hu2 : u * u = 1) :
    (∃ e : Y, e * u * e⁻¹ = z) ∨ ∀ a ∈ K, ∀ b ∈ K'', orderOf a = 4 → orderOf b = 4 →
      ∃ e : Y, e * u * e⁻¹ = a * b := by
  have hcKK : ∀ a ∈ K, ∀ b ∈ K'', a * b = b * a := fun a ha b hb => hcomm a (hKM ha) b (hKM'' hb)
  let S : Subgroup Y :=
    { carrier := {x | ∃ a ∈ K, ∃ b ∈ K'', x = a * b}
      one_mem' := ⟨1, K.one_mem, 1, K''.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', K.mul_mem ha ha', b * b', K''.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcKK a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, b⁻¹, K''.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hcKK a⁻¹ (K.inv_mem ha) b⁻¹ (K''.inv_mem hb)).symm }
  have hS : K ⊔ K'' ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, K''.one_mem, by simp⟩)
      (fun b hb => ⟨1, K.one_mem, b, hb, by simp⟩)
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := hS hu
  have hsq : a₀ * a₀ * (b₀ * b₀) = 1 := by
    rw [← hu2]
    calc a₀ * a₀ * (b₀ * b₀) = a₀ * (a₀ * b₀) * b₀ := by group
      _ = a₀ * (b₀ * a₀) * b₀ := by rw [hcKK a₀ ha₀ b₀ hb₀]
      _ = a₀ * b₀ * (a₀ * b₀) := by group
  have hKsq : ∀ x ∈ K, x * x = 1 ∨ x * x = z := by
    intro x hx
    have h1 : x * x ∈ K := K.mul_mem hx hx
    have h2 : (x * x) * (x * x) = 1 := by
      have := hK4 x hx
      calc (x * x) * (x * x) = x ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := this
    exact hz.unique _ h1 h2
  have hKsq'' : ∀ x ∈ K'', x * x = 1 ∨ x * x = z := by
    intro x hx
    have h1 : x * x ∈ K'' := K''.mul_mem hx hx
    have h2 : (x * x) * (x * x) = 1 := by
      have := hK4'' x hx
      calc (x * x) * (x * x) = x ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := this
    exact hz''.unique _ h1 h2
  have hzz : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hinvK : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = z := fun x hx h => hz.unique x hx h
  have hinvK'' : ∀ x ∈ K'', x * x = 1 → x = 1 ∨ x = z := fun x hx h => hz''.unique x hx h
  rcases hKsq a₀ ha₀ with h1 | h1 <;> rcases hKsq'' b₀ hb₀ with h2 | h2
  ·
    left
    rcases hinvK a₀ ha₀ h1 with rfl | rfl <;> rcases hinvK'' b₀ hb₀ h2 with rfl | rfl
    · exact absurd (by simp) hu1
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp⟩
    · exact absurd hzz hu1
  · exfalso
    rw [h1, h2, one_mul] at hsq
    exact hz1 hsq
  · exfalso
    rw [h1, h2, mul_one] at hsq
    exact hz1 hsq
  ·
    right
    intro a ha b hb ha4 hb4
    have ha2 : a ^ 2 ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [ha4] at this
      exact absurd this (by norm_num)
    have hb2 : b ^ 2 ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hb4] at this
      exact absurd this (by norm_num)
    have ha4' : a ^ 4 = 1 := ha4 ▸ pow_orderOf_eq_one a
    have hb4' : b ^ 4 = 1 := hb4 ▸ pow_orderOf_eq_one b
    have ha₀2 : a₀ ^ 2 ≠ 1 := by rw [pow_two, h1]; exact hz1
    have hb₀2 : b₀ ^ 2 ≠ 1 := by rw [pow_two, h2]; exact hz1
    have ha₀4 : a₀ ^ 4 = 1 := hK4 a₀ ha₀
    have hb₀4 : b₀ ^ 4 = 1 := hK4'' b₀ hb₀
    obtain ⟨m, hm, hma⟩ := exists_conj_order4 eM (hKM ha₀) (hKM ha) ha₀2 ha₀4 ha2 ha4'
    obtain ⟨n, hn, hnb⟩ := exists_conj_order4 eM'' (hKM'' hb₀) (hKM'' hb) hb₀2 hb₀4 hb2 hb4'
    refine ⟨m * n, ?_⟩
    have hna : n * a₀ = a₀ * n := (hcomm a₀ (hKM ha₀) n hn).symm
    have hmb : m * b = b * m := hcomm m hm b (hKM'' hb)
    have hmn : m * n = n * m := hcomm m hm n hn
    calc m * n * (a₀ * b₀) * (m * n)⁻¹ = m * (n * a₀ * b₀ * n⁻¹) * m⁻¹ := by group
      _ = m * (a₀ * (n * b₀ * n⁻¹)) * m⁻¹ := by rw [hna]; group
      _ = m * (a₀ * b) * m⁻¹ := by rw [hnb]
      _ = (m * a₀ * m⁻¹) * (m * b * m⁻¹) := by group
      _ = a * b := by rw [hma, hmb]; group

end Fuse

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
