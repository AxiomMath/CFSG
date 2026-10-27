module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement Pointwise

@[expose] def HasInvolMod (H : Type) [Group H] (e : H) : Prop :=
  ∃ u : H, u ∉ CFSG.pCore 2 H ∧ u * u ∈ CFSG.pCore 2 H ∧ ⁅u, e⁆ ∈ CFSG.pCore 2 H

section Basic

variable {H : Type} [Group H]

theorem mem_pCore_two_iff (φ : H ≃* H) (g : H) :
    φ g ∈ CFSG.pCore 2 H ↔ g ∈ CFSG.pCore 2 H := by
  have h := Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (p := 2) (G := H)) φ
  constructor
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', hg'e⟩ := hg
    have : g' = g := φ.injective hg'e
    exact this ▸ hg'
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩

theorem hasInvolMod_map (φ : H ≃* H) {e : H} (h : HasInvolMod H e) : HasInvolMod H (φ e) := by
  obtain ⟨u, hu, hu2, hc⟩ := h
  refine ⟨φ u, fun h' => hu ((mem_pCore_two_iff φ u).1 h'), ?_, ?_⟩
  · rw [← map_mul]; exact (mem_pCore_two_iff φ _).2 hu2
  · have : ⁅φ u, φ e⁆ = φ ⁅u, e⁆ := (map_commutatorElement φ.toMonoidHom u e).symm
    rw [this]; exact (mem_pCore_two_iff φ _).2 hc

theorem not_mem_pCore_two_of_pow_three {c : H} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    c ∉ CFSG.pCore 2 H := by
  intro hc
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨c, hc⟩
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h3 : orderOf c = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hc3 hc1
  rw [h3] at h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem not_mem_pCore_two_of_inverts {x c : H} (hx2 : x * x = 1) (hxc : x * c * x = c⁻¹)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) : x ∉ CFSG.pCore 2 H := by
  intro hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hn := (CFSG.pCore_normal (p := 2) (G := H)).conj_mem x hx c⁻¹
  have h1 : c * x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 H :=
    (CFSG.pCore 2 H).mul_mem ((CFSG.pCore_normal (p := 2) (G := H)).conj_mem x hx c) ((CFSG.pCore 2 H).inv_mem hx)
  have h2 : c * x * c⁻¹ * x⁻¹ = c * c := by
    rw [hxi]
    have : x * c⁻¹ * x = c := by
      have := congrArg (·⁻¹) hxc
      simpa [mul_inv_rev, hxi, mul_assoc] using this
    calc c * x * c⁻¹ * x = c * (x * c⁻¹ * x) := by group
      _ = c * c := by rw [this]
  have hcc : c * c ∈ CFSG.pCore 2 H := h2 ▸ h1
  have hc : c ∈ CFSG.pCore 2 H := by
    have : c = (c * c) * (c * c) := by
      calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
        _ = (c * c) * (c * c) := by
          rw [hc3, inv_one, mul_one]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact (CFSG.pCore 2 H).mul_mem hcc hcc
  exact not_mem_pCore_two_of_pow_three hc3 hc1 hc

end Basic

section Pair

variable {H : Type} [Group H]

theorem conj_c_eq_inv {x y : H} (hx2 : x * x = 1) (hy2 : y * y = 1) :
    x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rw [mul_inv_rev, hxi, hyi]
  calc x * (x * y) * x = (x * x) * y * x := by group
    _ = y * x := by rw [hx2, one_mul]

theorem conj_zpow_c {x y : H} (hx2 : x * x = 1) (hy2 : y * y = 1) (k : ℤ) :
    x * (x * y) ^ k * x⁻¹ = (x * y) ^ (-k) := by
  have h := map_zpow (MulAut.conj x) (x * y) k
  simp only [MulAut.conj_apply] at h
  rw [h, conj_c_eq_inv hx2 hy2, inv_zpow', zpow_neg]

theorem mem_closure_pair_cases {x y : H} (hx2 : x * x = 1) (hy2 : y * y = 1) {w : H}
    (hw : w ∈ Subgroup.closure {x, y}) : ∃ k : ℤ, w = (x * y) ^ k ∨ w = (x * y) ^ k * x := by
  set C : Subgroup H := Subgroup.zpowers (x * y) with hC
  set X : Subgroup H := Subgroup.zpowers x with hX
  have hkey : ∀ n ∈ C, x * n * x⁻¹ ∈ C := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [conj_zpow_c hx2 hy2 k]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hxN : X ≤ Subgroup.normalizer (C : Set H) := by
    rw [hX, Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.2 fun n => ⟨hkey n, fun hn => ?_⟩
    have h1 := hkey _ hn
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have : x * (x * n * x⁻¹) * x⁻¹ = n := by
      rw [hxi]
      calc x * (x * n * x) * x = (x * x) * n * (x * x) := by group
        _ = n := by rw [hx2]; group
    rwa [this] at h1
  have hle : Subgroup.closure ({x, y} : Set H) ≤ C ⊔ X := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hz
      have : y = x * (x * y) := by rw [← mul_assoc, hx2, one_mul]
      rw [hz, this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hwm : w ∈ (↑(C ⊔ X) : Set H) := hle hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left C X hxN] at hwm
  obtain ⟨a, ha, b, hb, rfl⟩ := hwm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  refine ⟨k, ?_⟩
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · left
    have : x ^ (2 * j) = 1 := by rw [zpow_mul, zpow_two, hx2, one_zpow]
    show (x * y) ^ k * x ^ (2 * j) = (x * y) ^ k
    rw [this, mul_one]
  · right
    have : x ^ (2 * j + 1) = x := by rw [zpow_add_one, zpow_mul, zpow_two, hx2, one_zpow, one_mul]
    show (x * y) ^ k * x ^ (2 * j + 1) = (x * y) ^ k * x
    rw [this]

end Pair

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
