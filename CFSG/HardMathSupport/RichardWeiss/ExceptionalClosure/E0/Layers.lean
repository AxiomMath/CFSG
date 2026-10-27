module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def layerTriv (V U K : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ Subgroup.normalizer (V : Set G) ∧ a ∈ Subgroup.normalizer (U : Set G) ∧
    (∀ k ∈ K, a * k = k * a) ∧ ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ U}
  mul_mem' := by
    rintro a b ⟨haV, haU, haK, haL⟩ ⟨hbV, hbU, hbK, hbL⟩
    refine ⟨mul_mem haV hbV, mul_mem haU hbU, fun k hk => ?_, fun v hv => ?_⟩
    · rw [mul_assoc, hbK k hk, ← mul_assoc, haK k hk, mul_assoc]
    · have h1 : a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp haU _).mp (hbL v hv)
      have h2 := haL v hv
      have := U.mul_mem h1 h2
      convert this using 1
      group
  one_mem' := ⟨one_mem _, one_mem _, fun k _ => by simp, fun v _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haV, haU, haK, haL⟩
    refine ⟨inv_mem haV, inv_mem haU, fun k hk => ?_, fun v hv => ?_⟩
    · have := haK k hk
      calc a⁻¹ * k = a⁻¹ * (k * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * k) * a⁻¹ := by rw [this]
        _ = k * a⁻¹ := by group
    · have hv' : a⁻¹ * v * a ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem haV) v).mp hv
        simpa using this
      have h1 := haL _ hv'
      have h2 : a⁻¹ * v * a * v⁻¹ = (a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹)⁻¹ := by group
      rw [inv_inv, h2]
      exact U.inv_mem h1

theorem mem_layerTriv_of_centralizer {V U K : Subgroup G} (hKV : K ≤ V) {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hac : a ∈ Subgroup.centralizer (V : Set G)) : a ∈ layerTriv V U K :=
  ⟨haV, haU, fun k hk => (Subgroup.mem_centralizer_iff.mp hac k (hKV hk)).symm,
    fun v hv => by
      have := Subgroup.mem_centralizer_iff.mp hac v hv
      rw [← this]; simp⟩

variable {S M : Subgroup G} {N : ℕ}

theorem le_layerTriv_of_thompsonJ {V U K : Subgroup G} (hKV : K ≤ V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hSM : S ≤ M) (θ : ↥M →* Equiv.Perm (Fin N))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G))
    (hJ : (S.subgroupOf M).map θ ≤ ((thompsonJ S).subgroupOf M).map θ)
    (hA : ∀ A, IsMaxElemAbelian S A → A ≤ layerTriv V U K) : S ≤ layerTriv V U K := by
  have hJle : thompsonJ S ≤ layerTriv V U K := iSup₂_le fun A hA' => hA A hA'
  intro s hs
  have hsM : s ∈ M := hSM hs
  have h1 : θ ⟨s, hsM⟩ ∈ ((thompsonJ S).subgroupOf M).map θ :=
    hJ ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  obtain ⟨⟨j, hjM⟩, hj, hjθ⟩ := h1
  have hjJ : j ∈ thompsonJ S := hj
  have hq : θ ((⟨j, hjM⟩ : ↥M)⁻¹ * ⟨s, hsM⟩) = 1 := by
    rw [map_mul, map_inv, hjθ]; simp
  have hqc := hker _ hq
  have hqM : j⁻¹ * s ∈ M := mul_mem (inv_mem hjM) hsM
  have hqL : j⁻¹ * s ∈ layerTriv V U K :=
    mem_layerTriv_of_centralizer hKV (hMV hqM) (hMU hqM) hqc
  have : s = j * (j⁻¹ * s) := by group
  rw [this]
  exact mul_mem (hJle hjJ) hqL

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
