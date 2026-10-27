module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem lit_odd_fixed {Y : Type*} [Group Y] [Finite Y] (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    {N : Subgroup Y} [N.Normal] (hN : ∀ y ∈ N, σ y ∈ N) (hodd : Odd (Nat.card N)) {y : Y}
    (hy : σ y * y⁻¹ ∈ N) : ∃ u ∈ N, σ (y * u) = y * u := by
  classical
  letI : Fintype ↥N := Fintype.ofFinite ↥N
  let n0 : Y := y⁻¹ * σ y
  have hn0 : n0 ∈ N := by
    have h : y⁻¹ * (σ y * y⁻¹) * (y⁻¹)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem (σ y * y⁻¹) hy y⁻¹
    have he : y⁻¹ * (σ y * y⁻¹) * (y⁻¹)⁻¹ = y⁻¹ * σ y := by group
    rw [he] at h
    exact h
  let g : ↥N → ↥N := fun u => ⟨n0 * σ (u : Y), N.mul_mem hn0 (hN (u : Y) u.2)⟩
  have hσn0 : σ n0 = (σ y)⁻¹ * y := by
    change σ (y⁻¹ * σ y) = (σ y)⁻¹ * y
    rw [map_mul, map_inv, hσ y]
  have hgg : Function.Involutive g := by
    intro u
    apply Subtype.ext
    change n0 * σ ((g u : ↥N) : Y) = (u : Y)
    have hu : ((g u : ↥N) : Y) = n0 * σ (u : Y) := rfl
    rw [hu, map_mul, hσn0, hσ]
    show (y⁻¹ * σ y) * ((σ y)⁻¹ * y * (u : Y)) = (u : Y)
    group
  let gperm : Equiv.Perm ↥N :=
    { toFun := g, invFun := g, left_inv := hgg, right_inv := hgg }
  have hg2 : gperm ^ 2 = 1 := by
    rw [pow_two]
    ext u
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hgg u)
  have hodd' : Odd (Fintype.card ↥N) := by simpa using hodd
  have hα : ¬ 2 ∣ Fintype.card ↥N := hodd'.not_two_dvd_nat
  obtain ⟨u, hu⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (α := ↥N) (p := 2) (n := 1) hα hg2
  have hu' : n0 * σ (u : Y) = (u : Y) := by
    have h := congrArg (fun w : ↥N => (w : Y)) hu
    change ((g u : ↥N) : Y) = (u : Y) at h
    simpa [g] using h
  refine ⟨(u : Y), u.2, ?_⟩
  calc σ (y * (u : Y)) = σ y * σ (u : Y) := map_mul σ y (u : Y)
    _ = y * (n0 * σ (u : Y)) := by
          show σ y * σ (u : Y) = y * (y⁻¹ * σ y * σ (u : Y))
          group
    _ = y * (u : Y) := by rw [hu']

theorem lit_odd_fixed_mod {X : Type*} [Group X] [Finite X] (τ : X ≃* X)
    (hτ : ∀ x, τ (τ x) = x) {Z O : Subgroup X} [Z.Normal] [O.Normal] (hZ : ∀ x ∈ Z, τ x ∈ Z)
    (hO : ∀ x ∈ O, τ x ∈ O) (hodd : Odd (Nat.card O)) {x : X} (hx : τ x * x⁻¹ ∈ Z ⊔ O) :
    ∃ u ∈ O, τ (x * u) * (x * u)⁻¹ ∈ Z := by
  classical
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hmap : Z.map (τ : X →* X) = Z := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr fun z hz => hZ z hz
    · intro z hz
      exact ⟨τ z, hZ z hz, hτ z⟩
  let σ : X ⧸ Z ≃* X ⧸ Z := QuotientGroup.congr Z Z τ hmap
  have hcongr : ∀ x, σ (π x) = π (τ x) := fun x => QuotientGroup.congr_mk' Z Z τ hmap x
  have hσ : ∀ q, σ (σ q) = q := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (N := Z) q
    rw [hcongr u, hcongr (τ u), hτ u]
  let N : Subgroup (X ⧸ Z) := O.map π
  haveI hNnormal : N.Normal :=
    Subgroup.Normal.map (inferInstance : O.Normal) π (QuotientGroup.mk'_surjective (N := Z))
  have hN : ∀ y ∈ N, σ y ∈ N := by
    intro y hy
    change y ∈ O.map π at hy
    obtain ⟨o, hoO, rfl⟩ := hy
    show σ (π o) ∈ O.map π
    rw [hcongr o]
    exact ⟨τ o, hO o hoO, rfl⟩
  have hoddN : Odd (Nat.card N) := by
    change Odd (Nat.card (O.map π))
    exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd O π)
  have hyN : σ (π x) * (π x)⁻¹ ∈ N := by
    have h1 : σ (π x) * (π x)⁻¹ = π (τ x * x⁻¹) := by
      rw [hcongr x, ← map_inv, ← map_mul]
    rw [h1]
    change π (τ x * x⁻¹) ∈ O.map π
    have hZbot : Z.map π = ⊥ := QuotientGroup.map_mk'_self Z
    have h2 : π (τ x * x⁻¹) ∈ Z.map π ⊔ O.map π := by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem π hx
    rw [hZbot] at h2
    simpa using h2
  obtain ⟨u', hu'mem, hu'fix⟩ := lit_odd_fixed σ hσ hN hoddN (y := π x) hyN
  have huN : u' ∈ O.map π := hu'mem
  obtain ⟨u, huO, rfl⟩ := (Subgroup.mem_map (f := π) (K := O)).mp huN
  refine ⟨u, huO, ?_⟩
  have hfix : σ (π (x * u)) = π (x * u) := by
    simpa only [map_mul] using hu'fix
  have hker : π (τ (x * u) * (x * u)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hcongr (x * u), hfix, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff (τ (x * u) * (x * u)⁻¹)).mp hker

theorem lit_fix_le {X G : Type*} [Group X] [Finite X] [Group G] {π : X →* G} {Z : Subgroup X}
    [Z.Normal] {τ : X ≃* X} {σ : G ≃* G} (d : LitTData π Z τ σ) {y : G} (hy : σ y = y) :
    y ∈ (litTSub τ Z).map π := by
  obtain ⟨x, rfl⟩ := d.surj y
  have hx : τ x * x⁻¹ ∈ Z ⊔ CFSG.oddCore X := by
    have h1 : π (τ x * x⁻¹) = 1 := by
      rw [map_mul, map_inv, ← d.comm x, hy, mul_inv_cancel]
    have h2 : τ x * x⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr h1
    rw [d.ker] at h2
    exact h2
  have hO : ∀ a ∈ CFSG.oddCore X, τ a ∈ CFSG.oddCore X := fun a ha =>
    (Subgroup.characteristic_iff_map_le.mp (lit_oddCore_characteristic X) τ) ⟨a, ha, rfl⟩
  obtain ⟨u, huO, hu⟩ :=
    lit_odd_fixed_mod (Z := Z) (O := CFSG.oddCore X) τ d.invol d.Z_inv hO
      (lit_odd_card_oddCore X) hx
  have hπu : π u = 1 := by
    have hker : u ∈ π.ker := by
      rw [d.ker]
      exact (le_sup_right : CFSG.oddCore X ≤ Z ⊔ CFSG.oddCore X) huO
    exact MonoidHom.mem_ker.mp hker
  refine ⟨x * u, hu, ?_⟩
  rw [map_mul, hπu, mul_one]

end CFSG.OddStandard.HigherRank.YamadaG23
