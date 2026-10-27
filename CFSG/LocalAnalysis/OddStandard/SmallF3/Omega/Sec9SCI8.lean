module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem sec9ci_exists_inv (hT6 : Asc82Tab6M) [Finite G] {L : Subgroup G} (hL : IsOm6M L)
    {hQ : Q.Nondegenerate} (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) {s : G} (hs2 : orderOf s = 2)
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) (hne : layerCent L s ≠ ⊥)
    (F : Subgroup (ProjSim Q))
    (hFB : ∀ (b : G) (hb : b ∈ B), ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ ∈ F)
    (hBF : ∀ f ∈ F, ∃ (b : G) (hb : b ∈ B),
      ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ = f)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} (hb : IsEvenFrame b (F.comap (phiSim Q)))
    (hn : 3 ≤ n) (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) {j : Fin n} {r : OGroup Q}
    (hr : phiSim Q r = ffInducesHom hm e ⟨s, hsN⟩)
    (hrb : ∀ i, (r : V ≃ₗ[ZMod 3] V) (b i) = (if i = j then (-1 : ZMod 3) else 1) • b i)
    {u v w z : Fin n} (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z)
    (hwz : w ≠ z) (huj : u ≠ j) (hvj : v ≠ j) (hwj : w ≠ j) (hzj : z ≠ j) :
    ∃ (g : OGroup Q) (x : G),
      (∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = b ((Equiv.swap u v * Equiv.swap w z) i)) ∧
      x ∈ layerCent L s ∧ x ∈ Subgroup.normalizer (B : Set G) ∧ x * x = 1 ∧
      ∀ c d : ↥B, (d : G) = x * c * x⁻¹ →
        sec9ciPsiB hm e hBL d = phiSim Q g * sec9ciPsiB hm e hBL c * (phiSim Q g)⁻¹ := by
  have hperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    exact h
  obtain ⟨g₁, y₁, hy₁, hg₁, -, hy₁s, hy₁N, hy₁odd, hy₁f⟩ :=
    sec9ci_lift_cycle hL hm e hBL hB hss hsN F hFB hBF hlift hb hn hc hr hrb huv huw hvw huj hvj
      hwj
  obtain ⟨g₂, y₂, hy₂, hg₂, -, hy₂s, hy₂N, hy₂odd, hy₂f⟩ :=
    sec9ci_lift_cycle hL hm e hBL hB hss hsN F hFB hBF hlift hb hn hc hr hrb hvw hvz hwz hvj hwj
      hzj
  have hy₁c : y₁ ∈ twoRes (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    Subgroup.subset_closure ⟨⟨hy₁, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hy₁s.symm⟩, hy₁odd⟩
  have hy₂c : y₂ ∈ twoRes (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    Subgroup.subset_closure ⟨⟨hy₂, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hy₂s.symm⟩, hy₂odd⟩
  have hmL : y₁ * y₂ ∈ L := L.mul_mem hy₁ hy₂
  have hm3 : y₁ * y₂ ∈ twoRes (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    Subgroup.mul_mem _ hy₁c hy₂c
  have hmN : y₁ * y₂ ∈ Subgroup.normalizer (B : Set G) := Subgroup.mul_mem _ hy₁N hy₂N
  obtain ⟨g, hgdef⟩ : ∃ g : OGroup Q, g = g₁ * g₂ := ⟨_, rfl⟩
  have hΦm : ffInducesHom hm e ⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩ = phiSim Q g := by
    have h : (⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨y₁, Subgroup.le_normalizer hy₁⟩ * ⟨y₂, Subgroup.le_normalizer hy₂⟩ := Subtype.ext rfl
    rw [h, map_mul, hy₁f, hy₂f, hgdef, map_mul]
  have hg : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = b ((Equiv.swap u v * Equiv.swap w z) i) := by
    intro i
    rw [hgdef, sec9ci_swap_mul_swap huv huw huz hvw hvz hwz]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hg₁, hg₂, Equiv.Perm.mul_apply]
  have hgg : g * g = 1 := by
    refine sec9ci_ext (b := b) fun i => ?_
    have hσ : (Equiv.swap u v * Equiv.swap w z) ((Equiv.swap u v * Equiv.swap w z) i) = i := by
      simpa using Equiv.Perm.ext_iff.mp (sec9ci_dbl_sq huv huw huz hvw hvz hwz) i
    show (g : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (b i)) = b i
    rw [hg i, hg, hσ]
  have hm4 : (y₁ * y₂) ^ 2 ∈ centerIn L := by
    have h1 : ffInducesHom hm e ⟨(y₁ * y₂) ^ 2, Subgroup.le_normalizer (L.pow_mem hmL 2)⟩ = 1 := by
      have h : (⟨(y₁ * y₂) ^ 2, Subgroup.le_normalizer (L.pow_mem hmL 2)⟩ :
          ↥(Subgroup.normalizer (L : Set G))) =
          ⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩ * ⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩ :=
        Subtype.ext (pow_two _)
      rw [h, map_mul, hΦm, ← map_mul, hgg, map_one]
    have hcent := (ffInducesHom_eq_one_iff hm e hperf _).mp h1
    exact (sec4_mem_centerIn_iff _).mpr ⟨L.pow_mem hmL 2, fun k hk =>
      (Subgroup.mem_centralizer_iff.mp hcent k hk).symm⟩
  obtain ⟨x, hxl, hxx, hxc⟩ := sec9ci_exists_layer_inv hT6 hL hs2 hsN hne hm3 hm4
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    have hfwd : ∀ h ∈ B, x * h * x⁻¹ ∈ B := fun h hh => by
      rw [hxc h (hBL hh)]
      exact (Subgroup.mem_normalizer_iff.mp hmN h).mp hh
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨hfwd h, fun hh => ?_⟩
    have h2 := hfwd _ hh
    have e1 : x * (x * h * x⁻¹) * x⁻¹ = h := by
      have : x * (x * h * x⁻¹) * x⁻¹ = (x * x) * h * (x * x)⁻¹ := by group
      rw [this, hxx]; simp
    rwa [e1] at h2
  refine ⟨g, x, hg, hxl, hxN, hxx, fun c d hd => ?_⟩
  have hd' : (d : G) = (y₁ * y₂) * (c : G) * (y₁ * y₂)⁻¹ := hd.trans (hxc c (hBL c.2))
  have h : (⟨(d : G), Subgroup.le_normalizer (hBL d.2)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩ * ⟨(c : G), Subgroup.le_normalizer (hBL c.2)⟩ *
        ⟨y₁ * y₂, Subgroup.le_normalizer hmL⟩⁻¹ := Subtype.ext hd'
  rw [sec9ciPsiB_apply, sec9ciPsiB_apply, h, map_mul, map_mul, map_inv, hΦm]

end CFSG.OddStandard.SmallF3.Omega
