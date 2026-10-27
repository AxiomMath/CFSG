module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

@[expose] noncomputable def sec9ciPsiB {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {B : Subgroup G} (hBL : B ≤ L) :
    ↥B →* ProjSim Q :=
  (ffInducesHom hm e).comp (Subgroup.inclusion (hBL.trans Subgroup.le_normalizer))

theorem sec9ciPsiB_apply {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {B : Subgroup G} (hBL : B ≤ L) (c : ↥B) :
    sec9ciPsiB hm e hBL c = ffInducesHom hm e ⟨(c : G), Subgroup.le_normalizer (hBL c.2)⟩ :=
  rfl

theorem sec9ciPsiB_injective [Finite G] {L : Subgroup G} (hL : IsOm6M L) {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) : Function.Injective (sec9ciPsiB hm e hBL) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hc1 : ffInducesHom hm e ⟨(c : G), Subgroup.le_normalizer (hBL c.2)⟩ = 1 := by
    rw [← sec9ciPsiB_apply hm e hBL c]
    exact hc
  have hcent : (c : G) ∈ Subgroup.centralizer (L : Set G) :=
    (ffInducesHom_eq_one_iff hm e hperf _).mp hc1
  have hcZ : (c : G) ∈ centerIn L := (sec4_mem_centerIn_iff (c : G)).mpr
    ⟨hBL c.2, fun k hk => (Subgroup.mem_centralizer_iff.mp hcent k hk).symm⟩
  have hc2 : (c : G) * (c : G) = 1 := by
    rw [← pow_two]
    exact hB.1.2 (c : G) c.2
  exact Subtype.ext (sec9g_centerIn_sq_eq_one hL hcZ hc2)

theorem sec9ci_lift_cycle [Finite G] {L : Subgroup G} (hL : IsOm6M L) {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) {s : G} (hss : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) (F : Subgroup (ProjSim Q))
    (hFB : ∀ (b : G) (hb : b ∈ B), ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ ∈ F)
    (hBF : ∀ f ∈ F, ∃ (b : G) (hb : b ∈ B),
      ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ = f)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} (hb : IsEvenFrame b (F.comap (phiSim Q)))
    (hn : 3 ≤ n) (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) {j : Fin n} {r : OGroup Q}
    (hr : phiSim Q r = ffInducesHom hm e ⟨s, hsN⟩)
    (hrb : ∀ i, (r : V ≃ₗ[ZMod 3] V) (b i) = (if i = j then (-1 : ZMod 3) else 1) • b i)
    {u v w : Fin n} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (huj : u ≠ j) (hvj : v ≠ j)
    (hwj : w ≠ j) :
    ∃ (g : OGroup Q) (y : G) (hy : y ∈ L),
      (∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = b ((Equiv.swap u w * Equiv.swap u v) i)) ∧
      g * g * g = 1 ∧ y * s = s * y ∧ y ∈ Subgroup.normalizer (B : Set G) ∧
      Odd (orderOf y) ∧ ffInducesHom hm e ⟨y, Subgroup.le_normalizer hy⟩ = phiSim Q g := by
  have hpol : ∀ i k : Fin n, i ≠ k → QuadraticMap.polar Q (b i) (b k) = 0 :=
    fun i k hik => IsEvenFrame.polar_eq_zero hb hn hik
  have hne : ∀ i : Fin n, Q (b i) ≠ 0 := fun i => IsEvenFrame.map_ne_zero hQ hb hn i
  obtain ⟨g, hgΩ, hgact, hg3⟩ := sec9ci_exists_cycle hQ hpol hc hne huv huw hvw
  have hfΩ : SimInOmegaStar hQ (phiSim Q g) :=
    ⟨toProj Q g, (mem_omegaProj_iff hQ).mpr ⟨g, hgΩ, rfl⟩, rfl⟩
  have hodd : Odd (orderOf (phiSim Q g)) := by
    have h3 : phiSim Q g ^ 3 = 1 := by
      rw [pow_three', ← map_mul, ← map_mul, hg3, map_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h <;>
      rw [h] <;> decide
  have hτj : (Equiv.swap u w * Equiv.swap u v) j = j := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huj.symm hvj.symm,
      Equiv.swap_apply_of_ne_of_ne huj.symm hwj.symm]
  have hgr : g * r = r * g := by
    have hd : ∀ i, (r : V ≃ₗ[ZMod 3] V) (b i) =
        (if i ∈ ({j} : Finset (Fin n)) then (-1 : ZMod 3) else 1) • b i := by
      intro i
      rw [hrb i]
      simp only [Finset.mem_singleton]
    have hconj := sec9ci_perm_conj_diag hgact hd
    have h : g * r * g⁻¹ = r := by
      refine sec9ci_ext (b := b) fun i => ?_
      rw [hconj i, hrb i]
      simp only [Finset.map_singleton, Equiv.coe_toEmbedding, hτj, Finset.mem_singleton]
    exact mul_inv_eq_iff_eq_mul.mp h
  have hfs : phiSim Q g * ffInducesHom hm e ⟨s, hsN⟩ = ffInducesHom hm e ⟨s, hsN⟩ * phiSim Q g := by
    rw [← hr, ← map_mul, ← map_mul, hgr]
  have hfF : ∀ f' ∈ F, phiSim Q g * f' * (phiSim Q g)⁻¹ ∈ F := by
    intro f' hf'
    by_cases h1 : f' = 1
    · rw [h1, mul_one, mul_inv_cancel]
      exact F.one_mem
    · obtain ⟨t, -, htf⟩ := hlift f' hf' h1
      have htFt : t ∈ F.comap (phiSim Q) := by
        rw [Subgroup.mem_comap, htf]
        exact hf'
      obtain ⟨S, hSe, hSd⟩ := (IsEvenFrame.mem_iff hb).mp htFt
      have hconj := sec9ci_perm_conj_diag hgact hSd
      have hmem : g * t * g⁻¹ ∈ F.comap (phiSim Q) :=
        (IsEvenFrame.mem_iff hb).mpr ⟨S.map (Equiv.swap u w * Equiv.swap u v).toEmbedding,
          by rw [Finset.card_map]; exact hSe, hconj⟩
      have h2 : phiSim Q (g * t * g⁻¹) ∈ F := hmem
      rwa [map_mul, map_mul, map_inv, htf] at h2
  obtain ⟨y, hy, hys, hyN, hyodd, hyf⟩ :=
    sec9ci_lift_odd hL hm e hss hsN hBL hB F hFB hBF hfΩ hfs hfF hodd
  exact ⟨g, y, hy, hgact, hg3, hys, hyN, hyodd, hyf⟩

end CFSG.OddStandard.SmallF3.Omega
