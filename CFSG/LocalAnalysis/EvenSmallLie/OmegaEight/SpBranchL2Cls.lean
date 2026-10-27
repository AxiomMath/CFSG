module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillSpec

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ} (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N)

include Φ h0 hinv hgens hG in
theorem exists_rep {C : List (ℕ × ℕ)} (rec : ℕ → List (ℕ × ℕ))
    (hnd : (C.map Prod.fst).Nodup)
    (hrecC : ∀ r ∈ C, r.1 < N ∧ mul r.1 r.1 = 0 ∧ r.1 ≠ 0 ∧
      orbOK mul inv N r.1 (rec r.1) = true ∧ orbClosed mul inv gens r.1 (rec r.1) = true ∧
      (rec r.1).length = r.2 ∧ ∀ p ∈ rec r.1, r.1 ≤ p.1)
    (hsumC : (C.map Prod.snd).sum = (kInv mul N).length) {u : H} (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ c ∈ C, ∃ g : H, g * Φ.g c.1 * g⁻¹ = u ∧
      (MulAction.orbit (ConjAct H) u).ncard = c.2 := by
  classical
  have hfin := Φ.finite
  obtain ⟨D, hD⟩ : ∃ D : List ℕ, D = C.map Prod.fst := ⟨_, rfl⟩
  rw [← hD] at hnd
  have hrec : ∀ r ∈ D, r < N ∧ mul r r = 0 ∧ r ≠ 0 ∧
      orbOK mul inv N r (rec r) = true ∧ orbClosed mul inv gens r (rec r) = true ∧
      ∀ p ∈ rec r, r ≤ p.1 := by
    intro r hr
    rw [hD] at hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hrecC c hc
    exact ⟨h1, h2, h3, h4, h5, h7⟩
  have hsum : (D.map fun r => (rec r).length).sum = (kInv mul N).length := by
    rw [hD, List.map_map, ← hsumC]
    refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
    rw [Function.comp_apply]
    exact (hrecC c hc).2.2.2.2.2.1
  have hmem : Φ.f u ∈ kInv mul N := (mem_kInv).2 ⟨Φ.lt u, (f_mul_self_eq_zero Φ h0 u).2 hu2,
    fun h => hu1 ((f_eq_zero Φ h0 u).1 h)⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Finset ℕ, A = fun r => ((rec r).map Prod.fst).toFinset := ⟨_, rfl⟩
  have hAmem : ∀ r ∈ D, ∀ x : H, x ∈ MulAction.orbit (ConjAct H) (Φ.g r) ↔ Φ.f x ∈ A r := by
    intro r hr x
    obtain ⟨hrl, -, -, hO, hCl, -⟩ := hrec r hr
    rw [hA, List.mem_toFinset]
    exact Φ.mem_orbit_iff h0 hinv hgens hG (O := rec r)
      ((Φ.f_g hrl).symm ▸ hO) ((Φ.f_g hrl).symm ▸ hCl) x
  have hAlt : ∀ r ∈ D, ∀ y ∈ A r, y < N := by
    intro r hr y hy
    obtain ⟨hrl, -, -, hO, -, -⟩ := hrec r hr
    rw [hA, List.mem_toFinset] at hy
    obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv (u := Φ.g r)
      (O := rec r) ((Φ.f_g hrl).symm ▸ hO) hy
    rw [← hg]
    exact Φ.lt _
  have hAsub : ∀ r ∈ D, A r ⊆ (kInv mul N).toFinset := by
    intro r hr y hy
    obtain ⟨hrl, hr2, hr0, -, -, -⟩ := hrec r hr
    have hyl := hAlt r hr y hy
    have hyo := (hAmem r hr (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    obtain ⟨g, hg⟩ := mem_orbit_iff_conj.1 hyo
    have hgr2 : Φ.g r * Φ.g r = 1 := (f_mul_self_eq_zero Φ h0 _).1 (by rwa [Φ.f_g hrl])
    have hgr1 : Φ.g r ≠ 1 := fun h => hr0 (by rw [← Φ.f_g hrl, h]; exact Φ.f_one h0)
    rw [List.mem_toFinset, mem_kInv]
    refine ⟨hyl, ?_, fun h => ?_⟩
    · rw [← Φ.f_g hyl, ← hg]
      refine (f_mul_self_eq_zero Φ h0 _).2 ?_
      calc g * Φ.g r * g⁻¹ * (g * Φ.g r * g⁻¹) = g * (Φ.g r * Φ.g r) * g⁻¹ := by group
        _ = 1 := by rw [hgr2]; group
    · have h1 : Φ.g y = 1 := by rw [h, ← Φ.f_one h0, Φ.g_f]
      rw [h1] at hg
      refine hgr1 ?_
      have e : Φ.g r = g⁻¹ * (g * Φ.g r * g⁻¹) * g := by group
      rw [e, hg]
      group
  have hdisj : ∀ r ∈ D, ∀ s ∈ D, r ≠ s → Disjoint (A r) (A s) := by
    intro r hr s hs hrs
    refine Finset.disjoint_left.2 fun y hyr hys => hrs ?_
    have hyl := hAlt r hr y hyr
    have h1 := (hAmem r hr (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    have h2 := (hAmem s hs (Φ.g y)).2 (by rwa [Φ.f_g hyl])
    have hrs' : MulAction.orbit (ConjAct H) (Φ.g r) = MulAction.orbit (ConjAct H) (Φ.g s) := by
      rw [← MulAction.orbit_eq_iff.2 h1, ← MulAction.orbit_eq_iff.2 h2]
    have hrl := (hrec r hr).1
    have hsl := (hrec s hs).1
    have hrA : r ∈ A s := by
      have := (hAmem s hs (Φ.g r)).1 (by rw [← hrs']; exact MulAction.mem_orbit_self _)
      rwa [Φ.f_g hrl] at this
    have hsA : s ∈ A r := by
      have := (hAmem r hr (Φ.g s)).1 (by rw [hrs']; exact MulAction.mem_orbit_self _)
      rwa [Φ.f_g hsl] at this
    rw [hA, List.mem_toFinset, List.mem_map] at hrA hsA
    obtain ⟨p, hp, hpr⟩ := hrA
    obtain ⟨q, hq, hqs⟩ := hsA
    have := (hrec s hs).2.2.2.2.2 p hp
    have := (hrec r hr).2.2.2.2.2 q hq
    omega
  have hcardA : ∀ r ∈ D, (A r).card = (rec r).length := by
    intro r hr
    rw [hA, List.toFinset_card_of_nodup (nodup_of_orbOK (hrec r hr).2.2.2.1), List.length_map]
  have hbu : D.toFinset.biUnion A = (kInv mul N).toFinset := by
    refine Finset.eq_of_subset_of_card_le
      (Finset.biUnion_subset.2 fun r hr => hAsub r (List.mem_toFinset.1 hr)) ?_
    rw [Finset.card_biUnion (fun r hr s hs hrs =>
      hdisj r (List.mem_toFinset.1 hr) s (List.mem_toFinset.1 hs) hrs),
      List.toFinset_card_of_nodup (by unfold kInv; exact (List.nodup_range).filter _), ← hsum,
      ← List.sum_toFinset _ hnd]
    exact (Finset.sum_congr rfl fun r hr => hcardA r (List.mem_toFinset.1 hr)).ge
  have hfu : Φ.f u ∈ D.toFinset.biUnion A := by rw [hbu]; exact List.mem_toFinset.2 hmem
  obtain ⟨r, hrC, hur⟩ := Finset.mem_biUnion.1 hfu
  have hr := List.mem_toFinset.1 hrC
  have hrl := (hrec r hr).1
  have huo := (hAmem r hr u).2 hur
  obtain ⟨g, hg⟩ := mem_orbit_iff_conj.1 huo
  have hrD := hr
  rw [hD] at hrD
  obtain ⟨c, hc, hcr⟩ := List.mem_map.1 hrD
  refine ⟨c, hc, g, by rw [hcr]; exact hg, ?_⟩
  obtain ⟨-, -, -, hO, hCl, -⟩ := hrec r hr
  rw [MulAction.orbit_eq_iff.2 huo, Φ.ncard_eq h0 hinv hgens hG (u := Φ.g r) (O := rec r)
    ((Φ.f_g hrl).symm ▸ hO) ((Φ.f_g hrl).symm ▸ hCl), ← hcr]
  exact (hrecC c hc).2.2.2.2.2.1

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
