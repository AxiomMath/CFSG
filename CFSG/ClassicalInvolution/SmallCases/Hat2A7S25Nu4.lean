module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu3
public import CFSG.ClassicalInvolution.Asc77.AscC25I1
public import CFSG.ClassicalInvolution.Asc77.AscC25H6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.Eps

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' t₀ : G}
  {π : OddQuot K →* A7} {zE : OddQuot K}


theorem swap_inv (hsw : C25I.IsSwap K K' z t₀) : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right hsw.sq

theorem swap_swapK' (hsw : C25I.IsSwap K K' z t₀) : conjSub t₀ K' = K := by
  have h1 : conjSub (t₀ * t₀) K = K := by rw [hsw.sq, conjSub_one]
  rwa [conjSub_mul, hsw.swapK] at h1

theorem swap_conj_mem_normalizer (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : C25I.IsSwap K K' z t₀) {x : G} (hxz : x * z = z * x) (hxK : conjSub x K = K) :
    t₀ * x * t₀ ∈ Subgroup.normalizer (K : Set G) := by
  have hxK' : conjSub x K' = K' := (N.cz_fix_iff h hxz).mp hxK
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub_mul, conjSub_mul, hsw.swapK, hxK', swap_swapK' hsw]

theorem swap_cover (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (hsw : C25I.IsSwap K K' z t₀)
    {g : G} (hg : g * z = z * g) : conjSub g K = K ∨ conjSub (g * t₀) K = K := by
  rcases N.cz_conj_K h hg with h1 | h1
  · exact Or.inl h1
  · right
    rw [conjSub_mul, hsw.swapK]
    rcases N.cz_conj_K' h hg with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans ((N.cz_fix_iff h hg).mpr h2)) h.hs.hne

theorem triv_of_triv_swap (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE)
    (hsw : C25I.IsSwap K K' z t₀) {y : G} (hy : y ∈ Triv cov z t₀ hsw.sq) :
    y ∈ Triv cov z t' h.ht'2 := by
  have htz : t' * z = z * t' := N.t'_comm_z h
  have hwz : (t₀ * t') * z = z * (t₀ * t') :=
    ((show Commute t₀ z from hsw.comm).mul_left (show Commute t' z from htz)).eq
  have hwK : conjSub (t₀ * t') K = K := by
    rw [conjSub_mul, N.conjSub_t'_K h, swap_swapK' hsw]
  have hwN : t₀ * t' ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hwK
  have hct : t₀ * (t₀ * t') * t₀ ∈ Subgroup.normalizer (K : Set G) :=
    swap_conj_mem_normalizer h hsw hwz hwK
  have hy2 := triv_conj_of_normalizer hwN hwz hct hy
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  obtain ⟨-, -, hN2, -, hν2⟩ := hy2
  have e1 : t' * y * t' = t₀ * ((t₀ * t') * y * (t₀ * t')⁻¹) * t₀ := by
    rw [mul_inv_rev, h.ht'inv, swap_inv hsw]
    calc t' * y * t' = (t₀ * t₀) * t' * y * t' * (t₀ * t₀) := by rw [hsw.sq]; group
      _ = t₀ * (t₀ * t' * y * (t' * t₀)) * t₀ := by group
  refine ⟨hN, hz, ?_, hν, ?_⟩
  · rw [e1]
    exact hN2
  · rw [e1]
    exact hν2

theorem exists_k_nuG' (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE)
    {a n : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hε : epsG cov n = epsG cov (t₀ * n * t₀) * epsG cov a) :
    ∃ k ∈ K, nuG cov k = nuG cov ((t₀ * n * t₀) * (a * z) * n⁻¹) := by
  classical
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hazN : a * z ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ haK hzK
  have hmN : (t₀ * n * t₀) * (a * z) * n⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK)
  have hνm : nuG cov ((t₀ * n * t₀) * (a * z) * n⁻¹) =
      nuG cov (t₀ * n * t₀) * nuG cov a * (nuG cov n)⁻¹ := by
    rw [nuG_mul cov (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK),
      nuG_mul cov hn'K hazN, nuG_mul cov haK hzK, nuG_inv cov hnK, nuG_z_eq_one h cov, mul_one]
  have hεm : epsG cov ((t₀ * n * t₀) * (a * z) * n⁻¹) = 1 := by
    have hε' : Equiv.Perm.sign (nuG cov n) =
        Equiv.Perm.sign (nuG cov (t₀ * n * t₀)) * Equiv.Perm.sign (nuG cov a) := hε
    rw [epsG, hνm, map_mul, map_mul, map_inv, hε']
    exact mul_inv_cancel _
  obtain ⟨k, hkK, hk⟩ := exists_mem_K_nuG_eq_one_of_epsG_eq_one cov hmN hεm
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have h1 : nuG cov (k⁻¹ * ((t₀ * n * t₀) * (a * z) * n⁻¹)) =
      (nuG cov k)⁻¹ * nuG cov ((t₀ * n * t₀) * (a * z) * n⁻¹) := by
    rw [nuG_mul cov (Subgroup.inv_mem _ hkN) hmN, nuG_inv cov hkN]
  rw [h1] at hk
  exact ⟨k, hkK, inv_mul_eq_one.mp hk⟩

theorem exists_triv_conj' (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE)
    (hsw : C25I.IsSwap K K' z t₀) {a n : G} (ha2 : a * a = 1) (haz : a * z = z * a)
    (hat : a * t₀ = t₀ * a) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hnK : n ∈ Subgroup.normalizer (K : Set G)) (hnz : n * z = z * n)
    (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hε : epsG cov n = epsG cov (t₀ * n * t₀) * epsG cov a) :
    ∃ c m₁ : G, c * z = z * c ∧ m₁ ∈ Triv cov z t₀ hsw.sq ∧ t₀ * m₁ * t₀ = m₁⁻¹ ∧
      t₀ * m₁ = c * (a * z * t₀) * c⁻¹ := by
  classical
  have hsq : z * z = 1 := h.hz.sq
  have htz : t₀ * z = z * t₀ := hsw.comm
  have ht2 : t₀ * t₀ = 1 := hsw.sq
  have hti : t₀⁻¹ = t₀ := swap_inv hsw
  obtain ⟨k, hkK, hkν⟩ := exists_k_nuG' h cov haK hnK hn'K hε
  obtain ⟨n', hn'⟩ : ∃ n' : G, n' = t₀ * n * t₀ := ⟨_, rfl⟩
  rw [← hn'] at hn'K hkν
  obtain ⟨m, hm⟩ : ∃ m : G, m = n' * (a * z) * n⁻¹ := ⟨_, rfl⟩
  rw [← hm] at hkν
  obtain ⟨hmt, hmx⟩ := C25H.swap_m_facts ht2 hti haz ha2 hsq hat htz hn'
  rw [← hm] at hmt hmx
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hazN : a * z ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ haK hzK
  have hmN : m ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK)
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hk'K' : t₀ * k * t₀ ∈ K' := by
    have h1 := conj_mem_conjSub (n := t₀) hkK
    rw [hti, hsw.swapK] at h1
    exact h1
  have hk'N : t₀ * k * t₀ ∈ Subgroup.normalizer (K : Set G) :=
    h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz hk'K'
  have hνk' : nuG cov (t₀ * k * t₀) = 1 := by
    refine (nuG_eq_one_iff_comm cov hk'N).mpr (fun l hl => ?_)
    have hc := h.hΩ.comm_le_oddCore_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz
    exact (hc (Subgroup.commutator_mem_commutator hk'K' hl)).2
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : G, m₁ = (t₀ * k * t₀) * m * k⁻¹ := ⟨_, rfl⟩
  have hC1 : Commute t₀ z := htz
  have hkz : Commute k z := (h.hz.commute_of_mem hkK).symm
  have hk'z : Commute (t₀ * k * t₀) z := (hC1.mul_left hkz).mul_left hC1
  have hnz' : Commute n z := hnz
  have hn'z : Commute n' z := by rw [hn']; exact (hC1.mul_left hnz').mul_left hC1
  have hmz : Commute m z := by
    rw [hm]
    exact (hn'z.mul_left ((show Commute a z from haz).mul_left (Commute.refl z))).mul_left
      hnz'.inv_left
  have hm₁N : m₁ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm₁]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk'N hmN) (Subgroup.inv_mem _ hkN)
  have hm₁z : m₁ * z = z * m₁ := by
    rw [hm₁]
    exact (hk'z.mul_left hmz).mul_left hkz.inv_left
  have e0 : t₀ * (t₀ * k * t₀) * t₀ = k := by
    calc t₀ * (t₀ * k * t₀) * t₀ = (t₀ * t₀) * k * (t₀ * t₀) := by group
      _ = k := by rw [ht2]; group
  have e1 : t₀ * k⁻¹ * t₀ = (t₀ * k * t₀)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  have hm₁t : t₀ * m₁ * t₀ = k * m⁻¹ * (t₀ * k * t₀)⁻¹ := by
    calc t₀ * m₁ * t₀ = (t₀ * (t₀ * k * t₀) * t₀) * (t₀ * m * t₀) * (t₀ * k⁻¹ * t₀) := by
          rw [hm₁]
          calc t₀ * ((t₀ * k * t₀) * m * k⁻¹) * t₀ =
              t₀ * (t₀ * k * t₀) * (t₀ * t₀) * m * (t₀ * t₀) * k⁻¹ * t₀ := by rw [ht2]; group
            _ = _ := by group
      _ = k * m⁻¹ * (t₀ * k * t₀)⁻¹ := by rw [e0, hmt, e1]
  have hm₁t₀N : t₀ * m₁ * t₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm₁t]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N)
  have hνm₁ : nuG cov m₁ = 1 := by
    rw [hm₁, nuG_mul cov (Subgroup.mul_mem _ hk'N hmN) (Subgroup.inv_mem _ hkN),
      nuG_mul cov hk'N hmN, hνk', one_mul, nuG_inv cov hkN, hkν, mul_inv_cancel]
  have hνm₁t : nuG cov (t₀ * m₁ * t₀) = 1 := by
    rw [hm₁t, nuG_mul cov (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N), nuG_mul cov hkN (Subgroup.inv_mem _ hmN),
      nuG_inv cov hmN, nuG_inv cov hk'N, hνk', inv_one, mul_one, hkν, mul_inv_cancel]
  refine ⟨k * n, m₁, (hkz.mul_left hnz'), ⟨hm₁N, hm₁z, hm₁t₀N, hνm₁, hνm₁t⟩, ?_, ?_⟩
  · rw [hm₁t, hm₁]
    group
  · calc t₀ * m₁ = k * (t₀ * m) * k⁻¹ := by
          rw [hm₁]
          calc t₀ * ((t₀ * k * t₀) * m * k⁻¹) = (t₀ * t₀) * k * t₀ * m * k⁻¹ := by group
            _ = k * (t₀ * m) * k⁻¹ := by rw [ht2, one_mul]; group
      _ = k * (n * (a * z * t₀) * n⁻¹) * k⁻¹ := by rw [hmx]
      _ = (k * n) * (a * z * t₀) * (k * n)⁻¹ := by group

theorem exists_conj_azt' (h11 : Hat2A7M.Asc77.C25_11)
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE)
    (hsw : C25I.IsSwap K K' z t₀) {a n : G} (ha2 : a * a = 1) (haz : a * z = z * a)
    (hat : a * t₀ = t₀ * a) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hnK : n ∈ Subgroup.normalizer (K : Set G)) (hnz : n * z = z * n)
    (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hε : epsG cov n = epsG cov (t₀ * n * t₀) * epsG cov a)
    (hg : ∃ g : G, g * z * g⁻¹ = t₀) :
    (∃ g : G, g * z * g⁻¹ = a * z * t₀) ∨ (∃ g : G, g * z * g⁻¹ = a * t₀) := by
  have hsq : z * z = 1 := h.hz.sq
  have htz : t₀ * z = z * t₀ := hsw.comm
  obtain ⟨c, m₁, hcz, hm₁, hmt, hcm⟩ :=
    exists_triv_conj' h cov hsw ha2 haz hat haK hnK hnz hn'K hε
  have h2 : ∀ (i : ℕ) (y : G), y ∈ Subgroup.zpowers m₁ → orderOf y = 2 ^ i → y = 1 ∨ y = z :=
    fun i y hy hord => eq_one_or_eq_z_of_triv h11 h cov
      (triv_of_triv_swap h cov hsw ((Subgroup.zpowers_le.mpr hm₁) hy)) hord
  obtain ⟨g, ε, hgm, hε', hconj⟩ := C25H.exists_conj_mul_of_inverted hsw.sq hsq hmt h2
  have hgz : g * z = z * g := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgm
    exact (Commute.zpow_left (show Commute m₁ z from hm₁.2.1) j).eq
  obtain ⟨g₁, hg₁⟩ := hg
  have hb : a * z * t₀ = (c⁻¹ * g) * (t₀ * z ^ ε) * (c⁻¹ * g)⁻¹ := by
    calc a * z * t₀ = c⁻¹ * (c * (a * z * t₀) * c⁻¹) * c := by group
      _ = c⁻¹ * (t₀ * m₁) * c := by rw [hcm]
      _ = c⁻¹ * (g * (t₀ * z ^ ε) * g⁻¹) * c := by rw [hconj]
      _ = (c⁻¹ * g) * (t₀ * z ^ ε) * (c⁻¹ * g)⁻¹ := by group
  have hhz' : (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ = z := by
    have hc' : Commute c z := hcz
    have hg' : Commute g z := hgz
    have : Commute (c⁻¹ * g) z := hc'.inv_left.mul_left hg'
    calc (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ = (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ := rfl
      _ = z * (c⁻¹ * g) * (c⁻¹ * g)⁻¹ := by rw [this.eq]
      _ = z := by group
  interval_cases ε
  · left
    refine ⟨(c⁻¹ * g) * g₁, ?_⟩
    calc (c⁻¹ * g) * g₁ * z * ((c⁻¹ * g) * g₁)⁻¹ =
        (c⁻¹ * g) * (g₁ * z * g₁⁻¹) * (c⁻¹ * g)⁻¹ := by group
      _ = (c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ := by rw [hg₁]
      _ = a * z * t₀ := by rw [hb, pow_zero, mul_one]
  · right
    rw [pow_one] at hb
    have e1 : a * t₀ = (a * z * t₀) * z := by
      calc a * t₀ = a * (z * z) * t₀ := by rw [hsq, mul_one]
        _ = a * z * (z * t₀) := by group
        _ = a * z * (t₀ * z) := by rw [htz]
        _ = (a * z * t₀) * z := by group
    refine ⟨(c⁻¹ * g) * g₁, ?_⟩
    calc (c⁻¹ * g) * g₁ * z * ((c⁻¹ * g) * g₁)⁻¹ =
        (c⁻¹ * g) * (g₁ * z * g₁⁻¹) * (c⁻¹ * g)⁻¹ := by group
      _ = (c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ := by rw [hg₁]
      _ = ((c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹)) * z := by
          rw [hhz', mul_assoc _ z z, hsq, mul_one]
      _ = ((c⁻¹ * g) * (t₀ * z) * (c⁻¹ * g)⁻¹) * z := by group
      _ = (a * z * t₀) * z := by rw [← hb]
      _ = a * t₀ := e1.symm

end Main

end CFSG.ClassicalInvolution.Hat2A7S.Eps
