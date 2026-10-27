module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSClos
public import CFSG.ClassicalInvolution.Q3.Q3T6DC5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t)
include d

theorem s_lam_of_adj {a₀ : G} (hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G)) {ρ : G}
    (hρ : ρ ∈ Subgroup.centralizer ({a₀} : Set G)) (hρt : ρ * t * ρ⁻¹ = z)
    {K₁ K₂ L₂ : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    (hz₁ : IsUniqueInvolution K₁ z) (htw : twinSet (CoreAssembly.conjClass K) K₁ = {K₁, K₂})
    (hsup : K₁ ⊔ K₂ = K ⊔ K') (hadj : aGraphAdj (CoreAssembly.conjClass K) K₁ L₂) :
    LamMem z a₀ L₂ := by
  have hΩ := d.late_hΩ
  have key : ∀ {L₂ : Subgroup G} {t₂ : G},
      AViol (CoreAssembly.conjClass K) K₁ L₂ z t₂ → LamMem z a₀ L₂ := by
    intro L₂ t₂ h
    have ht₂mem : t₂ ∈ K ⊔ K' := hsup ▸ t_mem_sup_of_aviolGen hΩ hK₁ h htw
    have ht₂z : t₂ ≠ z := AViol.ne_involution_gen hΩ hK₁ h
    obtain ⟨m, hm, hmt⟩ := exists_conj_of_involutions_sup_modGen d.hyp d.late_mem_K
      d.late_mem_K' d.ne d.viol.hzK d.late_hzK' d.htKK d.viol.hzJ.sq d.viol.hzJ.ne_one
      d.late_ne_inv ht₂mem h.hzJ.sq h.hzJ.ne_one ht₂z
    have hmc : m⁻¹ ∈ Subgroup.centralizer ({a₀} : Set G) :=
      (Subgroup.centralizer _).inv_mem (hcM hm)
    refine ⟨ρ * m⁻¹, (Subgroup.centralizer _).mul_mem hρ hmc, t₂, h.hzJ, ?_⟩
    calc ρ * m⁻¹ * t₂ * (ρ * m⁻¹)⁻¹ = ρ * (m⁻¹ * (m * t * m⁻¹) * m) * ρ⁻¹ := by rw [hmt]; group
      _ = ρ * t * ρ⁻¹ := by group
      _ = z := hρt
  obtain ⟨hL₂, h | h | ht⟩ := hadj
  · obtain ⟨zK, zJ, hv⟩ := h
    have hzz : zK = z := hv.hzK.eq hz₁
    subst hzz
    exact key hv
  · obtain ⟨zL, zK, hv⟩ := h
    have hzz : zK = z := hv.hzJ.eq hz₁
    subst hzz
    exact key (aviol_symmGen hΩ hL₂ hv)
  · obtain ⟨-, z', hz'K, hz'L⟩ := ht.1
    have hzz : z' = z := hz'K.eq hz₁
    subst hzz
    exact ⟨1, Subgroup.one_mem _, z', hz'L, by group⟩

theorem s_aStar_lam {a₀ : G} (hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G)) {ρ : G}
    (hρ : ρ ∈ Subgroup.centralizer ({a₀} : Set G)) (hρt : ρ * t * ρ⁻¹ = z) :
    ∀ L, Relation.ReflTransGen (aGraphAdj (CoreAssembly.conjClass K)) K L →
      L ∈ CoreAssembly.conjClass K ∧ LamMem z a₀ L := by
  intro L hL
  induction hL with
  | refl => exact ⟨d.late_mem_K, 1, Subgroup.one_mem _, z, d.viol.hzK, by group⟩
  | @tail L₁ L₂ _ hadj ih =>
    obtain ⟨hL₁, n, hn, e, he, hne⟩ := ih
    have hmem : conjSub n L₁ ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨d.hyp.conjInvariant n L₁ hL₁, z, d.viol.hzK, hne ▸ he.conj n⟩
    have hadj' := aGraphAdj_conj' d.hyp.conjInvariant hadj n
    refine ⟨hadj.1, LamMem.of_conj hn ?_⟩
    rw [d.twins] at hmem
    rcases hmem with h | h
    · rw [h] at hadj'
      exact d.s_lam_of_adj hcM hρ hρt d.late_mem_K d.viol.hzK d.twins rfl hadj'
    · rw [h] at hadj'
      exact d.s_lam_of_adj hcM hρ hρt d.late_mem_K' d.late_hzK' d.twinSet_K' (sup_comm _ _) hadj'

theorem s_cent_false [FrameSimple G] {a₀ : G} (ha1 : a₀ ≠ 1)
    (haK : ∀ k ∈ K, a₀ * k = k * a₀) (haK' : ∀ k ∈ K', a₀ * k = k * a₀)
    (haJ : ∀ j ∈ J, a₀ * j = j * a₀) : False := by
  have hKc : K ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haK k hk).symm
  have hK'c : K' ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haK' k hk).symm
  have hJc : J ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haJ k hk).symm
  have hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G) := sup_le hKc hK'c
  obtain ⟨ρ, hρ, hρt⟩ := d.exists_rho hKc hJc
  have hΩc := d.hyp.conjInvariant
  have hstar : ∀ L ∈ CoreAssembly.conjClass K, LamMem z a₀ L := fun L hL => by
    have hLs : L ∈ aStar (CoreAssembly.conjClass K) K := by rw [d.star]; exact hL
    exact (d.s_aStar_lam hcM hρ hρt L hLs).2
  have hall : ∀ L ∈ CoreAssembly.conjClass K, ∀ l ∈ L, a₀ * l = l * a₀ := by
    intro L hL
    refine (hstar L hL).cent fun n hn e he hne l hl => ?_
    have hmem : conjSub n L ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨hΩc n L hL, z, d.viol.hzK, hne ▸ he.conj n⟩
    have hl' : n * l * n⁻¹ ∈ conjSub n L := ⟨l, hl, rfl⟩
    rw [d.twins] at hmem
    rcases hmem with h | h
    · rw [h] at hl'
      exact haK _ hl'
    · rw [h] at hl'
      exact haK' _ hl'
  have htop := d.branch.gen
  have hcent : ∀ g : G, a₀ * g = g * a₀ := by
    intro g
    have hle : (⨆ L ∈ CoreAssembly.conjClass K, L) ≤ Subgroup.centralizer ({a₀} : Set G) :=
      iSup₂_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hall L hL l hl).symm
    have : g ∈ Subgroup.centralizer ({a₀} : Set G) := hle (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hnab := d.branch.nonabelian
  have : a₀ ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hcent g).symm
  rw [FrameSimple.center hnab, Subgroup.mem_bot] at this
  exact ha1 this

end Std20Three

@[expose] def Res20_7Hyp51Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_4 S K K' J z → ∀ a : G,
        a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J → a ≠ 1 →
          a * a = 1 → Hyp51 (Subgroup.closure ({z, t, a} : Set G))

theorem res20_7NoC3_of_hyp51Three (hH : Res20_7Hyp51Three) :
    ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
      (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
        Concl20_4 S K K' J z → Concl20_7 S K K' z := by
  intro G _ _ _ K K' J S R R' W V z t d c4
  show centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z
  have hA' : centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    by_contra ha1
    have haS : a ∈ (S : Subgroup G) := ha.1.1
    have hp2 : IsPGroup 2 ↥(Subgroup.zpowers a) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)
    obtain ⟨n, hn2, hn1⟩ := late_exists_pow_invol hp2 ha1
    have hnA : a ^ n ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J :=
      Subgroup.pow_mem _ ha n
    have hcfg : AlphaCfg3 S K K' J z t (a ^ n) :=
      ⟨hnA, hn1, hn2, c4, hH G K K' J S R R' W V z t d c4 (a ^ n) hnA hn1 hn2⟩
    exact d.s_cent_false hn1 (hcfg.comm_K d) (hcfg.comm_K' d) (hcfg.comm_J d)
  rw [c4.1, hA', bot_sup_eq]

theorem res20_7_of_hyp51Three (hH : Res20_7Hyp51Three) : Res20_7Three := by
  intro G _ _ _ K K' J S R R' W V z t d _ c4
  exact res20_7NoC3_of_hyp51Three hH G K K' J S R R' W V z t d c4

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
