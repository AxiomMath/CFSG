module

public import CFSG.ClassicalInvolution.Asc77.AscT3SClos
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC5
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected

section Final

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem s_lam_of_adj {a₀ : G} (hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G)) {ρ : G}
    (hρ : ρ ∈ Subgroup.centralizer ({a₀} : Set G)) (hρt : ρ * t * ρ⁻¹ = z)
    {K₁ K₂ L₂ : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    (hz₁ : IsUniqueInvolution K₁ z) (htw : twinSet (CoreAssembly.conjClass K) K₁ = {K₁, K₂})
    (hsup : K₁ ⊔ K₂ = K ⊔ K') (hadj : aGraphAdj (CoreAssembly.conjClass K) K₁ L₂) :
    LamMem z a₀ L₂ := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩ := d.hyp
  have key : ∀ {L₂ : Subgroup G} {t₂ : G},
      AViol (CoreAssembly.conjClass K) K₁ L₂ z t₂ → LamMem z a₀ L₂ := by
    intro L₂ t₂ h
    have ht₂mem : t₂ ∈ K ⊔ K' := hsup ▸ t_mem_sup_of_aviol hp hq hΩ hK₁ h htw
    have ht₂z : t₂ ≠ z := h.ne_involution hΩ hK₁
    obtain ⟨m, hm, hmt⟩ := T3S.exists_conj_of_involutions_sup_mod hp hq hΩ d.late_mem_K
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
    exact key (aviol_symm hp hq hΩ hL₂ hv)
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

theorem s_cent_false [IsSimpleGroup G] {a₀ : G} (ha1 : a₀ ≠ 1)
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
  have htop := gen_conjClass K d.viol.hzK.mem d.viol.hzK.ne_one
  have hcent : ∀ g : G, a₀ * g = g * a₀ := by
    intro g
    have hle : (⨆ L ∈ CoreAssembly.conjClass K, L) ≤ Subgroup.centralizer ({a₀} : Set G) :=
      iSup₂_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hall L hL l hl).symm
    have : g ∈ Subgroup.centralizer ({a₀} : Set G) := hle (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hab : ∀ g h : G, g * h = h * g := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exfalso
      apply ha1
      have : a₀ ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hcent g).symm
      rw [h, Subgroup.mem_bot] at this
      exact this
    · intro g h'
      have : g ∈ Subgroup.center G := h ▸ Subgroup.mem_top g
      exact (Subgroup.mem_center_iff.mp this h').symm
  have : Group.IsPerfect ↥K := d.hyp.isPerfect d.late_mem_K
  have : Nontrivial ↥K :=
    ⟨⟨⟨z, d.viol.hzK.mem⟩, 1, fun h => d.viol.hzK.ne_one (congrArg Subtype.val h)⟩⟩
  have : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext (hab a b)⟩⟩
  exact Group.IsPerfect.not_isMulCommutative ↥K inferInstance

end Std20

end Final

section Main

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Res20_7Hyp51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_4 S K K' J z → ∀ a : G,
        a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J → a ≠ 1 →
          a * a = 1 → Hyp51 (Subgroup.closure ({z, t, a} : Set G))

@[expose] def Res20_7NoC3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_4 S K K' J z → Concl20_7 S K K' z

variable {p f}

theorem res20_7NoC3_of_hyp51 (hH : Res20_7Hyp51 p f) : Res20_7NoC3 p f := by
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
    have hcfg : AlphaCfg S K K' J z t (a ^ n) :=
      ⟨hnA, hn1, hn2, c4, hH G K K' J S R R' W V z t d c4 (a ^ n) hnA hn1 hn2⟩
    exact d.s_cent_false hn1 (hcfg.comm_K d) (hcfg.comm_K' d) (hcfg.comm_J d)
  rw [c4.1, hA', bot_sup_eq]

theorem res20_7_of_hyp51 (hH : Res20_7Hyp51 p f) : Res20_7 p f := by
  intro G _ _ _ K K' J S R R' W V z t d _ c4
  exact res20_7NoC3_of_hyp51 hH G K K' J S R R' W V z t d c4

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII
