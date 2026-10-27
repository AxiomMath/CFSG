module

public import CFSG.ClassicalInvolution.Asc77.AscT3SAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT3SInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem alpha_normalizer {Z : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Z : Set G)) :
    g ∈ Subgroup.normalizer (alphaOf Z : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hg ⊢
  have := alphaOf_conjSub g Z
  rw [hg] at this
  exact this.symm

theorem comm_sq_one {a k : G} (ha2 : a * a = 1) (hc : a * ⁅a, k⁆ = ⁅a, k⁆ * a) :
    ⁅a, k⁆ * ⁅a, k⁆ = 1 := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have e1 : a * ⁅a, k⁆ * a⁻¹ = ⁅a, k⁆⁻¹ := by
    rw [commutatorElement_def]
    calc a * (a * k * a⁻¹ * k⁻¹) * a⁻¹ = (a * a) * k * a⁻¹ * k⁻¹ * a⁻¹ := by group
      _ = k * a⁻¹ * k⁻¹ * a⁻¹ := by rw [ha2, one_mul]
      _ = k * a * k⁻¹ * a⁻¹ := by rw [ha]
      _ = (a * k * a⁻¹ * k⁻¹)⁻¹ := by group
  have e2 : a * ⁅a, k⁆ * a⁻¹ = ⁅a, k⁆ := by rw [hc]; group
  rw [e2] at e1
  exact mul_eq_one_iff_eq_inv.mpr e1

end General

section Clos

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem s_exists_rho : ∃ ρ ∈ Subgroup.normalizer
    ((Subgroup.closure ({t, z} : Set G) : Subgroup G) : Set G), ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hpair : pairNormalizers K J z t ≤
      Subgroup.normalizer ((Subgroup.closure ({t, z} : Set G) : Subgroup G) : Set G) := by
    rw [Set.pair_comm t z]
    exact sup_le inf_le_right inf_le_right
  refine ⟨t₀ * r, Subgroup.mul_mem _ (hpair hh.t₀_mem_pair) (hpair hh.r_mem_pair), ?_⟩
  calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
    _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
    _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
    _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
    _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

end Std20

namespace AlphaCfg

variable (d : Std20 p f K K' J S R R' W V z t) {a : G} (h : AlphaCfg S K K' J z t a)
include d h

theorem Cz_le : Subgroup.centralizer ({z} : Set G) ≤
    Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  intro c hc
  have hcN := d.late_cent_le_normalizer_sup hc
  have hctM : c * t * c⁻¹ ∈ K ⊔ K' := (Subgroup.mem_normalizer_iff.mp hcN t).mp d.htKK
  have hczc : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
      _ = z := by group
  have hct2 : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [d.viol.hzJ.sq]; group
  have hct1 : c * t * c⁻¹ ≠ 1 := by
    intro e
    apply d.viol.hzJ.ne_one
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have hctz : c * t * c⁻¹ ≠ z := by
    intro e
    apply d.late_ne_inv
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [e]
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hczc]
      _ = z := by group
  obtain ⟨m, hm, hmt⟩ := T3S.exists_conj_of_involutions_sup_mod d.branch.odd d.branch.five d.hyp
    d.late_mem_K d.late_mem_K' d.ne d.viol.hzK d.late_hzK' d.htKK d.viol.hzJ.sq
    d.viol.hzJ.ne_one d.late_ne_inv hctM hct2 hct1 hctz
  have hmM : m ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := sup_le (h.K_le d) (h.K'_le d) hm
  have hmz : m * z = z * m := by
    have hmC : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := d.sup_le_centralizer_z
    exact Subgroup.mem_centralizer_singleton_iff.mp (hmC hm)
  have hy : m⁻¹ * c ∈ Subgroup.centralizer
      ((Subgroup.closure ({t, z} : Set G) : Subgroup G) : Set G) := by
    refine mem_centralizer_closure_pair ?_ ?_
    · have h1 : m * t * m⁻¹ = c * t * c⁻¹ := hmt
      calc t * (m⁻¹ * c) = m⁻¹ * (m * t * m⁻¹) * c := by group
        _ = m⁻¹ * (c * t * c⁻¹) * c := by rw [h1]
        _ = (m⁻¹ * c) * t := by group
    · have hmz' : m⁻¹ * z = z * m⁻¹ := by
        calc m⁻¹ * z = m⁻¹ * z * m * m⁻¹ := by group
          _ = m⁻¹ * (z * m) * m⁻¹ := by group
          _ = m⁻¹ * (m * z) * m⁻¹ := by rw [← hmz]
          _ = z * m⁻¹ := by group
      have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc z * (m⁻¹ * c) = (z * m⁻¹) * c := by group
        _ = (m⁻¹ * z) * c := by rw [hmz']
        _ = m⁻¹ * (z * c) := by group
        _ = m⁻¹ * (c * z) := by rw [hcz']
        _ = (m⁻¹ * c) * z := by group
  have hyM := h.cent_le d (h.isElemAbelian2_Z d) (h.Z_le_B d) hy
  have hc' : c = m * (m⁻¹ * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ hmM hyM

theorem neighbour_mem {L' : Subgroup G}
    (hadj : aGraphAdj (CoreAssembly.conjClass K) K L') :
    ∃ m ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G),
      conjSub m K = L' := by
  set M := Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) with hM
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩ := d.hyp
  obtain ⟨g, hgz, hgK⟩ := d.swap
  have hgM : g ∈ M := h.Cz_le d hgz
  obtain ⟨ρ, hρN, hρt⟩ := d.s_exists_rho
  have hρM : ρ ∈ M := alpha_normalizer hρN
  have hM₀ : K ⊔ K' ≤ M := sup_le (h.K_le d) (h.K'_le d)
  have key : ∀ {L₂ : Subgroup G} {t₂ : G}, AViol (CoreAssembly.conjClass K) K L₂ z t₂ →
      ∃ m ∈ M, conjSub m K = L₂ := by
    intro L₂ t₂ hv
    have ht₂mem : t₂ ∈ K ⊔ K' := t_mem_sup_of_aviol hp hq hΩ d.late_mem_K hv d.twins
    have ht₂z : t₂ ≠ z := hv.ne_involution hΩ d.late_mem_K
    obtain ⟨m, hm, hmt⟩ := T3S.exists_conj_of_involutions_sup_mod hp hq hΩ d.late_mem_K
      d.late_mem_K' d.ne d.viol.hzK d.late_hzK' d.htKK d.viol.hzJ.sq d.viol.hzJ.ne_one
      d.late_ne_inv ht₂mem hv.hzJ.sq hv.hzJ.ne_one ht₂z
    have hL₂Ω : L₂ ∈ CoreAssembly.conjClass K := hv.mem
    have hK₀ : IsUniqueInvolution (conjSub ρ⁻¹ K) t := by
      have := d.viol.hzK.conj ρ⁻¹
      have e : ρ⁻¹ * z * ρ⁻¹⁻¹ = t := by
        calc ρ⁻¹ * z * ρ⁻¹⁻¹ = ρ⁻¹ * (ρ * t * ρ⁻¹) * ρ := by rw [hρt]; group
          _ = t := by group
      rwa [e] at this
    have hL'' : IsUniqueInvolution (conjSub m⁻¹ L₂) t := by
      have := hv.hzJ.conj m⁻¹
      have e : m⁻¹ * t₂ * m⁻¹⁻¹ = t := by
        calc m⁻¹ * t₂ * m⁻¹⁻¹ = m⁻¹ * (m * t * m⁻¹) * m := by rw [hmt]; group
          _ = t := by group
      rwa [e] at this
    have hmem : conjSub m⁻¹ L₂ ∈ twinSet (CoreAssembly.conjClass K) (conjSub ρ⁻¹ K) :=
      ⟨hΩ.conjInvariant m⁻¹ L₂ hL₂Ω, t, hK₀, hL''⟩
    have hmem' := twinSet_conj hΩ.conjInvariant hmem ρ
    have e1 : conjSub ρ (conjSub ρ⁻¹ K) = K := by
      simpa using conjSub_inv_conjSub ρ⁻¹ K
    rw [e1, d.twins] at hmem'
    have e2 : conjSub ρ (conjSub m⁻¹ L₂) = conjSub (ρ * m⁻¹) L₂ := (conjSub_mul ρ m⁻¹ L₂).symm
    have e3 : conjSub (ρ * m⁻¹)⁻¹ (conjSub (ρ * m⁻¹) L₂) = L₂ := conjSub_inv_conjSub _ _
    have hmM : (ρ * m⁻¹)⁻¹ ∈ M := M.inv_mem (M.mul_mem hρM (M.inv_mem (hM₀ hm)))
    rcases hmem' with h1 | h1
    · refine ⟨(ρ * m⁻¹)⁻¹, hmM, ?_⟩
      rw [e2] at h1
      rw [h1] at e3
      exact e3
    · refine ⟨(ρ * m⁻¹)⁻¹ * g, M.mul_mem hmM hgM, ?_⟩
      rw [e2] at h1
      rw [conjSub_mul, hgK]
      rw [h1] at e3
      exact e3
  obtain ⟨hL'Ω, h' | h' | ⟨ht, hne⟩⟩ := hadj
  · obtain ⟨zK, zJ, hv⟩ := h'
    have hzz : zK = z := hv.hzK.eq d.viol.hzK
    subst hzz
    exact key hv
  · obtain ⟨zL, zK, hv⟩ := h'
    have hzz : zK = z := hv.hzJ.eq d.viol.hzK
    subst hzz
    exact key (aviol_symm hp hq hΩ hL'Ω hv)
  · rw [d.twins] at ht
    rcases ht with h1 | h1
    · exact absurd h1 hne
    · exact ⟨g, hgM, by rw [hgK, h1]⟩

theorem normalizer_eq_top : Subgroup.normalizer
    (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) = ⊤ := by
  set M := Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) with hM
  have hall : ∀ L, Relation.ReflTransGen (aGraphAdj (CoreAssembly.conjClass K)) K L →
      ∃ m ∈ M, conjSub m K = L := by
    intro L hL
    induction hL with
    | refl => exact ⟨1, M.one_mem, conjSub_one K⟩
    | @tail L₁ L₂ _ hadj ih =>
      obtain ⟨m, hm, rfl⟩ := ih
      have hadj' := aGraphAdj_conj' d.hyp.conjInvariant hadj m⁻¹
      rw [conjSub_inv_conjSub] at hadj'
      obtain ⟨m', hm', hm'e⟩ := h.neighbour_mem d hadj'
      refine ⟨m * m', M.mul_mem hm hm', ?_⟩
      rw [conjSub_mul, hm'e]
      simpa using conjSub_inv_conjSub m⁻¹ L₂
  rw [eq_top_iff]
  intro g _
  have hmem : conjSub g K ∈ aStar (CoreAssembly.conjClass K) K := by
    rw [d.star]
    exact ⟨g, rfl⟩
  obtain ⟨m, hm, hmg⟩ := hall _ hmem
  have hmg' : conjSub (m⁻¹ * g) K = K := by
    rw [conjSub_mul, ← hmg]
    exact conjSub_inv_conjSub m K
  have hzc : m⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    have := d.viol.hzK.conj_eq hmg'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (m⁻¹ * g) * z = ((m⁻¹ * g) * z * (m⁻¹ * g)⁻¹) * (m⁻¹ * g) := by group
      _ = z * (m⁻¹ * g) := by rw [this]
  have : m⁻¹ * g ∈ M := h.Cz_le d hzc
  have e : g = m * (m⁻¹ * g) := by group
  rw [e]
  exact M.mul_mem hm this

theorem alpha_eq_bot [IsSimpleGroup G] :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hn : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (h.normalizer_eq_top d)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (alphaOf (Subgroup.closure ({t, z} : Set G)))
    with h1 | h1
  · exact h1
  · exfalso
    have hodd := (h.alpha_facts d).1
    rw [h1, Subgroup.card_top] at hodd
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzK.sq)
      d.viol.hzK.ne_one
    have hdvd : 2 ∣ Nat.card G := hz2 ▸ orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem comm_oddCore_z [IsSimpleGroup G] {o : G}
    (ho : o ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) : a * o = o * a := by
  have hE := h.isElemAbelian2_za d
  have hα : alphaOf (Subgroup.closure ({z, a} : Set G)) = ⊥ := by
    rw [(h.alpha_facts d).2 _ (h.za_le_B d) hE]
    exact h.alpha_eq_bot d
  have haE : a ∈ Subgroup.closure ({z, a} : Set G) := Subgroup.subset_closure (by simp)
  have hzE : z ∈ Subgroup.closure ({z, a} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : ⁅o, a⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({z} : Set G)),
      Subgroup.closure ({z, a} : Set G)⁆ := Subgroup.commutator_mem_commutator ho haE
  have h2 := commutator_le_alphaOf (Subgroup.closure ({z, a} : Set G)) hzE d.viol.hzK.ne_one h1
  rw [hα, Subgroup.mem_bot] at h2
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem comm_oddCore_t [IsSimpleGroup G] {o : G}
    (ho : o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set G))) : a * o = o * a := by
  have hE := h.isElemAbelian2_ta d
  have hα : alphaOf (Subgroup.closure ({t, a} : Set G)) = ⊥ := by
    rw [(h.alpha_facts d).2 _ (h.ta_le_B d) hE]
    exact h.alpha_eq_bot d
  have haE : a ∈ Subgroup.closure ({t, a} : Set G) := Subgroup.subset_closure (by simp)
  have htE : t ∈ Subgroup.closure ({t, a} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : ⁅o, a⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t} : Set G)),
      Subgroup.closure ({t, a} : Set G)⁆ := Subgroup.commutator_mem_commutator ho haE
  have h2 := commutator_le_alphaOf (Subgroup.closure ({t, a} : Set G)) htE d.viol.hzJ.ne_one h1
  rw [hα, Subgroup.mem_bot] at h2
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem comm_member [IsSimpleGroup G] {L : Subgroup G} {w : G} (hL : L ∈ CoreAssembly.conjClass K)
    (hwL : IsUniqueInvolution L w)
    (hw : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({w} : Set G)), a * o = o * a)
    (hcomm : ∀ k ∈ L, ⁅a, k⁆ ∈ oddCoreOf L) : ∀ k ∈ L, a * k = k * a := by
  intro k hk
  have hLO : oddCoreOf L ≤ oddCoreOf (Subgroup.centralizer ({w} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (T7A.isSubnormal_centralizer d.hyp hL hwL)
  have ho := hcomm k hk
  have hc : a * ⁅a, k⁆ = ⁅a, k⁆ * a := hw _ (hLO ho)
  have hsq := comm_sq_one h.ha2 hc
  have h1 : ⁅a, k⁆ = 1 := by
    by_contra hne
    exact hne (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) ho
      (isPGroup_zpowers_of_mul_self_eq_one hsq hne))
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem comm_K [IsSimpleGroup G] : ∀ k ∈ K, a * k = k * a :=
  h.comm_member d d.late_mem_K d.viol.hzK (fun _ ho => h.comm_oddCore_z d ho)
    (fun _ hk => d.s_comm_K h.hA hk)

theorem comm_K' [IsSimpleGroup G] : ∀ k ∈ K', a * k = k * a :=
  h.comm_member d d.late_mem_K' d.late_hzK' (fun _ ho => h.comm_oddCore_z d ho)
    (fun _ hk => d.s_comm_K' h.hA hk)

theorem comm_J [IsSimpleGroup G] : ∀ j ∈ J, a * j = j * a :=
  h.comm_member d d.late_mem_J d.viol.hzJ (fun _ ho => h.comm_oddCore_t d ho)
    (fun _ hj => h.hA.2.2.2 _ hj)

end AlphaCfg

end Clos

end CFSG.ClassicalInvolution.Asc77.T3CII
