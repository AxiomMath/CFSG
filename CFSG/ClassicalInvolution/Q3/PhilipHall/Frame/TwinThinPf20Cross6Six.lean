module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Ker

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

local notation "gCentMembers" => CFSG.ClassicalInvolution.Generic.centMembers
local notation "gCentLayer" => CFSG.ClassicalInvolution.Generic.centLayer

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem not_mem_pi_self : K ∉ π := fun h =>
  (adj_of_mem_isMaxOrb S.hos.graph S.hπ h).2.2.1 rfl

theorem conjSub_g_not_mem_fam : conjSub g K ∉ fam K (conjSub g (piGen π)) := fun h => by
  apply S.not_mem_pi_self
  have := S.conj_inv_mem_pi h
  rwa [conjSub_inv_conjSub] at this

theorem pi_subset_centMembers {u : G} (huX : ∀ x ∈ piGen π, x * u = u * x) :
    ∀ M ∈ π, M ∈ gCentMembers (CoreAssembly.conjClass K₀) u := fun M hM =>
  CFSG.ClassicalInvolution.Generic.mem_centMembers_iff_commute.mpr
    ⟨S.mem_of_mem_pi hM, fun x hx => huX x (le_piGen hM hx)⟩

theorem eight_le_of_secYu {m : ℕ} (hm : 6 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G}
    (hu' : u ∈ pSpan (fam K (conjSub g (piGen π)))) {a c : Fin m} (hac : a ≠ c)
    (hφu : J.φ ⟨u, hu'⟩ = AE.mkQ m (ofVec (TL4.pairVec a c)))
    (huX : ∀ x ∈ piGen π, x * u = u * x) {k : ℕ} (hk5 : 5 ≤ k)
    (Ju : AEIdent (gCentMembers (CoreAssembly.conjClass K₀) u) k)
    (hkI : IsPGroup 2 Ju.φ.ker) : 8 ≤ k := by
  classical
  by_contra hlt
  push Not at hlt
  have hm5 : 5 ≤ m := by omega
  have hPΩ : gCentMembers (CoreAssembly.conjClass K₀) u ⊆ CoreAssembly.conjClass K₀ :=
    fun M hM => hM.1
  have hKgP : conjSub g K ∈ gCentMembers (CoreAssembly.conjClass K₀) u :=
    S.pi_subset_centMembers huX _ S.hg
  have hKgC : conjSub g K ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
    conjSub_le_centralizer' g S.pair_le_cent.1
  obtain ⟨β, hβ, c₀, hlabKg⟩ := Ju.label _ hKgP
  have hγ : ∃ γ : Finset (Fin m), γ.card = 4 ∧ a ∉ γ ∧ c ∉ γ := by
    have h1 := Finset.le_card_sdiff ({a, c} : Finset (Fin m)) Finset.univ
    have h2 : ({a, c} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin] at h1
    obtain ⟨γ, hγU, hγ⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ {a, c}) (n := 4)
      (by omega)
    refine ⟨γ, hγ, fun hh => ?_, fun hh => ?_⟩
    · have := hγU hh
      simp at this
    · have := hγU hh
      simp at this
  obtain ⟨γ, hγ4, haγ, hcγ⟩ := hγ
  have key : ∀ M ∈ gCentMembers (CoreAssembly.conjClass K₀) u, M ≠ conjSub g K →
      (∀ x ∈ M, ∀ y ∈ conjSub g K, x * y = y * x) →
      (M.subgroupOf (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u))).map Ju.φ =
        AE.memBar β hβ (!c₀) := by
    intro M hM hne hcomm
    obtain ⟨δ, hδ, c', hlabM⟩ := Ju.label M hM
    have himgcomm : ∀ x ∈ AE.memBar δ hδ c', ∀ y ∈ AE.memBar β hβ c₀, x * y = y * x := by
      intro x hx y hy
      rw [← hlabM] at hx
      rw [← hlabKg] at hy
      obtain ⟨l, hl, rfl⟩ := Ju.exists_of_mem_map hM hx
      obtain ⟨l', hl', rfl⟩ := Ju.exists_of_mem_map hKgP hy
      rw [← map_mul, ← map_mul]
      exact congrArg Ju.φ (Subtype.ext (hcomm l hl l' hl'))
    by_cases hδβ : δ = β
    · subst hδβ
      by_cases hcc : c' = c₀
      · subst hcc
        exact absurd (S.eq_of_map_le_gen hPΩ hk5 Ju hkI hM hKgP
          (le_of_eq (hlabM.trans hlabKg.symm))) hne
      · have : c' = !c₀ := by cases c' <;> cases c₀ <;> simp_all
        rw [hlabM, this]
    · exfalso
      have hdisj := AE.disjoint_of_zBar_comm (h := hδ) (h' := hβ) hδβ (c := c₀) fun y hy =>
        himgcomm _ (AE.zBar_mem_memBar δ hδ c') y hy
      have h1 := Finset.card_union_of_disjoint hdisj
      have h2 : (δ ∪ β).card ≤ k := by
        have := Finset.card_le_univ (δ ∪ β)
        rwa [Fintype.card_fin] at this
      omega
  obtain ⟨Lp, hLp, hlabp⟩ := J.label_surj γ hγ4 true
  obtain ⟨Lm, hLm, hlabm⟩ := J.label_surj γ hγ4 false
  have hPp := S.mem_centMembers_of_label hm5 J hu' hac hφu hLp hlabp haγ hcγ
  have hPm := S.mem_centMembers_of_label hm5 J hu' hac hφu hLm hlabm haγ hcγ
  have hnep : Lp ≠ conjSub g K := fun h => S.conjSub_g_not_mem_fam (h ▸ hLp)
  have hnem : Lm ≠ conjSub g K := fun h => S.conjSub_g_not_mem_fam (h ▸ hLm)
  have hcomm : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ x ∈ L, ∀ y ∈ conjSub g K, x * y = y * x :=
    fun L hL x hx y hy => Subgroup.mem_centralizer_iff.mp (hKgC hy) x (S.le_of_mem_fam' hL hx)
  have ep := key Lp hPp hnep (hcomm Lp hLp)
  have em := key Lm hPm hnem (hcomm Lm hLm)
  have hLL : Lp = Lm :=
    S.eq_of_map_le_gen hPΩ hk5 Ju hkI hPp hPm (le_of_eq (ep.trans em.symm))
  apply AE.memBar_true_ne_false hm5 γ hγ4
  rw [← hlabp, ← hlabm, hLL]

theorem ker_le_zpowers_secYu
    (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 6 ≤ m) (htw : S.TwinLab m)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) (hnb : NbrPiTwin K₀ K K' π g)
    (hsec : SecYu K₀ K K' z π g) :
    ∀ k ∈ J.φ.ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype,
      k = 1 ∨ k = g * z * g⁻¹ := by
  classical
  have hm5 : 5 ≤ m := by omega
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  obtain ⟨u, a, c, ha, hc, hac, hpair, huX, hu', hφu⟩ := S.exists_pairInv hm5 htw J hlab
  obtain ⟨-, hS2, kY, hk5, ⟨Ju⟩⟩ := hsec u hpair
  rintro _ ⟨k₀, hk₀, rfl⟩
  have hΩ := S.hs.hyp
  have hkc := Subgroup.mem_center_iff.mp (J.ker_le hk₀)
  have hkX' : ∀ x ∈ conjSub g (piGen π), (k₀ : G) * x = x * (k₀ : G) := by
    intro x hx
    have hxp : x ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact hx
    exact (congrArg Subtype.val (hkc ⟨x, hxp⟩)).symm
  have hk₀X' : (k₀ : G) ∈ conjSub g (piGen π) := by
    exact (SetLike.ext_iff.mp S.fam_gen (k₀ : G)).mp k₀.2
  have huX' : u ∈ conjSub g (piGen π) := by
    exact (SetLike.ext_iff.mp S.fam_gen u).mp hu'
  have hku : (k₀ : G) * u = u * (k₀ : G) := hkX' u huX'
  have hOY : classicalInvolutionOddCore ↥(gCentLayer (CoreAssembly.conjClass K₀) u) = ⊥ :=
    S.oddCore_centLayer_eq_bot hm J hodd hpair.2.1 huX
  have hkI : IsPGroup 2 Ju.φ.ker := Ju.isPGroup_ker hOY
  have hk8 := S.eight_le_of_secYu hm htw J hu' hac hφu huX hk5 Ju hkI
  have hPΩ : gCentMembers (CoreAssembly.conjClass K₀) u ⊆ CoreAssembly.conjClass K₀ :=
    fun M hM => hM.1
  have hcu : ∀ x ∈ pSpan (gCentMembers (CoreAssembly.conjClass K₀) u), x * u = u * x := by
    intro x hx
    have : pSpan (gCentMembers (CoreAssembly.conjClass K₀) u) ≤ Subgroup.centralizer ({u} : Set G) :=
      pSpan_le fun L hL => hL.2
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  have hconjP : ∀ M ∈ gCentMembers (CoreAssembly.conjClass K₀) u,
      ∀ x ∈ pSpan (gCentMembers (CoreAssembly.conjClass K₀) u),
      conjSub x M ∈ gCentMembers (CoreAssembly.conjClass K₀) u := by
    intro M hM x hx
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant
      (n := x) hM
    have h2 : x * u * x⁻¹ = u := by rw [hcu x hx]; group
    rwa [h2] at h1
  have hconjk : ∀ M ∈ gCentMembers (CoreAssembly.conjClass K₀) u,
      conjSub (k₀ : G) M ∈ gCentMembers (CoreAssembly.conjClass K₀) u := by
    intro M hM
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant
      (n := (k₀ : G)) hM
    have h2 : (k₀ : G) * u * (k₀ : G)⁻¹ = u := by rw [hku]; group
    rwa [h2] at h1
  have hkN : (k₀ : G) ∈ Subgroup.normalizer
      (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u) : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_centLayer hΩ.conjInvariant (k₀ : G) u
    have h2 : (k₀ : G) * u * (k₀ : G)⁻¹ = u := by rw [hku]; group
    rw [h2] at h1
    exact h1
  exact S.ker_of_chart hS hnab hk8 (Cross.aeAut_of_five_le hk5) hnb hPΩ Ju hkI hconjP
    (S.pi_subset_centMembers huX) (S.pi_subset_centMembers huX _ S.hg) hk₀X' hkX' hkN hconjk

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
