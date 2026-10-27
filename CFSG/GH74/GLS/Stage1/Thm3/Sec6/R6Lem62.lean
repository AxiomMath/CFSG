module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Ctrl
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem sylow_K_inf {G : Type} [Group G] [Finite G] {z a : G} {S K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({z} : Set G)) K)
    (hext : M.Syl2In (S ⊓ centralizer ({a} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G))) :
    M.Syl2In (S ⊓ K ⊓ centralizer ({a} : Set G)) (K ⊓ centralizer ({a} : Set G)) := by
  obtain ⟨hKC, hcomp⟩ := hK
  obtain ⟨K', -, hsub, -⟩ := hcomp
  have hXC : centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) ≤ centralizer ({z} : Set G) :=
    inf_le_left
  have hLX : K ⊓ centralizer ({a} : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) :=
    inf_le_inf_right _ hKC
  have hsubL : ((K ⊓ centralizer ({a} : Set G)).subgroupOf
      (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G))).IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.comap (Subgroup.inclusion hXC) hsub
    convert h1 using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
    constructor
    · rintro ⟨hx, -⟩; exact hx
    · intro hx; exact ⟨hx, x.2.2⟩
  have := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hext hLX hsubL
  have e : S ⊓ centralizer ({a} : Set G) ⊓ (K ⊓ centralizer ({a} : Set G)) =
      S ⊓ K ⊓ centralizer ({a} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [e] at this
  exact this

namespace Std6

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem orderOf_z (h : Std6 G z S) : orderOf z = 2 := h.classical.1

theorem z_sq (h : Std6 G z S) : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_z

theorem z_ne (h : Std6 G z S) : z ≠ 1 := ne_one_of_orderOf_eq_two h.orderOf_z

theorem syl_C (h : Std6 G z S) : M.Syl2In S (centralizer ({z} : Set G)) :=
  syl2In_of_isSylowOf h.sylow

theorem S_pgroup (h : Std6 G z S) : IsPGroup 2 ↥S := h.syl_C.2.1

theorem z_cent (h : Std6 G z S) {s : G} (hs : s ∈ S) : z * s = s * z :=
  (Subgroup.mem_centralizer_singleton_iff.1 (h.syl_C.1 hs)).symm

theorem z_mem_S (h : Std6 G z S) : z ∈ S := by
  obtain ⟨P', hP', hzP'⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq h.z_sq h.z_ne)
    (zpowers_le.2 (M.z_mem_centralizer (z := z)))
  obtain ⟨c, hc, hcP⟩ := h.syl_C.exists_conj hP'
  have hzP : z ∈ P' := hzP' (mem_zpowers z)
  rw [hcP, M.mem_cj] at hzP
  have : c * z * c⁻¹ = z := by rw [M.centralizer_comm hc]; group
  rwa [this] at hzP

theorem rigidProduct_le_C (_h : Std6 G z S) : rigidProduct z ≤ centralizer ({z} : Set G) :=
  sSup_le fun _ hK => hK.1.1.2.2.1

theorem inv_zStar (h : Std6 G z S) {w : G} (hw : w ∈ zStar (rigidProduct z)) (hw2 : w * w = 1) :
    w = 1 ∨ w = z := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hb' : M.Syl2In (zpowers z) (zStar (rigidProduct z)) := syl2In_of_isSylowOf hcl.2.1
  obtain ⟨W, hW, hwW⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq hw2 hw1)
    (zpowers_le.2 hw : zpowers w ≤ zStar (rigidProduct z))
  obtain ⟨c, hc, hcW⟩ := hb'.exists_conj hW
  have hcC : c ∈ centralizer ({z} : Set G) := h.rigidProduct_le_C hc.1
  have hwW' : w ∈ W := hwW (mem_zpowers w)
  rw [hcW, M.cj_zpowers_of_comm h.z_sq (M.centralizer_comm hcC)] at hwW'
  rcases (M.mem_zpowers_of_sq h.z_sq).1 hwW' with h1 | h1
  · exact absurd h1 hw1
  · exact h1

theorem conj_invol (h : Std6 G z S) {t : G} (hzt : IsConj z t) : t * t = 1 ∧ t ≠ 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hzt
  refine ⟨?_, ?_⟩
  · rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  · intro e
    apply h.z_ne
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [hc, e]; group

end Std6

theorem lemma_6_2 (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) : Lemma6_2 := by
  intro G _ _ z S h a haS ha2 hext ⟨K, hK, hfa⟩ t htS hta htc hconj
  by_contra htz
  have hSyl := sylow_K_inf hK.1.1.2.2 (syl2In_of_isSylowOf hext)
  obtain ⟨n, hn⟩ := h14 G z S h K hK a haS ha2 hfa (isSylowOf_of_syl2In hSyl)
  obtain ⟨ht2, ht1⟩ := h.conj_invol hconj
  have hto : orderOf t = 2 := orderOf_eq_two_of_mul_self_eq_one ht2 ht1
  have hWle : S ⊓ K ⊓ centralizer ({a} : Set G) ≤ S ⊓ K := inf_le_left
  have hfinduce : InducesFAut t K := by
    refine h119 G z S h K hK t htS hto (S ⊓ K ⊓ centralizer ({a} : Set G)) hWle ⟨n, hn⟩ ?_
    intro w hw
    have hwS : w ∈ S := hw.1.1
    have hwa : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.1 hw.2
    exact (htc w hwS hwa).symm
  by_cases htZ : t ∈ zStar (rigidProduct z)
  · rcases h.inv_zStar htZ ht2 with e | e
    · exact ht1 e
    · exact htz e
  · obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
    have hcl := h.classical.2 t ((h.syl_C.1 htS)) hconj htZ
    exact hcl.2.2.2.2.1 K hK hfinduce

theorem lemma_6_3 (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) : Lemma6_3 := by
  intro G _ _ z S h a haS ha2 hext hK
  have h62 : ∀ t ∈ S, t * a = a * t → (∀ s ∈ S, s * a = a * s → s * t = t * s) → IsConj z t →
      t = z := fun t ht hta htc hconj =>
    lemma_6_2 h14 h119 G z S h a haS ha2 hext hK t ht hta htc hconj
  obtain ⟨hext', hctrl⟩ := lemma63_abs h.syl_C.2.1 h.z_mem_S (fun s hs => h.z_cent hs) haS
    (syl2In_of_isSylowOf hext) h62
  exact ⟨isSylowOf_of_syl2In hext', fun g hg _ hcon => hctrl g hg hcon⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
