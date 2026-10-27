module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitE16
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPGrp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type*} [Group G] [Finite G]

@[expose] def LitMinNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ K : Subgroup G, K.Normal → K ≤ M → K = ⊥ ∨ K = M

private lemma lit_pow_two_of_mem {T : Subgroup G} (hT : IsPGroup 2 T) {x : G} (hx : x ∈ T) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
  exact ⟨k, by simpa using hk⟩

theorem lit_exists_minNormal_le {K : Subgroup G} [K.Normal] (hK : K ≠ ⊥) :
    ∃ M : Subgroup G, LitMinNormal M ∧ M ≤ K := by
  classical
  let P : ℕ → Prop := fun n => ∃ N : Subgroup G, N.Normal ∧ N ≤ K ∧ N ≠ ⊥ ∧ Nat.card N = n
  have hP : ∃ n, P n := ⟨Nat.card K, K, inferInstance, le_rfl, hK, rfl⟩
  obtain ⟨N, hNnorm, hNK, hNne, hNcard⟩ := Nat.find_spec hP
  refine ⟨N, ⟨hNnorm, hNne, fun L hL hLN => ?_⟩, hNK⟩
  by_cases hLbot : L = ⊥
  · exact Or.inl hLbot
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge hLN ?_)
    have hPL : P (Nat.card L) := ⟨L, hL, le_trans hLN hNK, hLbot, rfl⟩
    have := Nat.find_min' hP hPL
    rwa [hNcard]

theorem lit_exists_normalizer_gt {T A : Subgroup G} (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (hne : A ≠ T) : ∃ x ∈ T, x ∉ A ∧ x ∈ normalizer (A : Set G) := by
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hcond : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  have hne' : A.subgroupOf T ≠ ⊤ := fun h' =>
    hne (le_antisymm hAT (Subgroup.subgroupOf_eq_top.mp h'))
  have hlt : A.subgroupOf T < normalizer (A.subgroupOf T : Set ↥T) :=
    hcond (A.subgroupOf T) (lt_top_iff_ne_top.mpr hne')
  obtain ⟨y, hy, hyA⟩ := SetLike.exists_of_lt hlt
  have hfwd : ∀ (z : ↥T), z ∈ normalizer (A.subgroupOf T : Set ↥T) → ∀ u ∈ A,
      (z : G) * u * (z : G)⁻¹ ∈ A := by
    intro z hz u hu
    exact (hz ⟨u, hAT hu⟩).mp hu
  have hmem : (y : G) ∈ normalizer (A : Set G) := by
    intro u
    refine ⟨hfwd y hy u, fun hu => ?_⟩
    have := hfwd y⁻¹ ((normalizer (A.subgroupOf T : Set ↥T)).inv_mem hy) _ hu
    have e : (((y⁻¹ : ↥T)) : G) * ((y : G) * u * (y : G)⁻¹) * (((y⁻¹ : ↥T)) : G)⁻¹ = u := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at this
  exact ⟨(y : G), y.2, fun hyA' => hyA hyA', hmem⟩

variable {A : Subgroup G} {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)}

theorem lit_mono_le (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M) : A ≤ M := by
  haveI : M.Normal := hM.1
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [h.card]; norm_num)
  obtain ⟨T, hAT⟩ := hA2.exists_le_sylow
  have hMeven : Even (Nat.card M) := by
    by_contra hodd
    have hodd' : Odd (Nat.card M) := Nat.not_even_iff_odd.mp hodd
    have hle : M ≤ CFSG.oddCore G := lit_le_oddCore G hM.1 hodd'
    exact hM.2.1 (eq_bot_iff.mpr (by rwa [h.oddCore] at hle))
  let U : Subgroup G := M ⊓ (T : Subgroup G)
  have hU2 : IsPGroup 2 U := (lit_inf_normal_sylow T M).1
  have hUidx : ¬ 2 ∣ U.relIndex M := (lit_inf_normal_sylow T M).2
  have hUleM : U ≤ M := inf_le_left
  have hUleT : U ≤ (T : Subgroup G) := inf_le_right
  have hUne : U ≠ ⊥ := by
    have h := lit_inf_ne_bot_of_sylow (M := M) (U := U) (L := M) hUleM hU2 hUidx
      le_rfl (fun m hm l hl => hM.1.conj_mem l hl m) hMeven
    rwa [inf_of_le_left hUleM] at h
  obtain ⟨z, hzU, hz1, hzcent⟩ :=
    lit_normal_inf_center (T := (T : Subgroup G)) (N := U) T.isPGroup' hUleT
      (fun t ht n hn =>
        ⟨hM.1.conj_mem n hn.1 t,
          (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hn.2)
            ((T : Subgroup G).inv_mem ht)⟩)
      hUne
  have hzA : z ∈ A := by
    have hzC : z ∈ centralizer (A : Set G) :=
      mem_centralizer_iff.mpr fun a ha => (hzcent a (hAT ha)).symm
    exact h.two_mem z hzC (lit_pow_two_of_mem T.isPGroup' (hUleT hzU))
  have hWne : A ⊓ M ≠ ⊥ := by
    intro hWbot
    exact hz1 (Subgroup.mem_bot.mp (hWbot ▸ Subgroup.mem_inf.mpr ⟨hzA, hUleM hzU⟩))
  have hWN : normalizer (A : Set G) ≤ normalizer ((A ⊓ M : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    have hgM : x ∈ M ↔ g * x * g⁻¹ ∈ M :=
      Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer_of_normal (H := M) (K := normalizer (A : Set G)) hg) x
    exact ⟨fun hx => ⟨(hg x).mp hx.1, hgM.mp hx.2⟩,
           fun hx => ⟨(hg x).mpr hx.1, hgM.mpr hx.2⟩⟩
  rcases lit_irreducible (X := G) (N := normalizer (A : Set G)) (A := A) le_rfl h.card φ
      h.surj h.ker (W := A ⊓ M) inf_le_left hWN with hWbot | hWA
  · exact absurd hWbot hWne
  · exact hWA ▸ inf_le_right

theorem lit_mono_five (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M) :
    ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥(normalizer (A : Set G)), (g : G) ∈ M ∧ φ g = σ := by
  haveI : M.Normal := hM.1
  have hAM : A ≤ M := lit_mono_le h hM
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [h.card]; norm_num)
  obtain ⟨T, hAT⟩ := hA2.exists_le_sylow
  let U : Subgroup G := M ⊓ (T : Subgroup G)
  have hU2 : IsPGroup 2 U := (lit_inf_normal_sylow T M).1
  have hUidx : ¬ 2 ∣ U.relIndex M := (lit_inf_normal_sylow T M).2
  have hAU : A ≤ U := le_inf hAM hAT
  have hne : A ≠ U := by
    intro hAUeq
    have hidx' : ¬ 2 ∣ A.relIndex M := by rw [hAUeq]; exact hUidx
    exact (lit_index_normalizer_odd (M := M) (A := A) hAM hA2 hidx') h.even.two_dvd
  obtain ⟨x, hxU, hxA, hxN⟩ := lit_exists_normalizer_gt (T := U) (A := A) hU2 hAU hne
  have hxM : x ∈ M := (inf_le_left : U ≤ M) hxU
  have hφ_ne : φ ⟨x, hxN⟩ ≠ 1 := by
    intro h1
    have hxcent : x ∈ centralizer (A : Set G) :=
      mem_centralizer_iff.mpr fun a ha => ((h.ker ⟨x, hxN⟩).mp h1 a ha).symm
    have hxT : x ∈ (T : Subgroup G) := (inf_le_right : U ≤ (T : Subgroup G)) hxU
    exact hxA (h.two_mem x hxcent (lit_pow_two_of_mem T.isPGroup' hxT))
  let Q : Subgroup ↥(normalizer (A : Set G)) := M.subgroupOf (normalizer (A : Set G))
  have hQnorm : Q.Normal := hM.1.subgroupOf (normalizer (A : Set G))
  let E : Subgroup (Equiv.Perm (Fin 6)) := Q.map φ
  have hEnorm : E.Normal := hQnorm.map φ h.surj
  have hEne : E ≠ ⊥ := by
    have hxQ : (⟨x, hxN⟩ : ↥(normalizer (A : Set G))) ∈ Q :=
      (Subgroup.mem_subgroupOf (H := M) (K := normalizer (A : Set G))).mpr hxM
    have hxE : φ ⟨x, hxN⟩ ∈ E := ⟨⟨x, hxN⟩, hxQ, rfl⟩
    intro hEbot
    exact hφ_ne (Subgroup.mem_bot.mp (hEbot ▸ hxE))
  haveI : E.Normal := hEnorm
  have hAlt : alternatingGroup (Fin 6) ≤ E := lit_normal_perm6 E hEne
  intro σ hσ
  obtain ⟨g, hgQ, hgφ⟩ := Subgroup.mem_map.mp (hAlt hσ)
  exact ⟨g, Subgroup.mem_subgroupOf.mp hgQ, hgφ⟩

end CFSG.OddStandard.HigherRank.YamadaG23
