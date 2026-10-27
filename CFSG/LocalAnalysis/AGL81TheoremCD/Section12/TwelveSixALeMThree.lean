module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenProof
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.eq_of_le_block
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {L A B U : Subgroup G} (hL : L ∈ weakBlockSet M H) (hU : IsPGroup 3 U)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hAL : A ≤ L) (hBL : B ≤ L)
    (hAU : A ≤ U) (hBU : B ≤ U) : A = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ M := hL.le
  have hrankL : CFSG.Open.pRank 3 L = 1 := by
    rw [← CFSG.AGLEmbedding.pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]
    exact hc.hm3 L hL
  have hrank : CFSG.Open.pRank 3 (L ⊓ U) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) inf_le_left).trans hrankL.le
  exact CFSG.LocalAnalysis.RankThreeUC.eq_of_card_eq_prime_of_pRank_le_one
    hU.to_inf_right hrank (le_inf hAL hAU) (le_inf hBL hBU) hA hB

private theorem map_conj_eq_self_of_mem_pair {U L B : Subgroup G}
    (hU : IsPGroup 3 U)
    (horbit : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom ∈
      ({L, B} : Set (Subgroup G))) :
    ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = L := by
  classical
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥U (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp U.subtype)
  have hsmul : ∀ (u : ↥U) (P : Subgroup G),
      u • P = P.map (MulAut.conj (u : G)).toMonoidHom := by
    intro u P
    rw [MulAction.compHom_smul_def]
    change MulAut.conj (u : G) • P = P.map (MulAut.conj (u : G)).toMonoidHom
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hsub : MulAction.orbit ↥U L ⊆ ({L, B} : Set (Subgroup G)) := by
    rintro P ⟨u, rfl⟩
    change u • L ∈ ({L, B} : Set (Subgroup G))
    rw [hsmul u L]
    exact horbit u
  have hcard2 : (MulAction.orbit ↥U L).ncard ≤ 2 := by
    refine (Set.ncard_le_ncard hsub).trans ?_
    calc ({L, B} : Set (Subgroup G)).ncard ≤ ({B} : Set (Subgroup G)).ncard + 1 :=
          Set.ncard_insert_le L {B}
      _ = 2 := by simp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.card_orbit hU L
  rw [Nat.card_coe_set_eq] at hn
  have hn0 : n = 0 := by
    by_contra h
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    have h3n : 3 ≤ 3 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 3) h1
    omega
  have hcard1 : (MulAction.orbit ↥U L).ncard = 1 := by rw [hn, hn0, pow_zero]
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard1
  have hxL : x = L := by
    have hLmem : L ∈ MulAction.orbit ↥U L := ⟨1, by simp⟩
    rw [hx] at hLmem
    exact (Set.mem_singleton_iff.mp hLmem).symm
  rw [hxL] at hx
  intro u
  have hmem : u • L ∈ ({L} : Set (Subgroup G)) := by
    rw [← hx]
    exact ⟨u, rfl⟩
  simpa [hsmul u L] using hmem

private theorem map_conj_mem_pair_of_mem_three_of_fixed {U L A B : Subgroup G}
    (hperm : ∀ u : ↥U, A.map (MulAut.conj (u : G)).toMonoidHom = L ∨
      A.map (MulAut.conj (u : G)).toMonoidHom = A ∨
      A.map (MulAut.conj (u : G)).toMonoidHom = B)
    (hfixL : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = L) (hLA : L ≠ A) :
    ∀ u : ↥U, A.map (MulAut.conj (u : G)).toMonoidHom ∈ ({A, B} : Set (Subgroup G)) := by
  intro u
  rcases hperm u with h | h | h
  · exfalso
    have hmap := congrArg (fun P : Subgroup G =>
      P.map (MulAut.conj ((u : G)⁻¹)).toMonoidHom) h
    have hconj : (A.map (MulAut.conj (u : G)).toMonoidHom).map
        (MulAut.conj ((u : G)⁻¹)).toMonoidHom = A := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id A using 1
      ext x
      simp [mul_assoc]
    rw [hconj, hfixL ⟨(u : G)⁻¹, U.inv_mem u.2⟩] at hmap
    exact hLA hmap.symm
  · exact Or.inl h
  · exact Or.inr h

private theorem le_normalizer_pair_of_fixed {U L A B : Subgroup G}
    (hU : IsPGroup 3 U)
    (hpermA : ∀ u : ↥U, A.map (MulAut.conj (u : G)).toMonoidHom = L ∨
      A.map (MulAut.conj (u : G)).toMonoidHom = A ∨
      A.map (MulAut.conj (u : G)).toMonoidHom = B)
    (hpermB : ∀ u : ↥U, B.map (MulAut.conj (u : G)).toMonoidHom = L ∨
      B.map (MulAut.conj (u : G)).toMonoidHom = B ∨
      B.map (MulAut.conj (u : G)).toMonoidHom = A)
    (hfixL : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = L)
    (hLA : L ≠ A) (hLB : L ≠ B) :
    U ≤ Subgroup.normalizer (A : Set G) ∧ U ≤ Subgroup.normalizer (B : Set G) := by
  have hpairA := map_conj_mem_pair_of_mem_three_of_fixed hpermA hfixL hLA
  have hfixA := map_conj_eq_self_of_mem_pair hU hpairA
  have hpairB := map_conj_mem_pair_of_mem_three_of_fixed hpermB hfixL hLB
  have hfixB := map_conj_eq_self_of_mem_pair hU hpairB
  exact ⟨fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfixA ⟨x, hx⟩),
    fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfixB ⟨x, hx⟩)⟩

private theorem le_normalizer_three_of_fixed_left {U L₁ L₂ L₃ : Subgroup G}
    (hU : IsPGroup 3 U)
    (hperm : ∀ u : ↥U, ∀ P ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      P.map (MulAut.conj (u : G)).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hfix : ∀ u : ↥U, L₁.map (MulAut.conj (u : G)).toMonoidHom = L₁)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃) :
    U ≤ Subgroup.normalizer (L₁ : Set G) ⊓ Subgroup.normalizer (L₂ : Set G) ⊓
      Subgroup.normalizer (L₃ : Set G) := by
  have hpermA : ∀ u : ↥U, L₂.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₂ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₃ :=
    fun u => hperm u L₂ (by simp)
  have hpermB : ∀ u : ↥U, L₃.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₃ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₂ := by
    intro u
    rcases hperm u L₃ (by simp) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hpair := le_normalizer_pair_of_fixed hU hpermA hpermB hfix hne.1 hne.2.1
  exact le_inf (le_inf (fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (hfix ⟨x, hx⟩)) hpair.1) hpair.2

private theorem le_normalizer_three_of_fixed_middle {U L₁ L₂ L₃ : Subgroup G}
    (hU : IsPGroup 3 U)
    (hperm : ∀ u : ↥U, ∀ P ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      P.map (MulAut.conj (u : G)).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hfix : ∀ u : ↥U, L₂.map (MulAut.conj (u : G)).toMonoidHom = L₂)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃) :
    U ≤ Subgroup.normalizer (L₁ : Set G) ⊓ Subgroup.normalizer (L₂ : Set G) ⊓
      Subgroup.normalizer (L₃ : Set G) := by
  have hpermA : ∀ u : ↥U, L₁.map (MulAut.conj (u : G)).toMonoidHom = L₂ ∨
      L₁.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj (u : G)).toMonoidHom = L₃ := by
    intro u
    rcases hperm u L₁ (by simp) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hpermB : ∀ u : ↥U, L₃.map (MulAut.conj (u : G)).toMonoidHom = L₂ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₃ ∨
      L₃.map (MulAut.conj (u : G)).toMonoidHom = L₁ := by
    intro u
    rcases hperm u L₃ (by simp) with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpair := le_normalizer_pair_of_fixed hU hpermA hpermB hfix hne.1.symm hne.2.2
  exact le_inf (le_inf hpair.1 (fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (hfix ⟨x, hx⟩))) hpair.2

private theorem le_normalizer_three_of_fixed_right {U L₁ L₂ L₃ : Subgroup G}
    (hU : IsPGroup 3 U)
    (hperm : ∀ u : ↥U, ∀ P ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      P.map (MulAut.conj (u : G)).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hfix : ∀ u : ↥U, L₃.map (MulAut.conj (u : G)).toMonoidHom = L₃)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃) :
    U ≤ Subgroup.normalizer (L₁ : Set G) ⊓ Subgroup.normalizer (L₂ : Set G) ⊓
      Subgroup.normalizer (L₃ : Set G) := by
  have hpermA : ∀ u : ↥U, L₁.map (MulAut.conj (u : G)).toMonoidHom = L₃ ∨
      L₁.map (MulAut.conj (u : G)).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj (u : G)).toMonoidHom = L₂ := by
    intro u
    rcases hperm u L₁ (by simp) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  have hpermB : ∀ u : ↥U, L₂.map (MulAut.conj (u : G)).toMonoidHom = L₃ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₂ ∨
      L₂.map (MulAut.conj (u : G)).toMonoidHom = L₁ := by
    intro u
    rcases hperm u L₂ (by simp) with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  have hpair := le_normalizer_pair_of_fixed hU hpermA hpermB hfix hne.2.1.symm hne.2.2.symm
  exact le_inf (le_inf hpair.1 hpair.2) (fun x hx =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix ⟨x, hx⟩))

private theorem le_normalizer_three_of_fixed {U L L₁ L₂ L₃ : Subgroup G}
    (hU : IsPGroup 3 U)
    (hperm : ∀ u : ↥U, ∀ P ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      P.map (MulAut.conj (u : G)).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hfixL : ∀ u : ↥U, L.map (MulAut.conj (u : G)).toMonoidHom = L)
    (hL : L ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃) :
    U ≤ Subgroup.normalizer (L₁ : Set G) ⊓ Subgroup.normalizer (L₂ : Set G) ⊓
      Subgroup.normalizer (L₃ : Set G) := by
  have hL' := hL
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL'
  rcases hL' with rfl | rfl | rfl
  · exact le_normalizer_three_of_fixed_left hU hperm hfixL hne
  · exact le_normalizer_three_of_fixed_middle hU hperm hfixL hne
  · exact le_normalizer_three_of_fixed_right hU hperm hfixL hne

theorem TwelveSixKCtx.map_conj_ne_of_not_mem
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) (hVU : D.V ≤ U) {u : G}
    (hu : u ∈ U) (huV : u ∉ D.V) {L : Subgroup G}
    (hL : L ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    L.map (MulAut.conj u).toMonoidHom ≠ L := by
  classical
  intro hfix
  let U' : Subgroup G := D.V ⊔ Subgroup.zpowers u
  have hU'U : U' ≤ U := sup_le hVU (Subgroup.zpowers_le.mpr hu)
  have hU' : IsPGroup 3 U' := hU.to_le hU'U
  have hU'M : U' ≤ M := hU'U.trans hUM
  have hVJ : D.V ≤ jSub M H := by
    rw [hc.data.join_eq]
    exact D.V_le.trans (sup_le
      (sup_le (D.le_inf₁.trans (inf_le_right.trans (le_sup_left.trans le_sup_left)))
        (D.le_inf₂.trans (inf_le_right.trans (le_sup_right.trans le_sup_left))))
      (D.le_inf₃.trans (inf_le_right.trans le_sup_right)))
  have hDVN : D.V ≤ Subgroup.normalizer (L : Set G) := by
    have hL' := hL
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL'
    rcases hL' with rfl | rfl | rfl
    · exact hVJ.trans (TwelveFiveData.jSub_le_normalizer_left hc.data)
    · exact hVJ.trans (TwelveFiveData.jSub_le_normalizer_middle hc.data)
    · exact hVJ.trans (TwelveFiveData.jSub_le_normalizer_right hc.data)
  have hUN : U' ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hDVN (Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix))
  have hperm : ∀ x : ↥U', ∀ P ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      P.map (MulAut.conj (x : G)).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)) :=
    fun x P hP => TwelveFiveData.map_conj_mem hc.data (hU'M x.2) hP
  have hfixL : ∀ x : ↥U', L.map (MulAut.conj (x : G)).toMonoidHom = L :=
    fun x => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUN x.2)
  have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
  have hN := le_normalizer_three_of_fixed hU' hperm hfixL hL hne
  have hcardU' : Nat.card U' ≤ 27 :=
    TwelveFiveData.card_le_of_le_normalizers hc.data hn hc.h3 hc.hcard hU'M hU' hN
  have hU'eq : D.V = U' :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [D.cfg.card]; exact hcardU')
  have huU' : u ∈ U' := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  exact huV (hU'eq ▸ huU')
private theorem map_conj_le_of_inv_of_comm {V W_inv W_c1 W_c2 : Subgroup G} {t : G}
    (hVinv : W_inv ≤ V) (hVc1 : W_c1 ≤ V) (hVc2 : W_c2 ≤ V)
    (hjoin : V = W_inv ⊔ W_c1 ⊔ W_c2)
    (hinv : ∀ w ∈ W_inv, t * w * t⁻¹ = w⁻¹)
    (hc1 : ∀ w ∈ W_c1, t * w = w * t)
    (hc2 : ∀ w ∈ W_c2, t * w = w * t) :
    V.map (MulAut.conj t).toMonoidHom ≤ V := by
  have h1 : W_inv.map (MulAut.conj t).toMonoidHom ≤ V := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    exact hVinv (by
      change t * w * t⁻¹ ∈ W_inv
      rw [hinv w hw]
      exact W_inv.inv_mem hw)
  have h2 : W_c1.map (MulAut.conj t).toMonoidHom ≤ V := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    exact hVc1 (by simpa [hc1 w hw] using hw)
  have h3 : W_c2.map (MulAut.conj t).toMonoidHom ≤ V := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    exact hVc2 (by simpa [hc2 w hw] using hw)
  conv_lhs => rw [hjoin]
  rw [Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le (sup_le h1 h2) h3

private theorem IsE27InvConfig.conj_mem {V W1 W2 W3 : Subgroup G} {t1 t2 t3 : G}
    (h : IsE27InvConfig V W1 W2 W3 t1 t2 t3) {t : G}
    (ht : t ∈ ({t1, t2, t3} : Set G)) {x : G} (hx : x ∈ V) : t * x * t⁻¹ ∈ V := by
  have hV1 : W1 ≤ V := by rw [h.join]; exact le_sup_left.trans le_sup_left
  have hV2 : W2 ≤ V := by rw [h.join]; exact le_sup_right.trans le_sup_left
  have hV3 : W3 ≤ V := by rw [h.join]; exact le_sup_right
  have hmap : V.map (MulAut.conj t).toMonoidHom ≤ V := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with h | h | h
    · subst t
      exact map_conj_le_of_inv_of_comm hV1 hV2 hV3 h.join h.inv₁
        (fun w hw => h.comm₁ w (Subgroup.mem_sup_left hw))
        (fun w hw => h.comm₁ w (Subgroup.mem_sup_right hw))
    · subst t
      have hjoin : V = W2 ⊔ W1 ⊔ W3 := by rw [h.join]; ac_rfl
      exact map_conj_le_of_inv_of_comm hV2 hV1 hV3 hjoin h.inv₂
        (fun w hw => h.comm₂ w (Subgroup.mem_sup_left hw))
        (fun w hw => h.comm₂ w (Subgroup.mem_sup_right hw))
    · subst t
      have hjoin : V = W3 ⊔ W1 ⊔ W2 := by rw [h.join]; ac_rfl
      exact map_conj_le_of_inv_of_comm hV3 hV1 hV2 hjoin h.inv₃
        (fun w hw => h.comm₃ w (Subgroup.mem_sup_left hw))
        (fun w hw => h.comm₃ w (Subgroup.mem_sup_right hw))
  exact hmap (Subgroup.mem_map_of_mem _ hx)
private theorem map_conj_eq_of_map_conj_eq
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) {v : G} (hvV : v ∈ V)
    {W W' L L' : Subgroup G} (hWV : W ≤ V) (hW'V : W' ≤ V)
    (hWL : W ≤ L) (hW'L' : W' ≤ L')
    (hcardW : Nat.card W = 3) (hcardW' : Nat.card W' = 3)
    (hL' : L' ∈ weakBlockSet M H)
    (hLv : L.map (MulAut.conj v).toMonoidHom = L') :
    W.map (MulAut.conj v).toMonoidHom = W' := by
  have hVinv : V.map (MulAut.conj v).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hvV)
  refine TwelveSixKCtx.eq_of_le_block hc hL' hV3 ?_ hcardW' ?_ hW'L' ?_ hW'V
  · rw [Subgroup.card_map_of_injective (MulAut.conj v).injective, hcardW]
  · calc W.map (MulAut.conj v).toMonoidHom ≤ L.map (MulAut.conj v).toMonoidHom :=
          Subgroup.map_mono hWL
      _ = L' := hLv
  · exact (Subgroup.map_mono hWV).trans (le_of_eq hVinv)
private theorem eq_bot_of_inv_and_comm {W W' : Subgroup G} {t : G}
    (hW : Nat.card W = 3) (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (hcomm : ∀ w ∈ W', t * w = w * t) (hle : W ≤ W') : W = ⊥ := by
  refine le_bot_iff.mp ?_
  intro w hw
  have hw' : w ∈ W' := hle hw
  have hinv' := hinv w hw
  have hcent := hcomm w hw'
  have hw_eq_inv : w = w⁻¹ := by
    have h1 : t * w * t⁻¹ = w := by rw [hcent]; group
    rw [hinv'] at h1
    exact h1.symm
  have hw2 : w ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hw_eq_inv]
    exact mul_inv_cancel w
  have hdvd3 : orderOf w ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard W hw
    rwa [hW] at this
  have hdvd2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hdvd2
    exact absurd hdvd2 (by norm_num)
private theorem orbit_ncard_eq_three
    {U : Subgroup G} [MulAction ↥U (Subgroup G)]
    (hU3 : IsPGroup 3 U) {W W₁ W₂ W₃ : Subgroup G}
    (hne12 : W₁ ≠ W₂) (hne13 : W₁ ≠ W₃) (hne23 : W₂ ≠ W₃)
    {v : G} (hv : v ∈ U)
    (hsmul : ∀ u : ↥U, u • W = W.map (MulAut.conj (u : G)).toMonoidHom)
    (hmove : W.map (MulAut.conj v).toMonoidHom ≠ W)
    (hsub : MulAction.orbit ↥U W ⊆ ({W₁, W₂, W₃} : Set (Subgroup G))) :
    (MulAction.orbit ↥U W).ncard = 3 := by
  have htriple : ({W₁, W₂, W₃} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne12, hne13])]
    rw [Set.ncard_insert_of_notMem (by simp [hne23])]
    simp
  have hle3 : (MulAction.orbit ↥U W).ncard ≤ 3 := by
    refine (Set.ncard_le_ncard hsub).trans ?_
    rw [htriple]
  have hWmem : W ∈ MulAction.orbit ↥U W := ⟨1, by simp⟩
  have hvmem : W.map (MulAut.conj v).toMonoidHom ∈ MulAction.orbit ↥U W :=
    ⟨⟨v, hv⟩, hsmul ⟨v, hv⟩⟩
  have hgt1 : 1 < (MulAction.orbit ↥U W).ncard := by
    rw [Set.one_lt_ncard_iff]
    exact ⟨W, W.map (MulAut.conj v).toMonoidHom, hWmem, hvmem, hmove.symm⟩
  obtain ⟨n, hn⟩ := IsPGroup.card_orbit hU3 W
  rw [Nat.card_coe_set_eq] at hn
  have hnpos : 0 < n := by
    by_contra h
    have hzero : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero, pow_zero] at hn
    omega
  have hnle1 : n ≤ 1 := by
    have : 3 ^ n ≤ 3 ^ 1 := by rw [← hn]; simpa using hle3
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp this
  have hn1 : n = 1 := by omega
  rw [hn1] at hn
  simpa using hn

private theorem orbit_eq_three_of_move {v : G} {W W₁ W₂ W₃ : Subgroup G}
    (hv3 : IsPGroup 3 (Subgroup.zpowers v))
    (hne12 : W₁ ≠ W₂) (hne13 : W₁ ≠ W₃) (hne23 : W₂ ≠ W₃)
    (hmove : W.map (MulAut.conj v).toMonoidHom ≠ W)
    (horbit : ∀ u : ↥(Subgroup.zpowers v),
      W.map (MulAut.conj (u : G)).toMonoidHom ∈ ({W₁, W₂, W₃} : Set (Subgroup G))) :
    MulAction.orbit ↥(Subgroup.zpowers v) W = ({W₁, W₂, W₃} : Set (Subgroup G)) := by
  classical
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥(Subgroup.zpowers v) (Subgroup G) :=
    MulAction.compHom (Subgroup G)
      ((MulAut.conj : G →* MulAut G).comp (Subgroup.zpowers v).subtype)
  have hsmul : ∀ (u : ↥(Subgroup.zpowers v)) (P : Subgroup G),
      u • P = P.map (MulAut.conj (u : G)).toMonoidHom := by
    intro u P
    rw [MulAction.compHom_smul_def]
    change MulAut.conj (u : G) • P = P.map (MulAut.conj (u : G)).toMonoidHom
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hsub : MulAction.orbit ↥(Subgroup.zpowers v) W ⊆ ({W₁, W₂, W₃} : Set (Subgroup G)) := by
    rintro P ⟨u, rfl⟩
    change u • W ∈ ({W₁, W₂, W₃} : Set (Subgroup G))
    rw [hsmul u W]
    exact horbit u
  have htriple : ({W₁, W₂, W₃} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne12, hne13])]
    rw [Set.ncard_insert_of_notMem (by simp [hne23])]
    simp
  have hOrbitCard := orbit_ncard_eq_three (U := Subgroup.zpowers v) hv3 hne12 hne13 hne23
    (Subgroup.mem_zpowers v) (fun u => hsmul u W) hmove hsub
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  calc ({W₁, W₂, W₃} : Set (Subgroup G)).ncard = 3 := htriple
    _ = (MulAction.orbit ↥(Subgroup.zpowers v) W).ncard := hOrbitCard.symm
    _ ≤ (MulAction.orbit ↥(Subgroup.zpowers v) W).ncard := le_rfl

private theorem le_three_of_orbit {v : G} {W W₁ W₂ W₃ D₀ : Subgroup G}
    (hv3 : IsPGroup 3 (Subgroup.zpowers v))
    (hne12 : W₁ ≠ W₂) (hne13 : W₁ ≠ W₃) (hne23 : W₂ ≠ W₃)
    (hWle : W ≤ D₀)
    (hDnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (D₀ : Set G))
    (hmove : W.map (MulAut.conj v).toMonoidHom ≠ W)
    (horbit : ∀ u : ↥(Subgroup.zpowers v),
      W.map (MulAut.conj (u : G)).toMonoidHom ∈ ({W₁, W₂, W₃} : Set (Subgroup G))) :
    W₁ ≤ D₀ ∧ W₂ ≤ D₀ ∧ W₃ ≤ D₀ := by
  classical
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥(Subgroup.zpowers v) (Subgroup G) :=
    MulAction.compHom (Subgroup G)
      ((MulAut.conj : G →* MulAut G).comp (Subgroup.zpowers v).subtype)
  have hsmul : ∀ (u : ↥(Subgroup.zpowers v)) (P : Subgroup G),
      u • P = P.map (MulAut.conj (u : G)).toMonoidHom := by
    intro u P
    rw [MulAction.compHom_smul_def]
    change MulAut.conj (u : G) • P = P.map (MulAut.conj (u : G)).toMonoidHom
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hOrbitEq := orbit_eq_three_of_move hv3 hne12 hne13 hne23 hmove horbit
  have hMemLe : ∀ P ∈ ({W₁, W₂, W₃} : Set (Subgroup G)), P ≤ D₀ := by
    intro P hP
    rw [← hOrbitEq] at hP
    rcases hP with ⟨u, rfl⟩
    change u • W ≤ D₀
    rw [hsmul u W]
    have huN : (u : G) ∈ Subgroup.normalizer (D₀ : Set G) := hDnorm u.2
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp huN y).mp (hWle hy)
  exact ⟨hMemLe W₁ (by simp), hMemLe W₂ (by simp), hMemLe W₃ (by simp)⟩


private theorem map_conj_mem_three_of_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    {u : G} (huV : u ∈ V) {W L : Subgroup G} (hWV : W ≤ V) (hWL : W ≤ L)
    (hcardW : Nat.card W = 3) (hLmem : L ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    W.map (MulAut.conj u).toMonoidHom ∈
      ({D.W₁, D.W₂, D.W₃} : Set (Subgroup G)) := by
  have hW1V : D.W₁ ≤ V := by
    have h : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
    exact h.trans hV0V
  have hW2V : D.W₂ ≤ V := by
    have h : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
    exact h.trans hV0V
  have hW3V : D.W₃ ≤ V := by
    have h : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
    exact h.trans hV0V
  have hW1L : D.W₁ ≤ L₁ := D.le₁.trans (D.le_inf₁.trans inf_le_right)
  have hW2L : D.W₂ ≤ L₂ := D.le₂.trans (D.le_inf₂.trans inf_le_right)
  have hW3L : D.W₃ ≤ L₃ := D.le₃.trans (D.le_inf₃.trans inf_le_right)
  have hLu := TwelveFiveData.map_conj_mem hc.data (hVM huV) hLmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLu ⊢
  rcases hLu with h | h | h
  · exact Or.inl (map_conj_eq_of_map_conj_eq hc D hV3 huV hWV hW1V hWL hW1L
      hcardW D.cfg.card₁ hc.data.mem₁ h)
  · exact Or.inr (Or.inl (map_conj_eq_of_map_conj_eq hc D hV3 huV hWV hW2V hWL hW2L
      hcardW D.cfg.card₂ hc.data.mem₂ h))
  · exact Or.inr (Or.inr (map_conj_eq_of_map_conj_eq hc D hV3 huV hWV hW3V hWL hW3L
      hcardW D.cfg.card₃ hc.data.mem₃ h))

private structure StarPreimageData (H : Subgroup G) where
  R : Subgroup G
  le : R ≤ H
  subgroupOf_eq : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  normal : (R.subgroupOf H).Normal
  le_normalizer : H ≤ Subgroup.normalizer (R : Set G)
  relPPrimeCore_le : relPPrimeCore 3 H ≤ R
  starImg_eq : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H)
  isPGroup_starImg : IsPGroup 3 ↥(starImg 3 H R)

private theorem starPreimageData_exists (H : Subgroup G) :
    Nonempty (StarPreimageData H) := by
  let R : Subgroup G := ((CFSG.pCore 3 (StarGroup 3 H)).comap
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))).map H.subtype
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hRsub : R.subgroupOf H = (CFSG.pCore 3 (StarGroup 3 H)).comap
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) := by
    dsimp [R]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hRnorm : (R.subgroupOf H).Normal := by
    rw [hRsub]
    infer_instance
  have hHN : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRnorm
  have hOleR : relPPrimeCore 3 H ≤ R := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    dsimp [R]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact (CFSG.pCore 3 (StarGroup 3 H)).one_mem
  have hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H) := by
    dsimp only [starImg, R, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨⟨R, hRH, hRsub, hRnorm, hHN, hOleR, hstarR,
    by rw [hstarR]; exact CFSG.pCore_isPGroup⟩⟩

private theorem pCore_le_starImg_of_inf_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃} {R V : Subgroup G}
    (hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R))
    (hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H))
    (hle : V ⊓ R ≤ D.V) :
    CFSG.pCore 3 (StarGroup 3 H) ≤ starImg 3 H D.V := by
  have hRle : R ≤ relPPrimeCore 3 H ⊔ D.V :=
    hRsup.trans (sup_le le_sup_left (hle.trans le_sup_right))
  have hstarO : starImg 3 H (relPPrimeCore 3 H) = ⊥ := by
    rw [nineTenGen_relPPrimeCore_eq_map Nat.prime_three H]
    dsimp only [starImg, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hOH : relPPrimeCore 3 H ≤ H := sSup_le fun N hN => hN.1
  have hDVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hsup : starImg 3 H (relPPrimeCore 3 H ⊔ D.V) =
      starImg 3 H (relPPrimeCore 3 H) ⊔ starImg 3 H D.V := by
    unfold starImg
    rw [Subgroup.subgroupOf_sup hOH hDVH, Subgroup.map_sup]
  have hmono : starImg 3 H R ≤ starImg 3 H (relPPrimeCore 3 H ⊔ D.V) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (hRle (Subgroup.mem_subgroupOf.mp hy)))
  calc CFSG.pCore 3 (StarGroup 3 H) = starImg 3 H R := hstarR.symm
    _ ≤ starImg 3 H (relPPrimeCore 3 H ⊔ D.V) := hmono
    _ = starImg 3 H (relPPrimeCore 3 H) ⊔ starImg 3 H D.V := hsup
    _ = ⊥ ⊔ starImg 3 H D.V := by rw [hstarO]
    _ = starImg 3 H D.V := bot_sup_eq _

private theorem starImg_le_cStarL_of_hY
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hY : starImg 3 H D.I₁ ≤ cStarL 3 H ∧ starImg 3 H D.I₂ ≤ cStarL 3 H ∧
      starImg 3 H D.I₃ ≤ cStarL 3 H) :
    starImg 3 H D.V ≤ cStarL 3 H := by
  have hDVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  have hI1H : D.I₁ ≤ H := D.le_inf₁.trans inf_le_left
  have hI2H : D.I₂ ≤ H := D.le_inf₂.trans inf_le_left
  have hI3H : D.I₃ ≤ H := D.le_inf₃.trans inf_le_left
  have hsupI : starImg 3 H (D.I₁ ⊔ D.I₂ ⊔ D.I₃) =
      starImg 3 H D.I₁ ⊔ starImg 3 H D.I₂ ⊔ starImg 3 H D.I₃ := by
    unfold starImg
    rw [Subgroup.subgroupOf_sup (sup_le hI1H hI2H) hI3H,
      Subgroup.subgroupOf_sup hI1H hI2H, Subgroup.map_sup, Subgroup.map_sup]
  have hmonoV : starImg 3 H D.V ≤ starImg 3 H (D.I₁ ⊔ D.I₂ ⊔ D.I₃) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (D.V_le (Subgroup.mem_subgroupOf.mp hy)))
  exact hmonoV.trans (by
    rw [hsupI]
    exact sup_le (sup_le hY.1 hY.2.1) hY.2.2)

private theorem starImg_le_centralizer_pCore
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hRstar_le_V0 : CFSG.pCore 3 (StarGroup 3 H) ≤ starImg 3 H D.V) :
    starImg 3 H D.V ≤
      Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H)) := by
  have hV0elem : IsElemAbelian 3 (starImg 3 H D.V) :=
    (D.cfg.elem.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  have hV0comm : IsMulCommutative ↥(starImg 3 H D.V) := hV0elem.1
  have hV0centV0 : starImg 3 H D.V ≤
      Subgroup.centralizer (starImg 3 H D.V : Set (StarGroup 3 H)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV0comm
  exact Subgroup.le_centralizer_iff.mpr (hRstar_le_V0.trans hV0centV0)

private theorem starImg_V_le_pCore_of_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hY : starImg 3 H D.I₁ ≤ cStarL 3 H ∧ starImg 3 H D.I₂ ≤ cStarL 3 H ∧
      starImg 3 H D.I₃ ≤ cStarL 3 H)
    {V R : Subgroup G}
    (hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R))
    (hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H))
    (hle : V ⊓ R ≤ D.V) :
    starImg 3 H D.V ≤ CFSG.pCore 3 (StarGroup 3 H) := by
  have hRstar_le_V0 := pCore_le_starImg_of_inf_le hc hRsup hstarR hle
  have hV0Y := starImg_le_cStarL_of_hY hc D hY
  have hV0cent := starImg_le_centralizer_pCore D hRstar_le_V0
  exact (le_inf hV0Y hV0cent).trans (cStarL_inf_centralizer_le_pCore Nat.prime_three H)

private theorem W_le_V (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {V : Subgroup G}
    (hV0V : D.V ≤ V) : D.W₁ ≤ V ∧ D.W₂ ≤ V ∧ D.W₃ ≤ V := by
  refine ⟨?_, ?_, ?_⟩
  · have h : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
    exact h.trans hV0V
  · have h : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
    exact h.trans hV0V
  · have h : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
    exact h.trans hV0V

private theorem W_le_DV (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≤ D.V ∧ D.W₂ ≤ D.V ∧ D.W₃ ≤ D.V := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right

private theorem W_le_L (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≤ L₁ ∧ D.W₂ ≤ L₂ ∧ D.W₃ ≤ L₃ :=
  ⟨D.le₁.trans (D.le_inf₁.trans inf_le_right),
   D.le₂.trans (D.le_inf₂.trans inf_le_right),
   D.le₃.trans (D.le_inf₃.trans inf_le_right)⟩

private theorem W_pairwise_ne (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≠ D.W₂ ∧ D.W₁ ≠ D.W₃ ∧ D.W₂ ≠ D.W₃ := by
  have h12 : D.W₁ ≠ D.W₂ := by
    intro h
    have hcard := D.cfg.card₁
    have hbot := eq_bot_of_inv_and_comm D.cfg.card₁ D.cfg.inv₁
      (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_left hw)) (le_of_eq h)
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have h13 : D.W₁ ≠ D.W₃ := by
    intro h
    have hcard := D.cfg.card₁
    have hbot := eq_bot_of_inv_and_comm D.cfg.card₁ D.cfg.inv₁
      (fun w hw => D.cfg.comm₁ w (Subgroup.mem_sup_right hw)) (le_of_eq h)
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have h23 : D.W₂ ≠ D.W₃ := by
    intro h
    have hcard := D.cfg.card₂
    have hbot := eq_bot_of_inv_and_comm D.cfg.card₂ D.cfg.inv₂
      (fun w hw => D.cfg.comm₂ w (Subgroup.mem_sup_right hw)) (le_of_eq h)
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  exact ⟨h12, h13, h23⟩

private theorem W₁_map_conj_ne
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    {v : G} (hvV : v ∈ V) (hL1 : L₁.map (MulAut.conj v).toMonoidHom ≠ L₁)
    (hW12 : D.W₁ ≠ D.W₂) (hW13 : D.W₁ ≠ D.W₃) :
    D.W₁.map (MulAut.conj v).toMonoidHom ≠ D.W₁ := by
  obtain ⟨hW1V, hW2V, hW3V⟩ := W_le_V D hV0V
  obtain ⟨hW1L, hW2L, hW3L⟩ := W_le_L D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hVM hvV) (by simp : L₁ ∈ _)
  rcases hmem with h | h | h
  · exact absurd h hL1
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW1V hW2V hW1L hW2L
      D.cfg.card₁ D.cfg.card₂ hc.data.mem₂ h
    rw [hW]; exact hW12.symm
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW1V hW3V hW1L hW3L
      D.cfg.card₁ D.cfg.card₃ hc.data.mem₃ h
    rw [hW]; exact hW13.symm

private theorem W₂_map_conj_ne
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    {v : G} (hvV : v ∈ V) (hL2 : L₂.map (MulAut.conj v).toMonoidHom ≠ L₂)
    (hW12 : D.W₁ ≠ D.W₂) (hW23 : D.W₂ ≠ D.W₃) :
    D.W₂.map (MulAut.conj v).toMonoidHom ≠ D.W₂ := by
  obtain ⟨hW1V, hW2V, hW3V⟩ := W_le_V D hV0V
  obtain ⟨hW1L, hW2L, hW3L⟩ := W_le_L D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hVM hvV) (by simp : L₂ ∈ _)
  rcases hmem with h | h | h
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW2V hW1V hW2L hW1L
      D.cfg.card₂ D.cfg.card₁ hc.data.mem₁ h
    rw [hW]; exact hW12
  · exact absurd h hL2
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW2V hW3V hW2L hW3L
      D.cfg.card₂ D.cfg.card₃ hc.data.mem₃ h
    rw [hW]; exact hW23.symm

private theorem W₃_map_conj_ne
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    {v : G} (hvV : v ∈ V) (hL3 : L₃.map (MulAut.conj v).toMonoidHom ≠ L₃)
    (hW13 : D.W₁ ≠ D.W₃) (hW23 : D.W₂ ≠ D.W₃) :
    D.W₃.map (MulAut.conj v).toMonoidHom ≠ D.W₃ := by
  obtain ⟨hW1V, hW2V, hW3V⟩ := W_le_V D hV0V
  obtain ⟨hW1L, hW2L, hW3L⟩ := W_le_L D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hVM hvV) (by simp : L₃ ∈ _)
  rcases hmem with h | h | h
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW3V hW1V hW3L hW1L
      D.cfg.card₃ D.cfg.card₁ hc.data.mem₁ h
    rw [hW]; exact hW13
  · have hW := map_conj_eq_of_map_conj_eq hc D hV3 hvV hW3V hW2V hW3L hW2L
      D.cfg.card₃ D.cfg.card₂ hc.data.mem₂ h
    rw [hW]; exact hW23
  · exact absurd h hL3

private theorem W₁_map_conj_eq
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    {v : G} (hvV : v ∈ V) (hL1 : L₁.map (MulAut.conj v).toMonoidHom ≠ L₁) :
    D.W₁.map (MulAut.conj v).toMonoidHom = D.W₂ ∨
      D.W₁.map (MulAut.conj v).toMonoidHom = D.W₃ := by
  obtain ⟨hW1V, hW2V, hW3V⟩ := W_le_V D hV0V
  obtain ⟨hW1L, hW2L, hW3L⟩ := W_le_L D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hVM hvV) (by simp : L₁ ∈ _)
  rcases hmem with h | h | h
  · exact absurd h hL1
  · exact Or.inl (map_conj_eq_of_map_conj_eq hc D hV3 hvV hW1V hW2V hW1L hW2L
      D.cfg.card₁ D.cfg.card₂ hc.data.mem₂ h)
  · exact Or.inr (map_conj_eq_of_map_conj_eq hc D hV3 hvV hW1V hW3V hW1L hW3L
      D.cfg.card₁ D.cfg.card₃ hc.data.mem₃ h)

private theorem V_inf_jSub_eq
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {V : Subgroup G} (hV3 : IsPGroup 3 V) (hV0V : D.V ≤ V) :
    V ⊓ jSub M H = D.V := by
  have hVJ : D.V ≤ jSub M H := by
    rw [hc.data.join_eq]
    exact D.V_le.trans (sup_le
      (sup_le (D.le_inf₁.trans (inf_le_right.trans (le_sup_left.trans le_sup_left)))
        (D.le_inf₂.trans (inf_le_right.trans (le_sup_right.trans le_sup_left))))
      (D.le_inf₃.trans (inf_le_right.trans le_sup_right)))
  obtain ⟨A, hAsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (jSub M H)
  have hAcard : Nat.card A = 27 :=
    (TwelveFiveData.card_eq_and_comm_of_isSylowOf_jSub hc.data hn hc.h3 hc.hcard hAsyl).1
  have hDVsyl : CFSG.ABGLocalTools.IsSylowOf 3 D.V (jSub M H) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hVJ (by
      rw [D.cfg.card, ← hAsyl.card_eq, hAcard])
  exact hDVsyl.eq_of_le (le_inf hV0V hVJ) inf_le_right
    (hV3.to_inf_left (H := V) (K := jSub M H))

private theorem D0_t_invariant
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {R : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (R : Set G)) :
    ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G), ∀ x ∈ R ⊓ D.V, t * x * t⁻¹ ∈ R ⊓ D.V := by
  intro t ht x hx
  refine ⟨?_, IsE27InvConfig.conj_mem D.cfg ht hx.2⟩
  have htH : t ∈ H := by
    have ht' := ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact (D.t₁_mem hc.data).1
    · exact (D.t₂_mem hc.data).1
    · exact (D.t₃_mem hc.data).1
  exact (Subgroup.mem_normalizer_iff.mp (hHN htH) x).mp hx.1

private theorem D0_v_invariant
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {V R : Subgroup G}
    (hVJeq : V ⊓ jSub M H = D.V) {v : G} (hvV : v ∈ V) (hvR : v ∈ R)
    (hvHM : v ∈ H ⊓ M) (hHN : H ≤ Subgroup.normalizer (R : Set G)) :
    v ∈ Subgroup.normalizer (R ⊓ D.V : Set G) := by
  have hvVnorm : v ∈ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer hvV
  have hvJnorm : v ∈ Subgroup.normalizer (jSub M H : Set G) :=
    TwelveFiveData.le_normalizer_jSub hc.data hvHM.2
  have hvDVnorm : v ∈ Subgroup.normalizer (D.V : Set G) := by
    rw [← hVJeq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hvVnorm, hvJnorm⟩
  have hvRnorm : v ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hvR
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hvRnorm, hvDVnorm⟩

private theorem exists_w_not_mem_W2_W3
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hW12 : D.W₁ ≠ D.W₂) (hW13 : D.W₁ ≠ D.W₃) :
    ∃ w : G, w ∈ D.W₁ ∧ w ≠ 1 ∧ w ∉ D.W₂ ∧ w ∉ D.W₃ ∧ orderOf w = 3 := by
  obtain ⟨w, hwW1, hw1⟩ : ∃ w : G, w ∈ D.W₁ ∧ w ≠ 1 := by
    by_contra hall
    have hbot : D.W₁ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall D.W₁).mpr ?_
      intro x hx
      by_contra hx1
      exact hall ⟨x, hx, hx1⟩
    have hcard := D.cfg.card₁
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hwOrd : orderOf w = 3 := by
    have hdvd : orderOf w ∣ Nat.card D.W₁ := Subgroup.orderOf_dvd_natCard D.W₁ hwW1
    rw [D.cfg.card₁] at hdvd
    have hne1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hwW2 : w ∉ D.W₂ := by
    intro hmem
    have hzW1 : Subgroup.zpowers w = D.W₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW1) (by
        rw [Nat.card_zpowers, hwOrd, D.cfg.card₁])
    have hzW2 : Subgroup.zpowers w = D.W₂ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
        rw [Nat.card_zpowers, hwOrd, D.cfg.card₂])
    exact hW12 (hzW1.symm.trans hzW2)
  have hwW3 : w ∉ D.W₃ := by
    intro hmem
    have hzW1 : Subgroup.zpowers w = D.W₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW1) (by
        rw [Nat.card_zpowers, hwOrd, D.cfg.card₁])
    have hzW3 : Subgroup.zpowers w = D.W₃ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by
        rw [Nat.card_zpowers, hwOrd, D.cfg.card₃])
    exact hW13 (hzW1.symm.trans hzW3)
  exact ⟨w, hwW1, hw1, hwW2, hwW3, hwOrd⟩

private theorem commutator_mem_D0
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {R : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (R : Set G)) {v : G} (hvR : v ∈ R)
    (hW1v : D.W₁.map (MulAut.conj v).toMonoidHom = D.W₂ ∨
      D.W₁.map (MulAut.conj v).toMonoidHom = D.W₃)
    {w : G} (hwW1 : w ∈ D.W₁) :
    w * v * w⁻¹ * v⁻¹ ∈ R ⊓ D.V := by
  obtain ⟨hW1DV, hW2DV, hW3DV⟩ := W_le_DV D
  have hDVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hW1H : D.W₁ ≤ H := hW1DV.trans hDVH
  have hcR : w * v * w⁻¹ * v⁻¹ ∈ R :=
    R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN (hW1H hwW1)) v).mp hvR)
      (R.inv_mem hvR)
  have hcDV : w * v * w⁻¹ * v⁻¹ ∈ D.V := by
    rcases hW1v with h | h
    · have hmem : v * w⁻¹ * v⁻¹ ∈ D.W₂ := by
        have := Subgroup.mem_map_of_mem (MulAut.conj v).toMonoidHom (D.W₁.inv_mem hwW1)
        rw [h] at this
        change v * w⁻¹ * v⁻¹ ∈ D.W₂
        exact this
      have hmul : w * (v * w⁻¹ * v⁻¹) ∈ D.V :=
        Subgroup.mul_mem D.V (hW1DV hwW1) (hW2DV hmem)
      simpa [mul_assoc] using hmul
    · have hmem : v * w⁻¹ * v⁻¹ ∈ D.W₃ := by
        have := Subgroup.mem_map_of_mem (MulAut.conj v).toMonoidHom (D.W₁.inv_mem hwW1)
        rw [h] at this
        change v * w⁻¹ * v⁻¹ ∈ D.W₃
        exact this
      have hmul : w * (v * w⁻¹ * v⁻¹) ∈ D.V :=
        Subgroup.mul_mem D.V (hW1DV hwW1) (hW3DV hmem)
      simpa [mul_assoc] using hmul
  exact ⟨hcR, hcDV⟩

private theorem commutator_ne_one
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {v : G}
    (hW1v : D.W₁.map (MulAut.conj v).toMonoidHom = D.W₂ ∨
      D.W₁.map (MulAut.conj v).toMonoidHom = D.W₃)
    {w : G} (hwW1 : w ∈ D.W₁) (hwW2 : w ∉ D.W₂) (hwW3 : w ∉ D.W₃) :
    w * v * w⁻¹ * v⁻¹ ≠ 1 := by
  intro hc1
  have h1 : w * v * w⁻¹ = v := by
    have := congrArg (fun x => x * v) hc1
    simpa [mul_assoc] using this
  have h2 : w * v = v * w := by
    calc w * v = (w * v * w⁻¹) * w := by group
      _ = v * w := by rw [h1]
  have hconj : v * w * v⁻¹ = w := by
    rw [← h2]
    group
  rcases hW1v with h | h
  · apply hwW2
    have hmem : v * w * v⁻¹ ∈ D.W₂ := by
      have := Subgroup.mem_map_of_mem (MulAut.conj v).toMonoidHom hwW1
      rw [h] at this
      change v * w * v⁻¹ ∈ D.W₂
      exact this
    rwa [hconj] at hmem
  · apply hwW3
    have hmem : v * w * v⁻¹ ∈ D.W₃ := by
      have := Subgroup.mem_map_of_mem (MulAut.conj v).toMonoidHom hwW1
      rw [h] at this
      change v * w * v⁻¹ ∈ D.W₃
      exact this
    rwa [hconj] at hmem

private theorem W_le_D0
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {V R D0 : Subgroup G}
    (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    (hD0le : D0 ≤ D.V) (hD0ne : D0 ≠ ⊥)
    (hD0t : ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G), ∀ x ∈ D0, t * x * t⁻¹ ∈ D0)
    {v : G} (hvV : v ∈ V) (hvD0norm : v ∈ Subgroup.normalizer (D0 : Set G))
    (hW1v_ne : D.W₁.map (MulAut.conj v).toMonoidHom ≠ D.W₁)
    (hW2v_ne : D.W₂.map (MulAut.conj v).toMonoidHom ≠ D.W₂)
    (hW3v_ne : D.W₃.map (MulAut.conj v).toMonoidHom ≠ D.W₃)
    (hne : D.W₁ ≠ D.W₂ ∧ D.W₁ ≠ D.W₃ ∧ D.W₂ ≠ D.W₃) :
    D.W₁ ≤ D0 ∧ D.W₂ ≤ D0 ∧ D.W₃ ≤ D0 := by
  have hDW : D.W₁ ≤ D0 ∨ D.W₂ ≤ D0 ∨ D.W₃ ≤ D0 :=
    D.cfg.exists_le_of_invariant hD0le hD0ne hD0t
  have hzV3 : IsPGroup 3 (Subgroup.zpowers v) :=
    hV3.to_le (Subgroup.zpowers_le.mpr hvV)
  have hzvD0 : Subgroup.zpowers v ≤ Subgroup.normalizer (D0 : Set G) :=
    Subgroup.zpowers_le.mpr hvD0norm
  obtain ⟨hW1V, hW2V, hW3V⟩ := W_le_V D hV0V
  obtain ⟨hW1L, hW2L, hW3L⟩ := W_le_L D
  rcases hDW with h1 | h2 | h3
  · have horb : ∀ u : ↥(Subgroup.zpowers v),
        D.W₁.map (MulAut.conj (u : G)).toMonoidHom ∈
          ({D.W₁, D.W₂, D.W₃} : Set (Subgroup G)) :=
      fun u => map_conj_mem_three_of_le hc D hV3 hVM hV0V
        (Subgroup.zpowers_le.mpr hvV u.2) hW1V hW1L D.cfg.card₁ (by simp)
    exact le_three_of_orbit hzV3 hne.1 hne.2.1 hne.2.2 h1 hzvD0 hW1v_ne horb
  · have horb : ∀ u : ↥(Subgroup.zpowers v),
        D.W₂.map (MulAut.conj (u : G)).toMonoidHom ∈
          ({D.W₁, D.W₂, D.W₃} : Set (Subgroup G)) :=
      fun u => map_conj_mem_three_of_le hc D hV3 hVM hV0V
        (Subgroup.zpowers_le.mpr hvV u.2) hW2V hW2L D.cfg.card₂ (by simp)
    exact le_three_of_orbit hzV3 hne.1 hne.2.1 hne.2.2 h2 hzvD0 hW2v_ne horb
  · have horb : ∀ u : ↥(Subgroup.zpowers v),
        D.W₃.map (MulAut.conj (u : G)).toMonoidHom ∈
          ({D.W₁, D.W₂, D.W₃} : Set (Subgroup G)) :=
      fun u => map_conj_mem_three_of_le hc D hV3 hVM hV0V
        (Subgroup.zpowers_le.mpr hvV u.2) hW3V hW3L D.cfg.card₃ (by simp)
    exact le_three_of_orbit hzV3 hne.1 hne.2.1 hne.2.2 h3 hzvD0 hW3v_ne horb

private theorem starImg_le_pCore_of_le
    {D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃} {R : Subgroup G}
    (hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H))
    (hDVleR : D.V ≤ R) :
    starImg 3 H D.V ≤ CFSG.pCore 3 (StarGroup 3 H) := by
  rw [← hstarR]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
    (hDVleR (Subgroup.mem_subgroupOf.mp hy)))

private theorem starImg_V_le_pCore_of_not_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {V R : Subgroup G} (hV3 : IsPGroup 3 V) (hVM : V ≤ M) (hV0V : D.V ≤ V)
    (hVHM : V ≤ H ⊓ M) (hHN : H ≤ Subgroup.normalizer (R : Set G))
    (hVJeq : V ⊓ jSub M H = D.V)
    (hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H))
    {v : G} (hvVR : v ∈ V ⊓ R) (hvV0 : v ∉ D.V) :
    starImg 3 H D.V ≤ CFSG.pCore 3 (StarGroup 3 H) := by
  have hvV : v ∈ V := hvVR.1
  have hvR : v ∈ R := hvVR.2
  have hvHM : v ∈ H ⊓ M := hVHM hvV
  have hne := W_pairwise_ne D
  have hL1move : L₁.map (MulAut.conj v).toMonoidHom ≠ L₁ :=
    hc.map_conj_ne_of_not_mem D hn hVM hV3 hV0V hvV hvV0 (by simp)
  have hL2move : L₂.map (MulAut.conj v).toMonoidHom ≠ L₂ :=
    hc.map_conj_ne_of_not_mem D hn hVM hV3 hV0V hvV hvV0 (by simp)
  have hL3move : L₃.map (MulAut.conj v).toMonoidHom ≠ L₃ :=
    hc.map_conj_ne_of_not_mem D hn hVM hV3 hV0V hvV hvV0 (by simp)
  have hW1v_ne := W₁_map_conj_ne hc D hV3 hVM hV0V hvV hL1move hne.1 hne.2.1
  have hW2v_ne := W₂_map_conj_ne hc D hV3 hVM hV0V hvV hL2move hne.1 hne.2.2
  have hW3v_ne := W₃_map_conj_ne hc D hV3 hVM hV0V hvV hL3move hne.2.1 hne.2.2
  have hW1v := W₁_map_conj_eq hc D hV3 hVM hV0V hvV hL1move
  obtain ⟨w, hwW1, _, hwW2, hwW3, _⟩ := exists_w_not_mem_W2_W3 D hne.1 hne.2.1
  have hcomm := commutator_mem_D0 hc D hHN hvR hW1v hwW1
  have hcomm_ne := commutator_ne_one D hW1v hwW1 hwW2 hwW3
  let D0 : Subgroup G := R ⊓ D.V
  have hD0ne : D0 ≠ ⊥ := by
    intro hbot
    have hmem : w * v * w⁻¹ * v⁻¹ ∈ D0 := hcomm
    rw [hbot] at hmem
    exact hcomm_ne (Subgroup.mem_bot.mp hmem)
  have hD0t : ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G), ∀ x ∈ D0, t * x * t⁻¹ ∈ D0 :=
    D0_t_invariant hc D hHN
  have hvD0norm : v ∈ Subgroup.normalizer (D0 : Set G) :=
    D0_v_invariant hc D hVJeq hvV hvR hvHM hHN
  have hWleD0 := W_le_D0 (R := R) hc D hV3 hVM hV0V inf_le_right hD0ne hD0t hvV hvD0norm
    hW1v_ne hW2v_ne hW3v_ne hne
  have hDVleD0 : D.V ≤ D0 := by
    rw [D.cfg.join]
    exact sup_le (sup_le hWleD0.1 hWleD0.2.1) hWleD0.2.2
  exact starImg_le_pCore_of_le hstarR (hDVleD0.trans inf_le_left)

theorem TwelveSixKCtx.starImg_V_le_pCore
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (hY : starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H) :
    starImg p H D.V ≤ CFSG.pCore p (StarGroup p H) := by
  subst p
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hd : NineSettingGen G M 3 E H E 2 :=
    (hc.ctx.hypCGen hEQ hE hEc hΓ).toNineSettingGen
  have hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hc.ctx.p_not_mem_sigma
  have hU : NineNineOne M 3 := hc.hI G M E H E 3 hd hpσ
  have hDVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  obtain ⟨V, hVsyl, hV0V⟩ :=
    exists_isSylowOf_ge hDVHM (CFSG.Open.IsElemAbelian.isPGroup D.cfg.elem)
  have hVsylH : CFSG.ABGLocalTools.IsSylowOf 3 V H :=
    (isSylowOf_of_NineNineOne hc.ctx.maxLocal hc.ctx.mem_QSet hc.ctx.Q_le_H hpσ hU hVsyl).1
  have hV3 : IsPGroup 3 V := hVsylH.isPGroup
  have hVM : V ≤ M := hVsyl.le.trans inf_le_right
  obtain ⟨Rdata⟩ := starPreimageData_exists (G := G) H
  let R := Rdata.R
  have hRH : R ≤ H := Rdata.le
  have hHN : H ≤ Subgroup.normalizer (R : Set G) := Rdata.le_normalizer
  have hOleR : relPPrimeCore 3 H ≤ R := Rdata.relPPrimeCore_le
  have hstarR : starImg 3 H R = CFSG.pCore 3 (StarGroup 3 H) := Rdata.starImg_eq
  have hUp : IsPGroup 3 ↥(starImg 3 H R) := Rdata.isPGroup_starImg
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 (V ⊓ R) R :=
    hVsylH.inf_of_le_normalizer hRH hHN
  have hRsup : R ≤ relPPrimeCore 3 H ⊔ (V ⊓ R) :=
    nineTenGen_le_sup_of_starImg_isPGroup Nat.prime_three hRH hOleR hUp hS'
  by_cases hle : V ⊓ R ≤ D.V
  · exact starImg_V_le_pCore_of_le hc D hY hRsup hstarR hle
  · obtain ⟨v, hvVR, hvV0⟩ : ∃ v : G, v ∈ V ⊓ R ∧ v ∉ D.V := by
      by_contra h
      apply hle
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    have hVJeq := V_inf_jSub_eq hc D hn hV3 hV0V
    exact starImg_V_le_pCore_of_not_le hc D hn hV3 hVM hV0V hVsyl.le hHN hVJeq
      hstarR hvVR hvV0



end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
