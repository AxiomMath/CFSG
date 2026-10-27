module

public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Q3.TL3T49
public import CFSG.ClassicalInvolution.Q3.TL3T54
public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem even_vec_four : ∀ u : Fin 4 → ZMod 2, u 0 + u 1 + u 2 + u 3 = 0 →
    u = 0 ∨ u = (fun _ => 1) ∨ ∃ i j : Fin 4, i ≠ j ∧ u = TL4.pairVec i j := by
  decide +kernel

theorem zQ_vec : zQ.vec = fun _ => 1 := by decide

theorem eq_embedVec_of_vanish (ι : Fin 4 ↪ Fin n) {v : Fin n → ZMod 2}
    (hv : ∀ x, x ∉ Set.range ι → v x = 0) : v = embedVec ι (fun i => v (ι i)) := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply]
  · rw [embedVec_of_not_mem ι _ hx, hv x hx]

theorem sum_eq_sum_four (ι : Fin 4 ↪ Fin n) {v : Fin n → ZMod 2}
    (hv : ∀ x, x ∉ Set.range ι → v x = 0) : ∑ x, v x = v (ι 0) + v (ι 1) + v (ι 2) + v (ι 3) := by
  classical
  have h1 : ∑ x ∈ (Finset.univ : Finset (Fin 4)).map ι, v x = ∑ x, v x :=
    Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hv x (by
      rintro ⟨i, rfl⟩
      exact hx (Finset.mem_map_of_mem ι (Finset.mem_univ i)))
  rw [← h1, Finset.sum_map, Fin.sum_univ_four]

theorem vec_trichotomy {δ : Finset (Fin n)} (hδ : δ.card = 4) {b : Bool} {x x' : Wr n}
    (hx : x ∈ memAt δ hδ b) (hx' : x' ∈ memAt δ hδ (!b)) (hp : (x * x').perm = 1) :
    x * x' = 1 ∨ x * x' = zOf (emb δ hδ) ∨
      ∃ a ∈ δ, ∃ c ∈ δ, a ≠ c ∧ x * x' = ofVec (TL4.pairVec a c) := by
  set ι := emb δ hδ with hι
  have hsupp : SupportedOn (x * x') (Set.range ι) :=
    (supportedOn_of_mem_memAt hx).mul (supportedOn_of_mem_memAt hx')
  have hvan : ∀ y, y ∉ Set.range ι → (x * x').vec y = 0 := fun y hy => (hsupp y hy).1
  have hxx : x * x' = ofVec (x * x').vec := Wr.ext rfl hp
  have hmem : x * x' ∈ aeSub n :=
    (aeSub n).mul_mem (memAt_le_aeSub δ hδ b hx) (memAt_le_aeSub δ hδ (!b) hx')
  have hsum : ∑ y, (x * x').vec y = 0 := hmem.1
  rw [sum_eq_sum_four ι hvan] at hsum
  have hrange : ∀ i, ι i ∈ δ := fun i => by
    have : ι i ∈ Set.range ι := ⟨i, rfl⟩
    rw [hι, range_emb] at this
    exact_mod_cast this
  rcases even_vec_four (fun i => (x * x').vec (ι i)) hsum with h0 | h1 | ⟨i, j, hij, hu⟩
  · left
    rw [hxx, eq_embedVec_of_vanish ι hvan, h0]
    have h00 : embedVec ι (0 : Fin 4 → ZMod 2) = 0 := by
      funext y
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨k, rfl⟩ := hy
        rw [embedVec_apply]
        rfl
      · rw [embedVec_of_not_mem ι _ hy]
        rfl
    rw [h00]
    rfl
  · right; left
    have hz : zQ = ofVec (fun _ => 1) := by rw [← zQ_vec]; rfl
    rw [hxx, eq_embedVec_of_vanish ι hvan, h1, zOf, hz, TC.Thin.embed_ofVec]
  · right; right
    refine ⟨ι i, hrange i, ι j, hrange j, fun e => hij (ι.injective e), ?_⟩
    rw [hxx, eq_embedVec_of_vanish ι hvan, hu, TC.Thin.embedVec_pairVec]

theorem vbar_pairVec_ne_one (hn : 3 ≤ n) {a c : Fin n} (hac : a ≠ c) :
    mkQ n (ofVec (TL4.pairVec a c)) ≠ 1 := by
  classical
  intro h
  rcases mem_piSub.mp ((QuotientGroup.eq_one_iff _).mp h) with h1 | h1
  · have := congrFun (congrArg Wr.vec h1) a
    change TL4.pairVec a c a = (0 : ZMod 2) at this
    rw [TL4.pairVec_apply] at this
    simp [hac] at this
  · obtain ⟨d, hda, hdc⟩ : ∃ d : Fin n, d ≠ a ∧ d ≠ c := by
      by_contra hne
      push Not at hne
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, c} := fun d _ => by
        by_cases hd : d = a
        · simp [hd]
        · simp [hne d hd]
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h2
      have h3 := Finset.card_insert_le a ({c} : Finset (Fin n))
      rw [Finset.card_singleton] at h3
      omega
    have := congrFun (congrArg Wr.vec h1) d
    change TL4.pairVec a c d = (1 : ZMod 2) at this
    rw [TL4.pairVec_apply] at this
    simp [hda, hdc] at this

theorem vbar_pairVec_ne_zBar (hn : 7 ≤ n) (a c : Fin n) (δ : Finset (Fin n))
    (hδ : δ.card = 4) : mkQ n (ofVec (TL4.pairVec a c)) ≠ zBar δ hδ := by
  classical
  intro h
  rw [zBar, mkQ_eq_iff] at h
  obtain ⟨d, hdδ, hda, hdc⟩ : ∃ d ∈ δ, d ≠ a ∧ d ≠ c := by
    by_contra hne
    push Not at hne
    have hsub : δ ⊆ {a, c} := fun d hd => by
      by_cases hda : d = a
      · simp [hda]
      · simp [hne d hd hda]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le a ({c} : Finset (Fin n))
    rw [Finset.card_singleton] at h3
    omega
  obtain ⟨e, he⟩ := AE.Block4.exists_not_mem (s := δ ∪ {a, c}) (by
    have h1 := Finset.card_union_le δ {a, c}
    have h3 := Finset.card_insert_le a ({c} : Finset (Fin n))
    rw [Finset.card_singleton] at h3
    omega)
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at he
  have hdr : d ∈ Set.range (emb δ hδ) := by rw [range_emb]; exact_mod_cast hdδ
  have her : e ∉ Set.range (emb δ hδ) := by rw [range_emb]; exact_mod_cast he.1
  have hd : (zOf (emb δ hδ)).vec d = 1 := by
    rw [zOf_vec_apply]
    simp [hdr]
  have he' : (zOf (emb δ hδ)).vec e = 0 := by
    rw [zOf_vec_apply]
    simp [her]
  rcases h with h1 | h1
  · have h2 : ofVec (TL4.pairVec a c) = zOf (emb δ hδ) := inv_mul_eq_one.mp h1
    have := congrFun (congrArg Wr.vec h2) d
    rw [hd] at this
    change TL4.pairVec a c d = (1 : ZMod 2) at this
    rw [TL4.pairVec_apply] at this
    simp [hda, hdc] at this
  · have h2 : zOf (emb δ hδ) = ofVec (TL4.pairVec a c) * allOnes n :=
      inv_mul_eq_iff_eq_mul.mp h1
    have := congrFun (congrArg Wr.vec h2) e
    rw [he', mul_vec] at this
    change (0 : ZMod 2) = TL4.pairVec a c e + 1 at this
    rw [TL4.pairVec_apply] at this
    simp [he.2.1, he.2.2] at this

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.map_mul_twins (I : AEIdent P n) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    {δ : Finset (Fin n)} {hδ : δ.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar δ hδ b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!b)) {l l' : G} (hl : l ∈ L)
    (hl' : l' ∈ L')
    (hp : permQ n (I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩) = 1) :
    I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ = 1 ∨
      I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ = zBar δ hδ ∨
      ∃ a ∈ δ, ∃ c ∈ δ, a ≠ c ∧
        I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ =
          mkQ n (ofVec (TL4.pairVec a c)) := by
  have h1 : I.φ ⟨l, le_pSpan hL hl⟩ ∈ memBar δ hδ b := by
    rw [← hlab]
    exact I.mem_map hL hl
  have h2 : I.φ ⟨l', le_pSpan hL' hl'⟩ ∈ memBar δ hδ (!b) := by
    rw [← hlab']
    exact I.mem_map hL' hl'
  obtain ⟨x, hx, hxe⟩ := h1
  obtain ⟨x', hx', hxe'⟩ := h2
  have e : I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ = mkQ n (x * x') := by
    have e0 : (⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ : ↥(pSpan P)) =
        ⟨l, le_pSpan hL hl⟩ * ⟨l', le_pSpan hL' hl'⟩ := rfl
    rw [e0, map_mul, ← hxe, ← hxe', ← map_mul]
  rw [e] at hp ⊢
  rcases vec_trichotomy hδ hx hx' hp with h | h | ⟨a, ha, c, hc, hac, h⟩
  · left
    rw [h, map_one]
  · right; left
    rw [h]
    rfl
  · right; right
    exact ⟨a, ha, c, hc, hac, by rw [h]⟩

theorem AEIdent.exists_mul_eq_pairVec (I : AEIdent P n) {L L' : Subgroup G} (hL : L ∈ P)
    (hL' : L' ∈ P) {δ : Finset (Fin n)} {hδ : δ.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar δ hδ b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!b)) :
    ∃ l ∈ L, ∃ l' ∈ L', ∃ a ∈ δ, ∃ c ∈ δ, a ≠ c ∧
      ∃ hll : l * l' ∈ pSpan P, I.φ ⟨l * l', hll⟩ = mkQ n (ofVec (TL4.pairVec a c)) := by
  set ι := emb δ hδ with hι
  obtain ⟨k, hk, k', hk', hkk⟩ := pair_mem_twins b 0 1 (by decide)
  have hm : mkQ n (embed ι k) ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact mkQ_embed_mem_memBar hk
  have hm' : mkQ n (embed ι k') ∈ (L'.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab']
    exact mkQ_embed_mem_memBar hk'
  obtain ⟨l, hl, hle⟩ := I.exists_of_mem_map hL hm
  obtain ⟨l', hl', hle'⟩ := I.exists_of_mem_map hL' hm'
  have hrange : ∀ i, ι i ∈ δ := fun i => by
    have : ι i ∈ Set.range ι := ⟨i, rfl⟩
    rw [hι, range_emb] at this
    exact_mod_cast this
  refine ⟨l, hl, l', hl', ι 0, hrange 0, ι 1, hrange 1,
    fun e => absurd (ι.injective e) (by decide), mul_mem (le_pSpan hL hl) (le_pSpan hL' hl'), ?_⟩
  have e : (⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ : ↥(pSpan P)) =
      ⟨l, le_pSpan hL hl⟩ * ⟨l', le_pSpan hL' hl'⟩ := rfl
  rw [e, map_mul, hle, hle', ← map_mul, ← map_mul, hkk, embed_ofVec, embedVec_pairVec]

theorem AEIdent.conj_mem_ker_permHom [Finite G] (I : AEIdent P n) (hn : 5 ≤ n)
    (hH : TL4.AECoverHyp I) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) {x : ↥(pSpan P)}
    (hx : x ∈ (AECov.permHom I).ker) : conjSpan ha x ∈ (AECov.permHom I).ker := by
  have ha' : a⁻¹ ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ ha
  have hsurj : Function.Surjective (conjSpan ha) := fun y =>
    ⟨conjSpan ha' y, Subtype.ext (by rw [conjSpan_apply, conjSpan_apply]; group)⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    AECov.comm_of_isUniqueInvolution I hn hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL' hu
      hu'
  have h2 : IsPGroup 2 ↥(AECov.permHom I).ker :=
    AECov.isPGroup_ker_permHom I hn hH.card hH.ker_two (AECov.zSpan_elem hcomm)
  have hT : ((AECov.permHom I).ker.map (conjSpan ha)).Normal :=
    (MonoidHom.normal_ker _).map _ hsurj
  have hT2 : IsPGroup 2 ↥((AECov.permHom I).ker.map (conjSpan ha)) := h2.map _
  exact AECov.le_ker_permHom_of_normal I hn hT hT2 ⟨x, hx, rfl⟩

end CFSG.ClassicalInvolution.Q3.TC.Thin
