
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.Vol2.Ch1List

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_1_three lemma_1_2_2_b
  Lemma122A lemma_1_2_4_exists lemma_1_2_4_unique lemma_1_2_4_existsUnique lemma_1_2_4_normal
  lemma_1_2_4_list normal_conjClosure_of_pCoreOf_ne_bot

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_1_three_of_a3 {H L : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hL : L ∈ cComp H) :
    (L.subgroupOf H).Normal ∨
      (Set.ncard (conjSubgroupsBy H L) = 2 ∧ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hLb := modO2Image_mem_cComp hL
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨hL1, -⟩ := h38 _ hLb
  rcases hL1 with hnorm | ⟨htypes, t', ht'n, -, -, hcl'⟩
  · left
    exact normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
      (subgroupOf_mem_cComp hL) hnorm
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨th, hth⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) t'
      set Lb := modO2Image H L with hLb'
      have hL₂ : L.map (MulAut.conj (th : G)).toMonoidHom ∈ cComp H :=
        map_conj_mem_cComp hL th.2
      have hL₂b : modO2Image H (L.map (MulAut.conj (th : G)).toMonoidHom) =
          Lb.map (MulAut.conj t').toMonoidHom := by
        rw [modO2Image_conj th, hth]
      have hne : L ≠ L.map (MulAut.conj (th : G)).toMonoidHom := by
        intro h
        apply ht'n
        have : Lb.map (MulAut.conj t').toMonoidHom = Lb := by
          rw [← hL₂b, ← h]
        exact A38.map_conj_eq_iff.mp this
      have hset : conjSubgroupsBy H L = {L, L.map (MulAut.conj (th : G)).toMonoidHom} := by
        ext K'
        constructor
        · rintro ⟨h, hhH, rfl⟩
          have hLh : L.map (MulAut.conj h).toMonoidHom ∈ cComp H := map_conj_mem_cComp hL hhH
          have hb : modO2Image H (L.map (MulAut.conj h).toMonoidHom) =
              Lb.map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hhH⟩)).toMonoidHom :=
            modO2Image_conj ⟨h, hhH⟩
          set g := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨h, hhH⟩ with hg
          have hLg := A38.cComp_conj (t := g) hLb
          have hLt' := A38.cComp_conj (t := t') hLb
          have hle : Lb.map (MulAut.conj g).toMonoidHom ≤
              Lb ⊔ Lb.map (MulAut.conj t').toMonoidHom := by
            rw [← hcl']
            intro x hx
            rw [A38.mem_map_conj] at hx
            have := mem_conjClosure (Subgroup.mem_top g) hx
            simpa [mul_assoc] using this
          rcases A38.eq_or_eq_of_le_sup h37 hLg hLb hLt' hle with h1 | h1
          · left
            exact (modO2Image_injOn H) hLh hL (by rw [hb, h1])
          · right
            exact (modO2Image_injOn H) hLh hL₂ (by rw [hb, hL₂b, h1])
        · rintro (rfl | rfl)
          · exact ⟨1, H.one_mem, (by ext x; simp)⟩
          · exact ⟨th, th.2, rfl⟩
      rw [hset]
      exact Set.ncard_pair hne
    · obtain ⟨e⟩ := modO2_mulEquiv hL
      exact A38Types.of_mulEquiv e.symm htypes

theorem lemma_1_2_1_three (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) :
    (L.subgroupOf H).Normal ∨
      (Set.ncard (conjSubgroupsBy H L) = 2 ∧ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)) :=
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  lemma_1_2_1_three_of_a3 (h37 _ hQ) (h38 _ hQ) hL

@[expose] def Lemma122A : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QTKECore G → ∀ H L : Subgroup G, pCoreOf 2 H ≠ ⊥ → L ∈ cComp H → ∀ p : ℕ, p.Prime → p ≠ 2 →
      Set.ncard (conjSubgroupsBy H L) = 2 → p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) →
        Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} = conjClosure L H

theorem lemma_1_2_2_b (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (hrank : Lemma122Rank) {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : CFSG.Open.pRank p L = 2) :
    (L.subgroupOf H).Normal := by
  rcases lemma_1_2_1_three hK h37 h38 hH hL with hn | ⟨-, htypes⟩
  · exact hn
  · exfalso
    have h1 := hrank _ htypes p hp hp2
    rw [pRank_modO2_eq L hp hp2, hm] at h1
    omega

theorem lemma_1_2_4_normal_of_a3 {H S B L : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hS : IsSylowTwoOf S H) (hB : B ∈ lFamily S) (hBL : B ≤ L) (hL : L ∈ cComp H)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) : (L.subgroupOf H).Normal := by
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs'
    have hLs : L.map (MulAut.conj s).toMonoidHom ∈ cComp H := map_conj_mem_cComp hL (hS.1 hs')
    have hBs : B.map (MulAut.conj s).toMonoidHom = B := A38.map_conj_eq_iff.mpr (hSB hs')
    have hBLs : B ≤ L.map (MulAut.conj s).toMonoidHom := by
      rw [← hBs]
      exact Subgroup.map_mono hBL
    have := CFSG.Quasithin.lemma_1_2_4_unique h37 hB hL hLs hBL hBLs
    exact A38.map_conj_eq_iff.mp this.symm
  have hLb := modO2Image_mem_cComp hL
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2⟩ := h38 _ hLb
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨t, htT, htn, -⟩
  · exact normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
      (subgroupOf_mem_cComp hL) hnorm
  · exfalso
    apply htn
    obtain ⟨s', hs'T, rfl⟩ := htT
    have hs'N : s' ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hsG : (s' : G) ∈ S := hs'T
      have := (Subgroup.mem_normalizer_iff.mp (hSL hsG) (x : G))
      simpa using this
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      ⟨s', hs'N, rfl⟩

theorem lemma_1_2_4_normal (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    {H S B L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hB : B ∈ lFamily S)
    (hBL : B ≤ L) (hL : L ∈ cComp H) (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    (L.subgroupOf H).Normal :=
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  lemma_1_2_4_normal_of_a3 (h37 _ hQ) (h38 _ hQ) hS hB hBL hL hSB

theorem lemma_1_2_4_list_of_a3 {H S B L : Subgroup G}
    (h312 : A312Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) (hL : L ∈ cComp H) (hBL : B ≤ L) :
    modO2Image H B = modO2Image H L ∨ A312Case (modO2Image H B) (modO2Image H L) ∨
      A312Nonquasi (modO2Image H B) (modO2Image H L) := by
  have hSbar := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨L', hL', hBL', huniq, hlist⟩ := h312 _ hSbar _ (modO2Image_mem_lFamily hS hBH hB)
  have hLbar : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_mem_cComp hL
  have hBLbar : modO2Image H B ≤ modO2Image H L :=
    Subgroup.map_mono (fun x hx => hBL hx)
  have heq : modO2Image H L = L' := huniq _ hLbar hBLbar
  rw [heq]
  exact hlist

theorem lemma_1_2_4_list (hK : LocalSQTK G) (h312 : A312ForSQTKCat) {H S B L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H) (hB : B ∈ lFamily S)
    (hL : L ∈ cComp H) (hBL : B ≤ L) :
    modO2Image H B = modO2Image H L ∨ A312Case (modO2Image H B) (modO2Image H L) ∨
      A312Nonquasi (modO2Image H B) (modO2Image H L) :=
  lemma_1_2_4_list_of_a3 (h312 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH)) hS hBH hB hL hBL

end Ambient

end CFSG.QuasithinUnique.Vol2Native
