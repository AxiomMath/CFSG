module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.StronglyEmbedded
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.ConjOrderP

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

section Conj

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem eq_of_card_eq_of_le_cyclic {Q X Y : Subgroup G} (hQ : IsCyclic ↥Q) (hX : X ≤ Q)
    (hY : Y ≤ Q) (hXc : Nat.card X = p) (hYc : Nat.card Y = p) : X = Y := by
  have hX' : Nat.card (X.subgroupOf Q) = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv).trans hXc
  have hY' : Nat.card (Y.subgroupOf Q) = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv).trans hYc
  have heq : X.subgroupOf Q = Y.subgroupOf Q :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (hX'.trans hY'.symm)
  calc X = (X.subgroupOf Q).map Q.subtype := (Subgroup.map_subgroupOf_eq_of_le hX).symm
    _ = (Y.subgroupOf Q).map Q.subtype := by rw [heq]
    _ = Y := Subgroup.map_subgroupOf_eq_of_le hY

theorem exists_conj_mem_of_card_eq
    (hcyc : ∀ R : Subgroup G, IsPGroup p R → IsCyclic R) {H B C : Subgroup G}
    (hBH : B ≤ H) (hCH : C ≤ H) (hB : Nat.card B = p) (hC : Nat.card C = p) :
    ∃ g ∈ H, C = B.map (MulAut.conj g).toMonoidHom := by
  classical
  have hB' : Nat.card (B.subgroupOf H) = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv).trans hB
  have hC' : Nat.card (C.subgroupOf H) = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv).trans hC
  obtain ⟨P₁, hP₁⟩ :=
    (IsPGroup.iff_card.mpr ⟨1, by rw [hB', pow_one]⟩ : IsPGroup p (B.subgroupOf H)).exists_le_sylow
  obtain ⟨P₂, hP₂⟩ :=
    (IsPGroup.iff_card.mpr ⟨1, by rw [hC', pow_one]⟩ : IsPGroup p (C.subgroupOf H)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P₁ P₂
  have hW : (B.subgroupOf H).map (MulAut.conj g).toMonoidHom ≤ (P₂ : Subgroup H) := by
    rintro _ hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hx1 : x ∈ (P₁ : Subgroup H) := hP₁ hx
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx1
  have hWc : Nat.card ((B.subgroupOf H).map (MulAut.conj g).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB']
  have hP₂cyc : IsCyclic ↥(P₂ : Subgroup H) := by
    have hSp : IsPGroup p ((P₂ : Subgroup H).map H.subtype) := P₂.isPGroup'.map H.subtype
    have hc : IsCyclic ((P₂ : Subgroup H).map H.subtype) := hcyc _ hSp
    have e : (P₂ : Subgroup H) ≃* ((P₂ : Subgroup H).map H.subtype) :=
      Subgroup.equivMapOfInjective (P₂ : Subgroup H) H.subtype H.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hBeq : C.subgroupOf H = (B.subgroupOf H).map (MulAut.conj g).toMonoidHom :=
    eq_of_card_eq_of_le_cyclic hP₂cyc hP₂ hW hC' hWc
  refine ⟨g, g.2, ?_⟩
  calc C = (C.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hCH).symm
    _ = ((B.subgroupOf H).map (MulAut.conj g).toMonoidHom).map H.subtype := by rw [hBeq]
    _ = (B.subgroupOf H).map (H.subtype.comp (MulAut.conj g).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (B.subgroupOf H).map ((MulAut.conj (g : G)).toMonoidHom.comp H.subtype) := by
        congr 1
    _ = ((B.subgroupOf H).map H.subtype).map (MulAut.conj (g : G)).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = B.map (MulAut.conj (g : G)).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hBH]

end Conj

section Three

variable {N : Type} [Group N] [Finite N]

theorem isCyclic_of_isPGroup_three {N₀ : Subgroup N} (hN₀ : GLBStronglyEmbedded 3 N₀)
    (hr : Open.pRank 3 N₀ = 1) {R : Subgroup N} (hR : IsPGroup 3 R) : IsCyclic ↥R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPN₀⟩ := exists_sylow_le_of_glbStronglyEmbedded hN₀
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q P
  have hle : R.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup N) := by
    rintro _ hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hRQ hx)
  have hpg : IsPGroup 3 (R.map (MulAut.conj g).toMonoidHom) := hR.map _
  have hcyc : IsCyclic ↥(R.map (MulAut.conj g).toMonoidHom) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      (hle.trans hPN₀) hpg (pRank_le_one_of_open_eq_one hr)
  have e : R ≃* R.map (MulAut.conj g).toMonoidHom :=
    Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem le_pPrimeCore_of_normal_normal {p : ℕ} [Fact p.Prime] {X M : Subgroup N} (hX : X.Normal) (hM : M ≤ X)
    (hMn : (M.subgroupOf X).Normal) (hM3 : Nat.Coprime p (Nat.card M)) :
    M ≤ CFSG.pPrimeCore p N := by
  classical
  set C : Subgroup N := (CFSG.pPrimeCore p ↥X).map X.subtype with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g c', ?_, ?_⟩
    · have hfix := (inferInstance : (CFSG.pPrimeCore p ↥X).Characteristic).fixed
        (MulAut.conjNormal g)
      have : c' ∈ (CFSG.pPrimeCore p ↥X).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [hfix]; exact hc'
      exact this
    · rfl
  have hCcard : Nat.Coprime p (Nat.card C) := by
    rw [hC, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hCle : C ≤ CFSG.pPrimeCore p N := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hCn, hCcard⟩
  refine le_trans ?_ hCle
  have hMX : M.subgroupOf X ≤ CFSG.pPrimeCore p ↥X := by
    unfold CFSG.pPrimeCore
    refine le_sSup ⟨hMn, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv]
    exact hM3
  intro m hm
  exact Subgroup.mem_map.mpr ⟨⟨m, hM hm⟩, hMX (Subgroup.mem_subgroupOf.mpr hm), rfl⟩

end Three

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
