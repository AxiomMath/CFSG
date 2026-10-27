module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07AutRankU38
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model
public import CFSG.GF2Type.Smith1980Orth.TriD4Rank
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Triality


theorem ys07_elemAb_aut_triality_le
    (hZ : Subgroup.center ↥CFSG.Quasithin.trialityGroup8 = ⊥)
    (hA : Nat.card (MulAut ↥CFSG.Quasithin.trialityGroup8) = 3 * 211341312)
    (hT : Nat.card ↥CFSG.Quasithin.trialityGroup8 = 211341312)
    {E : Subgroup (MulAut ↥CFSG.Quasithin.trialityGroup8)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  classical
  set T := ↥CFSG.Quasithin.trialityGroup8 with hTdef
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ
  set I : Subgroup (MulAut T) := CFSG.ComponentClassification.OuterAutomorphisms.inner T with hIdef
  have hIcard : Nat.card I = 211341312 := by
    rw [← hT]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hQcard : Nat.card (MulAut T ⧸ I) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup I
    rw [hA, hIcard] at h
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
  let f : E →* (MulAut T ⧸ I) := (QuotientGroup.mk' I).comp E.subtype
  have hf1 : Nat.card f.ker * Nat.card f.range = Nat.card E := by
    rw [← Subgroup.index_ker f, Subgroup.card_mul_index]
  have hrange : Nat.card f.range ≤ 3 := by
    rw [← hQcard]
    exact Subgroup.card_le_card_group _
  have hK₁E : ∀ z ∈ f.ker.map E.subtype, z ∈ E := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hker : Nat.card f.ker ≤ 9 := by
    set K₁ : Subgroup (MulAut T) := f.ker.map E.subtype with hK₁
    have hK₁card : Nat.card K₁ = Nat.card f.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective E)
    have hK₁I : K₁ ≤ I := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    set K₂ : Subgroup T := K₁.comap (MulAut.conj : T →* MulAut T) with hK₂
    have hmap : K₂.map (MulAut.conj : T →* MulAut T) = K₁ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 (hK₁I hy)
        exact ⟨x, hy, rfl⟩
    have hK₂card : Nat.card K₂ = Nat.card K₁ := by
      rw [← Subgroup.card_map_of_injective (K := K₂) (f := (MulAut.conj : T →* MulAut T)) hinj, hmap]
    have hcomm : ∀ x ∈ K₂, ∀ y ∈ K₂, x * y = y * x := by
      intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      exact ys07_comm_of_elemAb hE (hK₁E _ hx) (hK₁E _ hy)
    have h3 : ∀ x ∈ K₂, x ^ 3 = 1 := by
      intro x hx
      apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ (hK₁E _ hx)
    have hb := CFSG.GF2Type.Smith1980Orth.card_le_nine_of_elementary_trialityGroup8 hT K₂ hcomm h3
    calc Nat.card f.ker = Nat.card K₁ := hK₁card.symm
      _ = Nat.card K₂ := hK₂card.symm
      _ ≤ 9 := hb
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := hf1.symm
    _ ≤ 9 * 3 := Nat.mul_le_mul hker hrange
    _ = 27 := by norm_num

theorem aut_td4_le_27 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcat : catalogIs S S9.isTD4two) (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isTD4two hcat
  obtain ⟨h1, h2⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
  obtain ⟨⟨eT⟩, hZ, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec19.lineGroup_facts_of_isoLie q h1 h2 ⟨hv, ⟨e⟩⟩
  have hcardS : Nat.card S = 211341312 := by
    have hc := CFSG.AGLEmbedding.card_catGroup_trialityD4_even
      (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) h1 rfl
    rw [Nat.card_congr e.toEquiv, hc, h2]
    norm_num [CFSG.Open.ordTrialityD4]
  let e₀ : S ≃* ↥CFSG.Quasithin.trialityGroup8 :=
    eT.trans (MulEquiv.subgroupCongr CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup_eq)
  have hT : Nat.card ↥CFSG.Quasithin.trialityGroup8 = 211341312 := by
    rw [← Nat.card_congr e₀.toEquiv]
    exact hcardS
  have hZT : Subgroup.center ↥CFSG.Quasithin.trialityGroup8 = ⊥ := by
    rw [← CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup_eq]
    exact hZ
  have hAT : Nat.card (MulAut ↥CFSG.Quasithin.trialityGroup8) = 3 * 211341312 := by
    rw [← CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup_eq]
    exact hA
  let E₀ : Subgroup (MulAut ↥CFSG.Quasithin.trialityGroup8) :=
    E.map (MulAut.congr e₀).toMonoidHom
  have hE₀ : IsElemAbelian 3 E₀ := hE.map (MulAut.congr e₀).toMonoidHom
  have hE₀card : Nat.card E₀ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e₀).injective
  rw [← hE₀card]
  exact ys07_elemAb_aut_triality_le hZT hAT hT hE₀

theorem aut_psimple_le_27 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcat : catalogIs S (fun i => S9.isTD4two i ∨ S9.isU3eight i)) (E : Subgroup (MulAut S))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  obtain ⟨i, hi | hi, e⟩ := hcat
  · exact aut_td4_le_27 ⟨i, hi, e⟩ E hE
  · exact aut_u38_le_27 ⟨i, hi, e⟩ E hE

theorem autRank96At_holds (G : Type) [Group G] [Finite G] : AutRank96At G := by
  intro X L B _ hL hcat hB hBN
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : IsSimpleGroup (PSimple 3 L) := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
  let φ : ↥B →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hBN)
  have hφ : ∀ b : ↥B, φ b = 1 ↔ (b : G) ∈ centModSubgroup 3 L := fun b =>
    (chevAut_eq_one_iff hp hL (hBN b.2)).trans centMod_iff
  have hker : Nat.card φ.ker = Nat.card ↥(B ⊓ centModSubgroup 3 L) := by
    have h : φ.ker.map B.subtype = B ⊓ centModSubgroup 3 L := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b.2, (hφ b).1 (MonoidHom.mem_ker.1 hb)⟩
      · rintro ⟨hxB, hx⟩
        exact ⟨⟨x, hxB⟩, MonoidHom.mem_ker.2 ((hφ ⟨x, hxB⟩).2 hx), rfl⟩
    have hk := Subgroup.card_map_of_injective (K := φ.ker) (f := B.subtype) Subtype.val_injective
    rw [← hk, h]
  have hBcard : Nat.card ↥B = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker φ, Subgroup.card_mul_index]
  have hcomm : ∀ b : ↥B, ∀ c : ↥B, b * c = c * b := fun b c =>
    Subtype.ext (ys07_comm_of_elemAb hB b.2 c.2)
  have hcommR : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, hcomm b c]
  have hpowR : ∀ x ∈ φ.range, x ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hB.2 b.1 b.2)
    rw [hb3, map_one]
  have hrange : IsElemAbelian 3 φ.range :=
    ⟨⟨⟨fun x y => Subtype.ext (hcommR x.1 x.2 y.1 y.2)⟩⟩, fun x hx => hpowR x hx⟩
  have hbound : Nat.card φ.range ≤ 27 := aut_psimple_le_27 hcat φ.range hrange
  rw [hBcard, ← hker]
  calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 27 := Nat.mul_le_mul_left _ hbound
    _ = 3 ^ 3 * Nat.card φ.ker := by ring

end Triality

end CFSG.LocalAnalysis.GLTheoremA.CatB
