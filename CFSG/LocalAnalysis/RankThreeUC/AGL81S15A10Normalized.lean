module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10TwoFourSFive
public import CFSG.GroupTheory.OddIndexFixedPoint
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Equiv Equiv.Perm

namespace A10TwoFourSFive

theorem blockHomFull_surjective : Function.Surjective blockHomFull := by
  intro π
  let d : Perm Pt := Equiv.sumCongr π π
  have hd : d ∈ Full := ⟨π, by rintro (i | i) <;> rfl⟩
  exact ⟨⟨d, hd⟩, by ext i; simp [blockHomFull, blockPermFull_apply, d, blk]⟩

theorem blockHomFull_ker : blockHomFull.ker = Fiber.subgroupOf Full := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h p
    obtain ⟨π, hπ⟩ := σ.2
    have hπ2 : blockPermFull σ = π := by
      refine Equiv.ext fun i => ?_
      simpa [blockPermFull_apply, blk_inl] using hπ (Sum.inl i)
    have h1 : blockPermFull σ = 1 := by simpa [blockHomFull] using h
    have hπ1 : π = 1 := by rw [← hπ2]; exact h1
    rw [hπ p, hπ1]
    rfl
  · intro h
    refine Equiv.ext fun i => ?_
    change blockPermFull σ i = (1 : Perm (Fin 5)) i
    exact h (Sum.inl i)

theorem card_Full : Nat.card Full = 3840 := by
  have hq : Nat.card (↥Full ⧸ blockHomFull.ker) = 120 := by
    rw [Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective blockHomFull blockHomFull_surjective).toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (α := ↥Full) (s := blockHomFull.ker)
  have hker : Nat.card (Fiber.subgroupOf Full) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := Fiber) (K := Full) fiber_le_full).toEquiv, card_fiber]
  rw [hq, blockHomFull_ker, hker] at hmul
  norm_num at hmul ⊢
  exact hmul

end A10TwoFourSFive

theorem isTwoFourSFive_iff_pCore {G : Type} [Group G] (P : Subgroup G) :
    KFactsPair.IsTwoFourSFive P ↔
      CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 ↥P) ∧
      Nat.card (CFSG.pCore 2 ↥P) = 2 ^ 4 ∧
      Nonempty ((↥P ⧸ CFSG.pCore 2 ↥P) ≃* Perm (Fin 5)) := by
  constructor
  · rintro ⟨hea, hcard, hquo⟩
    refine ⟨?_, ?_, hquo⟩
    · have h1 := CFSG.Open.IsElemAbelian.comap hea P.subtype_injective
      rw [CFSG.Open.pCoreOf,
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective] at h1
      exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h1
    · rw [CFSG.Open.pCoreOf,
        Subgroup.card_map_of_injective P.subtype_injective] at hcard
      exact hcard
  · rintro ⟨hel, hcard, hquo⟩
    have hel' : CFSG.Open.IsElemAbelian 2 (CFSG.pCore 2 ↥P) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hel
    refine ⟨?_, ?_, hquo⟩
    · unfold CFSG.Open.pCoreOf
      exact hel'.map P.subtype
    · unfold CFSG.Open.pCoreOf
      rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]

theorem isTwoFourSFive_of_mulEquiv {G H : Type} [Group G] [Group H]
    {P : Subgroup G} {Q : Subgroup H} (e : ↥P ≃* ↥Q)
    (hP : KFactsPair.IsTwoFourSFive P) : KFactsPair.IsTwoFourSFive Q := by
  rw [isTwoFourSFive_iff_pCore] at hP ⊢
  obtain ⟨hel, hcard, hquo⟩ := hP
  have hpc : (CFSG.pCore 2 ↥P).map e.toMonoidHom = CFSG.pCore 2 ↥Q :=
    CFSG.pCore_map_iso 2 e
  let eB : ↥(CFSG.pCore 2 ↥P) ≃* ↥(CFSG.pCore 2 ↥Q) :=
    (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥P) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hpc)
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.IsElementaryAbelian.of_mulEquiv eB hel
  · rw [← Nat.card_congr eB.toEquiv]
    exact hcard
  · exact ⟨(QuotientGroup.congr (G' := CFSG.pCore 2 ↥P)
      (H' := CFSG.pCore 2 ↥Q) e hpc).symm.trans hquo.some⟩

theorem isTwoFourSFive_map {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (P : Subgroup G) (hP : KFactsPair.IsTwoFourSFive P) :
    KFactsPair.IsTwoFourSFive (P.map f) :=
  isTwoFourSFive_of_mulEquiv (Subgroup.equivMapOfInjective P f hf) hP

theorem exists_isTwoFourSFive_normalized_perm_ten (Tstar : Subgroup (Perm (Fin 10)))
    (h2 : IsPGroup 2 Tstar) :
    ∃ P : Subgroup (Perm (Fin 10)), P ≤ alternatingGroup (Fin 10) ∧
      KFactsPair.IsTwoFourSFive P ∧
      Tstar ≤ Subgroup.normalizer (P : Set (Perm (Fin 10))) := by
  let e : A10TwoFourSFive.Pt ≃ Fin 10 := finSumFinEquiv
  let E : Perm A10TwoFourSFive.Pt ≃* Perm (Fin 10) := e.permCongrHom
  let Q : Subgroup (Perm (Fin 10)) := A10TwoFourSFive.Full.map E.toMonoidHom
  have hcardQ : Nat.card Q = 3840 := by
    change Nat.card (A10TwoFourSFive.Full.map E.toMonoidHom) = 3840
    rw [Subgroup.card_map_of_injective E.injective, A10TwoFourSFive.card_Full]
  have hS : Nat.card (Perm (Fin 10)) = 3628800 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hidx : Q.relIndex ⊤ = 945 := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_eq_card_div, hcardQ, hS]
  have hodd : Odd (Q.relIndex ⊤) := by rw [hidx]; norm_num
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_conj_normalizer_of_odd_relIndex Q Tstar h2 hodd
  have hAmap : (alternatingGroup A10TwoFourSFive.Pt).map E.toMonoidHom =
      alternatingGroup (Fin 10) := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτ' : Equiv.Perm.sign τ = 1 := Equiv.Perm.mem_alternatingGroup.mp hτ
      rw [Equiv.Perm.mem_alternatingGroup]
      change Equiv.Perm.sign (e.permCongr τ) = 1
      rw [Equiv.Perm.sign_permCongr]
      exact hτ'
    · intro hσ
      refine ⟨E.symm σ, ?_, by simp⟩
      have hσ' : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp hσ
      change Equiv.Perm.sign (E.symm σ) = 1
      have hsign : Equiv.Perm.sign (E.symm σ) = Equiv.Perm.sign σ := by
        have h2' : E (E.symm σ) = σ := by simp
        calc Equiv.Perm.sign (E.symm σ) = Equiv.Perm.sign (e.permCongr (E.symm σ)) := by
              rw [Equiv.Perm.sign_permCongr]
          _ = Equiv.Perm.sign (E (E.symm σ)) := rfl
          _ = Equiv.Perm.sign σ := by rw [h2']
      rw [hsign, hσ']
  have hbase : Q ⊓ alternatingGroup (Fin 10) =
      (A10TwoFourSFive.Full ⊓ alternatingGroup A10TwoFourSFive.Pt).map E.toMonoidHom := by
    change A10TwoFourSFive.Full.map E.toMonoidHom ⊓ alternatingGroup (Fin 10) = _
    rw [← hAmap]
    exact (Subgroup.map_inf _ _ _ E.injective).symm
  have hQshape : KFactsPair.IsTwoFourSFive (Q ⊓ alternatingGroup (Fin 10)) := by
    rw [hbase]
    exact isTwoFourSFive_map E.toMonoidHom E.injective _ A10TwoFourSFive.isTwoFourSFive_P
  have hAmapConj : (alternatingGroup (Fin 10)).map (MulAut.conj g).toMonoidHom =
      alternatingGroup (Fin 10) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change MulAut.conj g y ∈ alternatingGroup (Fin 10)
      rw [MulAut.conj_apply]
      exact (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem y hy g
    · intro hx
      refine ⟨(MulAut.conj g).symm x, ?_, ?_⟩
      · change (MulAut.conj g).symm x ∈ alternatingGroup (Fin 10)
        rw [MulAut.conj_symm_apply]
        exact (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem x hx g⁻¹
      · simpa using (MulAut.conj g).apply_symm_apply x
  let P : Subgroup (Perm (Fin 10)) :=
    Q.map (MulAut.conj g).toMonoidHom ⊓ alternatingGroup (Fin 10)
  refine ⟨P, inf_le_right, ?_, ?_⟩
  ·
    have hP : P = (Q ⊓ alternatingGroup (Fin 10)).map (MulAut.conj g).toMonoidHom := by
      change Q.map (MulAut.conj g).toMonoidHom ⊓ alternatingGroup (Fin 10) =
        (Q ⊓ alternatingGroup (Fin 10)).map (MulAut.conj g).toMonoidHom
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hAmapConj]
    rw [hP]
    exact isTwoFourSFive_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _ hQshape
  ·
    rw [Subgroup.le_normalizer_iff]
    intro t ht p hp
    have htQ : t ∈ Subgroup.normalizer
        (Q.map (MulAut.conj g).toMonoidHom : Set (Perm (Fin 10))) := hg ht
    have htA : t ∈ Subgroup.normalizer
        (alternatingGroup (Fin 10) : Set (Perm (Fin 10))) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top t
    change t * p * t⁻¹ ∈
      Q.map (MulAut.conj g).toMonoidHom ⊓ alternatingGroup (Fin 10)
    exact ⟨(Subgroup.mem_normalizer_iff.mp htQ p).mp hp.1,
      (Subgroup.mem_normalizer_iff.mp htA p).mp hp.2⟩

theorem A10TwoFourSFiveNormalized {Y : Type} [Group Y] [Finite Y] (Ls Tstar : Subgroup Y)
    (hLs : Nonempty (↥Ls ≃* alternatingGroup (Fin 10)))
    (hT : Tstar ≤ Subgroup.normalizer (Ls : Set Y)) (h2 : IsPGroup 2 Tstar) :
    ∃ P₂ : Subgroup Y, P₂ ≤ Ls ∧ KFactsPair.IsTwoFourSFive P₂ ∧
      Tstar ≤ Subgroup.normalizer (P₂ : Set Y) := by
  classical
  obtain ⟨φ⟩ := hLs
  let ρ : Tstar →* MulAut ↥Ls :=
    (Subgroup.normalizerMonoidHom Ls).comp (Subgroup.inclusion hT)
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  let eb : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10))) hbij
  let ψ : MulAut (alternatingGroup (Fin 10)) ≃* Perm (Fin 10) := eb.symm
  let σ : Tstar →* Perm (Fin 10) :=
    ψ.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp ρ)
  have hσconj : ∀ t : Tstar,
      MulAut.conjNormal (H := alternatingGroup (Fin 10)) (σ t) =
        (MulAut.congr φ) (ρ t) := by
    intro t
    change eb (eb.symm ((MulAut.congr φ) (ρ t))) = (MulAut.congr φ) (ρ t)
    exact MulEquiv.apply_symm_apply eb _
  let T' : Subgroup (Perm (Fin 10)) := (⊤ : Subgroup ↥Tstar).map σ
  have htop : IsPGroup 2 (⊤ : Subgroup ↥Tstar) :=
    h2.of_equiv (Subgroup.topEquiv (G := ↥Tstar)).symm
  have hT'2 : IsPGroup 2 T' := htop.map σ
  obtain ⟨P', hP'le, hP'shape, hP'norm⟩ :=
    exists_isTwoFourSFive_normalized_perm_ten T' hT'2
  let P₀ : Subgroup (alternatingGroup (Fin 10)) :=
    P'.comap (Subgroup.subtype (alternatingGroup (Fin 10)))
  have hP₀map : P₀.map (Subgroup.subtype (alternatingGroup (Fin 10))) = P' := by
    change (P'.comap (Subgroup.subtype (alternatingGroup (Fin 10)))).map
      (Subgroup.subtype (alternatingGroup (Fin 10))) = P'
    exact Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hP'le)
  have hP₀shape : KFactsPair.IsTwoFourSFive P₀ := by
    let eP : ↥P₀ ≃* ↥P' :=
      (Subgroup.equivMapOfInjective P₀ (Subgroup.subtype (alternatingGroup (Fin 10)))
        (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hP₀map)
    exact isTwoFourSFive_of_mulEquiv eP.symm hP'shape
  let ι : alternatingGroup (Fin 10) →* Y :=
    Ls.subtype.comp φ.symm.toMonoidHom
  have hι : Function.Injective ι := by
    intro a b hab
    exact φ.symm.injective (Subtype.ext hab)
  let P₂ : Subgroup Y := P₀.map ι
  refine ⟨P₂, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact (φ.symm a).2
  · exact isTwoFourSFive_map ι hι P₀ hP₀shape
  · rw [Subgroup.le_normalizer_iff]
    intro t ht y hy
    obtain ⟨a, ha, rfl⟩ := hy
    let t' : ↥Tstar := ⟨t, ht⟩
    have hσmem : σ t' ∈ T' :=
      Subgroup.mem_map_of_mem σ (Subgroup.mem_top t')
    have hN : σ t' ∈ Subgroup.normalizer (P' : Set (Perm (Fin 10))) := hP'norm hσmem
    have hconj : MulAut.conjNormal (H := alternatingGroup (Fin 10)) (σ t') a ∈ P₀ := by
      change MulAut.conjNormal (H := alternatingGroup (Fin 10)) (σ t') a ∈
        P'.comap (Subgroup.subtype (alternatingGroup (Fin 10)))
      rw [Subgroup.mem_comap]
      have hcoe := MulAut.conjNormal_apply (H := alternatingGroup (Fin 10)) (σ t') a
      rw [show (Subgroup.subtype (alternatingGroup (Fin 10)))
          ((MulAut.conjNormal (H := alternatingGroup (Fin 10)) (σ t')) a) =
          σ t' * (a : Perm (Fin 10)) * (σ t')⁻¹ from hcoe]
      exact (Subgroup.mem_normalizer_iff.mp hN (a : Perm (Fin 10))).mp
        (Subgroup.mem_comap.mp ha)
    have hιconj : ι (MulAut.conjNormal (H := alternatingGroup (Fin 10)) (σ t') a) =
        t * ι a * t⁻¹ := by
      rw [hσconj t']
      change ((φ.symm ((MulAut.congr φ) (ρ t') a) : ↥Ls) : Y) =
        t * ((φ.symm a : ↥Ls) : Y) * t⁻¹
      rw [show (MulAut.congr φ) (ρ t') a = φ ((ρ t') (φ.symm a)) from rfl,
        MulEquiv.symm_apply_apply]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe Ls ⟨t, hT ht⟩ (φ.symm a)
    rw [← hιconj]
    exact Subgroup.mem_map_of_mem ι hconj

end CFSG.LocalAnalysis.RankThreeUC.S15
