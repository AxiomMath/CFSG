module

public import Certificates.Data.CFSGNative.Bridge.SuzGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzU43

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Bridge TauCeti
open scoped commutatorElement

private theorem suz_presentation_eq :
    SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl

theorem commutator_eq_top_of_quot_aux {T : Type} [Group T] (Z : Subgroup T) [Z.Normal]
    (hZK : Z ≤ commutator T) (h : commutator (T ⧸ Z) = ⊤) : commutator T = ⊤ := by
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hπker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have htop : (⊤ : Subgroup T).map (QuotientGroup.mk' Z) = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 hπs
  have hmapc : (commutator T).map (QuotientGroup.mk' Z) = commutator (T ⧸ Z) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, htop]
  rw [eq_top_iff]
  intro t _
  have ht : QuotientGroup.mk' Z t ∈ (commutator T).map (QuotientGroup.mk' Z) := by
    rw [hmapc, h]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.1 ht
  have hkz : k⁻¹ * t ∈ Z := by
    rw [← hπker]
    change QuotientGroup.mk' Z (k⁻¹ * t) = 1
    rw [map_mul, map_inv, hkt, inv_mul_cancel]
  have : t = k * (k⁻¹ * t) := by group
  rw [this]
  exact (commutator T).mul_mem hk (hZK hkz)


theorem suz_central_quot_gen (P : GroupPresentation) (hP : P = Sporadic.suzPresentation)
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* P.Group))
    {T : Type} [Group T] [Finite T] (Z : Subgroup T) [Z.Normal] (g : ℕ → T)
    (hZ : Z ≤ Subgroup.center T)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd g v ∈ Z)
    (hnc : g 0 * g 1 ≠ g 1 * g 0)
    (hcard : Nat.card T ≤ Nat.card Z * 448345497600) :
    Subgroup.center T = Z ∧ Nat.card (T ⧸ Z) = 448345497600 ∧ commutator (T ⧸ Z) = ⊤ ∧
      IsSimpleGroup (T ⧸ Z) ∧ Nonempty ((T ⧸ Subgroup.center T) ≃* P.Group) := by
  classical
  subst hP
  let π : T →* T ⧸ Z := QuotientGroup.mk' Z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  obtain ⟨β⟩ := hb
  haveI hNat : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Suz :=
    CFSG.Sporadic.Suz.isSimpleGroup_Suz
  haveI hSimple : IsSimpleGroup Sporadic.suzPresentation.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ hNat β.symm
  have hcardS : Nat.card Sporadic.suzPresentation.Group = 448345497600 := by
    rw [← Nat.card_congr β.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  have hrelQ : ∀ v ∈ Sporadic.suzPresentation.relatorLetters,
      wordProd (fun i => π (g i)) v = 1 := by
    intro v hv
    rw [← map_wordProd π g v]
    exact (QuotientGroup.eq_one_iff _).2 (hrel v hv)
  let Φ : Sporadic.suzPresentation.Group →* T ⧸ Z :=
    presHom Sporadic.suzPresentation (fun i => π (g i)) hrelQ
  have hΦ0 : Φ (presGen Sporadic.suzPresentation 0) = π (g 0) :=
    presHom_presGen Sporadic.suzPresentation (fun i => π (g i)) hrelQ (i := 0) (by
      rw [Suz.generatorCount_eq]; norm_num)
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with h | h
    · exact h
    · exfalso
      have h1 : π (g 0) = 1 := by
        rw [← hΦ0]
        exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
      have h2 : g 0 ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
      exact hnc (Subgroup.mem_center_iff.1 (hZ h2) (g 1)).symm
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hTcard : Nat.card (T ⧸ Z) * Nat.card Z = Nat.card T := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [this]
  have hQle : Nat.card (T ⧸ Z) ≤ Nat.card Sporadic.suzPresentation.Group := by
    rw [hcardS]
    by_contra hlt
    push Not at hlt
    have h3 : (448345497600 + 1) * Nat.card Z ≤ Nat.card (T ⧸ Z) * Nat.card Z :=
      Nat.mul_le_mul_right _ hlt
    rw [hTcard] at h3
    omega
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hQle
  have eG : (T ⧸ Z) ≃* Sporadic.suzPresentation.Group := (MulEquiv.ofBijective Φ hbij).symm
  have hsimpleG : IsSimpleGroup (T ⧸ Z) := @MulEquiv.isSimpleGroup _ _ _ _ hSimple eG
  have hGcard : Nat.card (T ⧸ Z) = 448345497600 := by
    rw [Nat.card_congr eG.toEquiv]
    exact hcardS
  have hnab : ∃ x y : T ⧸ Z, x * y ≠ y * x :=
    exists_noncomm_of_simple_sq_dvd Nat.prime_two (by rw [hGcard]; norm_num)
  have hcenG : Subgroup.center (T ⧸ Z) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (T ⧸ Z))
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x)
  have hcommG : commutator (T ⧸ Z) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (T ⧸ Z))
      with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have h1 : ⁅x, y⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      exact hxy (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  have hcenT : Subgroup.center T = Z := by
    refine le_antisymm (fun t ht => ?_) hZ
    have hπt : π t ∈ Subgroup.center (T ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨s, rfl⟩ := hπs h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ht s]
    rw [hcenG, Subgroup.mem_bot] at hπt
    rw [← hπker]
    exact hπt
  exact ⟨hcenT, hGcard, hcommG, hsimpleG,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenT).trans eG⟩⟩

theorem suz_central_ext_gen (P : GroupPresentation) (hP : P = Sporadic.suzPresentation)
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* P.Group))
    {T : Type} [Group T] [Finite T] (Z : Subgroup T) (g : ℕ → T)
    (hZ : Z ≤ Subgroup.center T)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd g v ∈ Z)
    (hnc : g 0 * g 1 ≠ g 1 * g 0) (hZK : Z ≤ commutator T)
    (hcard : Nat.card T ≤ Nat.card Z * 448345497600) :
    CFSG.Open.IsQuasisimple T ∧ Subgroup.center T = Z ∧
      Nonempty ((T ⧸ Subgroup.center T) ≃* P.Group) := by
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  obtain ⟨hcen, -, hcomm, hsimple, he⟩ :=
    suz_central_quot_gen P hP hb Z g hZ hrel hnc hcard
  have hperf : commutator T = ⊤ := commutator_eq_top_of_quot_aux Z hZK hcomm
  have hsimple' : IsSimpleGroup (T ⧸ Subgroup.center T) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hsimple (QuotientGroup.quotientMulEquivOfEq hcen)
  exact ⟨⟨hperf, hsimple'⟩, hcen, he⟩

theorem suz_central_ext
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.Group))
    {T : Type} [Group T] [Finite T] (Z : Subgroup T) (g : ℕ → T)
    (hZ : Z ≤ Subgroup.center T)
    (hrel : ∀ v ∈ SporadicName.Suz.presentation.relatorLetters, wordProd g v ∈ Z)
    (hnc : g 0 * g 1 ≠ g 1 * g 0) (hZK : Z ≤ commutator T)
    (hcard : Nat.card T ≤ Nat.card Z * 448345497600) :
    CFSG.Open.IsQuasisimple T ∧ Subgroup.center T = Z ∧
      Nonempty ((T ⧸ Subgroup.center T) ≃* SporadicName.Suz.Group) :=
  suz_central_ext_gen SporadicName.Suz.presentation suz_presentation_eq hb Z g hZ hrel hnc hZK hcard

theorem suz_central_quot
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.Group))
    {T : Type} [Group T] [Finite T] (Z : Subgroup T) [Z.Normal] (g : ℕ → T)
    (hZ : Z ≤ Subgroup.center T)
    (hrel : ∀ v ∈ SporadicName.Suz.presentation.relatorLetters, wordProd g v ∈ Z)
    (hnc : g 0 * g 1 ≠ g 1 * g 0) (hcard : Nat.card T ≤ Nat.card Z * 448345497600) :
    Subgroup.center T = Z ∧ Nat.card (T ⧸ Z) = 448345497600 ∧
      Nonempty ((T ⧸ Subgroup.center T) ≃* SporadicName.Suz.Group) := by
  obtain ⟨h1, h2, -, -, h5⟩ :=
    suz_central_quot_gen SporadicName.Suz.presentation suz_presentation_eq hb Z g hZ hrel hnc hcard
  exact ⟨h1, h2, h5⟩

theorem suz_relatorLetters_eq :
    SporadicName.Suz.presentation.relatorLetters =
      CFSG.Sporadic.Bridge.SuzGPL.Native.rels () := by
  rw [suz_presentation_eq, TauCeti.Sporadic.suzPresentation_relatorLetters]
  rfl

end CFSG.HardMathSupport.Dickson.I271
