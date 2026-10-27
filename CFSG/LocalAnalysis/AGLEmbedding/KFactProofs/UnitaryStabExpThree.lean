module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryStabDerived

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

section RootStabilizer

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] def rootStabilizer : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) where
  carrier := {α | (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ}
  one_mem' := by
    show (rootGroup J hJ).map ((1 : MulAut _).toMonoidHom) = rootGroup J hJ
    have h : (1 : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)).toMonoidHom =
        MonoidHom.id _ := rfl
    rw [h, Subgroup.map_id]
  mul_mem' := by
    intro α β hα hβ
    show (rootGroup J hJ).map ((α * β).toMonoidHom) = rootGroup J hJ
    have hcomp : (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hβ, hα]
  inv_mem' := by
    intro α hα
    show (rootGroup J hJ).map ((α⁻¹).toMonoidHom) = rootGroup J hJ
    have hcomp : (α⁻¹).toMonoidHom.comp α.toMonoidHom = MonoidHom.id _ := by
      ext x
      simpa using MulAut.inv_apply_self _ α x
    have h : (rootGroup J hJ).map ((α⁻¹).toMonoidHom.comp α.toMonoidHom) =
        rootGroup J hJ := by
      rw [hcomp, Subgroup.map_id]
    rw [← Subgroup.map_map, hα] at h
    exact h

end RootStabilizer

section RootGroupBound

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]

private def rootInnerAut : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (rootGroup J hJ).map (MulAut.conj :
    ProjectiveSpecialUnitaryMatrixGroup J →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J))

private def rootBorelAut : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  rootInnerAut J hJ ⊔ (torusAut J hJ).range

private theorem rootBorelAut_le_rootStabilizer :
    rootBorelAut J hJ ≤ rootStabilizer J hJ := by
  change rootInnerAut J hJ ⊔ (torusAut J hJ).range ≤ rootStabilizer J hJ
  refine sup_le ?_ ?_
  · change rootInnerAut J hJ ≤ rootStabilizer J hJ
    rintro _ ⟨x, hx, rfl⟩
    show (rootGroup J hJ).map (MulAut.conj x).toMonoidHom = rootGroup J hJ
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      change (MulAut.conj x) z ∈ rootGroup J hJ
      rw [MulAut.conj_apply]
      exact (rootGroup J hJ).mul_mem ((rootGroup J hJ).mul_mem hx hz)
        ((rootGroup J hJ).inv_mem hx)
    · intro y hy
      refine ⟨x⁻¹ * y * x, ?_, ?_⟩
      · exact (rootGroup J hJ).mul_mem ((rootGroup J hJ).mul_mem
          ((rootGroup J hJ).inv_mem hx) hy) hx
      · change (MulAut.conj x) (x⁻¹ * y * x) = y
        rw [MulAut.conj_apply]
        group
  · rintro _ ⟨c, rfl⟩
    exact torusAut_maps_rootGroup J hJ c

private theorem normal_rootBorelAut_subgroupOf_rootStabilizer
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 2 < p ^ f) :
    ((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)).Normal := by
  have hcomm : ⁅rootStabilizer J hJ, rootStabilizer J hJ⁆ ≤ rootBorelAut J hJ :=
    commutator_le_of_stabilizes_rootGroup J hJ hK hfix hq
      (A := rootStabilizer J hJ) (fun α hα => hα)
  have hle : commutator ↥(rootStabilizer J hJ) ≤
      (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ) := by
    intro x hx
    have hx' : (Subgroup.subtype (rootStabilizer J hJ)) x ∈
        (commutator ↥(rootStabilizer J hJ)).map
          (Subgroup.subtype (rootStabilizer J hJ)) :=
      Subgroup.mem_map_of_mem (Subgroup.subtype (rootStabilizer J hJ)) hx
    rw [Subgroup.map_subtype_commutator] at hx'
    exact hcomm hx'
  exact Subgroup.Normal.of_commutator_le ↥(rootStabilizer J hJ) hle

private theorem isCyclic_rootStabilizer_quotient_rootBorelAut
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 2 < p ^ f)
    [((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)).Normal] :
    IsCyclic ((rootStabilizer J hJ) ⧸
      (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)) := by
  have hBle : rootBorelAut J hJ ≤ rootStabilizer J hJ :=
    rootBorelAut_le_rootStabilizer J hJ
  have hfieldMem : ∀ σ : K ≃+* K,
      psuFieldHom J hJ hK hfix σ ∈ rootStabilizer J hJ :=
    fun σ => psuFieldHom_stabilizes_rootGroup J hJ hK hfix σ
  let f : (K ≃+* K) →* ((rootStabilizer J hJ) ⧸
      (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)) :=
    (QuotientGroup.mk' ((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ))).comp
      ((psuFieldHom J hJ hK hfix).codRestrict (rootStabilizer J hJ) hfieldMem)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨β, rfl⟩ :=
      QuotientGroup.mk'_surjective
        ((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)) q
    obtain ⟨x, σ, hxσ⟩ :=
      exists_eq_psuConj_mul_psuField J hJ hK hfix hq (β : MulAut _)
    have hmem : psuConjHom J x * psuFieldHom J hJ hK hfix σ ∈ rootStabilizer J hJ :=
      hxσ ▸ β.2
    have hxP : x ∈ stabPinf J hJ :=
      mem_stabPinf_of_factor J hJ hK hfix hq (A := rootStabilizer J hJ)
        (fun α hα => hα) hmem
    obtain ⟨h10, h20⟩ := first_column_of_fixes_pinf J hJ _
      ((mem_stabPinf J hJ).1 hxP)
    obtain ⟨h21, ha, h22, h11⟩ := unitary_entries_of_upper J hJ _ h10 h20
    have hxsup : psuConjHom J x ∈ rootBorelAut J hJ :=
      psuConjHom_mem_sup_of_upper J hJ x h10 h20 h21 ha h22 h11
    have hxS : psuConjHom J x ∈ rootStabilizer J hJ := hBle hxsup
    refine ⟨σ, ?_⟩
    have hβeq : β = (⟨psuConjHom J x, hxS⟩ : rootStabilizer J hJ) *
        ⟨psuFieldHom J hJ hK hfix σ, hfieldMem σ⟩ := by
      apply Subtype.ext
      simpa using hxσ
    rw [hβeq, map_mul]
    have hc1 : QuotientGroup.mk'
        ((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ))
        (⟨psuConjHom J x, hxS⟩ : rootStabilizer J hJ) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxsup
    rw [hc1, one_mul]
    rfl
  haveI hcycK : IsCyclic (K ≃+* K) := CFSG.GH74.GLS.IVK.ringAut_isCyclic K
  exact isCyclic_of_surjective f hf

private theorem isCyclic_rootBorelAut_quotient_rootInnerAut
    [((rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ)).Normal] :
    IsCyclic ((rootBorelAut J hJ) ⧸
      (rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ)) := by
  have hR'B : rootInnerAut J hJ ≤ rootBorelAut J hJ := by
    change rootInnerAut J hJ ≤ rootInnerAut J hJ ⊔ (torusAut J hJ).range
    exact le_sup_left
  have hTB : (torusAut J hJ).range ≤ rootBorelAut J hJ := by
    change (torusAut J hJ).range ≤ rootInnerAut J hJ ⊔ (torusAut J hJ).range
    exact le_sup_right
  have hsup : (rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ) ⊔
      (torusAut J hJ).range.subgroupOf (rootBorelAut J hJ) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hR'B hTB]
    exact Subgroup.subgroupOf_self _
  have hTcyc : IsCyclic ((torusAut J hJ).range.subgroupOf (rootBorelAut J hJ)) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hTB)).2
      (isCyclic_torusAut_range J hJ)
  exact CFSG.quotient_isCyclic_of_sup_cyclic_right hsup hTcyc

private theorem inf_rootInnerAut_eq_bot_of_pow_eq_one
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hEexp : ∀ x ∈ E, x ^ 3 = 1) : E ⊓ rootInnerAut J hJ = ⊥ := by
  have hE3p : IsPGroup 3 E := fun e => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hEexp (e : MulAut _) e.2)⟩
  have hR'p : IsPGroup p (rootInnerAut J hJ) :=
    IsPGroup.map (isPGroup_rootGroup J hJ hK hfix)
      (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
        MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hE3p.exists_card_eq
  obtain ⟨b, hb⟩ := hR'p.exists_card_eq
  have h3p : Nat.Coprime 3 p :=
    (Nat.coprime_primes Nat.prime_three Fact.out).mpr (Ne.symm hp3)
  have hcop : (Nat.card E).Coprime (Nat.card (rootInnerAut J hJ)) := by
    rw [ha, hb]
    exact Nat.Coprime.pow a b h3p
  exact Subgroup.inf_eq_bot_of_coprime hcop

private theorem isCyclic_of_le_rootBorelAut
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hEB : E ≤ rootBorelAut J hJ) (hEexp : ∀ x ∈ E, x ^ 3 = 1) : IsCyclic E := by
  have hR'B : rootInnerAut J hJ ≤ rootBorelAut J hJ := by
    change rootInnerAut J hJ ≤ rootInnerAut J hJ ⊔ (torusAut J hJ).range
    exact le_sup_left
  have hNB : rootBorelAut J hJ ≤ Subgroup.normalizer
      (rootInnerAut J hJ : Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    change rootInnerAut J hJ ⊔ (torusAut J hJ).range ≤
      Subgroup.normalizer (rootInnerAut J hJ :
        Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    exact sup_le Subgroup.le_normalizer (torusAut_range_le_normalizer_map_conj J hJ)
  haveI : ((rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNB
  haveI : IsCyclic ((rootBorelAut J hJ) ⧸
      (rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ)) :=
    isCyclic_rootBorelAut_quotient_rootInnerAut J hJ
  have hinf : E ⊓ rootInnerAut J hJ = ⊥ :=
    inf_rootInnerAut_eq_bot_of_pow_eq_one J hJ hK hfix hp3 hEexp
  let χ : E →* ((rootBorelAut J hJ) ⧸
      (rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ)) :=
    (QuotientGroup.mk' ((rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ))).comp
      (Subgroup.inclusion hEB)
  have hχinj : Function.Injective χ := by
    intro x y hxy
    have h1 : χ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : (Subgroup.inclusion hEB) (x * y⁻¹) ∈
        (rootInnerAut J hJ).subgroupOf (rootBorelAut J hJ) :=
      (QuotientGroup.eq_one_iff _).1 (by
        simpa [χ, QuotientGroup.mk'_apply] using h1)
    have h3 : ((x * y⁻¹ : E) : MulAut _) ∈ E ⊓ rootInnerAut J hJ :=
      ⟨(x * y⁻¹).2, by simpa using (Subgroup.mem_subgroupOf).1 h2⟩
    have h4 : (x * y⁻¹ : E) = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.1 (hinf ▸ h3)
    exact mul_inv_eq_one.mp h4
  exact isCyclic_of_injective χ hχinj

private theorem card_le_three_of_le_rootBorelAut
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hEB : E ≤ rootBorelAut J hJ) (hEexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  haveI : IsCyclic E := isCyclic_of_le_rootBorelAut J hJ hK hfix hp3 hEB hEexp
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hEexp (g : MulAut _) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [← hg]
  exact Nat.le_of_dvd (by norm_num) hdvd

private theorem card_le_nine_of_le_rootStabilizer
    (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp3 : p ≠ 3) (hq : 2 < p ^ f)
    {A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hAS : A ≤ rootStabilizer J hJ) (hexp : ∀ α ∈ A, α ^ 3 = 1) :
    Nat.card A ≤ 9 := by
  haveI := normal_rootBorelAut_subgroupOf_rootStabilizer J hJ hK hfix hq
  haveI : IsCyclic ((rootStabilizer J hJ) ⧸
      (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)) :=
    isCyclic_rootStabilizer_quotient_rootBorelAut J hJ hK hfix hq
  let φ : A →* ((rootStabilizer J hJ) ⧸
      (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ)) :=
    (QuotientGroup.mk' ((rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ))).comp
      (Subgroup.inclusion hAS)
  have hker : Nat.card φ.ker ≤ 3 := by
    let ψ : φ.ker →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
      { toFun := fun x => x.1.1
        map_one' := rfl
        map_mul' := fun x y => rfl }
    have hψinj : Function.Injective ψ := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    have hEcard : Nat.card (Subgroup.map ψ ⊤) = Nat.card φ.ker := by
      rw [Subgroup.card_map_of_injective hψinj]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← hEcard]
    refine card_le_three_of_le_rootBorelAut J hJ hK hfix hp3 ?_ ?_
    · rintro _ ⟨x, -, rfl⟩
      have hx1 : (Subgroup.inclusion hAS x.1 : rootStabilizer J hJ) ∈
          (rootBorelAut J hJ).subgroupOf (rootStabilizer J hJ) :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hAS x.1)).1 x.2
      exact (Subgroup.mem_subgroupOf).1 hx1
    · rintro _ ⟨x, -, rfl⟩
      have hx3 : x ^ 3 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact hexp x.1.1 x.1.2
      rw [← map_pow, hx3, map_one]
  have hrange : Nat.card φ.range ≤ 3 := by
    haveI : IsCyclic φ.range := Subgroup.isCyclic φ.range
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := φ.range)
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨x, hx⟩ := g.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hx, ← map_pow]
      have hx3 : x ^ 3 = 1 := by
        apply Subtype.ext
        exact hexp x.1 x.2
      rw [hx3, map_one, Subgroup.coe_one]
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range :=
      (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hrange
    _ = 9 := by norm_num

theorem card_le_nine_of_stabilizes_rootGroup (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hp3 : p ≠ 3) (hq : 2 < p ^ f)
    {A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hA : ∀ α ∈ A, (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ)
    (hexp : ∀ α ∈ A, α ^ 3 = 1) : Nat.card A ≤ 9 := by
  exact card_le_nine_of_le_rootStabilizer J hJ hK hfix hp3 hq (fun α hα => hA α hα) hexp

end RootGroupBound

section SylowTransport

theorem card_le_nine_of_stabilizes_sylow {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hp3 : p ≠ 3)
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (e : L ≃* CFSG.AGLEmbedding.CatGroup d) (U : Sylow p L)
    (A : Subgroup (MulAut L))
    (hA : ∀ α ∈ A, (U : Subgroup L).map α.toMonoidHom = U)
    (hexp : ∀ α ∈ A, α ^ 3 = 1) : Nat.card A ≤ 9 := by
  classical
  have hcm : CFSG.Open.StatedClassicalModel L .PSU 3 p d.1.fieldExponent :=
    statedClassicalModel hd ⟨e⟩
  obtain ⟨-, hf, hq, K, hKfield, hKfin, J, hJ, hKcard, hfix, ⟨eP⟩⟩ :=
    exists_equiv_psu (f := d.1.fieldExponent) hcm
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hKcard hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq eP U S
  let Φ : MulAut L ≃* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.congr e'
  let A' : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := A.map Φ.toMonoidHom
  have hA' : ∀ β ∈ A', (rootGroup J hJ).map β.toMonoidHom = rootGroup J hJ := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hβ
    rw [← hS, ← he', Subgroup.map_map]
    change Subgroup.map ((Φ α).toMonoidHom.comp e'.toMonoidHom) U =
      Subgroup.map e'.toMonoidHom U
    have hcomp : (Φ α).toMonoidHom.comp e'.toMonoidHom =
        e'.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [Φ, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hA α hα]
  have hexp' : ∀ β ∈ A', β ^ 3 = 1 := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hβ
    rw [← map_pow, hexp α hα, map_one]
  have hstep : Nat.card A' ≤ 9 :=
    card_le_nine_of_stabilizes_rootGroup J hJ hKcard hfix hp3 hq hA' hexp'
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective Φ.injective
  rwa [hcard] at hstep

end SylowTransport

end

end CFSG.AGLEmbedding.UnitaryModel
