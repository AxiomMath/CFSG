module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcAsm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOEvenTwin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTri
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

attribute [local instance] GeneralizedFitting.normal

theorem burgoynePropBPlusFourInput_holds :
    BurgoynePropBPlusFourInput := by
  intro J _ _ K _ t Y c hH p f hp2 hL
  obtain ⟨hq, hM4, ht, hY1, hY2, s, hs2, hst, hsY, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, hprop⟩ :=
    id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  rcases hL with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hadm := hcl.1
  have : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨θ₀⟩ := exists_galois_coordinatePlus hcl
  obtain ⟨ρ, hρ⟩ := Tri.exists_triality_spin (GaloisField p f)
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have h2 : (2 : GaloisField p f) ≠ 0 := Ring.two_ne_zero hK
  have hKc : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨p₁, n₁, hp₁f, hp₁, hn₁, ⟨e⟩⟩ := hQiso
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  have hnorm : ∀ g ∈ closure (insert t (Y : Set J)), Q.map (phiO K g).toMonoidHom = Q :=
    fun g hg => (hprop.1 g hg).1
  have hpic := exists_adapted_picture K hq hsimple hnab (GaloisField p f) hp2 hρ θ₀ hQQ hQs hp₁ e
    hcZ hcQ hc2 hnorm
  obtain ⟨θ, α, hα, hαs, hαc, hnegQ, hsemi, hsemis⟩ := hpic
  obtain ⟨X', hX'⟩ : ∃ X' : Subgroup (rhoZ K).range,
      X' = (projectivePointFamilyAut (Q8 (GaloisField p f))).comap (socleAction θ) := ⟨_, rfl⟩
  have hle : GeneralizedFitting.subgroup (rhoZ K).range ≤ X' := by
    intro x hx
    rw [hX', mem_comap]
    have : socleAction θ x = MulAut.conj (θ ⟨x, hx⟩) := by
      rw [← socleAction_symm θ, MulEquiv.symm_apply_apply]
    rw [this]
    exact projective_inner_le_pointFamilyAut _ ⟨_, rfl⟩
  have htX' : (rhoZ K).rangeRestrict t ∈ X' := by
    rw [hX']
    exact hsemi t (subset_closure (Set.mem_insert _ _))
  have hYX' : Y.map (rhoZ K).rangeRestrict ≤ X' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hX']
    exact hsemi y (subset_closure (Set.mem_insert_of_mem _ hy))
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (Q8 (GaloisField p f))
    (regular_coordinateQuadPlus 4 (GaloisField p f) (by norm_num)).1
  have hS₁ : ∀ v, oQ R ((1 : GL (Fin (2 * 4)) (GaloisField p f)).val *ᵥ v) =
      ((1 : (GaloisField p f)ˣ) : GaloisField p f) *
        reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 (GaloisField p f)) v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    rfl
  obtain ⟨f₀, hcard₀, hmod⟩ := exists_model8 (GaloisField p f) (p := p)
  have hker₀ : OKer (coordinateQuadPlus 4 (GaloisField p f)) :=
    oKer_coordinatePlus hmod _ hcard₀ (MulEquiv.refl _)
  have hker : OKer (oQ R) := hker₀.transport 1 1 hS₁
  have hsimple' := isSimpleGroup_sub hsimple hnab hle
  have hnab' := nab_sub hsimple hnab hle
  have hkap : ∀ x : X', ∃ g : similarityPairs (oQ R),
      socleAction (picR (subSocleEquiv hsimple hnab θ hle) 1 1 hS₁) x = oκ (oQ R) g := by
    intro x
    have hx : socleAction θ (x : (rhoZ K).range) ∈
        projectivePointFamilyAut (Q8 (GaloisField p f)) := by
      have h : (x : (rhoZ K).range) ∈
          (projectivePointFamilyAut (Q8 (GaloisField p f))).comap (socleAction θ) := hX' ▸ x.2
      exact h
    obtain ⟨g₀, hg₀⟩ := exists_kappa_of_mem_family (p := p) hx
    refine ⟨transPair 1 1 hS₁ g₀, ?_⟩
    rw [picR, socleAction_trans', socleAction_trans', socleAction_subSocleEquiv, hg₀,
      oTransport_kappa]
  have hsurj : OSurjX (picR (subSocleEquiv hsimple hnab θ hle) 1 1 hS₁) (⟨_, htX'⟩ : X') :=
    fun x _ => hkap x
  have ht' : orderOf (⟨_, htX'⟩ : X') = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_rangeRestrict_of_phiO K hq ht
  have hY1' : (Y.map (rhoZ K).rangeRestrict).subgroupOf X' ≠ ⊥ := by
    intro h
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYX' hy⟩ : X') ∈ (Y.map (rhoZ K).rangeRestrict).subgroupOf X' :=
      mem_subgroupOf.mpr hy
    rw [h, mem_bot] at hy'
    exact (mem_bot).mpr (congrArg Subtype.val hy')
  have hY2' : (Y.map (rhoZ K).rangeRestrict).subgroupOf X' ≤
      oddCentralizerCore (⟨_, htX'⟩ : X') := by
    intro y hy
    rw [mem_subgroupOf] at hy
    exact oddCentralizerCore_subgroupOf_le (⟨_, htX'⟩ : X') (mem_subgroupOf.mpr (hY2 hy))
  obtain ⟨g, hg⟩ := hkap ⟨_, htX'⟩
  by_cases hσ : g.val.right = 1
  · rcases inner_even_twin hK (by norm_num : 4 ≤ 4) hR hker hsimple' hnab'
      (picR (subSocleEquiv hsimple hnab θ hle) 1 1 hS₁) hsurj ht' hσ hg with h | hT | hpc
    · exact (hY1' (le_bot_iff.mp (h ▸ hY2'))).elim
    · exact propB_of_twin8 K hq hsimple hnab hH hp2 hK hKc θ hα hαc hle htX' hYX' 1 1 hS₁ hT
    ·
      have hg' : socleAction (picR θ 1 1 hS₁) ((rhoZ K).rangeRestrict t) = oκ _ g := by
        rw [← hg, picR, picR, socleAction_trans', socleAction_trans', socleAction_trans',
          socleAction_trans', socleAction_subSocleEquiv]
      exact (exc_false K hq hsimple hnab ht hs2 hst hQs hQc hp₁ e hcZ hcQ hc2
        (hnorm t (subset_closure (Set.mem_insert _ _))) hp2 hf hKc θ hα hαs hαc hnegQ hsemis hR
        hker hS₁ hg' hσ hpc).elim
  · exact (hY1' (le_bot_iff.mp ((field_odd_core_bot hK (by norm_num) hadm.1 hf hKc hR hker
      hsimple' hnab' (picR (subSocleEquiv hsimple hnab θ hle) 1 1 hS₁) hsurj ht' hσ hg) ▸
        hY2'))).elim

end CFSG.ComponentClassification.Burgoyne.DX
