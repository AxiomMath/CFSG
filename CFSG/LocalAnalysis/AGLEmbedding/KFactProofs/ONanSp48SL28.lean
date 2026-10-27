module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin
open scoped MatrixGroups

theorem fintype_card_gf8 : Fintype.card GF8 = 8 := by decide

noncomputable def gf8Equiv : GaloisField 2 3 ≃+* GF8 :=
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [fintype_card_gf8, ← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num)

noncomputable def slCongr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (MonoidHom.ext fun A => Subtype.ext (Matrix.ext fun i j => e.symm_apply_apply (A i j)))
    (MonoidHom.ext fun A => Subtype.ext (Matrix.ext fun i j => e.apply_symm_apply (A i j)))

theorem center_sl2_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center SL(2, F) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot]
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have h2 : r ^ 2 = 1 := by simpa using hr
    have h3 : (r - 1) ^ 2 = 0 := by
      have h4 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      linear_combination h2 + (1 - r) * h4
    have h5 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    subst h5
    exact Subtype.ext (by simpa using hrA.symm)
  · rintro rfl
    exact Subgroup.one_mem _

noncomputable def slEquivPSL (F : Type*) [Field F] [CharP F 2] : SL(2, F) ≃* PSL(2, F) :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot (F := F)).symm)

noncomputable def sl28Equiv : SL(2, GF8) ≃* PSL(2, GaloisField 2 3) :=
  (slCongr gf8Equiv.symm).trans (slEquivPSL (GaloisField 2 3))

theorem valid_A_one_eight :
    (TauCeti.LieTypeIndex.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [TauCeti.PrimePower.card_def]
  norm_num

theorem sl28_isCaseTwoGroup : CFSG.AGLEmbedding.IsCaseTwoGroup 3 (SL(2, GF8)) := by
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨.A 1 q, valid_A_one_eight⟩
  obtain ⟨eP⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3)
    (d := d) ⟨q, rfl, rfl, rfl⟩
  exact ⟨d, Or.inl ⟨rfl, q, rfl, rfl, rfl⟩, ⟨sl28Equiv.trans eP.symm⟩⟩

theorem sl28_isSimpleGroup : IsSimpleGroup (SL(2, GF8)) := by
  have : IsSimpleGroup PSL(2, GaloisField 2 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [GaloisField.card 2 3 (by norm_num)]; norm_num)
  exact sl28Equiv.isSimpleGroup

def tvUpper : SL(2, GF8) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

def tvLower : SL(2, GF8) :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem tvUpper_mul_tvLower_ne : tvUpper * tvLower ≠ tvLower * tvUpper := by
  intro h
  have h00 := congrArg (fun M : SL(2, GF8) => (M : Matrix (Fin 2) (Fin 2) GF8) 0 0) h
  revert h00
  decide

theorem sl28_nonabelian : ∃ a b : SL(2, GF8), a * b ≠ b * a :=
  ⟨tvUpper, tvLower, tvUpper_mul_tvLower_ne⟩

end CFSG.AGLEmbedding.KFactProofs.Sp48
