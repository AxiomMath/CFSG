module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCentData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO8pCentAbs
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.AGLEmbedding.O8pCent

open CFSG.EvenSmallLie.OmegaEight

theorem nonempty_mulEquiv_omegaT_catalog
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq : q.card = 2)
    (hd : d.1 = .D 4 q) : Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* omegaT) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.D 4 q := hd
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 1 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hp,
      he]
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, _, inferInstance, inferInstance, hcard, ⟨e⟩⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hmodel⟩)
  exact ⟨φ⟩

theorem kFactD4TwoGraphCentralizer :
    KFactD4TwoGraphCentralizer := by
  intro J _ _ d ⟨q, hq, hd⟩ ⟨e⟩ α hα _
  obtain ⟨φ₀⟩ := nonempty_mulEquiv_omegaT_catalog d q hq hd
  let φ : J ≃* omegaT := e.trans φ₀
  obtain ⟨Q, D, g, hQ, hQ243, hDQ, hD, hD81, hgQ, hC⟩ := exists_o8pCentData_omegaT
  have hJ : Nat.card J = Nat.card omegaT := Nat.card_congr φ.toEquiv
  have hmapcard : ∀ S : Subgroup omegaT, Nat.card (S.map φ.symm.toMonoidHom) = Nat.card S :=
    fun _ => Subgroup.card_map_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective
  have hC' : ∀ C : Subgroup J, C ≤ D.map φ.symm.toMonoidHom →
      (∀ c ∈ C, φ.symm g * c = c * φ.symm g) → Nat.card C ≤ 9 := by
    intro C hCD hCg
    have hle : C.map φ.toMonoidHom ≤ D := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨d', hd', hdc⟩ := hCD hc
      change φ c ∈ D
      rw [← hdc]
      simpa using hd'
    have hcomm : ∀ x ∈ C.map φ.toMonoidHom, g * x = x * g := by
      rintro _ ⟨c, hc, rfl⟩
      have := congrArg φ (hCg c hc)
      simpa using this
    have := hC (C.map φ.toMonoidHom) hle hcomm
    rwa [Subgroup.card_map_of_injective φ.injective] at this
  obtain ⟨E, hE, hE9, hEfix⟩ := exists_fixed_elemAbelian_nine_of_sylow
    (Q := Q.map φ.symm.toMonoidHom) (D := D.map φ.symm.toMonoidHom) (g := φ.symm g)
    (by rw [hmapcard, hJ]; exact hQ) (by rw [hmapcard]; exact hQ243)
    (Subgroup.map_mono hDQ) (isElemAbelian_map_hom _ hD) (by rw [hmapcard]; exact hD81)
    (Subgroup.mem_map_of_mem _ hgQ) hC' hα
  exact ⟨E, hE, by rw [hE9]; norm_num, hEfix⟩

end CFSG.AGLEmbedding.O8pCent
