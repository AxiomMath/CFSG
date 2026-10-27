module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniBranch
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Omega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU mem_heldGU)

open scoped commutatorElement

section Certs


theorem l154OmegaFld_uni : L154OmegaFld l154Uni := by
  intro p hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ hInn hF hJ hJy
  classical
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := hInn.1 (Subgroup.mem_zpowers x)
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  obtain ⟨n, d, K, instK, finK, τ, hτ, θ, A, B, σ, φx, ψ, hd, hn, hdq, hK, hτq, hA, hφxA, hψB, hBmem,
    hσ1, hmoved, hindx, hindy⟩ := uni_marking_data hp hp2 hQ hInn hF
  let h : UnitaryFieldData 2 n K := unitaryData_two hn hK
  have hτbar : ∀ c, h.bar c = τ c := fun c => by rw [UnitaryFieldData.bar_apply, hτq]
  have hmoved' : ∃ c : K, h.bar c = c ∧ σ c ≠ c := by
    obtain ⟨c, h1, h2⟩ := hmoved
    exact ⟨c, by rw [hτbar]; exact h1, h2⟩
  have hAmem : A ∈ primeFormUnitary h (idGram K d) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    have : (⇑h.bar : K → K) = ⇑τ := funext hτbar
    rw [this]
    exact mem_heldGU.1 hA
  have hφx' : φx = MulAut.congr θ (MI.indAut p S x hxN) := (MI.induces_indRel_iff hxN θ).1 hindx
  have hpow : φx ^ p = 1 := by
    rw [hφx', ← map_pow, l154_indAut_pow_eq_one hxN hxp, map_one]
  obtain ⟨c, hAc⟩ := l154_uni_pow_scalar hτ hτq hK hd hdq A hA φx hφxA hpow
  set JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K)) := (chevTransfer p S J).map θ.toMonoidHom with hJPdef
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (S ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [l154_centralizer_inv_singleton]
    exact hJ
  have hT := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  have hcompat : ∀ k : PSimple p S, θ (MI.indAut p S x hxN k) = φx (θ k) := by
    intro k
    rw [hφx']
    simp [MulAut.congr_apply]
  have hJP : GLAPComponent p (fixSubgroup φx) JP :=
    glaPComponent_map_fixSubgroup θ.toMonoidHom
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 θ.injective]; exact bot_le) (MI.indAut p S x hxN) φx hcompat
      θ.surjective hp hT
  rcases l154_uni_block_data hn hd h hp hp2 A hAmem hAc φx hφxA JP hJP with hSU | hSL | hSL2
  · exact l154_uni_fieldOn_su hp hp2 hSp hJ hJS hJy hyp h θ ψ hindy B σ hψB hBmem hmoved' hSU
  · exact l154_uni_fieldOn_sl hp hp2 hSp hJ hJS hJy hyp h θ ψ hindy B σ hψB hBmem hmoved' hSL
  · exact l154_uni_fieldOn_sl2 hp hp2 hSp hJ hJS hJy hyp h θ ψ hindy B σ hψB hBmem hmoved' hSL2

end Certs

section Final


theorem l154NIDOn_uni : L154NIDOn l154Uni := l154NIDOn_of_fldOn (l154FldOn_of_omega l154OmegaFld_uni)

theorem l154TD4On_uni : L154TD4On l154Uni := l154TD4On_of_fldOn (l154FldOn_of_omega l154OmegaFld_uni)

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X
