module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMRee
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeIdInvolve

public section

namespace CFSG.AGLEmbedding

theorem kFactCaseTwoCM_of_oneLieIdent
    (hId : KFactOneLieIdent) : KFactCaseTwoCM := by
  intro K _ _ hs hnab hcat p hp T hT hcore hrank A L _ hL f hf
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨d, hd, ⟨e⟩⟩ := hId K hs hnab hcat p hprime hp2 T hT hcore (by omega)
  set A' : Subgroup (CatGroup d) := A.map e.toMonoidHom with hA'
  set f' : A' →* L := f.comp (A.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    with hf'
  have hsurj : Function.Surjective f' :=
    hf.comp (A.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  rcases hp with rfl | rfl
  · rcases hd with ⟨n, hn, hd⟩ | ⟨hd, h2⟩ | hd
    · exact (linTwo_not_surjective_caseTwo d n hn hd A' L hL f' hsurj).elim
    · exact (unitary_not_surjective_caseTwo d hd h2 A' L hL f' hsurj).elim
    · exact ⟨rfl, fun B Y _ g hg hsY hnY hY => ree_sections hd e B Y g hg hsY hnY hY⟩
  · rcases hd with ⟨n, hn, hd⟩ | ⟨hd, h2⟩ | hd
    · exact (linTwo_not_surjective_caseTwo_five d n hn hd A' L hL f' hsurj).elim
    · exact (unitary_not_surjective_caseTwo_five d hd h2 A' L hL f' hsurj).elim
    · exact absurd hd.1 (by norm_num)

end CFSG.AGLEmbedding
