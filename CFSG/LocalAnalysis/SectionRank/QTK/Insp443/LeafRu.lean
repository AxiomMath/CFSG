module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RuConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RuRef
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RuTypes

public section

namespace CFSG.SectionRank.QTK.Insp443.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Ru

section Main


theorem conclK_ru {A : Type} [Group A] [Finite A] (e : G₀ ≃* A) {L V MK : Subgroup A}
    (h : KConfig A L V MK) : ConclK A L V MK := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨e', τ', hτ', y', hUV, hyM, hyN, hy1, hp⟩ :=
    exists_ref_of h.perfect h.le_normalizer hne h.elemAbelian e
  interval_cases τ'
  ·
    rcases hp with ⟨hp, -⟩ | ⟨-, hy7⟩
    · simp [refPrime] at hp
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hyN' : (y' : Equiv.Perm (Fin 4060)) ∈ ruN := by
      rw [← ruN_eq_normalizer_E, ← uE_eq]
      exact ⟨y'.2, hyN⟩
    obtain ⟨n, hnN, hxM⟩ := exists_conj_std e' ruN_le xE_memN orderOf_xE
      (by rw [card_ruN]; norm_num) hyN' ⟨1, hy7⟩ hy1 hyM
    have hnE : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
        Subgroup.normalizer (uE : Set (Equiv.Perm (Fin 4060))) := by
      have h1 : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈ ruN := by simpa using ruN.inv_mem hnN
      rw [← ruN_eq_normalizer_E, ← uE_eq] at h1
      exact h1.2
    have hEV : img (conjE e' n⁻¹) uE ≤ V := by
      have e1 : uE.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = uE :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnE
      rw [img_conjE, e1]
      exact hUV
    obtain ⟨hV, hC2⟩ := config_e h (conjE e' n⁻¹) hEV hxM
    exact conclK_e h (conjE e' n⁻¹) hV hC2
  ·
    obtain ⟨hV, hO, hL, hC⟩ := config_e64 h e' (refSub_le_ruP _) hUV centralizer64_le
    exact conclK_e64 h e' hV hO hL hC
  ·
    obtain ⟨hV, hO, hL, hC⟩ := config_e64 h e' (refSub_le_ruP _) hUV centralizer3_le
    exact conclK_e64 h e' hV hO hL hC
  ·
    rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_w16 h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp
  ·
    rcases hp with ⟨-, hy5⟩ | ⟨hp, -⟩
    · exact (false_vz h e' hUV hyM hyN ⟨3, hy5⟩ hy1).elim
    · simp [refPrime] at hp

theorem conclK_Ru {L V MK : Subgroup (NativeSporadic.Carrier .Ru)}
    (h : KConfig (NativeSporadic.Carrier .Ru) L V MK) :
    ConclK (NativeSporadic.Carrier .Ru) L V MK := by
  let φ : NativeSporadic.Carrier .Ru ≃* G₀ := ruEquivP
  haveI : Finite (NativeSporadic.Carrier .Ru) := Finite.of_injective (⇑φ) φ.injective
  exact conclK_ru φ.symm h


theorem forK_Ru : ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .Ru)) := by
  haveI : Finite (NativeSporadic.Carrier .Ru) :=
    Finite.of_injective (⇑ruEquivP) ruEquivP.injective
  refine forK_of_kConfig (X := NativeSporadic.Carrier .Ru) ?_ ?_
  · rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_Ru]
    decide
  · intro L V MK h
    exact conclK_Ru h

theorem for_Ru (h37 : CFSG.Quasithin.A37ForSQTK) (h38 : CFSG.Quasithin.A38ForSQTK)
    (h39 : CFSG.Quasithin.A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .Ru)) :=
  For.of_forK h37 h38 h39 forK_Ru

end Main

end CFSG.SectionRank.QTK.Insp443.Ru

end
