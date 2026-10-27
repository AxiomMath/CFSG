module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent
public import CFSG.Quasithin.Vol2.KGFactHeInspRank
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Bridge.RuSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.RuSchreier CFSG.QuasithinUnique.Lin2.RankCert

theorem ruP_inv_cent :
    ∀ t z : ↥ruP, orderOf t = 2 → orderOf z = 13 → t * z = z * t →
      ¬ 2 ^ 12 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥ruP)) := by
  intro t z ht hz htz hdvd
  rw [card_centralizer_subtype] at hdvd
  have hmem : (t : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
    ⟨t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩
  rw [ruInvolutions_eq] at hmem
  have hzmem : (z : Equiv.Perm (Fin 4060)) ∈
      ruP ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 4060))} :=
    ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val htz).symm⟩
  have h13 : 13 ∣ Nat.card ↥(ruP ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 4060))}) := by
    rw [← hz, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hzmem]
    exact orderOf_dvd_natCard _
  rcases hmem with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · rw [← hgt, card_inf_centralizer_conj hg, ← ruC_eq_centralizer, card_ruC] at h13
    norm_num at h13
  · rw [← hgt, card_inf_centralizer_conj hg, ruCentralizer_a, card_ruL] at hdvd
    norm_num at hdvd

theorem row_Ru_13 :
    KFactSporLocalRow .Ru 13 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have e0 : (TauCeti.CFSGIndex.sporadic .Ru).Group ≃* CFSG.Blueprint.NativeSporadic.Ru := b.symm
  have eR : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* ↥ruP := ruEquivP
  have h12 : orderOf (2 : ZMod 13) = 12 :=
    orderOf_two_zmod_eq 13 12 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank' ↥ruP ⟨(e0.trans ruEquivP).symm⟩ ?_ ?_
  · rw [h12]
    exact ruP_inv_cent
  · rw [h12]
    have h := ElemAbelianLt.of_mulEquiv eR.symm CFSG.Quasithin.H13.KGRank.elemAbelianLt_ru
    exact fun E hE => lt_of_lt_of_le (h E hE) (by norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
