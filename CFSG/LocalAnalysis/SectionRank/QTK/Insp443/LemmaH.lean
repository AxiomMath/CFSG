module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M22Cases
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M22

private theorem card_map_mk_mul_card_inf_lemmaH {X : Type*} [Group X] (N H : Subgroup X)
    [N.Normal] :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card ↥(N ⊓ H) = Nat.card H := by
  have h1 := Subgroup.relIndex_ker (K := H) (QuotientGroup.mk' N)
  have h2 := Subgroup.relIndex_mul_card (H := (QuotientGroup.mk' N).ker) (K := H)
  rw [QuotientGroup.ker_mk'] at h1 h2
  rw [← h1]
  exact h2

theorem KConf.card_V_of_threeA6
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}
    (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22)
    (hZ3 : Nat.card ↥(Subgroup.center K) = 3)
    (h3 : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6))) :
    Nat.card V = 2 ^ 4 := by
  set Z := Subgroup.center K with hZ
  have hVZ : Z ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxZ, hxV⟩ := Subgroup.mem_inf.mp hx
    have hx2 : x ^ 2 = 1 := hK.elemAbelian.2 x hxV
    have hx3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Z) (x := ⟨x, hxZ⟩)
      rw [hZ3] at this
      exact congrArg Subtype.val this
    rw [Subgroup.mem_bot]
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx2, hx3, inv_one, mul_one]
  have hVcard : Nat.card ↥(V.map (QuotientGroup.mk' Z)) = Nat.card V := by
    have := card_map_mk_mul_card_inf_lemmaH Z V
    rwa [hVZ, Subgroup.card_bot, mul_one] at this
  have hQ : 5 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨-, hc, ⟨φ⟩⟩ := h3
    have hmul := Subgroup.card_mul_index (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    have hidx : (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).index = 360 := by
      rw [Subgroup.index, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hc, hidx] at hmul
    rw [← hmul]
    norm_num
  have hL5 : 5 ∣ Nat.card L := hQ.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  have hLb5 : 5 ∣ Nat.card ↥(L.map (QuotientGroup.mk' Z)) := by
    have hmul := card_map_mk_mul_card_inf_lemmaH Z L
    have hd : Nat.card ↥(Z ⊓ L) ∣ 3 := by
      rw [← hZ3]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime 5 (Nat.card ↥(Z ⊓ L)) :=
      Nat.Coprime.coprime_dvd_right hd (by norm_num)
    rw [← hmul] at hL5
    exact hcop.dvd_of_dvd_mul_right hL5
  obtain ⟨g, hg | hg | hg⟩ := KConfig.m22_cases (hK.kConfig_bar.map_mulEquiv e)
  · have h := congrArg (fun H : Subgroup G₀ => Nat.card ↥H) hg.1
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, card_eSub] at h
    rw [← hVcard, ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h
  · have h := congrArg (fun H : Subgroup G₀ => Nat.card ↥H) hg.1
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, card_eSub] at h
    rw [← hVcard, ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h
  · exfalso
    have h := congrArg (fun H : Subgroup G₀ => Nat.card ↥H) hg.2
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, card_eNorm_e8] at h
    have h' : Nat.card ↥(L.map (QuotientGroup.mk' Z)) = 1344 := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      exact h
    rw [h'] at hLb5
    norm_num at hLb5

end CFSG.SectionRank.QTK.Insp443
