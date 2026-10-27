module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Ev
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat (isPrimeFormGram_one4)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem card_P43 : Nat.card P43 = 3265920 := by
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv hud (isPrimeFormGram_one (n := 4) (K := F9))
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F9) (p := 3) (f := 1)
    (n := 4) Nat.prime_three le_rfl (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num)
    (by norm_num)
  rw [Nat.card_congr (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hud
    (by norm_num))).toEquiv, h]
  decide

theorem card_outer_P43 : Nat.card (Outer P43) = 8 := by
  have h := (unitary_full_diagonal_outer_order hud (n := 4) (by norm_num) (by norm_num)).2.2.2.1
  rw [h]
  norm_num

theorem card_inner_dvd : Nat.card (inner P43) ∣ Nat.card P43 := by
  exact Subgroup.card_dvd_of_surjective (f := (MulAut.conj : P43 →* MulAut P43).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _)

theorem card_mulAut_dvd : Nat.card (MulAut P43) ∣ 2 ^ 10 * 25515 := by
  have h1 : Nat.card (MulAut P43) = Nat.card (Outer P43) * Nat.card (inner P43) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (inner P43)
  rw [h1, card_outer_P43]
  have h2 := card_inner_dvd
  rw [card_P43] at h2
  have : 8 * 3265920 = 2 ^ 10 * 25515 := by norm_num
  rw [← this]
  exact Nat.mul_dvd_mul_left 8 h2


theorem idCode_eq : idCode = scal 3 := rfl

theorem rawValid_idCode : rawValid idCode = true := by
  rw [idCode_eq]
  exact rawValid_scal (by simp)

theorem ev_idCode : ev idCode = 1 := by
  rw [idCode_eq]
  exact ev_scal (by simp)

theorem valid_iff (x : Array ℕ) : valid x = true ↔ rawValid x = true ∧ normalize x = x := by
  simp [valid]

noncomputable def Ssub (D : Data) : Subgroup (MulAut P43) :=
  Subgroup.closure ((fun k => ev D.gens[k]!) '' {k | k < D.gens.size})

theorem sylow_spec {D : Data} (h : sylowOK D = true) :
    (∀ k < D.gens.size, rawValid D.gens[k]! = true) ∧
    (∀ g : MulAut P43, g ∈ Ssub D ↔ ∃ i < (bfs D).pts.size, ev (bfs D).pts[i]! = g) ∧
    Nat.card (Ssub D) = 1024 ∧ (∀ i < (bfs D).pts.size, valid (bfs D).pts[i]! = true) := by
  unfold sylowOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hg, hcert⟩, hsz⟩ := h
  have hact : ∀ k < D.gens.size, ∀ a, valid a = true →
      ev (act D.gens k a) = ev D.gens[k]! * ev a := by
    intro k hk a ha
    obtain ⟨hav, -⟩ := (valid_iff a).1 ha
    have hm := rawValid_mulRaw (hg k hk) hav
    unfold act
    rw [ev_normalize hm, ev_mulRaw (hg k hk) hav]
  have hkey : ∀ a b, valid a = true → valid b = true → ev a = ev b → keyOf a = keyOf b := by
    intro a b ha hb hab
    obtain ⟨hav, hna⟩ := (valid_iff a).1 ha
    obtain ⟨hbv, hnb⟩ := (valid_iff b).1 hb
    have := normalize_eq_of_ev_eq hav hbv hab
    rw [hna, hnb] at this
    rw [this]
  obtain ⟨hmem, hcard⟩ := card_closure_of_arrCertOK (G := MulAut P43) (dec := ev)
    (gens := fun k => ev D.gens[k]!) hcert hact hkey ev_idCode
  exact ⟨hg, hmem, hcard.trans hsz, fun i hi => arrCertOK_valid hcert hi⟩

theorem ssub_isPGroup {D : Data} (h : sylowOK D = true) : IsPGroup 2 (Ssub D) :=
  IsPGroup.of_card (n := 10) (by rw [(sylow_spec h).2.2.1]; norm_num)

theorem ssub_index_odd {D : Data} (h : sylowOK D = true) : ¬ 2 ∣ (Ssub D).index := by
  intro h2
  have hc := Subgroup.card_mul_index (Ssub D)
  rw [(sylow_spec h).2.2.1] at hc
  have hd : 1024 * (Ssub D).index ∣ 2 ^ 10 * 25515 := hc ▸ card_mulAut_dvd
  have hd' : (Ssub D).index ∣ 25515 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 1024) (by simpa using hd)
  have := h2.trans hd'
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
