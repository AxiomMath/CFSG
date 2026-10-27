module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeSeven
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesThree
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
public import CFSG.RankThree.PartOne.KS.HeSevenData
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.ONActions
import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.HardMathSupport.Dickson.I271

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB in
theorem kFactNineThreeNoTwoAt_he :
    KFactNineThreeNoTwoAt 7 (.sporadic .He) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨hQP, -, hQcard, hQexp⟩, -⟩ := R3E_He_full_seven_centralizer_structures
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have hZ : Subgroup.center heP = ⊥ := autModel_center_eq_bot heAutModel
  obtain ⟨E₀, -, hE₀, hE₀2⟩ := exists_isElemAbelian_card_sq_of_card_cube (X := heP) (p := 7)
    (E := heSevenQ.subgroupOf heP)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQcard]; norm_num)
    fun x hx => by
      have h := Monoid.pow_exponent_eq_one
        (⟨(x : Equiv.Perm (Fin 8330)), Subgroup.mem_subgroupOf.1 hx⟩ : heSevenQ)
      rw [hQexp] at h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  refine kFactNineThreeNoTwoAt_of_model_coprime (by norm_num) (by norm_num)
    ⟨heEquivP.symm.trans b⟩ hE₀.isPGroup fun V hV hN =>
      heSeven_noSig (E₀.map MulAut.conj) (hE₀.map _) ?_ V
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hV) hN
  rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot_sg hZ), hE₀2]

open CFSG.ONSchreier CFSG.RankThree.Native in
theorem kFactNineThreeNoTwoAt_onan :
    KFactNineThreeNoTwoAt 7 (.sporadic .ONan) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have hD := on7_sevenModel
  have hZ : Subgroup.center Pv = ⊥ := by
    haveI : IsSimpleGroup Pv := @MulEquiv.isSimpleGroup Pv _ Blueprint.NativeSporadic.ON _
      CFSG.Sporadic.ON.isSimpleGroup_ON onEquivPv.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Pv) with h | h
    · exact h
    · exfalso
      have hz : on7W 0 ∈ Subgroup.center Pv := by
        rw [h]
        exact Subgroup.mem_top _
      have htop : Subgroup.centralizer ({on7W 0} : Set Pv) = ⊤ :=
        eq_top_iff.2 fun g _ =>
          Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hz g)
      have hc := card_centralizer_on7W 0
      rw [htop, Subgroup.card_top, card_Pv] at hc
      norm_num at hc
  have hQP : onSevenQ ≤ Pv := onSeven_mem_P.1
  obtain ⟨E₀, hE₀Q, hE₀, hE₀2⟩ := exists_isElemAbelian_card_sq_of_card_cube (X := Pv) (p := 7)
    (E := onSevenQ.subgroupOf Pv)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, card_onSevenQ]; norm_num)
    fun x hx => Subtype.ext (by simpa using onSevenQ_pow_seven (Subgroup.mem_subgroupOf.1 hx))
  have hE₀F : E₀ ≤ on7F 0 := fun x hx =>
    Subgroup.mem_subgroupOf.2 (onSevenQ_le_F0 (Subgroup.mem_subgroupOf.1 (hE₀Q hx)))
  have hfix : ∀ u : MulAut Pv, Nat.Coprime (orderOf u) 7 → (∀ s ∈ E₀, u s = s) → u = 1 :=
    fun u hu hus => hD.fix_plane hE₀F hE₀ hE₀2 hu hus
  refine kFactNineThreeNoTwoAt_of_model (by norm_num) ⟨onEquivPv.symm.trans b⟩ hE₀.isPGroup
    fun V hV hN => aut_twoGroup_eq_bot hZ (T := E₀) ?_ ?_ V hV fun t ht => hN ⟨t, ht, rfl⟩
  ·
    intro U hU hEU
    have hUcop : Nat.Coprime 7 (Nat.card U) := by
      obtain ⟨k, hk⟩ := hU.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    refine noSig_of_rank (by norm_num) hE₀ hE₀2 (fun u hu hcomm => ?_)
      (fun e he he1 => on7_rankOK e (orderOf_eq_prime (hE₀.2 e he) he1)) U hUcop hEU
    have h1 : (MulAut.conj u : MulAut Pv) = 1 :=
      hfix _ (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd (MulAut.conj : Pv →* MulAut Pv) u)
        hu) fun f hf => by rw [MulAut.conj_apply, hcomm f hf, mul_inv_cancel_right]
    exact conj_injective_of_center_bot_sg hZ (h1.trans (map_one _).symm)
  ·
    intro W hW hWE
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
    have hw2 : w ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hfix w (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hw2)
      (Nat.Coprime.pow_left n (by norm_num))) (hWE w hw)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
