module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneSporBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Model
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeSeven
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
public import CFSG.RankThree.PartOne.KS.HeSevenData
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.ONActions

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.HardMathSupport.Dickson.I271
open CFSG.LocalAnalysis.RankThreeTheoremC (exists_isElemAbelian_card_sq_of_card_cube)

theorem noSig_map_conj_of_fix {K : Type*} [Group K] [Finite K] (hZ : Subgroup.center K = ⊥)
    {p : ℕ} {E : Subgroup K}
    (hNo : ∀ U : Subgroup K, Nat.Coprime p (Nat.card U) →
      E ≤ Subgroup.normalizer (U : Set K) → U = ⊥)
    (hfix : ∀ v : MulAut K, Nat.Coprime (orderOf v) p → (∀ e ∈ E, v e = e) → v = 1) :
    NoSig p (E.map (MulAut.conj : K →* MulAut K)) := by
  have hinj := conj_injective_of_center_bot_sg hZ
  intro V hV hEV
  set U : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hUdef
  have hUcop : Nat.Coprime p (Nat.card U) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hV
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hEU : E ≤ Subgroup.normalizer (U : Set K) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro u
    simp only [hUdef, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hEV ⟨e, he, rfl⟩) (MulAut.conj u)
  have hU : U = ⊥ := hNo U hUcop hEU
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  refine hfix v (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard V hv) hV.symm)
    fun e he => ?_
  have hc : v * MulAut.conj e * v⁻¹ * (MulAut.conj e)⁻¹ ∈ V := by
    have h1 : MulAut.conj e * v⁻¹ * (MulAut.conj e)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hEV ⟨e, he, rfl⟩) v⁻¹).mp (V.inv_mem hv)
    have e1 : v * MulAut.conj e * v⁻¹ * (MulAut.conj e)⁻¹ =
        v * (MulAut.conj e * v⁻¹ * (MulAut.conj e)⁻¹) := by group
    rw [e1]
    exact V.mul_mem hv h1
  have e2 : v * MulAut.conj e * v⁻¹ * (MulAut.conj e)⁻¹ = MulAut.conj (v e * e⁻¹) := by
    rw [map_mul, map_inv, mulAut_conj_conj]
  rw [e2] at hc
  have hmem : v e * e⁻¹ ∈ U := hc
  rw [hU, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

theorem noSig_map_conj_of_sevenModel {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup X} {z : X} {gens : Set X} (D : SevenModel X p Q z gens)
    (hZ : Subgroup.center X = ⊥) {E₀ : Subgroup X} (hE₀Q : E₀ ≤ Q) (hE₀ : IsElemAbelian p E₀)
    (hE₀2 : Nat.card E₀ = p ^ 2) : NoSig p (E₀.map (MulAut.conj : X →* MulAut X)) := by
  have hfix : ∀ v : MulAut X, Nat.Coprime (orderOf v) p → (∀ e ∈ E₀, v e = e) → v = 1 :=
    fun v hv hve => D.fix_plane hE₀Q hE₀ hE₀2 hv hve
  refine noSig_map_conj_of_fix hZ (fun U hUcop hEU => ?_) hfix
  refine noSig_of_rank Fact.out hE₀ hE₀2 (fun u hu hcomm => ?_)
    (fun e he he1 => D.rankOK e (orderOf_eq_prime (hE₀.2 e he) he1)) U hUcop hEU
  have h1 : (MulAut.conj u : MulAut X) = 1 :=
    hfix _ (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd (MulAut.conj : X →* MulAut X) u) hu)
      fun f hf => by rw [MulAut.conj_apply, hcomm f hf, mul_inv_cancel_right]
  exact conj_injective_of_center_bot_sg hZ (h1.trans (map_one _).symm)

open CFSG.ONSchreier CFSG.RankThree.Native in
theorem signalizerThreeAt_onan :
    SignalizerThreeAt 7 (TauCeti.CFSGIndex.sporadic .ONan).Group := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
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
  exact signalizerThreeAt_of_model_noSig (by norm_num) (by norm_num) ⟨onEquivPv.symm.trans b⟩
    hE₀.isPGroup (noSig_map_conj_of_sevenModel on7_sevenModel hZ hE₀F hE₀ hE₀2)

private theorem not_mem_zpowers_of_mul_comm {G : Type*} [Group G] {c x y : G}
    (hcx : c * x = x * c) (hxy : x * y ≠ y * x) : y ∉ Subgroup.zpowers c := by
  intro h
  have hc : c ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcx
  have hy : y ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.zpowers_le.2 hc h
  exact hxy (Subgroup.mem_centralizer_singleton_iff.1 hy).symm

open CFSG.Sporadic.Fi24 Fi7 in
theorem signalizerThreeAt_fi24Prime :
    SignalizerThreeAt 7 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hZ : Subgroup.center J = ⊥ := by
    haveI : IsSimpleGroup J := isSimpleGroup_J
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · exfalso
      have hx : X7 ∈ Subgroup.center J := by
        rw [h]
        exact Subgroup.mem_top _
      exact X7_Y7_noncomm (Subgroup.mem_center_iff.1 hx Y7).symm
  have hcy : C7 * Y7 = Y7 * C7 := fi7_cube.2.2.2.2.1
  have hy7 : Y7 ^ 7 = 1 := fi7_cube.2.1
  have hyc : Y7 ∉ Subgroup.zpowers C7 :=
    not_mem_zpowers_of_mul_comm fi7_cube.2.2.2.1 X7_Y7_noncomm
  have hE₀2 : Nat.card (Subgroup.closure ({C7, Y7} : Set J)) = 7 ^ 2 :=
    card_closure_pair_sq hcy C7_pow_seven hy7 C7_ne_one hyc
  have hE₀ : IsElemAbelian 7 (Subgroup.closure ({C7, Y7} : Set J)) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a (rfl | rfl) c (rfl | rfl)
      exacts [rfl, hcy, hcy.symm, rfl]
    · rintro a (rfl | rfl)
      exacts [C7_pow_seven, hy7]
  have hE₀Q : Subgroup.closure ({C7, Y7} : Set J) ≤ Q7 := (Subgroup.closure_le _).2 (by
    rintro _ (rfl | rfl)
    exacts [C7_mem, Y7_mem])
  have b₀ : Blueprint.NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := b
  have bJ : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := fi24EquivJ.symm.trans b₀
  exact @signalizerThreeAt_of_model_noSig 7 (by norm_num) (by norm_num) _ _ ↥J
    (Subgroup.toGroup J) inferInstance ⟨bJ⟩ _ hE₀.isPGroup
    (noSig_map_conj_of_sevenModel fi7_sevenModel hZ hE₀Q hE₀ hE₀2)

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB in
theorem signalizerThreeAt_he :
    SignalizerThreeAt 7 (TauCeti.CFSGIndex.sporadic .He).Group := by
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
  refine signalizerThreeAt_of_model_noSig (by norm_num) (by norm_num) ⟨heEquivP.symm.trans b⟩
    hE₀.isPGroup (heSeven_noSig _ (hE₀.map _) ?_)
  rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot_sg hZ), hE₀2]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
