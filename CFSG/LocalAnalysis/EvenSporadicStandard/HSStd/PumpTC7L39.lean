module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Syl
public import Certificates.Certificate27266

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSmallLie.Child3.SelL39
  CFSG.Blueprint

structure U3Facts : Prop where
  enum : enumOKL 182 uGens tKeys uCert = true
  size : uCert.pts.size = 729
  fix : uCert.pts.toList.all
    (fun a => eqA 182 a (idA 182) || fixCount a == 2 || fixCount a == 20) = true
  valid : validA 182 g7 = true
  pow : eqA 182 (compA 182 g7 (compA 182 g7 (compA 182 g7 (compA 182 g7
    (compA 182 g7 (compA 182 g7 g7)))))) (idA 182) = true
  fix7 : fixCount g7 = 0

theorem u3Facts_of_check (h : u3OK = true) : U3Facts := by
  simp only [u3OK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

@[expose] def fixF (z : Equiv.Perm (Fin 182)) : Finset (Fin 182) :=
  Finset.univ.filter fun p => z p = p

theorem card_fixF_eq {a : Array ℕ} {z : Equiv.Perm (Fin 182)} (hz : Rep 182 a z) :
    (fixF z).card = fixCount a := by
  unfold fixCount fixF
  refine Finset.card_bij (fun p _ => (p : ℕ)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨p.2, ?_⟩
    have := hz p
    rw [hp] at this
    exact this
  · intro p _ q _ h
    exact Fin.ext h
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨⟨m, hm.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext ((hz ⟨m, hm.1⟩).symm.trans hm.2)

theorem card_fixF_conj (c y : Equiv.Perm (Fin 182)) :
    (fixF (c⁻¹ * y * c)).card = (fixF y).card := by
  have key : ∀ p, (c⁻¹ * y * c) p = p ↔ y (c p) = c p := by
    intro p
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  unfold fixF
  refine Finset.card_bij (fun p _ => c p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (key p).1 hp
  · intro p _ q _ h
    exact c.injective h
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨c⁻¹ q, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [key]
    simpa using hq

theorem seven_dvd_card_fixF {x y : Equiv.Perm (Fin 182)} (hx : x ^ 7 = 1)
    (hcomm : x * y = y * x) (hfree : ∀ p, x p ≠ p) : 7 ∣ (fixF y).card := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hxy : ∀ p, y (x p) = x (y p) := fun p => by
    have := congrArg (fun w : Equiv.Perm (Fin 182) => w p) hcomm
    simpa [Equiv.Perm.mul_apply] using this.symm
  have hiff : ∀ p, (fun q => q ∈ fixF y) (x p) ↔ (fun q => q ∈ fixF y) p := by
    intro p
    simp only [fixF, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hxy p]
    exact ⟨fun h => x.injective h, fun h => by rw [h]⟩
  let σ : Equiv.Perm {q // q ∈ fixF y} := x.subtypePerm hiff
  have hσ : σ ^ 7 ^ 1 = 1 := by
    rw [pow_one]
    ext ⟨q, hq⟩
    simp [σ, Equiv.Perm.subtypePerm_pow, hx]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hempty : σ.supportᶜ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hq
    exact hfree q.1 (congrArg Subtype.val hq)
  rw [hempty, Finset.card_empty, Fintype.card_coe] at hmod
  exact (Nat.modEq_zero_iff_dvd.1 hmod.symm)

noncomputable abbrev G7 : Equiv.Perm (Fin 182) := permOfArr 182 g7

theorem g7_mem : G7 ∈ tT :=
  (CFSG.EvenSmallLie.OmegaEight.chain_word_mem (hn := by norm_num)
    (hk := by rw [tS_size]; norm_num) (hb := by decide) tChain_ok.2.1.1 [1, 2, 1, 1]
    (by rw [tS_size]; decide)).2

theorem U3Facts.g7_spec (f : U3Facts) : orderOf G7 = 7 ∧ ∀ p, G7 p ≠ p := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hr : Rep 182 g7 G7 := rep_of_validA f.valid
  have hfree : ∀ p, G7 p ≠ p := by
    intro p hp
    have h1 : (fixF G7).card = 0 := by rw [card_fixF_eq hr, f.fix7]
    have h2 : p ∈ fixF G7 := by simp [fixF, hp]
    exact absurd (Finset.card_pos.2 ⟨p, h2⟩) (by omega)
  have h7 : G7 * (G7 * (G7 * (G7 * (G7 * (G7 * G7))))) = 1 :=
    (eqA_iff (rep_compA hr (rep_compA hr (rep_compA hr (rep_compA hr (rep_compA hr
      (rep_compA hr hr)))))) rep_idA).1 f.pow
  have hne : G7 ≠ 1 := fun h1 => hfree 0 (by rw [h1]; rfl)
  have hpow : G7 ^ 7 = 1 := by
    rw [← h7]
    simp [pow_succ, mul_assoc]
  exact ⟨orderOf_eq_prime hpow hne, hfree⟩

theorem fixed_point_free_of_order_seven
    {x : Equiv.Perm (Fin 182)} (hx : x ∈ tT)
    (hx7 : orderOf x = 7) : ∀ p, x p ≠ p := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have f := u3Facts_of_check Certificates.certificate27266
  obtain ⟨hg7, hgfree⟩ := f.g7_spec
  set g₀ : ↥tT := ⟨G7, g7_mem⟩ with hg₀
  set X : ↥tT := ⟨x, hx⟩ with hX
  have hg₀o : orderOf g₀ = 7 := (Subgroup.orderOf_coe g₀).symm.trans hg7
  have hXo : orderOf X = 7 := (Subgroup.orderOf_coe X).symm.trans hx7
  have h2 : ¬ 7 ^ 2 ∣ Nat.card ↥tT := by
    rw [card_tT]
    decide
  obtain ⟨c, hc⟩ := exists_conj_zpowers_eq hg₀o hXo h2
  intro p hp
  set q : Fin 182 := (c : Equiv.Perm (Fin 182))⁻¹ p with hq
  let S : Subgroup ↥tT := (MulAction.stabilizer (Equiv.Perm (Fin 182)) q).comap tT.subtype
  have hzS : c⁻¹ * X * c ∈ S := by
    show (((c⁻¹ * X * c : ↥tT) : Equiv.Perm (Fin 182))) • q = q
    simp only [Equiv.Perm.smul_def, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hq,
      hX, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [hp]
  have hg₀S : g₀ ∈ S := by
    have : g₀ ∈ zpowers (c⁻¹ * X * c) := hc ▸ mem_zpowers g₀
    exact (zpowers_le.2 hzS) this
  exact hgfree q (by simpa [S, Equiv.Perm.smul_def, hg₀] using hg₀S)

theorem fix_of_order_three
    {y : Equiv.Perm (Fin 182)} (hy : y ∈ tT) (hy3 : orderOf y = 3) :
    (fixF y).card = 2 ∨ (fixF y).card = 20 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have f := u3Facts_of_check Certificates.certificate27266
  have hkeys : ∀ p ∈ tKeys, p < 182 := by
    intro p hp
    simp only [tKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hkeys (enumOK_of_enumOKL f.enum)
  set U := Subgroup.closure (permsA 182 uGens) with hU
  have hUT : U ≤ tT := by
    rw [hU, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hsz : uGens.size = 6 := by simp [uGens, uWords]
    have hk' : k < uGens.size := hk
    have hk6 : k < 6 := by rwa [hsz] at hk'
    have hget : uGens[k]! = tW (uWords.getD k []) := by
      have hlen : k < uWords.length := by simpa [uWords] using hk6
      have hlen' : k < (uWords.map tW).toArray.size := by simpa using hlen
      show (uWords.map tW).toArray[k]! = _
      rw [getElem!_pos _ k hlen', List.getElem_toArray, List.getElem_map,
        List.getD_eq_getElem _ _ hlen]
    show permOfArr 182 uGens[k]! ∈ tT
    rw [hget]
    refine (CFSG.EvenSmallLie.OmegaEight.chain_word_mem (hn := by norm_num)
      (hk := by rw [tS_size]; norm_num) (hb := by decide) tChain_ok.2.1.1 _ ?_).2
    rw [tS_size]
    interval_cases k <;> decide
  have hUcard : Nat.card (U.subgroupOf tT) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv, hcard, f.size]
    norm_num
  have h3 : ¬ 3 ^ (6 + 1) ∣ Nat.card ↥tT := by
    rw [card_tT]
    decide
  have hy' : (⟨y, hy⟩ : ↥tT) ^ 3 = 1 := Subtype.ext (by
    simpa using (orderOf_eq_iff (by norm_num)).1 hy3 |>.1)
  obtain ⟨c, hc⟩ := exists_conj_mem_of_pow_eq_one hUcard h3 hy'
  rw [Subgroup.mem_subgroupOf] at hc
  have hcy : ((c⁻¹ * ⟨y, hy⟩ * c : ↥tT) : Equiv.Perm (Fin 182)) =
      (c : Equiv.Perm (Fin 182))⁻¹ * y * c := by simp
  rw [hcy] at hc
  obtain ⟨i, hi, hrep⟩ := (hmem _).1 hc
  have hrep' : Rep 182 uCert.pts[i]! ((c : Equiv.Perm (Fin 182))⁻¹ * y * c) := by
    rw [← hrep]
    exact rep_of_validA (hval i hi)
  have hne : (c : Equiv.Perm (Fin 182))⁻¹ * y * c ≠ 1 := by
    intro h1
    have : y = 1 := by
      have := congrArg (fun w => (c : Equiv.Perm (Fin 182)) * w * (c : Equiv.Perm (Fin 182))⁻¹) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hy3
    omega
  have hall := List.all_eq_true.1 f.fix uCert.pts[i]! (by
    rw [getElem!_pos uCert.pts i hi]
    exact Array.getElem_mem_toList ..)
  have hne' : eqA 182 uCert.pts[i]! (idA 182) = false := by
    by_contra h
    exact hne ((eqA_iff hrep' rep_idA).1 (by simpa using h))
  rw [hne'] at hall
  have hcnt := card_fixF_eq hrep'
  rw [card_fixF_conj] at hcnt
  simp only [Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hall
  rcases hall with h | h
  · exact Or.inl (hcnt.trans h)
  · exact Or.inr (hcnt.trans h)

theorem not_commute_orders_three_seven_tT
    {x y : Equiv.Perm (Fin 182)} (hx : x ∈ tT) (hy : y ∈ tT)
    (hx7 : orderOf x = 7) (hy3 : orderOf y = 3) : x * y ≠ y * x := by
  intro hcomm
  have hfree := fixed_point_free_of_order_seven hx hx7
  have hx7' : x ^ 7 = 1 := by rw [← hx7]; exact pow_orderOf_eq_one x
  have h7 := seven_dvd_card_fixF hx7' hcomm hfree
  rcases fix_of_order_three hy hy3 with h | h <;> omega

theorem index_tT : (tT.subgroupOf autT).index = 4 := by
  have h := (tT.subgroupOf autT).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tT_le_autT).toEquiv, card_tT, card_autT] at h
  omega

theorem pow_four_mem_tT {z : Equiv.Perm (Fin 182)}
    (hz : z ∈ autT) : z ^ 4 ∈ tT := by
  have hnorm : (tT.subgroupOf autT).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer tT_le_autT).2 autT_le_normalizer
  have h := Subgroup.pow_index_mem (tT.subgroupOf autT) (⟨z, hz⟩ : ↥autT)
  rw [index_tT, mem_subgroupOf] at h
  simpa [Subgroup.coe_pow] using h

theorem mem_tT_of_pow_three {z : Equiv.Perm (Fin 182)}
    (hz : z ∈ autT) (hz3 : z ^ 3 = 1) : z ∈ tT := by
  have h := pow_four_mem_tT hz
  have e : z ^ 4 = z := by rw [pow_succ, hz3, one_mul]
  rwa [e] at h

theorem mem_tT_of_pow_seven {z : Equiv.Perm (Fin 182)}
    (hz : z ∈ autT) (hz7 : z ^ 7 = 1) : z ∈ tT := by
  have h := pow_four_mem_tT hz
  have e : z = (z ^ 4) ^ 2 := by
    rw [← pow_mul]
    calc z = z ^ 7 * z := by rw [hz7, one_mul]
      _ = z ^ (4 * 2) := by rw [← pow_succ]
  rw [e]
  exact pow_mem h 2

theorem not_seven_dvd_centralizer_of_l39
    {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal]
    (hC : centralizer (N : Set Γ) = ⊥) (hN : LieModel ↥N .PSL 3 3 2) {y : Γ}
    (hy : orderOf y = 3) : ¬ 7 ∣ Nat.card ↥(centralizer ({y} : Set Γ)) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_lieModel hN
  obtain ⟨M, -, hA⟩ := exists_autModel e
  let ρ : Γ →* Equiv.Perm (Fin 182) := M.ι.comp (conjEmb N (MulEquiv.refl ↥N))
  have hρ : Function.Injective ρ :=
    M.ι_injective.comp (conjEmb_injective N (MulEquiv.refl ↥N) hC)
  have hρA : ∀ γ, ρ γ ∈ autT := fun γ => hA ▸ M.ι_mem _
  obtain ⟨g, hg⟩ := exists_orderOf_of_dvd_card (Γ := ↥(centralizer ({y} : Set Γ))) h7
  have hg7 : orderOf (g : Γ) = 7 := by rw [Subgroup.orderOf_coe]; exact hg
  have hcomm : (g : Γ) * y = y * (g : Γ) := mem_centralizer_singleton_iff.1 g.2
  have hx7 : orderOf (ρ g) = 7 := by rw [orderOf_injective ρ hρ]; exact hg7
  have hy3 : orderOf (ρ y) = 3 := by rw [orderOf_injective ρ hρ]; exact hy
  have hxT : ρ g ∈ tT := mem_tT_of_pow_seven (hρA _) (by
    rw [← map_pow, ← hg7, pow_orderOf_eq_one, map_one])
  have hyT : ρ y ∈ tT := mem_tT_of_pow_three (hρA _) (by
    rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one])
  exact not_commute_orders_three_seven_tT hxT hyT hx7 hy3 (by rw [← map_mul, ← map_mul, hcomm])

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
