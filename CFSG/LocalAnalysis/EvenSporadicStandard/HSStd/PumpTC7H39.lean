module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L39
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Der
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Skel
public import Certificates.Certificate27267

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSmallLie.Child3.SelL39

structure H39Facts : Prop where
  s2 : s2OK s2Cert = true
  x : xOK xCert = true
  rep : ∀ j < 11, repOK xCert j = true

theorem h39Facts_of_check (h : h39OK = true) : H39Facts := by
  simp only [h39OK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem tKeys_lt : ∀ p ∈ tKeys, p < 182 := by
  intro p hp
  simp only [tKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem tW_mem {w : List ℤ} (hw : lettersOK tS.size w = true) :
    Rep 182 (tW w) (permOfArr 182 (tW w)) ∧ permOfArr 182 (tW w) ∈ tT :=
  CFSG.EvenSmallLie.OmegaEight.chain_word_mem (hn := by norm_num)
    (hk := by rw [tS_size]; norm_num) (hb := by decide) tChain_ok.2.1.1 w hw

theorem getElem!_mapW {ws : List (List ℤ)} {k : ℕ} (hk : k < ws.length) :
    (ws.map tW).toArray[k]! = tW ws[k] := by
  have hlen : k < (ws.map tW).toArray.size := by simpa using hk
  rw [getElem!_pos _ k hlen, List.getElem_toArray, List.getElem_map]

theorem closure_permsA_le_tT {ws : List (List ℤ)}
    (hws : ws.all (lettersOK tS.size) = true) :
    Subgroup.closure (permsA 182 (ws.map tW).toArray) ≤ tT := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < ws.length := by simpa using hk
  show permOfArr 182 (ws.map tW).toArray[k]! ∈ tT
  rw [getElem!_mapW hk']
  exact (tW_mem (List.all_eq_true.1 hws _ (List.getElem_mem hk'))).2

theorem fixSet_eq_fixF (z : Equiv.Perm (Fin 182)) : fixSet z = fixF z := rfl

theorem involution_fixF_card
    {w : Equiv.Perm (Fin 182)} (hw : w ∈ tT) (hw2 : orderOf w = 2) : (fixF w).card = 22 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have f := h39Facts_of_check Certificates.certificate27267
  have hs2 := f.s2
  simp only [s2OK, Bool.and_eq_true, beq_iff_eq] at hs2
  obtain ⟨⟨⟨hlet, henum⟩, hsize⟩, hall⟩ := hs2
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec tKeys_lt (enumOK_of_enumOKL henum)
  set S := Subgroup.closure (permsA 182 s2Gens) with hS
  have hST : S ≤ tT := closure_permsA_le_tT (ws := s2Words) hlet
  have hScard : Nat.card (S.subgroupOf tT) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv, hcard, hsize]
    norm_num
  have h2 : ¬ 2 ^ (7 + 1) ∣ Nat.card ↥tT := by
    rw [card_tT]
    decide
  have hy : (⟨w, hw⟩ : ↥tT) ^ 2 = 1 :=
    Subtype.ext (by simpa using (orderOf_eq_iff (by norm_num)).1 hw2 |>.1)
  obtain ⟨c, hc⟩ := exists_conj_mem_of_pow_eq_one hScard h2 hy
  rw [Subgroup.mem_subgroupOf] at hc
  have hcy : ((c⁻¹ * ⟨w, hw⟩ * c : ↥tT) : Equiv.Perm (Fin 182)) =
      (c : Equiv.Perm (Fin 182))⁻¹ * w * c := by simp
  rw [hcy] at hc
  obtain ⟨i, hi, hrep⟩ := (hmem _).1 hc
  have hrep' : Rep 182 s2Cert.pts[i]! ((c : Equiv.Perm (Fin 182))⁻¹ * w * c) := by
    rw [← hrep]
    exact rep_of_validA (hval i hi)
  have hpt := List.all_eq_true.1 hall s2Cert.pts[i]! (by
    rw [getElem!_pos s2Cert.pts i hi]
    exact Array.getElem_mem_toList ..)
  have hu2 : orderOf ((c : Equiv.Perm (Fin 182))⁻¹ * w * c) = 2 := by
    have h := (MulAut.conj (c : Equiv.Perm (Fin 182))⁻¹).orderOf_eq w
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hw2]
  have hsq : ((c : Equiv.Perm (Fin 182))⁻¹ * w * c) * ((c : Equiv.Perm (Fin 182))⁻¹ * w * c) =
      1 := by
    have := pow_orderOf_eq_one ((c : Equiv.Perm (Fin 182))⁻¹ * w * c)
    rwa [hu2, pow_two] at this
  have hsqA : eqA 182 (compA 182 s2Cert.pts[i]! s2Cert.pts[i]!) (idA 182) = true :=
    (eqA_iff (rep_compA hrep' hrep') rep_idA).2 hsq
  rw [hsqA] at hpt
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hpt
  rcases hpt with h | h
  · exfalso
    have h1 := (eqA_iff hrep' rep_idA).1 h
    rw [h1, orderOf_one] at hu2
    omega
  · have hcnt := card_fixF_eq hrep'
    rw [card_fixF_conj] at hcnt
    exact hcnt.trans h

theorem exists_conj_uCert
    {y : Equiv.Perm (Fin 182)} (hy : y ∈ tT) (hy3 : orderOf y = 3) :
    ∃ c : ↥tT, ∃ i < uCert.pts.size, validA 182 uCert.pts[i]! = true ∧
      permOfArr 182 uCert.pts[i]! = (c : Equiv.Perm (Fin 182))⁻¹ * y * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have f := u3Facts_of_check Certificates.certificate27266
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec tKeys_lt (enumOK_of_enumOKL f.enum)
  set U := Subgroup.closure (permsA 182 uGens) with hU
  have hUT : U ≤ tT := closure_permsA_le_tT (ws := uWords) (by decide)
  have hUcard : Nat.card (U.subgroupOf tT) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv, hcard, f.size]
    norm_num
  have h3 : ¬ 3 ^ (6 + 1) ∣ Nat.card ↥tT := by
    rw [card_tT]
    decide
  have hy' : (⟨y, hy⟩ : ↥tT) ^ 3 = 1 :=
    Subtype.ext (by simpa using (orderOf_eq_iff (by norm_num)).1 hy3 |>.1)
  obtain ⟨c, hc⟩ := exists_conj_mem_of_pow_eq_one hUcard h3 hy'
  rw [Subgroup.mem_subgroupOf] at hc
  have hcy : ((c⁻¹ * ⟨y, hy⟩ * c : ↥tT) : Equiv.Perm (Fin 182)) =
      (c : Equiv.Perm (Fin 182))⁻¹ * y * c := by simp
  rw [hcy] at hc
  obtain ⟨i, hi, hrep⟩ := (hmem _).1 hc
  exact ⟨c, i, hi, hval i hi, hrep⟩

theorem closure_gsT : Subgroup.closure (permsA 182 gsT) = tT := by
  have hg : ∀ k < 2, gsT[k]! = tS[k]! := by
    intro k hk
    interval_cases k
    · rw [tS_getElem_zero]
      simp [gsT]
    · rw [tS_getElem_one]
      simp [gsT]
  have hsz : gsT.size = 2 := by simp [gsT]
  rw [tT_eq]
  congr 1
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, hsz]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [hg k hk]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [hg k hk]⟩

theorem mem_xClass_of_fix_twenty
    {z : Equiv.Perm (Fin 182)} (hz : z ∈ tT) (hz3 : orderOf z = 3)
    (hfz : (fixF z).card = 20) : ∃ m < xCert.pts.size, permOfArr 182 xCert.pts[m]! = z := by
  have f := h39Facts_of_check Certificates.certificate27267
  have hx := f.x
  simp only [xOK, Bool.and_eq_true] at hx
  obtain ⟨⟨⟨hlet, hgs⟩, hcert⟩, hU⟩ := hx
  have hgs' : ∀ k < gsT.size, validA 182 gsT[k]! = true := fun k hk => allLt_spec hgs hk
  have hcert' := arrCertOK_of_arrCertOKL hcert
  obtain ⟨c, i, hi, hvalid, hrep⟩ := exists_conj_uCert hz hz3
  have hrepi : Rep 182 uCert.pts[i]! (permOfArr 182 uCert.pts[i]!) := rep_of_validA hvalid
  have hfix : fixCount uCert.pts[i]! = 20 := by
    have h1 := card_fixF_eq hrepi
    rw [hrep, card_fixF_conj] at h1
    omega
  have hmemU : uCert.pts[i]! ∈ uCert.pts.toList := by
    rw [getElem!_pos uCert.pts i hi]
    exact Array.getElem_mem_toList ..
  have hany := List.all_eq_true.1 hU _ hmemU
  simp only [hfix, bne_self_eq_false, Bool.false_or, List.any_eq_true] at hany
  obtain ⟨a', ha', hea⟩ := hany
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ha'
  have hm' : m < xCert.pts.size := by simpa using hm
  rw [Array.getElem_toList] at hea
  have hvm := arrCertOK_valid hcert' hm'
  rw [← getElem!_pos xCert.pts m hm'] at hea
  have heq : permOfArr 182 uCert.pts[i]! = permOfArr 182 xCert.pts[m]! :=
    (eqA_iff hrepi (rep_of_validA hvm)).1 hea |>.trans rfl
  have hu : permOfArr 182 xCert.pts[m]! = (c : Equiv.Perm (Fin 182))⁻¹ * z * c := by
    rw [← heq, hrep]
  have hu' := (mem_class_iff hgs' hcert' (permOfArr 182 xCert.pts[m]!)).2 ⟨m, hm', rfl⟩
  obtain ⟨g, hg, hgu⟩ := hu'
  rw [closure_gsT] at hg
  refine (mem_class_iff (n := 182) (ps := tKeys) hgs' hcert' z).1 ⟨c * g, ?_, ?_⟩
  · rw [closure_gsT]
    exact tT.mul_mem c.2 hg
  · rw [hu] at hgu
    have : z = (c : Equiv.Perm (Fin 182)) * ((c : Equiv.Perm (Fin 182))⁻¹ * z * c) *
        (c : Equiv.Perm (Fin 182))⁻¹ := by group
    rw [this, hgu]
    group

theorem odd_inf_centralizer_of_two_fixed
    {z : Equiv.Perm (Fin 182)} (hz3 : orderOf z = 3)
    (hfz : (fixF z).card = 2) :
    ¬ 2 ∣ Nat.card ↥(tT ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 182)))) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_orderOf_of_dvd_card
    (Γ := ↥(tT ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 182))))) h2
  have hwT : (w : Equiv.Perm (Fin 182)) ∈ tT := (Subgroup.mem_inf.1 w.2).1
  have hwC : (w : Equiv.Perm (Fin 182)) ∈ centralizer ({z} : Set (Equiv.Perm (Fin 182))) :=
    (Subgroup.mem_inf.1 w.2).2
  have hw2 : orderOf (w : Equiv.Perm (Fin 182)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  have hcomm : z * (w : Equiv.Perm (Fin 182)) = (w : Equiv.Perm (Fin 182)) * z :=
    (mem_centralizer_singleton_iff.1 hwC).symm
  have h22 := involution_fixF_card hwT hw2
  refine false_of_commuting_fixed (z := z) (w := (w : Equiv.Perm (Fin 182))) ?_ ?_ hcomm hfz ?_
  · rw [← hz3]
    exact pow_orderOf_eq_one z
  · rw [← hw2]
    exact pow_orderOf_eq_one _
  · rw [fixSet_eq_fixF, h22]

theorem xCert_valid {m : ℕ} (hm : m < xCert.pts.size) :
    validA 182 xCert.pts[m]! = true := by
  have f := h39Facts_of_check Certificates.certificate27267
  have hx := f.x
  simp only [xOK, Bool.and_eq_true] at hx
  exact arrCertOK_valid (arrCertOK_of_arrCertOKL hx.1.2) hm

theorem survivor_repPerm
    {j : ℕ} (hj : j < 11) (hnone : exclTab.getD j none = none) :
    SurvivorProp autT (repPerm j) := by
  intro z hz hz3 hzc
  have f := h39Facts_of_check Certificates.certificate27267
  have hrep := f.rep j hj
  simp only [repOK, hnone, survOK, List.all_eq_true] at hrep
  have hzp : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hzT : z ∈ tT := mem_tT_of_pow_three hz hzp
  rcases fix_of_order_three hzT hz3 with h2 | h20
  · exact not_eight_dvd_card_inf_centralizer tT_le_autT (le_of_eq index_tT)
      (odd_inf_centralizer_of_two_fixed hz3 h2)
  · exfalso
    obtain ⟨m, hm, hmz⟩ := mem_xClass_of_fix_twenty hzT hz3 h20
    have hx := hrep xCert.pts[m]! (by
      rw [getElem!_pos xCert.pts m hm]
      exact Array.getElem_mem_toList ..)
    have hxr : Rep 182 xCert.pts[m]! z := by
      rw [← hmz]
      exact rep_of_validA (xCert_valid hm)
    have hr := (repPerm_spec hj).1
    have hcomm : z * repPerm j = repPerm j * z := mem_centralizer_singleton_iff.1 hzc
    have := (eqA_iff (rep_compA hxr hr) (rep_compA hr hxr)).2 hcomm
    rw [this] at hx
    exact absurd hx (by decide)

theorem excluded_repPerm {j : ℕ}
    (hj : j < 11) {ws : List (List ℤ)} {k : ℕ} (hsome : exclTab.getD j none = some (ws, k)) :
    ExcludedProp tT (repPerm j) := by
  have f := h39Facts_of_check Certificates.certificate27267
  have hrep := f.rep j hj
  simp only [repOK, hsome, exclOK, groupOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, List.all_eq_true] at hrep
  obtain ⟨⟨⟨⟨hlet, henum⟩, hsize⟩, hcomm⟩, hk⟩ := hrep
  have hlet' : ws.all (lettersOK tS.size) = true := List.all_eq_true.2 hlet
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec tKeys_lt (enumOK_of_enumOKL henum)
  have hr := (repPerm_spec hj).1
  refine ⟨Subgroup.closure (permsA 182 (ws.map tW).toArray), le_inf
    (closure_permsA_le_tT hlet') ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    have hk'' : k' < ws.length := by simpa using hk'
    show permOfArr 182 (ws.map tW).toArray[k']! ∈ centralizer ({repPerm j} : Set _)
    rw [getElem!_mapW hk'']
    have hw := (tW_mem (List.all_eq_true.1 hlet' _ (List.getElem_mem hk''))).1
    have hc := hcomm (tW ws[k']) (List.mem_map.2 ⟨_, List.getElem_mem hk'', rfl⟩)
    rw [mem_centralizer_singleton_iff]
    exact (eqA_iff (rep_compA hw hr) (rep_compA hr hw)).1 hc
  · rw [hcard, hsize]
    exact hk

theorem cases_repPerm
    {j : ℕ} (hj : j < 11) :
    ExcludedProp tT (repPerm j) ∨ SurvivorProp autT (repPerm j) := by
  cases h : exclTab.getD j none with
  | none => exact Or.inr (survivor_repPerm hj h)
  | some p =>
    obtain ⟨ws, k⟩ := p
    exact Or.inl (excluded_repPerm hj h)

theorem harrisL39_noD8
    {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal]
    (hC : centralizer (N : Set Γ) = ⊥) (hN : CFSG.Blueprint.LieModel ↥N .PSL 3 3 2) {t : Γ}
    (ht : orderOf t = 2)
    (hD : Nonempty (↥(centralizer ({t} : Set Γ)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))) {y : Γ}
    (hy : y ∈ centralizer ({t} : Set Γ)) (hy3 : orderOf y = 3) :
    ¬ 8 ∣ Nat.card ↥(centralizer ({y} : Set Γ)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_lieModel hN
  obtain ⟨M, hP, hA⟩ := exists_autModel e
  have hcent : ∀ c : Equiv.Perm (Fin 182), (∀ x ∈ M.P, c * x = x * c) → c = 1 := fun c hc =>
    eq_one_of_comm_tT fun g hg => (hc g (hP ▸ hg)).symm
  obtain ⟨ρ, hρ, hρA, hPρ⟩ := exists_embedding N hC (MulEquiv.refl ↥N) M hcent
  rw [hA] at hρA
  rw [hP] at hPρ
  obtain ⟨e2⟩ := hD
  obtain ⟨hC2880, hDder⟩ := card_centralizer_commutator_le e2
  refine harris_skeleton tT autT autT_le_normalizer ρ hρ hρA hPρ repPerm 11 ?_
    (fun j hj => ?_) ht hC2880 hDder hy3 hy
  · intro τ hτ hτ2
    obtain ⟨g, hg, hgs⟩ := exists_conj_sylowT τ hτ hτ2
    have hgo : orderOf (g * τ * g⁻¹) = 2 := by
      have h := (MulAut.conj g).orderOf_eq τ
      rw [MulAut.conj_apply] at h
      rw [h, hτ2]
    obtain ⟨j, hj, c, hc, hcg⟩ := exists_rep_of_involution hgs hgo
    refine ⟨j, hj, g⁻¹ * c, autT.mul_mem (autT.inv_mem hg) (sylowT_le_autT hc), ?_⟩
    have : τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
    rw [this, hcg]
    group
  · rcases cases_repPerm hj with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
