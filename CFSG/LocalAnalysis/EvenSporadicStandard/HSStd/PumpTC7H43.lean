module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Der
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Skel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Word
public import Certificates.Certificate27268
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecG
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LModel
public import CFSG.RankThree.PartOne.KS.OrbitCert

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Certificates.Native
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43

open CFSG.Sporadic.Th.Native (Table)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

section Groups


noncomputable abbrev P43 : Subgroup (Equiv.Perm (Fin 80)) := pi.range

noncomputable abbrev R43 : Subgroup (Equiv.Perm (Fin 80)) := l43Model.T.range

theorem P43_le_R43 : P43 ≤ R43 := by
  rintro _ ⟨g, rfl⟩
  exact ⟨MulAut.conj g, l43Model.T_conj g⟩

theorem conj_mem_P43 {τ : Equiv.Perm (Fin 80)} (hτ : τ ∈ R43) {p : Equiv.Perm (Fin 80)}
    (hp : p ∈ P43) : τ * p * τ⁻¹ ∈ P43 := by
  obtain ⟨α, rfl⟩ := hτ
  obtain ⟨g, rfl⟩ := hp
  exact ⟨α g, (l43Model.T_spec α g).symm⟩

theorem R43_le_normalizer : R43 ≤ normalizer (P43 : Set (Equiv.Perm (Fin 80))) := by
  intro τ hτ
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_P43 hτ hh, fun hh => ?_⟩
  have := conj_mem_P43 (R43.inv_mem hτ) hh
  simpa [mul_assoc] using this

@[expose] noncomputable def uL : List (Equiv.Perm (Fin 80)) :=
  1 :: l43Runs.map fun R => tp 80 R.u

theorem uL_length : uL.length = 4 := by simp [uL, l43Runs]

theorem exists_coset {x : Equiv.Perm (Fin 80)} (hx : x ∈ R43) : ∃ u ∈ uL, x * u⁻¹ ∈ P43 := by
  obtain ⟨α, rfl⟩ := hx
  rcases l43_cos α with h | ⟨R', hR', h⟩ | ⟨u, hu, -⟩
  · exact ⟨1, List.mem_cons_self, by simpa using h⟩
  · exact ⟨tp 80 R'.u, List.mem_cons_of_mem _ (List.mem_map.2 ⟨R', hR', rfl⟩), h⟩
  · exact absurd hu List.not_mem_nil

theorem card_R43_le : Nat.card R43 ≤ 4 * Nat.card P43 := by
  classical
  have hcov : ∀ x : R43, ∃ i : Fin uL.length, (x : Equiv.Perm (Fin 80)) * (uL.get i)⁻¹ ∈ P43 := by
    intro x
    obtain ⟨u, hu, h⟩ := exists_coset x.2
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hu
    exact ⟨i, h⟩
  choose i hi using hcov
  let f : R43 → P43 × Fin uL.length := fun x =>
    (⟨(x : Equiv.Perm (Fin 80)) * (uL.get (i x))⁻¹, hi x⟩, i x)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    rw [h2] at h1
    exact Subtype.ext (mul_right_cancel h1)
  calc Nat.card R43 ≤ Nat.card (P43 × Fin uL.length) := Nat.card_le_card_of_injective f hf
    _ = Nat.card P43 * uL.length := by rw [Nat.card_prod, Nat.card_fin]
    _ = 4 * Nat.card P43 := by rw [uL_length, mul_comm]

theorem relIndex_P43_R43 : P43.relIndex R43 ≤ 4 := by
  have h := Subgroup.relIndex_mul_card (H := P43) (K := R43)
  rw [inf_eq_left.2 P43_le_R43] at h
  have hpos : 0 < Nat.card P43 := Nat.card_pos
  have h2 : P43.relIndex R43 * Nat.card P43 ≤ 4 * Nat.card P43 := h ▸ card_R43_le
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem card_R43_inf_le (x : Equiv.Perm (Fin 80)) :
    Nat.card ↥(R43 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 80)))) ≤
      4 * Nat.card ↥(P43 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 80)))) := by
  set C := centralizer ({x} : Set (Equiv.Perm (Fin 80))) with hCdef
  have hne : P43.relIndex R43 ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card (H := P43) (K := R43)
    rw [h0, zero_mul] at this
    exact (Nat.card_pos (α := ↥R43)).ne' this.symm
  have hle : P43.relIndex (R43 ⊓ C) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left hne).trans relIndex_P43_R43
  have h := Subgroup.relIndex_mul_card (H := P43) (K := R43 ⊓ C)
  have hPC : P43 ⊓ (R43 ⊓ C) = P43 ⊓ C := by
    rw [← inf_assoc, inf_eq_left.2 P43_le_R43]
  rw [hPC] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ hle

theorem mem_P43_of_pow_three {z : Equiv.Perm (Fin 80)}
    (hz : z ∈ R43) (hz3 : z ^ 3 = 1) : z ∈ P43 := by
  obtain ⟨α, rfl⟩ := hz
  have hz3' : l43Model.T α * l43Model.T α * l43Model.T α = 1 := by
    simpa [pow_succ] using hz3
  rcases l43_cos α with h | ⟨R', hR', h⟩ | ⟨u, hu, -⟩
  · exact h
  · have hRF := Certificates.certificate22242.2.1 R' hR'
    set U := tp 80 R'.u with hU
    have hU2 : U * U = 1 := by rw [← pow_two]; exact hRF.u2
    have hUinv : U⁻¹ = U := inv_eq_of_mul_eq_one_right hU2
    obtain ⟨a, ha, haz⟩ : ∃ a ∈ P43, l43Model.T α = a * U :=
      ⟨l43Model.T α * U⁻¹, h, by simp⟩
    have hsq : l43Model.T α * l43Model.T α ∈ P43 := by
      have e : l43Model.T α * l43Model.T α = a * (U * a * U⁻¹) := by
        rw [haz, hUinv]
        simp [mul_assoc]
      rw [e]
      exact P43.mul_mem ha (hRF.unorm a ha)
    have e2 : l43Model.T α = (l43Model.T α * l43Model.T α)⁻¹ :=
      eq_inv_of_mul_eq_one_right hz3'
    rw [e2]
    exact P43.inv_mem hsq
  · exact absurd hu List.not_mem_nil

end Groups

theorem getElem!_map_toArray {α β : Type*} [Inhabited β] (f : α → β) (L : List α) {k : ℕ}
    (hk : k < L.length) : (L.map f).toArray[k]! = f L[k] := by
  have hlen : k < (L.map f).toArray.size := by simpa using hk
  rw [getElem!_pos _ k hlen, List.getElem_toArray, List.getElem_map]

theorem permsA_map_natArr (L : List Table) :
    permsA 80 (L.map natArr).toArray = tp 80 '' {x | x ∈ L.toArray} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < L.length := by simpa using hk
    exact ⟨L[k], by simp, by rw [getElem!_map_toArray natArr L hk']⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (by simpa using hx : x ∈ L)
    exact ⟨k, by simpa using hk, by rw [getElem!_map_toArray natArr L hk]⟩

theorem keys43_lt : ∀ p ∈ keys43, p < 80 := by decide

section Rows


theorem l43_runFacts : ∀ R ∈ l43Runs, RunFacts pi.range R :=
  Certificates.certificate22242.2.1

theorem closure_gsP : Subgroup.closure (permsA 80 gsP) = P43 := by
  have hsz : gsP.size = pgTbls.size := by simp [gsP]
  have hge : ∀ k, k < pgTbls.size → gsP[k]! = natArr pgTbls[k]! := by
    intro k hk
    show (pgTbls.map natArr)[k]! = natArr pgTbls[k]!
    rw [getElem!_pos (pgTbls.map natArr) k (by simpa using hk), Array.getElem_map,
      getElem!_pos pgTbls k hk]
  have hset : permsA 80 gsP = l43Gens '' {l | l < pgTbls.size} := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, hsz]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k, hk, ?_⟩
      rw [hge k hk]
      exact (permOfArr_eq_of_rep (co2Rep_natArr_iff.2 (l43_groupData.rep k hk))).symm
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k, hk, ?_⟩
      rw [hge k hk]
      exact permOfArr_eq_of_rep (co2Rep_natArr_iff.2 (l43_groupData.rep k hk))
  rw [hset, ← l43_groupData.gen]

@[expose] noncomputable def repP (j : ℕ) : Equiv.Perm (Fin 80) :=
  if h : j < rows43.length then tp 80 rows43[j].row.rep else 1

theorem cover43 : ∀ τ ∈ R43, orderOf τ = 2 →
    ∃ j < rows43.length, ∃ c ∈ R43, τ = c * repP j * c⁻¹ := by
  rintro τ hτ hτ2
  obtain ⟨α, rfl⟩ := hτ
  have key : ∀ R ∈ l43Runs, l43Model.T α ∈ pi.range ⊔ zpowers (tp 80 R.u) →
      ∃ j < rows43.length, ∃ c ∈ R43, l43Model.T α = c * repP j * c⁻¹ := by
    intro R hR hmem
    have hRF := l43_runFacts R hR
    obtain ⟨r, hr, g, hg, hτg⟩ := hRF.cover _ hmem hτ2
    obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.1
      (show r ∈ rows43 from List.mem_flatMap.2 ⟨R, hR, hr⟩)
    refine ⟨j, hj, g, P43_le_R43 hg, ?_⟩
    rw [hτg]
    simp [repP, hj, hjr]
  rcases mem_A₀_or_run_of_involution (extra := []) l43_groupData
      (fun _ hu => absurd hu List.not_mem_nil) hτ2 (l43_cos α) with
    h0 | ⟨R', hR', hRu⟩
  · exact key runuD (by simp [l43Runs]) (mem_sup_left h0)
  · have hRF := l43_runFacts R' hR'
    refine key R' hR' ((hRF.memR _).2 (Or.inr ?_))
    have hUinv : (tp 80 R'.u)⁻¹ = tp 80 R'.u := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hRF.u2]
    rwa [hUinv] at hRu

theorem der_lower {r : Row} (hrf : RowFacts pi.range r.row) {pairs : List (List ℤ × List ℤ)}
    (h : derOK43 r pairs = true) :
    360 < Nat.card ↥⁅P43 ⊓ centralizer ({tp 80 r.row.rep} : Set (Equiv.Perm (Fin 80))),
      P43 ⊓ centralizer ({tp 80 r.row.rep} : Set (Equiv.Perm (Fin 80)))⁆ := by
  simp only [derOK43, derCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hgs, hpairs⟩, henum⟩, hsize⟩ := h
  have hgs' : ∀ k < (cgArr r).size, validA 80 (cgArr r)[k]! = true :=
    fun k hk => allLt_spec hgs hk
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec keys43_lt (enumOK_of_enumOKL henum)
  set D := P43 ⊓ centralizer ({tp 80 r.row.rep} : Set (Equiv.Perm (Fin 80))) with hD
  have hcl : Subgroup.closure (permsA 80 (cgArr r)) = D := by
    rw [cgArr, permsA_map_natArr]
    exact hrf.cent
  have hWle : Subgroup.closure (permsA 80 (derComms r pairs)) ≤ ⁅D, D⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < pairs.length := by simpa [derComms] using hk
    have hp := hpairs pairs[k] (List.getElem_mem hk')
    have hk2 : (derComms r pairs)[k]! =
        commutatorA 80 (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) pairs[k].1)
          (wordA 80 (cgArr r) (rawInvs 80 (cgArr r)) pairs[k].2) := by
      unfold derComms
      exact getElem!_map_toArray _ pairs hk'
    show permOfArr 80 (derComms r pairs)[k]! ∈ ⁅D, D⁆
    rw [hk2]
    obtain ⟨hx1, hx2⟩ := wordA_mem_closure hgs' pairs[k].1 hp.1
    obtain ⟨hy1, hy2⟩ := wordA_mem_closure hgs' pairs[k].2 hp.2
    rw [permOfArr_eq_of_rep (rep_commutatorA (validA_of_rep hx1) (validA_of_rep hy1))]
    rw [hcl] at hx2 hy2
    exact Subgroup.commutator_mem_commutator hx2 hy2
  have h720 : Nat.card ↥(Subgroup.closure (permsA 80 (derComms r pairs))) = 720 := by
    rw [hcard, hsize]
  have := Subgroup.card_le_of_le hWle
  omega

theorem survivor_of_survCheck {r : Row} (hrf : RowFacts pi.range r.row) {ec : ArrCert}
    {x0 : Array ℕ} {cc : ArrCert} (h : survCheck r ec x0 cc = true) :
    SurvivorProp R43 (tp 80 r.row.rep) := by
  intro z hz hz3 hzc
  have hz3' : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hzP := mem_P43_of_pow_three hz hz3'
  have hcl : Subgroup.closure (permsA 80 (cgArr r)) =
      P43 ⊓ centralizer ({tp 80 r.row.rep} : Set (Equiv.Perm (Fin 80))) := by
    rw [cgArr, permsA_map_natArr]
    exact hrf.cent
  have hzD : z ∈ Subgroup.closure (permsA 80 (cgArr r)) := by
    rw [hcl]
    exact Subgroup.mem_inf.2 ⟨hzP, hzc⟩
  simp only [survCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨henum, hgsP⟩, hx0⟩, hcc⟩, hsize⟩, hall⟩ := h
  have hgsP' : ∀ k < gsP.size, validA 80 gsP[k]! = true := fun k hk => allLt_spec hgsP hk
  obtain ⟨hmem, -, hval⟩ := enumOK_spec keys43_lt (enumOK_of_enumOKL henum)
  obtain ⟨i, hi, hiz⟩ := (hmem z).1 hzD
  have hrepi : Rep 80 ec.pts[i]! z := by
    rw [← hiz]
    exact rep_of_validA (hval i hi)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    omega
  have hord3 : isOrd3 ec.pts[i]! = true := by
    have h1 : eqA 80 ec.pts[i]! (idA 80) = false := by
      by_contra hne
      exact hz1 ((eqA_iff hrepi rep_idA).1 (by simpa using hne))
    have h2 : eqA 80 (compA 80 ec.pts[i]! (compA 80 ec.pts[i]! ec.pts[i]!)) (idA 80) = true :=
      (eqA_iff (rep_compA hrepi (rep_compA hrepi hrepi)) rep_idA).2 (by
        rw [← mul_assoc]
        simpa [pow_succ] using hz3')
    simp [isOrd3, h1, h2]
  have hmemi : ec.pts[i]! ∈ ec.pts.toList := by
    rw [getElem!_pos ec.pts i hi]
    exact Array.getElem_mem_toList ..
  have hany := List.all_eq_true.1 hall _ hmemi
  rw [hord3] at hany
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hany
  obtain ⟨a, ha, hea⟩ := hany
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ha
  have hm' : m < cc.pts.size := by simpa using hm
  have hcc' := arrCertOK_of_arrCertOKL hcc
  have hvm := arrCertOK_valid hcc' hm'
  rw [Array.getElem_toList, ← getElem!_pos cc.pts m hm'] at hea
  have hzm : permOfArr 80 cc.pts[m]! = z :=
    ((eqA_iff hrepi (rep_of_validA hvm)).1 hea).symm
  obtain ⟨g, hg, hzg⟩ := (mem_class_iff hgsP' hcc' z).2 ⟨m, hm', hzm⟩
  rw [closure_gsP] at hg
  have hos := (CFSG.RankThree.PartOne.card_closure_eq_card_mul_card_centralizer keys43_lt hgsP'
    hcc').2
  rw [closure_gsP, card_range_pi, hsize] at hos
  have hC81 : Nat.card ↥(P43 ⊓ centralizer ({permOfArr 80 x0} : Set (Equiv.Perm (Fin 80)))) =
      81 := by
    omega
  have hcz : Nat.card ↥(P43 ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 80)))) = 81 := by
    rw [hzg, card_inf_centralizer_conj hg, hC81]
  exact not_eight_dvd_card_inf_centralizer P43_le_R43 relIndex_P43_R43 (by rw [hcz]; decide)

theorem cases_row {r : Row} (hrf : RowFacts pi.range r.row) (hok : rowOK43 r = true) :
    ExcludedProp P43 (tp 80 r.row.rep) ∨ ExcludedCard R43 (tp 80 r.row.rep) ∨
      ExcludedDer P43 (tp 80 r.row.rep) ∨ SurvivorProp R43 (tp 80 r.row.rep) := by
  simp only [rowOK43, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ((h1 | h2) | ⟨h3, h3'⟩) | ⟨h4, h4'⟩
  · exact Or.inl ⟨_, le_rfl, by rw [hrf.card]; exact h1⟩
  · refine Or.inr (Or.inl ?_)
    intro hdvd
    have hpos : 0 < Nat.card ↥(R43 ⊓ centralizer ({tp 80 r.row.rep} : Set _)) :=
      Nat.card_pos
    have h5 := Nat.le_of_dvd hpos hdvd
    have h6 := card_R43_inf_le (tp 80 r.row.rep)
    rw [hrf.card] at h6
    omega
  · refine Or.inr (Or.inr (Or.inl ?_))
    cases hf : derPairs.find? (fun p => p.1 == r.row.rep) with
    | none => rw [hf] at h3'; exact absurd h3' (by simp)
    | some p =>
      rw [hf] at h3'
      exact ⟨by rw [hrf.card, h3], der_lower hrf h3'⟩
  · refine Or.inr (Or.inr (Or.inr ?_))
    exact survivor_of_survCheck hrf (ec := _) (x0 := _) (cc := _) h4'

end Rows

section Final


theorem exists_embedding_p1 {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    (hC : centralizer (N : Set Γ) = ⊥) (e : N ≃* projectiveSL 4 (ZMod 3)) :
    ∃ ρ : Γ →* Equiv.Perm (Fin 80), Function.Injective ρ ∧ ρ.range ≤ R43 ∧ P43 ≤ ρ.range := by
  refine ⟨l43Model.T.comp (conjEmb N e),
    l43Model.T_injective.comp (conjEmb_injective N e hC), ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨k, rfl⟩
    refine ⟨((e.symm k : N) : Γ), ?_⟩
    have hconj : conjEmb N e ((e.symm k : N) : Γ) = MulAut.conj k := by
      ext x
      rw [conjEmb_apply]
      simp [MulAut.conj_apply]
    show l43Model.T (conjEmb N e ((e.symm k : N) : Γ)) = pi k
    rw [hconj]
    exact l43Model.T_conj k

theorem h43Facts_of_check (h : h43OK = true) :
    rows43.length = 11 ∧ ∀ r ∈ rows43, rowOK43 r = true := by
  simp only [h43OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h

theorem harrisL43_noD8 {Γ : Type} [Group Γ] [Finite Γ]
    (N : Subgroup Γ) [N.Normal] (hC : centralizer (N : Set Γ) = ⊥)
    (hN : CFSG.Blueprint.LieModel ↥N .PSL 4 3 1) {t : Γ} (ht : orderOf t = 2)
    (hD : Nonempty (↥(centralizer ({t} : Set Γ)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))) {y : Γ}
    (hy : y ∈ centralizer ({t} : Set Γ)) (hy3 : orderOf y = 3) :
    ¬ 8 ∣ Nat.card ↥(centralizer ({y} : Set Γ)) := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hN
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  let e' : ↥N ≃* projectiveSL 4 (ZMod 3) := e.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
      (ZMod.ringEquivOfPrime K Nat.prime_three hc).symm)
  obtain ⟨ρ, hρ, hρR, hPρ⟩ := exists_embedding_p1 N hC e'
  obtain ⟨e2⟩ := hD
  obtain ⟨hC2880, hDder⟩ := card_centralizer_commutator_le e2
  obtain ⟨hlen, hall⟩ := h43Facts_of_check Certificates.certificate27268
  refine harris_skeleton P43 R43 R43_le_normalizer ρ hρ hρR hPρ repP rows43.length cover43
    (fun j hj => ?_) ht hC2880 hDder hy3 hy
  have hmem : rows43[j] ∈ rows43 := List.getElem_mem hj
  obtain ⟨R, hR, hrR⟩ := List.mem_flatMap.1 hmem
  have hrf := (l43_runFacts R hR).row _ hrR
  have hcase := cases_row hrf (hall _ hmem)
  simpa [repP, hj] using hcase

end Final

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
