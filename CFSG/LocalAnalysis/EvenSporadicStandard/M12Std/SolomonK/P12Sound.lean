module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Enum
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Count
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

open Equiv Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434F42 (wordElt wordElt_mem)

variable {n : ℕ}

@[expose] def arrA (n : ℕ) (x : alternatingGroup (Fin n)) : Array ℕ :=
  permArr n (x : Perm (Fin n))

theorem arrA_injective : Function.Injective (arrA n) := fun _ _ h =>
  Subtype.ext (permArr_injective h)

theorem arrA_mul (x y : alternatingGroup (Fin n)) :
    pmul n (arrA n x) (arrA n y) = arrA n (x * y) := pmul_permArr _ _

theorem arrA_one : pid n = arrA n 1 := pid_eq_permArr

@[expose] def genSub (n : ℕ) (ws : List (List (ℕ × ℕ))) : Subgroup (alternatingGroup (Fin n)) :=
  Subgroup.closure (gensFn n ws '' {k | k < ws.length})

theorem genSub_card {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {L : List (List ℕ)} (h : enumOK n (ws.map (swapsArr n)) L = true) :
    Nat.card (genSub n ws) = L.length :=
  (enumOK_sound hv h).2

theorem genSub_vals {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {L : List (List ℕ)} (h : enumOK n (ws.map (swapsArr n)) L = true) (y : Array ℕ) :
    y ∈ L.map (wordArr n (ws.map (swapsArr n))) ↔ ∃ x ∈ genSub n ws, arrA n x = y :=
  enumOK_vals hv h y

theorem arr_gen {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true) {k : ℕ}
    (hk : k < ws.length) : (ws.map (swapsArr n)).getD k #[] = arrA n (gensFn n ws k) :=
  permArr_gensFn hk hv

theorem gen_mem_genSub {ws : List (List (ℕ × ℕ))} {k : ℕ} (hk : k < ws.length) :
    gensFn n ws k ∈ genSub n ws := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem gen_getD_mem {ws : List (List (ℕ × ℕ))} {k : ℕ} (hk : k < ws.length) :
    (ws.map (swapsArr n)).getD k #[] ∈ ws.map (swapsArr n) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  exact List.getElem_mem _

theorem elemAb_sound {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    (h : elemAbOK n (ws.map (swapsArr n)) = true) : ∀ x ∈ genSub n ws, x * x = 1 := by
  simp only [elemAbOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsq, hcomm⟩ := h
  have hgsq : ∀ k < ws.length, gensFn n ws k * gensFn n ws k = 1 := by
    intro k hk
    have h1 := hsq _ (gen_getD_mem hk)
    rw [arr_gen hv hk] at h1
    exact (sqB_arr (arrA n) arrA_mul arrA_one arrA_injective _).1 h1
  have hgcomm : ∀ k < ws.length, ∀ j < ws.length,
      gensFn n ws k * gensFn n ws j = gensFn n ws j * gensFn n ws k := by
    intro k hk j hj
    have h1 := hcomm _ (gen_getD_mem hk) _ (gen_getD_mem hj)
    rw [arr_gen hv hk, arr_gen hv hj] at h1
    exact (commB_arr (arrA n) arrA_mul arrA_injective _ _).1 h1
  have hel : CFSG.Open.IsElemAbelian 2 (genSub n ws) := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨j, hj, rfl⟩
      exact hgcomm k hk j hj
    · rintro _ ⟨k, hk, rfl⟩
      rw [pow_two]
      exact hgsq k hk
  intro x hx
  exact hel.mul_self_eq_one hx

theorem genSub_le_of_contains {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {PV : List (Array ℕ)} {P : Subgroup (alternatingGroup (Fin n))}
    (hPV : ∀ y, y ∈ PV ↔ ∃ x ∈ P, arrA n x = y)
    (h : (ws.map (swapsArr n)).all (fun x => PV.contains x) = true) : genSub n ws ≤ P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < ws.length := hk
  have h1 := List.all_eq_true.1 h _ (gen_getD_mem hk')
  obtain ⟨x, hxP, hx⟩ := (hPV _).1 (List.contains_iff_mem.1 h1)
  rw [arr_gen hv hk'] at hx
  show gensFn n ws k ∈ P
  rw [← arrA_injective hx]
  exact hxP

theorem order8_sound {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true) {w : List ℕ}
    (h : order8OK n (ws.map (swapsArr n)) w = true) :
    ∃ g ∈ genSub n ws, orderOf g = 8 := by
  simp only [order8OK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hlet, h4⟩, h8⟩ := h
  have hlet' : ∀ l ∈ w, l < ws.length := fun l hl => by simpa using hlet l hl
  set x := wordElt (gensFn n ws) w with hx
  have hxmem : x ∈ genSub n ws :=
    wordElt_mem (fun l hl => gen_mem_genSub hl) hlet'
  have harr : wordArr n (ws.map (swapsArr n)) w = arrA n x := wordArr_eq hv hlet'
  have e2 : pmul n (wordArr n (ws.map (swapsArr n)) w) (wordArr n (ws.map (swapsArr n)) w) =
      arrA n (x * x) := by rw [harr, arrA_mul]
  have e4 : pmul n (pmul n (wordArr n (ws.map (swapsArr n)) w)
      (wordArr n (ws.map (swapsArr n)) w)) (pmul n (wordArr n (ws.map (swapsArr n)) w)
      (wordArr n (ws.map (swapsArr n)) w)) = arrA n (x * x * (x * x)) := by
    rw [e2, arrA_mul]
  rw [e4, arrA_one] at h4
  rw [e4, arrA_mul, arrA_one] at h8
  have h4' : ¬ x ^ 2 ^ 2 = 1 := by
    have e : x ^ 2 ^ 2 = x * x * (x * x) := by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
    rw [e]
    exact fun h' => h4 (by rw [h'])
  have h8' : x ^ 2 ^ (2 + 1) = 1 := by
    have e : x ^ 2 ^ (2 + 1) = x * x * (x * x) * (x * x * (x * x)) := by
      rw [show (2 : ℕ) ^ (2 + 1) = 2 * 2 * 2 from rfl, pow_mul, pow_mul, pow_two, pow_two,
        pow_two]
    rw [e]
    exact arrA_injective h8
  exact ⟨x, hxmem, by simpa using orderOf_eq_prime_pow (p := 2) h4' h8'⟩

theorem normalizes_sound {cs es : List (List (ℕ × ℕ))} (hvc : ∀ w ∈ cs, swapsOK n w = true)
    (hve : ∀ w ∈ es, swapsOK n w = true) {EV : List (Array ℕ)}
    (hEV : ∀ y, y ∈ EV ↔ ∃ x ∈ genSub n es, arrA n x = y)
    (h : (cs.map (swapsArr n)).all (normOK n EV (es.map (swapsArr n))) = true) :
    genSub n cs ≤ normalizer (genSub n es : Set (alternatingGroup (Fin n))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < cs.length := hk
  set c := gensFn n cs k with hc
  have h1 := List.all_eq_true.1 h _ (gen_getD_mem hk')
  rw [arr_gen hvc hk'] at h1
  simp only [normOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  obtain ⟨h3, hu⟩ := h1
  have hc3 : c * (c * c) = 1 := by
    rw [arrA_mul, arrA_mul, arrA_one] at h3
    exact arrA_injective h3
  have hci : c⁻¹ = c * c := inv_eq_of_mul_eq_one_right hc3
  have hgen : ∀ j < es.length, c * gensFn n es j * c⁻¹ ∈ genSub n es := by
    intro j hj
    have h2 := hu _ (gen_getD_mem hj)
    rw [arr_gen hve hj, arrA_mul, arrA_mul, arrA_mul] at h2
    obtain ⟨y, hy, hyeq⟩ := (hEV _).1 (List.contains_iff_mem.1 h2)
    rw [hci, ← arrA_injective hyeq]
    exact hy
  have hstable : ∀ y ∈ genSub n es, c * y * c⁻¹ ∈ genSub n es := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨j, hj, rfl⟩ := ha
      exact hgen j hj
    | one => simpa using (genSub n es).one_mem
    | mul a b _ _ iha ihb =>
      have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      rw [e]
      exact (genSub n es).mul_mem iha ihb
    | inv a _ iha =>
      have e : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
      rw [e]
      exact (genSub n es).inv_mem iha
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hstable y hy, fun hy => ?_⟩
  have h2 := hstable _ (hstable _ hy)
  have e : c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = y := by
    calc c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * y * (c * (c * c))⁻¹ := by group
      _ = y := by rw [hc3]; group
  rw [e] at h2
  exact h2

theorem sylowData_of_checks {ps es cs : List (List (ℕ × ℕ))} {PW EW CW : List (List ℕ)}
    {g : List ℕ} (hvp : ∀ w ∈ ps, swapsOK n w = true) (hve : ∀ w ∈ es, swapsOK n w = true)
    (hvc : ∀ w ∈ cs, swapsOK n w = true)
    (hPe : enumOK n (ps.map (swapsArr n)) PW = true) (hPl : PW.length = 512)
    (hEe : enumOK n (es.map (swapsArr n)) EW = true) (hEl : EW.length = 64)
    (hCe : enumOK n (cs.map (swapsArr n)) CW = true) (hCl : CW.length = 9)
    (hab : elemAbOK n (es.map (swapsArr n)) = true)
    (hEP : (es.map (swapsArr n)).all
      (fun x => (PW.map (wordArr n (ps.map (swapsArr n)))).contains x) = true)
    (hord : order8OK n (ps.map (swapsArr n)) g = true)
    (hcnt : countOK n (PW.map (wordArr n (ps.map (swapsArr n))))
      (EW.map (wordArr n (es.map (swapsArr n)))) = true)
    (hnorm : (cs.map (swapsArr n)).all
      (normOK n (EW.map (wordArr n (es.map (swapsArr n)))) (es.map (swapsArr n))) = true) :
    SylowData (alternatingGroup (Fin n)) := by
  have hPV := genSub_vals hvp hPe
  have hEV := genSub_vals hve hEe
  have hEP' : genSub n es ≤ genSub n ps := genSub_le_of_contains hve hPV hEP
  refine ⟨genSub n ps, genSub n es, genSub n cs, ?_, hEP', elemAb_sound hve hab, ?_, ?_, ?_,
    normalizes_sound hvc hve hEV hnorm, ?_⟩
  · rw [genSub_card hvp hPe, hPl]; norm_num
  · rw [genSub_card hve hEe, hEl]; norm_num
  · obtain ⟨x, hx, hxo⟩ := order8_sound hvp hord
    exact ⟨x, hx, hxo⟩
  · exact countOK_sound (arrA n) arrA_injective arrA_mul arrA_one
      (enumOK_nodup hvp hPe) hPV hEV hcnt
  · rw [genSub_card hvc hCe, hCl]

theorem p12Check_sound (h : p12Check n () = true) : SylowData (alternatingGroup (Fin n)) := by
  simp only [p12Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsP, hsE⟩, hsC⟩, hPe⟩, hPl⟩, hEe⟩, hEl⟩, hCe⟩, hCl⟩, hab⟩, hEP⟩, hord⟩,
    hcnt⟩, hnorm⟩ := h
  exact sylowData_of_checks (List.all_eq_true.1 hsP) (List.all_eq_true.1 hsE)
    (List.all_eq_true.1 hsC) hPe hPl hEe hEl hCe hCl hab hEP hord hcnt hnorm

end CFSG.EvenSporadicStandard.M12Std.SolomonK.P12
