module

public import CFSG.Certificates.Kernel.GMS78RuCzJEval
public import CFSG.Certificates.Kernel.GMS78RuGenCzJ

public section

namespace CFSG.KC.GMS.CzJ

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS
open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

variable {M : Array (Array Nat)} {inv : Array Nat} {c : ArrCert} {RW : Nat → Nat}
  {PAR LAB INV : Nat}

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
private theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
private theorem div_eq' (a b : Nat) : Nat.div a b = a / b := rfl
private theorem mod_eq' (a b : Nat) : Nat.mod a b = a % b := rfl
private theorem add_eq' (a b : Nat) : Nat.add a b = a + b := rfl
private theorem mul_eq' (a b : Nat) : Nat.mul a b = a * b := rfl

private theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (beq_iff.trans beq_iff_eq.symm)

private theorem listRec_map {α β : Type} (f : α → β) (l : List α) :
    List.rec (motive := fun _ => List β) [] (fun x _ ih => List.cons (f x) ih) l = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (f x)) ih

private theorem getD_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem getD_lt {l : List Nat} (h : ∀ x ∈ l, x < 2048) (i : Nat) : l.getD i 0 < 2048 := by
  by_cases hi : i < l.length
  · rw [getD_of_lt hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

private theorem mem6_lt {a b c d e f : Nat} (ha : a < 2048) (hb : b < 2048) (hc : c < 2048)
    (hd : d < 2048) (he : e < 2048) (hf : f < 2048) : ∀ x ∈ [a, b, c, d, e, f], x < 2048 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem filter_lt {p : Nat → Bool} : ∀ x ∈ (List.range 2048).filter p, x < 2048 :=
  fun _ hx => List.mem_range.1 (List.mem_filter.1 hx).1

private theorem evs_lt (I : TabI M inv c RW PAR LAB INV) (gi : List Nat) (W : List (List Nat)) :
    ∀ x ∈ W.map (evW M inv gi), x < 2048 := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact evW_lt I gi w

private theorem hom_fget (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) (W : List (List Nat)) {K : Nat}
    (hK : Nat.beq K (czHom RW PAR LAB (czEvs RW INV (czPack gi) W)) = true) :
    ∀ a < 2048, fget K a 11 = ix (homTab 2048 M c (W.map (evW M inv gi))) a := by
  intro a ha
  rw [beq_iff.1 hK, czEvs_evW I hgi, ix_homTab I (evs_lt I gi W) ha]

private theorem fix_eq {KQ : Nat} {kq : Array Nat} (hKQ : ∀ a < 2048, fget KQ a 11 = ix kq a)
    {FIX : List Nat} (h : czListEq FIX (czFilter fun a => Nat.beq (fget KQ a 11) a) = true) :
    FIX = (List.range 2048).filter fun a => ix kq a == a := by
  rw [czListEq_iff.1 h, czFilter_eq]
  apply List.filter_congr
  intro a ha
  rw [hKQ a (List.mem_range.1 ha), beq_eq]

private theorem d_eq (I : TabI M inv c RW PAR LAB INV) {KQ : Nat} {kq : Array Nat}
    (hKQ : ∀ a < 2048, fget KQ a 11 = ix kq a) (hkq : ∀ a, ix kq a < 2048)
    (T : Nat → Nat → List Nat) (hT : ∀ a b, a < 2048 → b < 2048 → ∀ x ∈ T a b, x < 2048)
    (W : List (List Nat)) (n : Nat) {D : List Nat}
    (h : czListEq D (czFilter fun a => Nat.beq (fget KQ (fget KQ a 11) 11)
      (czEv RW INV (czPack (T a (fget KQ a 11))) (neGet [] W n))) = true) :
    D = (List.range 2048).filter fun a => ix kq (ix kq a) == evW M inv (T a (ix kq a)) (W.getD n []) := by
  rw [czListEq_iff.1 h, czFilter_eq]
  apply List.filter_congr
  intro a ha
  have ha' := List.mem_range.1 ha
  rw [hKQ a ha', hKQ _ (hkq a), neGet_eq, ← evW_eq I (hT _ _ ha' (hkq a)), beq_eq]

private theorem ct_eq (I : TabI M inv c RW PAR LAB INV) {gi : List Nat} (hgi : ∀ x ∈ gi, x < 2048)
    {CT : List Nat} (h : czListEq CT (czConjTs RW INV gi) = true) :
    CT = (List.range 2048).map fun d => czPack (gi.map fun g => mt M (mt M (ix inv d) g) d) := by
  rw [czListEq_iff.1 h, czConjTs_eq]
  apply List.map_congr_left
  intro d hd
  have hd' := List.mem_range.1 hd
  unfold czConjT
  rw [listRec_map (fun g => czMt RW (czMt RW (fget INV d 11) g) d)]
  congr 1
  apply List.map_congr_left
  intro g hg
  simp only [czMt]
  rw [← I.inv_eq d hd', ← I.mt_eq _ (I.inv_lt d) g (hgi g hg), ← I.mt_eq _ (I.mt_lt _ _) d hd']

private theorem sols_eq (I : TabI M inv c RW PAR LAB INV) {gi : List Nat} (hgi : ∀ x ∈ gi, x < 2048)
    {sols : List (List (List Nat))} {SOLS : List Nat}
    (h : czListEq SOLS (List.rec (motive := fun _ => List Nat) []
      (fun s _ ih => List.cons (czEvs RW INV (czPack gi) s) ih) sols) = true) :
    SOLS = sols.map fun s => czPack (s.map (evW M inv gi)) := by
  rw [czListEq_iff.1 h, listRec_map (czEvs RW INV (czPack gi))]
  apply List.map_congr_left
  intro s _
  exact czEvs_evW I hgi s

private theorem mem_eq (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    {sols : List (List (List Nat))} (hsl : ∀ s ∈ sols, s.length = 6) {SOLS : List Nat}
    (hSOLS : SOLS = sols.map fun s => czPack (s.map (evW M inv gi))) {t : List Nat}
    (hlen : t.length = 6) (ht : ∀ x ∈ t, x < 2048) :
    czAny (Nat.beq (czPack t)) SOLS = (sols.map fun s => s.map (evW M inv gi)).contains t := by
  rw [czAny_eq, hSOLS, Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨_, hx, h⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    refine List.mem_map.2 ⟨s, hs, (czPack_inj (evs_lt I gi s) ht ?_ (beq_iff.1 h).symm)⟩
    rw [List.length_map, hsl s hs, hlen]
  · intro hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    exact ⟨_, List.mem_map.2 ⟨s, hs, rfl⟩, Nat.beq_refl _⟩

private theorem cube_eq (I : TabI M inv c RW PAR LAB INV) {gi : List Nat}
    (hgi : ∀ x ∈ gi, x < 2048) {KW : Nat} {kw : Array Nat}
    (hKW : ∀ a < 2048, fget KW a 11 = ix kw a) (hkw : ∀ a, ix kw a < 2048) {CT : List Nat}
    (hCT : CT = (List.range 2048).map fun d => czPack (gi.map fun g => mt M (mt M (ix inv d) g) d))
    {t : List Nat} (ht : ∀ x ∈ t, x < 2048) :
    czCube RW PAR LAB gi KW CT (czPack t) = cubeInner 2048 M c gi (conjTuples 2048 M inv gi) kw t := by
  have hphi : ∀ a < 2048, czHomVal RW PAR LAB (czPack t) (fget KW a 11) =
      homVal M c t 2048 (ix kw a) := by
    intro a ha
    rw [hKW a ha, homVal_eq I ht (hkw a)]
  have hlt : ∀ a, homVal M c t 2048 (ix kw a) < 2048 := fun a => homVal_lt I t _ _
  simp only [czCube, cubeInner]
  rw [listRec_map]
  rw [List.map_congr_left (g := fun g => homVal M c t 2048 (ix kw (homVal M c t 2048
    (ix kw (homVal M c t 2048 (ix kw g)))))) (fun g hg => by
      rw [hphi g (hgi g hg), hphi _ (hlt g), hphi _ (hlt _)])]
  rw [czAny_eq, hCT, Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem, conjTuples]
  have hL : ∀ x ∈ gi.map fun g => homVal M c t 2048 (ix kw (homVal M c t 2048
      (ix kw (homVal M c t 2048 (ix kw g))))), x < 2048 := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact hlt _
  have hC : ∀ d, ∀ x ∈ gi.map fun g => mt M (mt M (ix inv d) g) d, x < 2048 := by
    intro d x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact I.mt_lt _ _
  constructor
  · rintro ⟨_, hx, h⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨d, hd, (czPack_inj hL (hC d) (by simp) (beq_iff.1 h)).symm⟩
  · intro hx
    obtain ⟨d, hd, e⟩ := List.mem_map.1 hx
    exact ⟨_, List.mem_map.2 ⟨d, hd, rfl⟩, beq_iff.2 (by rw [e])⟩

private theorem block (I : TabI M inv c RW PAR LAB INV) {gi : List Nat} {KQ KW : Nat}
    {FIX D3 D5 CT SOLS : List Nat} {rels1 rels3 rels5 : List (List Nat)} {kq : Array Nat}
    (hKQ : ∀ a < 2048, fget KQ a 11 = ix kq a) (hkq : ∀ a, ix kq a < 2048)
    (hF : ∀ x ∈ FIX, x < 2048) (hD3 : ∀ x ∈ D3, x < 2048) (hD5 : ∀ x ∈ D5, x < 2048)
    {cube mem : List Nat → Bool}
    (hcube : ∀ t : List Nat, t.length = 6 → (∀ x ∈ t, x < 2048) →
      czCube RW PAR LAB gi KW CT (czPack t) = cube t)
    (hmem : ∀ t : List Nat, t.length = 6 → (∀ x ∈ t, x < 2048) →
      czAny (Nat.beq (czPack t)) SOLS = mem t)
    {j : Nat} (h : kSearch RW PAR LAB INV gi rels1 rels3 rels5 KQ KW FIX D3 D5 CT SOLS j = true) :
    ∀ a0 a1, a0 = FIX.getD (j / 64) 0 → a1 = FIX.getD (j / 8 % 8) 0 →
      relsHold M inv rels1 [a0, a1, 0, 0, 0, 0] = true → ∀ t < 8, ∀ a2,
      a2 = D3.getD (8 * (j % 8) + t) 0 →
      relsHold M inv rels3 [a0, a1, a2, ix kq a2, 0, 0] = true → ∀ a4 ∈ D5,
      (!(relsHold M inv rels5 [a0, a1, a2, ix kq a2, a4, ix kq a4] &&
        cube [a0, a1, a2, ix kq a2, a4, ix kq a4]) ||
        mem [a0, a1, a2, ix kq a2, a4, ix kq a4]) = true := by
  intro a0 a1 e0 e1 h1 t ht a2 e2 h3 a4 ha4
  have l0 : a0 < 2048 := e0 ▸ getD_lt hF _
  have l1 : a1 < 2048 := e1 ▸ getD_lt hF _
  have l2 : a2 < 2048 := e2 ▸ getD_lt hD3 _
  have l4 : a4 < 2048 := hD5 a4 ha4
  have z : (0 : Nat) < 2048 := by decide
  unfold kSearch at h
  simp only [neGet_eq, div_eq', mod_eq', add_eq', mul_eq'] at h
  rw [← e0, ← e1, orB_iff, notB_iff] at h
  rw [relsHold_eq I (mem6_lt l0 l1 z z z z)] at h1
  rcases h with h | h
  · rw [h1] at h; cases h
  have h := allN_iff'.1 h t ht
  rw [← e2, hKQ a2 l2, orB_iff, notB_iff] at h
  rw [relsHold_eq I (mem6_lt l0 l1 l2 (hkq a2) z z)] at h3
  rcases h with h | h
  · rw [h3] at h; cases h
  have h := neAllL_iff.1 h a4 ha4
  have l6 := mem6_lt l0 l1 l2 (hkq a2) l4 (hkq a4)
  rw [hKQ a4 l4, ← relsHold_eq I l6, hcube _ rfl l6, hmem _ rfl l6, orB_eq, notB_eq, andB_eq] at h
  exact h

private theorem search_core {FIX D3 D5 : List Nat} {R1 : Nat → Nat → Bool}
    {R3 : Nat → Nat → Nat → Bool} {P : Nat → Nat → Nat → Nat → Bool}
    (hF : FIX.length = 8) (hD : D3.length = 64)
    (h : ∀ j < 512, ∀ a0 a1, a0 = FIX.getD (j / 64) 0 → a1 = FIX.getD (j / 8 % 8) 0 →
      R1 a0 a1 = true → ∀ t < 8, ∀ a2, a2 = D3.getD (8 * (j % 8) + t) 0 →
      R3 a0 a1 a2 = true → ∀ a4 ∈ D5, P a0 a1 a2 a4 = true) :
    (FIX.all fun a0 => FIX.all fun a1 => !R1 a0 a1 ||
      D3.all fun a2 => !R3 a0 a1 a2 || D5.all fun a4 => P a0 a1 a2 a4) = true := by
  rw [List.all_eq_true]
  intro a0 ha0
  rw [List.all_eq_true]
  intro a1 ha1
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem ha0
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem ha1
  rw [Bool.or_eq_true]
  by_cases h1 : R1 FIX[p] FIX[q] = true
  · right
    rw [List.all_eq_true]
    intro a2 ha2
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem ha2
    have e1 : (64 * p + 8 * q + r / 8) / 64 = p := by omega
    have e2 : (64 * p + 8 * q + r / 8) / 8 % 8 = q := by omega
    have e3 : 8 * ((64 * p + 8 * q + r / 8) % 8) + r % 8 = r := by omega
    have hb := h (64 * p + 8 * q + r / 8) (by omega) FIX[p] FIX[q]
      (by rw [e1, getD_of_lt hp]) (by rw [e2, getD_of_lt hq]) h1 (r % 8) (by omega) D3[r]
      (by rw [e3, getD_of_lt hr])
    rw [Bool.or_eq_true]
    by_cases h3 : R3 FIX[p] FIX[q] D3[r] = true
    · right
      rw [List.all_eq_true]
      exact hb h3
    · left
      simpa using h3
  · left
    simpa using h1

theorem czJ_rigid (I : TabI M inv c RW PAR LAB INV) {LK : Nat → Nat} {gi : List Nat}
    (hgi : gi = (List.range 6).map fun k => fget (LK k) 0 11)
    {KQ KW : Nat} {FIX D3 D5 CT SOLS : List Nat}
    {relsJ rels1 rels3 rels5 Wq Ww : List (List Nat)} {sols : List (List (List Nat))}
    (hr1 : rels1 = relsJ.filter fun r => r.all fun l => l < 4)
    (hr3 : rels3 = relsJ.filter fun r => (r.all fun l => l < 8) && !(r.all fun l => l < 4))
    (hr5 : rels5 = relsJ.filter fun r => !(r.all fun l => l < 8))
    (hPrep : kPrep RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) Wq Ww sols KQ KW
      FIX D3 D5 CT SOLS = true)
    (hS : ∀ j < 512, kSearch RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) rels1
      rels3 rels5 KQ KW FIX D3 D5 CT SOLS j = true) :
    Gen.rigidSearchG relsJ Wq Ww sols 2048 M inv c gi = true := by
  subst hr1 hr3 hr5
  rw [← hgi] at hPrep hS
  have hgi' : ∀ x ∈ gi, x < 2048 := by
    rw [hgi]
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact fget11_lt _ _
  unfold kPrep at hPrep
  simp only [andB_iff] at hPrep
  obtain ⟨hKQ, hKW, hFIX, hD3, hD5, hCT, hSOLS, hk0, hk1, hk2, hk4, hsl, -, hF8, hD64⟩ := hPrep
  simp only [Gen.rigidSearchG, Bool.and_eq_true, beq_iff_eq]
  set kq := homTab 2048 M c (Wq.map (evW M inv gi)) with hkq_def
  set kw := homTab 2048 M c (Ww.map (evW M inv gi)) with hkw_def
  have hKQ' : ∀ a < 2048, fget KQ a 11 = ix kq a := hom_fget I hgi' Wq hKQ
  have hKW' : ∀ a < 2048, fget KW a 11 = ix kw a := hom_fget I hgi' Ww hKW
  have hkq : ∀ a, ix kq a < 2048 := ix_homTab_lt I _
  have hkw : ∀ a, ix kw a < 2048 := ix_homTab_lt I _
  have hFIX' : FIX = (List.range 2048).filter fun a => ix kq a == a := fix_eq hKQ' hFIX
  have hD3' : D3 = (List.range 2048).filter fun a =>
      ix kq (ix kq a) == evW M inv [0, 0, a, ix kq a, 0, 0] (Wq.getD 3 []) :=
    d_eq I hKQ' hkq (fun a b => [0, 0, a, b, 0, 0])
      (fun a b ha hb => mem6_lt (by decide) (by decide) ha hb (by decide) (by decide)) Wq 3 hD3
  have hD5' : D5 = (List.range 2048).filter fun a =>
      ix kq (ix kq a) == evW M inv [0, 0, 0, 0, a, ix kq a] (Wq.getD 5 []) :=
    d_eq I hKQ' hkq (fun a b => [0, 0, 0, 0, a, b])
      (fun a b ha hb => mem6_lt (by decide) (by decide) (by decide) (by decide) ha hb) Wq 5 hD5
  have hCT' := ct_eq I hgi' hCT
  have hSOLS' := sols_eq I hgi' hSOLS
  have hsl' : ∀ s ∈ sols, s.length = 6 := fun s hs => by
    have := neAllL_iff.1 hsl s hs
    rwa [beq_iff, neLen_eq] at this
  have hKQg : ∀ i, fget KQ (gi.getD i 0) 11 = ix kq (gi.getD i 0) :=
    fun i => hKQ' _ (getD_lt hgi' i)
  simp only [czPack_fget hgi', hKQg, beq_iff] at hk0 hk1 hk2 hk4
  refine ⟨⟨⟨⟨hk0, hk1⟩, hk2⟩, hk4⟩, ?_⟩
  rw [← hFIX', ← hD3', ← hD5']
  rw [beq_iff, neLen_eq] at hF8 hD64
  have hFl : ∀ x ∈ FIX, x < 2048 := hFIX' ▸ filter_lt
  have hD3l : ∀ x ∈ D3, x < 2048 := hD3' ▸ filter_lt
  have hD5l : ∀ x ∈ D5, x < 2048 := hD5' ▸ filter_lt
  refine search_core hF8 hD64 fun j hj => ?_
  exact block I hKQ' hkq hFl hD3l hD5l (fun t _ ht => cube_eq I hgi' hKW' hkw hCT' ht)
    (fun t hl ht => mem_eq I hsl' hSOLS' hl ht) (hS j hj)

end CFSG.KC.GMS.CzJ

end
