module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK1A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU CFSG.GH74.GLS.Bg.TwoGroups

theorem fzb_uMul_zero_left (y : ℕ) : uMul 0 y = y := by
  unfold uMul f4mul
  simp only [Nat.zero_div, Nat.zero_mod, Nat.zero_xor, Nat.xor_zero, Nat.zero_mul,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  omega

theorem fzb_uMul_assoc {x y z : ℕ} (hx : x < 64) (hy : y < 64) (hz : z < 64) :
    uMul (uMul x y) z = uMul x (uMul y z) := by
  obtain ⟨x', rfl⟩ := fzbEnc_surj hx
  obtain ⟨y', rfl⟩ := fzbEnc_surj hy
  obtain ⟨z', rfl⟩ := fzbEnc_surj hz
  rw [← fzbEnc_mul, ← fzbEnc_mul, ← fzbEnc_mul, ← fzbEnc_mul, mul_assoc]

private theorem isAutArr_spec {a : Array ℕ} (ha : isAutArr a = true) :
    a.size = 64 ∧ (∀ x < 64, a[x]! < 64) ∧ a[0]! = 0 ∧
      (∀ x < 64, ∀ y < x, a[x]! ≠ a[y]!) ∧
      (∀ i < 4, ∀ x < 64, a[uMul gensU[i]! x]! = uMul a[gensU[i]!]! a[x]!) := by
  simp only [isAutArr, Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ha
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · intro x hx
    have h := (fzb_allBelow_iff (fun x => decide (a[x]! < 64)) 64).mp h2 x hx
    simpa using h
  · intro x hx y hy
    have h := (fzb_allBelow_iff _ _).mp ((fzb_allBelow_iff _ _).mp h4 x hx) y hy
    simpa using h
  · intro i hi x hx
    have h := (fzb_allBelow_iff _ _).mp ((fzb_allBelow_iff _ _).mp h5 i hi) x hx
    simpa using h

theorem fzb_isAutArr_lt {a : Array ℕ} (ha : isAutArr a = true) {x : ℕ} (hx : x < 64) :
    a[x]! < 64 :=
  (isAutArr_spec ha).2.1 x hx

theorem fzb_isAutArr_zero {a : Array ℕ} (ha : isAutArr a = true) : a[0]! = 0 :=
  (isAutArr_spec ha).2.2.1

theorem fzb_isAutArr_inj {a : Array ℕ} (ha : isAutArr a = true) {x y : ℕ} (hx : x < 64)
    (hy : y < 64) (h : a[x]! = a[y]!) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exfalso
    have h1 := (isAutArr_spec ha).2.2.2.1 y hy x hlt
    exact h1 h.symm
  · exact heq
  · exfalso
    have h1 := (isAutArr_spec ha).2.2.2.1 x hx y hgt
    exact h1 h

theorem fzb_isAutArr_surj {a : Array ℕ} (ha : isAutArr a = true) {y : ℕ} (hy : y < 64) :
    ∃ x < 64, a[x]! = y := by
  let f : Fin 64 → Fin 64 := fun x => ⟨a[x]!, fzb_isAutArr_lt ha x.isLt⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have h := congrArg Fin.val hxy
    simp only [f] at h
    exact fzb_isAutArr_inj ha x.isLt y.isLt h
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
  exact ⟨x, x.isLt, by simpa [f] using congrArg Fin.val hx⟩

private theorem gensU_getElem!_lt (i : ℕ) : gensU[i]! < 64 := by
  rcases lt_or_ge i 4 with hi | hi
  · interval_cases i <;> decide
  · rw [getElem!_neg gensU i (by simp [gensU]; omega)]
    norm_num

private theorem fzb_evalW_lt (w : List ℕ) : evalW gensU w < 64 := by
  induction w with
  | nil => simp [evalW]
  | cons i w ih =>
    simp only [evalW]
    exact fzb_uMul_lt (gensU_getElem!_lt i) ih

private theorem evalW_words {words : Array (List ℕ)} (hw : wordsOK words = true) {i : ℕ}
    (hi : i < 64) : evalW gensU words[i]! = i := by
  have h : allBelow (fun z => evalW gensU words[z]! == z) 64 = true := by
    simpa [wordsOK] using hw
  have h2 := (fzb_allBelow_iff (fun z => evalW gensU words[z]! == z) 64).mp h i hi
  simpa using h2

private theorem isAutArr_gen {a : Array ℕ} (ha : isAutArr a = true) {i x : ℕ} (hi : i < 4)
    (hx : x < 64) : a[uMul gensU[i]! x]! = uMul a[gensU[i]!]! a[x]! :=
  (isAutArr_spec ha).2.2.2.2 i hi x hx

private theorem fzb_hom_word {a : Array ℕ} (ha : isAutArr a = true) :
    ∀ (w : List ℕ), ∀ y < 64,
      a[uMul (evalW gensU w) y]! = uMul a[evalW gensU w]! a[y]! := by
  intro w
  induction w with
  | nil =>
    intro y _
    simp only [evalW]
    rw [fzb_uMul_zero_left, fzb_isAutArr_zero ha, fzb_uMul_zero_left]
  | cons i w ih =>
    intro y hy
    simp only [evalW]
    rcases lt_or_ge i 4 with hi | hi
    · have hg_lt : gensU[i]! < 64 := gensU_getElem!_lt i
      have he_lt : evalW gensU w < 64 := fzb_evalW_lt w
      calc a[uMul (uMul gensU[i]! (evalW gensU w)) y]!
          = a[uMul gensU[i]! (uMul (evalW gensU w) y)]! := by
            rw [fzb_uMul_assoc hg_lt he_lt hy]
        _ = uMul a[gensU[i]!]! a[uMul (evalW gensU w) y]! :=
            isAutArr_gen ha hi (fzb_uMul_lt he_lt hy)
        _ = uMul a[gensU[i]!]! (uMul a[evalW gensU w]! a[y]!) := by rw [ih y hy]
        _ = uMul (uMul a[gensU[i]!]! a[evalW gensU w]!) a[y]! :=
            (fzb_uMul_assoc (fzb_isAutArr_lt ha hg_lt) (fzb_isAutArr_lt ha he_lt)
              (fzb_isAutArr_lt ha hy)).symm
        _ = uMul a[uMul gensU[i]! (evalW gensU w)]! a[y]! := by
            rw [isAutArr_gen ha hi he_lt]
    · have hg0 : gensU[i]! = 0 := by
        rw [getElem!_neg gensU i (by simp [gensU]; omega)]
        rfl
      rw [hg0, fzb_uMul_zero_left]
      exact ih y hy

theorem fzb_isAutArr_hom {words : Array (List ℕ)} (hw : wordsOK words = true) {a : Array ℕ}
    (ha : isAutArr a = true) {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    a[uMul x y]! = uMul a[x]! a[y]! := by
  have hwx : evalW gensU words[x]! = x := evalW_words hw hx
  calc a[uMul x y]! = a[uMul (evalW gensU words[x]!) y]! := by
        conv_lhs => rw [← hwx]
    _ = uMul a[evalW gensU words[x]!]! a[y]! := fzb_hom_word ha (words[x]!) y hy
    _ = uMul a[x]! a[y]! := by rw [hwx]

private theorem fzb_genImg {a : Array ℕ} (ha : isAutArr a = true) (i : ℕ) :
    #[a[16]!, a[32]!, a[4]!, a[8]!][i]! = a[gensU[i]!]! := by
  rcases lt_or_ge i 4 with hi | hi
  · have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl <;> rfl
  · rw [getElem!_neg #[a[16]!, a[32]!, a[4]!, a[8]!] i (by simp; omega),
      getElem!_neg gensU i (by simp [gensU]; omega)]
    exact (fzb_isAutArr_zero ha).symm

private theorem fzb_evalW_map {words : Array (List ℕ)} (hw : wordsOK words = true) {a : Array ℕ}
    (ha : isAutArr a = true) (w : List ℕ) :
    evalW #[a[16]!, a[32]!, a[4]!, a[8]!] w = a[evalW gensU w]! := by
  induction w with
  | nil => simp [evalW, fzb_isAutArr_zero ha]
  | cons i w ih =>
    simp only [evalW]
    rw [fzb_genImg ha i, ih,
      ← fzb_isAutArr_hom hw ha (gensU_getElem!_lt i) (fzb_evalW_lt w)]

private theorem extArr_getElem! (words : Array (List ℕ)) (y : Array ℕ) {x : ℕ} (hx : x < 64) :
    (extArr words y)[x]! = evalW y words[x]! := by
  have hsize : x < ((Array.range 64).map (fun z => evalW y words[z]!)).size := by
    simpa [Array.size_map, Array.size_range] using hx
  rw [show extArr words y = (Array.range 64).map (fun z => evalW y words[z]!) from rfl,
    getElem!_pos _ x hsize, Array.getElem_map, Array.getElem_range]

theorem fzb_extArr_eq {words : Array (List ℕ)} (hw : wordsOK words = true) {a : Array ℕ}
    (ha : isAutArr a = true) : extArr words #[a[16]!, a[32]!, a[4]!, a[8]!] = a := by
  apply Array.ext
  · simp [extArr, Array.size_map, Array.size_range, (isAutArr_spec ha).1]
  · intro i hi hi'
    rw [← getElem!_pos (extArr words #[a[16]!, a[32]!, a[4]!, a[8]!]) i hi, ← getElem!_pos a i hi']
    have hi64 : i < 64 := by simpa [(isAutArr_spec ha).1] using hi'
    rw [extArr_getElem! words _ hi64, fzb_evalW_map hw ha (words[i]!), evalW_words hw hi64]

@[expose] noncomputable def FzbCoding.twist {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)
    {words : Array (List ℕ)} (hw : wordsOK words = true) (g : Array ℕ)
    (hg : isAutArr g = true) : FzbCoding P := by
  classical
  let pre : ℕ → ℕ := fun x => if h : ∃ y < 64, g[y]! = x then h.choose else 0
  have pre_lt : ∀ x < 64, pre x < 64 := by
    intro x hx
    have h : ∃ y < 64, g[y]! = x := fzb_isAutArr_surj hg hx
    simp only [pre, dif_pos h]
    exact (Classical.choose_spec h).1
  have pre_spec : ∀ x < 64, g[pre x]! = x := by
    intro x hx
    have h : ∃ y < 64, g[y]! = x := fzb_isAutArr_surj hg hx
    simp only [pre, dif_pos h]
    exact (Classical.choose_spec h).2
  refine ⟨fun p => g[C.enc p]!, fun x => C.dec (pre x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact fzb_isAutArr_lt hg (C.enc_lt p hp)
  · intro x hx
    exact C.dec_mem (pre x) (pre_lt x hx)
  · intro x hx
    rw [C.enc_dec (pre x) (pre_lt x hx)]
    exact pre_spec x hx
  · intro p hp
    have hx : g[C.enc p]! < 64 := fzb_isAutArr_lt hg (C.enc_lt p hp)
    have hpre : pre (g[C.enc p]!) = C.enc p :=
      fzb_isAutArr_inj hg (pre_lt _ hx) (C.enc_lt p hp) (pre_spec _ hx)
    rw [hpre]
    exact C.dec_enc p hp
  · rw [C.enc_one]
    exact fzb_isAutArr_zero hg
  · intro p hp p' hp'
    rw [C.enc_mul p hp p' hp']
    exact fzb_isAutArr_hom hw hg (C.enc_lt p hp) (C.enc_lt p' hp')

theorem FzbCoding.twist_enc {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)
    {words : Array (List ℕ)} (hw : wordsOK words = true) (g : Array ℕ)
    (hg : isAutArr g = true) (p : G) : (C.twist hw g hg).enc p = g[C.enc p]! := rfl

end CFSG.OddStandard.SmallF3.FritzII
