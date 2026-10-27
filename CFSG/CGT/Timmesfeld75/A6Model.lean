module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.Timmesfeld75.A6Model

abbrev P6 : Type := Equiv.Perm (Fin 6)

private abbrev Wd : Type := List (ℕ × ℕ)

private abbrev L6 : Type := List ℕ

private def sw (i j : ℕ) : P6 := Equiv.swap (Fin.ofNat 6 i) (Fin.ofNat 6 j)

private def prodL : Wd → P6
  | [] => 1
  | (i, j) :: ws => sw i j * prodL ws

private def swN (i j x : ℕ) : ℕ := if x = i % 6 then j % 6 else if x = j % 6 then i % 6 else x

private def ev (w : Wd) (x : ℕ) : ℕ := w.foldr (fun l x => swN l.1 l.2 x) x

private def encW (w : Wd) : L6 := [ev w 0, ev w 1, ev w 2, ev w 3, ev w 4, ev w 5]

private def enc (σ : P6) : L6 := [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val, (σ 5).val]

private def codeL (p : L6) : ℕ := p.foldr (fun x acc => x + 6 * acc) 0

private def code (σ : P6) : ℕ := codeL (enc σ)

private theorem enc_getD (σ : P6) (k : Fin 6) : (enc σ).getD k.val 0 = (σ k).val := by
  fin_cases k <;> rfl

private theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  ext k
  have e1 := enc_getD σ k
  have e2 := enc_getD τ k
  rw [h] at e1
  have := e1.symm.trans e2
  exact this.symm ▸ rfl

private theorem sw_val (i j : ℕ) (k : Fin 6) : (sw i j k).val = swN i j k.val := by
  unfold sw swN
  rw [Equiv.swap_apply_def]
  simp only [Fin.ext_iff, Fin.ofNat]
  split_ifs <;> simp_all

private theorem prodL_val (w : Wd) (k : Fin 6) : (prodL w k).val = ev w k.val := by
  induction w with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨i, j⟩ := p
    simp only [prodL, Equiv.Perm.coe_mul, Function.comp_apply, sw_val, ih, ev, List.foldr_cons]

private theorem enc_prodL (w : Wd) : enc (prodL w) = encW w := by
  simp only [enc, encW, prodL_val]
  rfl

private theorem code_injective : Function.Injective code := by
  intro σ τ h
  apply enc_injective
  have hσ : ∀ k : Fin 6, (σ k).val < 6 := fun k => (σ k).isLt
  have hτ : ∀ k : Fin 6, (τ k).val < 6 := fun k => (τ k).isLt
  simp only [code, codeL, enc, List.foldr_cons, List.foldr_nil] at h ⊢
  have a0 := hσ 0; have a1 := hσ 1; have a2 := hσ 2; have a3 := hσ 3; have a4 := hσ 4
  have a5 := hσ 5
  have b0 := hτ 0; have b1 := hτ 1; have b2 := hτ 2; have b3 := hτ 3; have b4 := hτ 4
  have b5 := hτ 5
  have : (σ 0).val = (τ 0).val ∧ (σ 1).val = (τ 1).val ∧ (σ 2).val = (τ 2).val ∧
      (σ 3).val = (τ 3).val ∧ (σ 4).val = (τ 4).val ∧ (σ 5).val = (τ 5).val := by omega
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := this
  rw [h0, h1, h2, h3, h4, h5]

private theorem prodL_append (u v : Wd) : prodL (u ++ v) = prodL u * prodL v := by
  induction u with
  | nil => simp [prodL]
  | cons p us ih =>
    obtain ⟨i, j⟩ := p
    simp [prodL, ih, mul_assoc]

private def ValidW (w : Wd) : Prop := ∀ p ∈ w, p.1 < 6 ∧ p.2 < 6 ∧ p.1 ≠ p.2

private theorem sign_sw (i j : ℕ) (h : i < 6 ∧ j < 6 ∧ i ≠ j) :
    Equiv.Perm.sign (sw i j) = -1 := by
  unfold sw
  apply Equiv.Perm.sign_swap
  intro hh
  have := congrArg Fin.val hh
  simp only [Fin.ofNat, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2.1] at this
  exact h.2.2 this

private theorem sign_prodL (w : Wd) (hw : ValidW w) :
    Equiv.Perm.sign (prodL w) = (-1) ^ w.length := by
  induction w with
  | nil => simp [prodL]
  | cons p ws ih =>
    obtain ⟨i, j⟩ := p
    have h1 : ValidW ws := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have h2 := hw (i, j) (List.mem_cons_self ..)
    simp only [prodL, map_mul, sign_sw i j h2, ih h1, List.length_cons, pow_succ]
    exact mul_comm _ _

private def lehmer : ℕ → List Wd
  | 0 => [[]]
  | m + 1 => (lehmer m).flatMap fun w =>
      (List.range (m + 2)).map fun j => if j = m + 1 then w else w ++ [(m + 1, j)]

private def evW : List Wd := (lehmer 5).filter fun w => w.length % 2 = 0

private theorem lehmer_len : (lehmer 5).length = 720 := by decide +kernel

private def hasDupBits : List ℕ → ℕ → Bool
  | [], _ => false
  | x :: xs, seen => seen.testBit x || hasDupBits xs (seen ||| (1 <<< x))

private theorem nodup_of_hasDupBits {l : List ℕ} {seen : ℕ} (h : hasDupBits l seen = false) :
    l.Nodup ∧ ∀ x ∈ l, seen.testBit x = false := by
  induction l generalizing seen with
  | nil => exact ⟨List.nodup_nil, by simp⟩
  | cons x xs ih =>
    simp only [hasDupBits, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := ih h.2
    have hx : x ∉ xs := by
      intro hm
      have := h2 x hm
      simp [Nat.testBit_or, Nat.one_shiftLeft] at this
    refine ⟨List.nodup_cons.2 ⟨hx, h1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · have := h2 y hy
      simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
      exact this.1

private theorem lehmer_nodup : ((lehmer 5).map fun w => codeL (encW w)).Nodup :=
  (nodup_of_hasDupBits (seen := 0) (by decide +kernel)).1

private def validB (w : Wd) : Bool := w.all fun p => p.1 < 6 && p.2 < 6 && p.1 != p.2

private theorem validB_sound {w : Wd} (h : validB w = true) : ValidW w := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simpa [Bool.and_eq_true, bne_iff_ne, and_assoc] using this

private theorem lehmer_valid : ∀ w ∈ lehmer 5, validB w = true := by decide +kernel

private theorem lehmer_surj (σ : P6) : ∃ w ∈ lehmer 5, prodL w = σ := by
  have hnd := lehmer_nodup
  have hinj : Set.InjOn prodL {w | w ∈ lehmer 5} := by
    intro u hu v hv huv
    have h1 : codeL (encW u) = codeL (encW v) := by
      rw [← enc_prodL, ← enc_prodL, huv]
    exact List.inj_on_of_nodup_map hnd hu hv h1
  have hnd' : (lehmer 5).Nodup := List.Nodup.of_map _ hnd
  have hcard : ((lehmer 5).toFinset.image prodL).card = Fintype.card P6 := by
    rw [Finset.card_image_of_injOn (by simpa using hinj), List.toFinset_card_of_nodup hnd',
      lehmer_len, Fintype.card_perm, Fintype.card_fin]
    rfl
  have huniv := Finset.eq_univ_of_card _ hcard
  have hmem : σ ∈ (lehmer 5).toFinset.image prodL := by rw [huniv]; exact Finset.mem_univ σ
  obtain ⟨w, hw, hws⟩ := Finset.mem_image.1 hmem
  exact ⟨w, List.mem_toFinset.1 hw, hws⟩

private theorem exists_even_word (σ : P6) (h : Equiv.Perm.sign σ = 1) :
    ∃ w ∈ evW, prodL w = σ := by
  obtain ⟨w, hw, rfl⟩ := lehmer_surj σ
  have hs := sign_prodL w (validB_sound (lehmer_valid w hw))
  rw [h] at hs
  have hev : Even w.length := by
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    exact (neg_one_pow_eq_one_iff_even hne).1 hs.symm
  exact ⟨w, List.mem_filter.2 ⟨hw, by simpa [Nat.even_iff] using hev⟩, rfl⟩

@[expose] def cj (c s : P6) : P6 := c * s * c⁻¹

private theorem cj_mul (c d s : P6) : cj (c * d) s = cj c (cj d s) := by
  simp [cj, mul_assoc]

private theorem cj_inj (c : P6) {s t : P6} (h : cj c s = cj c t) : s = t := by
  simpa [cj] using h

private theorem cj_cj_inv (c s : P6) : cj c (cj c⁻¹ s) = s := by
  rw [← cj_mul]; simp [cj]

private theorem cj_inv_cj (c s : P6) : cj c⁻¹ (cj c s) = s := by
  rw [← cj_mul]; simp [cj]

private theorem cj_cj_mul (c s t : P6) : cj c (s * t) = cj c s * cj c t := by
  simp [cj, mul_assoc]

private theorem cj_cj_one (c : P6) : cj c 1 = 1 := by simp [cj]

@[expose] def Nrm (L : List P6) (σ : P6) : Prop := σ ∈ Subgroup.normalizer {s | s ∈ L}

private theorem nrm_iff (L : List P6) (σ : P6) : Nrm L σ ↔ ∀ s, s ∈ L ↔ cj σ s ∈ L :=
  Subgroup.mem_set_normalizer_iff

private def keyP (L : List P6) (σ : P6) : List ℕ := L.map fun s => code (cj σ s)

private def SetEq (l₁ l₂ : List ℕ) : Prop := ∀ c, c ∈ l₁ ↔ c ∈ l₂

private theorem mem_keyP {L : List P6} {σ : P6} {c : ℕ} :
    c ∈ keyP L σ ↔ ∃ s ∈ L, code (cj σ s) = c := by
  simp [keyP]

private theorem keyEq_iff (L : List P6) (σ₁ σ₂ : P6) :
    SetEq (keyP L σ₁) (keyP L σ₂) ↔ Nrm L (σ₁⁻¹ * σ₂) := by
  rw [nrm_iff]
  have hcj : ∀ s, cj σ₂ s = cj σ₁ (cj (σ₁⁻¹ * σ₂) s) := by
    intro s; rw [← cj_mul]; simp
  constructor
  · intro h
    have hA : ∀ t ∈ L, ∃ s ∈ L, cj (σ₁⁻¹ * σ₂) s = t := by
      intro t ht
      have : code (cj σ₁ t) ∈ keyP L σ₁ := mem_keyP.2 ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hsc⟩ := mem_keyP.1 ((h _).1 this)
      refine ⟨s, hs, ?_⟩
      have h1 : cj σ₂ s = cj σ₁ t := code_injective hsc
      rw [hcj] at h1
      exact cj_inj σ₁ h1
    have hB : ∀ s ∈ L, cj (σ₁⁻¹ * σ₂) s ∈ L := by
      intro s hs
      have : code (cj σ₂ s) ∈ keyP L σ₂ := mem_keyP.2 ⟨s, hs, rfl⟩
      obtain ⟨t, ht, htc⟩ := mem_keyP.1 ((h _).2 this)
      have h1 : cj σ₁ t = cj σ₂ s := code_injective htc
      rw [hcj] at h1
      have := cj_inj σ₁ h1
      rw [← this]; exact ht
    intro s
    refine ⟨hB s, fun hs => ?_⟩
    obtain ⟨s', hs', hss'⟩ := hA _ hs
    have := cj_inj _ hss'
    rw [← this]; exact hs'
  · intro h c
    constructor
    · intro hc
      obtain ⟨s, hs, hsc⟩ := mem_keyP.1 hc
      refine mem_keyP.2 ⟨cj (σ₁⁻¹ * σ₂)⁻¹ s, ?_, ?_⟩
      · have := (h (cj (σ₁⁻¹ * σ₂)⁻¹ s)).2
        rw [cj_cj_inv] at this
        exact this hs
      · rw [hcj, cj_cj_inv]; exact hsc
    · intro hc
      obtain ⟨s, hs, hsc⟩ := mem_keyP.1 hc
      refine mem_keyP.2 ⟨cj (σ₁⁻¹ * σ₂) s, (h s).1 hs, ?_⟩
      rw [← hcj]; exact hsc

private theorem mem_map_cj {L : List P6} {c u : P6} : u ∈ L.map (cj c) ↔ cj c⁻¹ u ∈ L := by
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
    rw [cj_inv_cj]; exact hs
  · intro h
    exact List.mem_map.2 ⟨cj c⁻¹ u, h, cj_cj_inv c u⟩

private theorem nrm_map_cj (L : List P6) (c σ : P6) :
    Nrm (L.map (cj c)) σ ↔ Nrm L (cj c⁻¹ σ) := by
  rw [nrm_iff, nrm_iff]
  constructor
  · intro h s
    have h1 := h (cj c s)
    rw [mem_map_cj, mem_map_cj] at h1
    have e2 : cj c⁻¹ (cj σ (cj c s)) = cj (cj c⁻¹ σ) s := by
      simp only [cj]; group
    rwa [cj_inv_cj, e2] at h1
  · intro h t
    have h1 := h (cj c⁻¹ t)
    have e2 : cj (cj c⁻¹ σ) (cj c⁻¹ t) = cj c⁻¹ (cj σ t) := by
      simp only [cj]; group
    rw [e2] at h1
    rw [mem_map_cj, mem_map_cj]
    exact h1

private theorem nrm_mul {L : List P6} {σ τ : P6} (h1 : Nrm L σ) (h2 : Nrm L τ) :
    Nrm L (σ * τ) := Subgroup.mul_mem _ h1 h2

private theorem nrm_inv {L : List P6} {σ : P6} (h : Nrm L σ) : Nrm L σ⁻¹ :=
  Subgroup.inv_mem _ h

@[expose] def ntP (L : List P6) (σ : P6) : Prop := ∃ v ∈ L, v ≠ 1 ∧ Nrm L (σ⁻¹ * v * σ)

private def cjW (w s : Wd) : Wd := s.map fun l => (ev w (l.1 % 6), ev w (l.2 % 6))

private theorem fin_ofNat_ev (w : Wd) (i : ℕ) :
    Fin.ofNat 6 (ev w (i % 6)) = prodL w (Fin.ofNat 6 i) := by
  apply Fin.ext
  have h := prodL_val w (Fin.ofNat 6 i)
  have hv : (Fin.ofNat 6 i).val = i % 6 := rfl
  rw [hv] at h
  have hlt := (prodL w (Fin.ofNat 6 i)).isLt
  have hv2 : (Fin.ofNat 6 (ev w (i % 6))).val = ev w (i % 6) % 6 := rfl
  rw [hv2, h]
  omega

private theorem cj_sw (w : Wd) (i j : ℕ) :
    cj (prodL w) (sw i j) = sw (ev w (i % 6)) (ev w (j % 6)) := by
  unfold cj sw
  rw [← Equiv.swap_apply_apply, fin_ofNat_ev, fin_ofNat_ev]

private theorem cj_prodL (w s : Wd) : cj (prodL w) (prodL s) = prodL (cjW w s) := by
  induction s with
  | nil => simp [prodL, cjW, cj]
  | cons l s' ih =>
    obtain ⟨i, j⟩ := l
    simp only [prodL, cjW, List.map_cons]
    rw [cj_cj_mul, cj_sw, ih]
    rfl

private def kw (SW : List Wd) (w : Wd) : List ℕ := SW.map fun s => codeL (encW (cjW w s))

private theorem keyP_prodL (SW : List Wd) (w : Wd) :
    keyP (SW.map prodL) (prodL w) = kw SW w := by
  simp only [keyP, kw, List.map_map]
  apply List.map_congr_left
  intro s _
  simp [Function.comp, code, cj_prodL, enc_prodL]

private def seteqb (l₁ l₂ : List ℕ) : Bool :=
  l₁.all (fun c => l₂.contains c) && l₂.all (fun c => l₁.contains c)

private theorem seteqb_iff {l₁ l₂ : List ℕ} : seteqb l₁ l₂ = true ↔ SetEq l₁ l₂ := by
  simp only [seteqb, SetEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨h1, h2⟩ c
    exact ⟨fun hc => h1 c hc, fun hc => h2 c hc⟩
  · intro h
    exact ⟨fun c hc => (h c).1 hc, fun c hc => (h c).2 hc⟩

private theorem sign_prodL_even (w : Wd) (hv : validB w = true) (he : w.length % 2 = 0) :
    Equiv.Perm.sign (prodL w) = 1 := by
  rw [sign_prodL w (validB_sound hv)]
  exact Even.neg_one_pow (Nat.even_iff.2 he)

private structure OrbitData where
  vws : List Wd
  repW : List Wd
  typ : List Bool
  nW : List Wd
  bF : ℕ
  bT : ℕ

private def OrbitData.SW (D : OrbitData) : List Wd := [] :: D.vws

private def OrbitData.S (D : OrbitData) : List P6 := D.SW.map prodL

private def OrbitData.K0 (D : OrbitData) : List ℕ := kw D.SW []

private def OrbitData.rk (D : OrbitData) (j : ℕ) : List ℕ := kw D.SW (D.repW.getD j [])

private def OrbitData.rks (D : OrbitData) : List (List ℕ) := D.repW.map fun r => kw D.SW r

private def OrbitData.ntB (D : OrbitData) (w : Wd) (kv : List ℕ) : Bool :=
  D.vws.any fun vw => seteqb (kw D.SW (vw ++ w)) kv

private def OrbitData.base (D : OrbitData) (b : Bool) : ℕ := if b then D.bT else D.bF

private def OrbitData.okA (D : OrbitData) : Bool :=
  D.repW.getD 0 [] == [] && 8 ≤ D.repW.length &&
    (D.vws ++ D.repW ++ D.nW).all validB &&
    (D.repW ++ D.nW).all (fun w => w.length % 2 == 0) &&
    D.vws.all (fun vw => codeL (encW vw) != codeL (encW []))

private def OrbitData.okClosure (D : OrbitData) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun j => i == j ||
    D.repW.all fun r => D.rks.any fun r' => seteqb (kw D.SW ((i, j) :: r)) r'

private def OrbitData.okType (D : OrbitData) : Bool :=
  (List.range' 1 (D.repW.length - 1)).all fun j =>
    D.ntB (D.repW.getD j []) (D.rks.getD j []) == D.typ.getD j false

private def OrbitData.okWit (D : OrbitData) : Bool :=
  (List.range' 1 (D.repW.length - 1)).all fun j =>
    seteqb (kw D.SW (D.nW.getD j [])) D.K0 &&
      seteqb (kw D.SW (D.nW.getD j [] ++ D.repW.getD (D.base (D.typ.getD j false)) []))
        (D.rk j)

private def OrbitData.okDist (D : OrbitData) : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j => i == j || !(seteqb (D.rk i) (D.rk j))

private def OrbitData.ok (D : OrbitData) : Bool :=
  D.okA && D.okClosure && D.okType && D.okWit && D.okDist

private theorem OrbitData.keyP_S (D : OrbitData) (w : Wd) :
    keyP D.S (prodL w) = kw D.SW w := keyP_prodL D.SW w

private theorem OrbitData.keyP_rk (D : OrbitData) (j : ℕ) :
    keyP D.S (prodL (D.repW.getD j [])) = D.rk j :=
  OrbitData.keyP_S D _

private theorem OrbitData.keyP_one (D : OrbitData) : keyP D.S 1 = D.K0 := OrbitData.keyP_S D []

private theorem OrbitData.nrm_of_seteqb (D : OrbitData) (w : Wd)
    (h : seteqb (kw D.SW w) D.K0 = true) : Nrm D.S (prodL w) := by
  have h1 : SetEq (keyP D.S 1) (keyP D.S (prodL w)) := by
    rw [OrbitData.keyP_one, OrbitData.keyP_S]; exact fun c => (seteqb_iff.1 h c).symm
  simpa using (keyEq_iff D.S 1 (prodL w)).1 h1

private theorem OrbitData.mem_S_ne_one (D : OrbitData) (hnz : ∀ vw ∈ D.vws, prodL vw ≠ 1)
    {v : P6} : (v ∈ D.S ∧ v ≠ 1) ↔ ∃ vw ∈ D.vws, prodL vw = v := by
  constructor
  · rintro ⟨hv, hv1⟩
    simp only [OrbitData.S, OrbitData.SW, List.map_cons, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨vw, hvw, rfl⟩
    · exact absurd rfl hv1
    · exact ⟨vw, hvw, rfl⟩
  · rintro ⟨vw, hvw, rfl⟩
    refine ⟨?_, hnz vw hvw⟩
    simp only [OrbitData.S, OrbitData.SW, List.map_cons, List.mem_cons, List.mem_map]
    exact Or.inr ⟨vw, hvw, rfl⟩

private theorem OrbitData.ntB_iff (D : OrbitData) (hnz : ∀ vw ∈ D.vws, prodL vw ≠ 1)
    (w : Wd) : D.ntB w (kw D.SW w) = true ↔ ntP D.S (prodL w) := by
  have hconj : ∀ vw : Wd, (prodL w)⁻¹ * prodL (vw ++ w) = (prodL w)⁻¹ * prodL vw * prodL w := by
    intro vw
    rw [prodL_append, mul_assoc]
  have hiff : ∀ vw : Wd, seteqb (kw D.SW (vw ++ w)) (kw D.SW w) = true ↔
      Nrm D.S ((prodL w)⁻¹ * prodL vw * prodL w) := by
    intro vw
    rw [seteqb_iff, ← hconj, ← keyEq_iff, ← OrbitData.keyP_S, ← OrbitData.keyP_S]
    exact ⟨fun h c => (h c).symm, fun h c => (h c).symm⟩
  unfold OrbitData.ntB ntP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨vw, hvw, h⟩
    exact ⟨prodL vw, ((OrbitData.mem_S_ne_one D hnz).2 ⟨vw, hvw, rfl⟩).1, hnz vw hvw,
      (hiff vw).1 h⟩
  · rintro ⟨v, hv, hv1, hN⟩
    obtain ⟨vw, hvw, rfl⟩ := (OrbitData.mem_S_ne_one D hnz).1 ⟨hv, hv1⟩
    exact ⟨vw, hvw, (hiff vw).2 hN⟩

private theorem getD_mem_of_lt {l : List Wd} {j : ℕ} (hj : j < l.length) : l.getD j [] ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

private theorem OrbitData.rks_getD (D : OrbitData) {j : ℕ} (hj : j < D.repW.length) :
    D.rks.getD j [] = D.rk j := by
  simp only [OrbitData.rks, OrbitData.rk, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

private theorem OrbitData.exists_index_of_mem_rks (D : OrbitData) {r : List ℕ}
    (hr : r ∈ D.rks) : ∃ j, j < D.repW.length ∧ D.rk j = r := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 ha
  refine ⟨j, hj, ?_⟩
  unfold OrbitData.rk
  rw [List.getD_eq_getElem _ _ hj, hja]

private theorem OrbitData.ntP_congr (D : OrbitData) {x y : P6}
    (h : SetEq (keyP D.S x) (keyP D.S y)) : ntP D.S x ↔ ntP D.S y := by
  have hm : Nrm D.S (x⁻¹ * y) := (keyEq_iff D.S x y).1 h
  have key : ∀ v : P6, Nrm D.S (x⁻¹ * v * x) ↔ Nrm D.S (y⁻¹ * v * y) := by
    intro v
    constructor
    · intro hv
      have e : y⁻¹ * v * y = (x⁻¹ * y)⁻¹ * (x⁻¹ * v * x) * (x⁻¹ * y) := by group
      rw [e]; exact nrm_mul (nrm_mul (nrm_inv hm) hv) hm
    · intro hv
      have e : x⁻¹ * v * x = (x⁻¹ * y) * (y⁻¹ * v * y) * (x⁻¹ * y)⁻¹ := by group
      rw [e]; exact nrm_mul (nrm_mul hm hv) (nrm_inv hm)
  unfold ntP
  constructor
  · rintro ⟨v, hv, hv1, hN⟩; exact ⟨v, hv, hv1, (key v).1 hN⟩
  · rintro ⟨v, hv, hv1, hN⟩; exact ⟨v, hv, hv1, (key v).2 hN⟩

private theorem OrbitData.cover_all (D : OrbitData) (hclo : D.okClosure = true)
    (h0 : D.repW.getD 0 [] = []) (hlen : 0 < D.repW.length) (σ : P6) :
    ∃ j, j < D.repW.length ∧ SetEq (keyP D.S σ) (D.rk j) := by
  obtain ⟨w, hw, rfl⟩ := lehmer_surj σ
  have hv := validB_sound (lehmer_valid w hw)
  clear hw
  induction w with
  | nil =>
    refine ⟨0, hlen, ?_⟩
    have : D.rk 0 = D.K0 := by
      unfold OrbitData.rk OrbitData.K0
      rw [h0]
    rw [this, show prodL [] = (1 : P6) from rfl, OrbitData.keyP_one]
    exact fun c => Iff.rfl
  | cons l ws ih =>
    obtain ⟨i, j⟩ := l
    obtain ⟨hi, hj, hij⟩ := hv (i, j) (List.mem_cons_self ..)
    obtain ⟨j₁, hj₁, hs₁⟩ := ih (fun q hq => hv q (List.mem_cons_of_mem _ hq))
    have hc := List.all_eq_true.1 (List.all_eq_true.1 hclo i (List.mem_range.2 hi)) j
      (List.mem_range.2 hj)
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact absurd hc hij
    · obtain ⟨r', hr', hrb⟩ := List.any_eq_true.1
        (List.all_eq_true.1 hc _ (getD_mem_of_lt hj₁))
      obtain ⟨j₂, hj₂, hrj⟩ := OrbitData.exists_index_of_mem_rks D hr'
      refine ⟨j₂, hj₂, ?_⟩
      have h2 : SetEq (kw D.SW ((i, j) :: D.repW.getD j₁ [])) (D.rk j₂) := by
        rw [hrj]; exact seteqb_iff.1 hrb
      have h3 : SetEq (keyP D.S (prodL ws)) (keyP D.S (prodL (D.repW.getD j₁ []))) := by
        rw [OrbitData.keyP_rk]; exact hs₁
      have h4 := (keyEq_iff D.S _ _).1 h3
      have h5 : SetEq (keyP D.S (prodL ((i, j) :: ws)))
          (keyP D.S (prodL ((i, j) :: D.repW.getD j₁ []))) := by
        apply (keyEq_iff D.S _ _).2
        simp only [prodL]
        rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [OrbitData.keyP_S D ((i, j) :: D.repW.getD j₁ [])] at h5
      exact fun c => (h5 c).trans (h2 c)

private theorem OrbitData.orbit (D : OrbitData) (h : D.ok = true) :
    (∀ x y : P6, ¬ Nrm D.S x → ¬ Nrm D.S y → (ntP D.S x ↔ ntP D.S y) →
      ∃ n : P6, Equiv.Perm.sign n = 1 ∧ Nrm D.S n ∧ Nrm D.S (y⁻¹ * n * x)) ∧
    ∃ f : Fin 8 → P6, (∀ i, Equiv.Perm.sign (f i) = 1) ∧
      ∀ i j, i ≠ j → ¬ Nrm D.S ((f i)⁻¹ * f j) := by
  simp only [OrbitData.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hClo⟩, hTy⟩, hWi⟩, hDi⟩ := h
  simp only [OrbitData.okA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at hA
  obtain ⟨⟨⟨⟨h0, hlen⟩, hvalid⟩, hpar⟩, hnz⟩ := hA
  have hlen0 : 0 < D.repW.length := by omega
  have hnz' : ∀ vw ∈ D.vws, prodL vw ≠ 1 := by
    intro vw hvw hone
    apply hnz vw hvw
    have h1 : code (prodL vw) = code (prodL []) := by rw [hone]; rfl
    simpa only [code, enc_prodL] using h1
  have hty : ∀ j, 1 ≤ j → j < D.repW.length →
      D.ntB (D.repW.getD j []) (D.rk j) = D.typ.getD j false := by
    intro j hj1 hj2
    have h2 := List.all_eq_true.1 hTy j (List.mem_range'_1.2 ⟨hj1, by omega⟩)
    simpa only [beq_iff_eq, OrbitData.rks_getD D hj2] using h2
  have htyp : ∀ x j, 1 ≤ j → j < D.repW.length → SetEq (keyP D.S x) (D.rk j) →
      (ntP D.S x ↔ D.typ.getD j false = true) := by
    intro x j hj1 hj2 hs
    have hs' : SetEq (keyP D.S x) (keyP D.S (prodL (D.repW.getD j []))) := by
      rw [OrbitData.keyP_rk]; exact hs
    have h3 := OrbitData.ntB_iff D hnz' (D.repW.getD j [])
    have h4 := hty j hj1 hj2
    rw [OrbitData.ntP_congr D hs', ← h3]
    change D.ntB (D.repW.getD j []) (D.rk j) = true ↔ _
    rw [h4]
  have hwit : ∀ j, 1 ≤ j → j < D.repW.length →
      seteqb (kw D.SW (D.nW.getD j [])) D.K0 = true ∧
      seteqb (kw D.SW (D.nW.getD j [] ++ D.repW.getD (D.base (D.typ.getD j false)) []))
        (D.rk j) = true := by
    intro j hj1 hj2
    have := List.all_eq_true.1 hWi j (List.mem_range'_1.2 ⟨hj1, by omega⟩)
    simpa [Bool.and_eq_true] using this
  have hdist : ∀ i j : ℕ, i < 8 → j < 8 → i ≠ j → seteqb (D.rk i) (D.rk j) = false := by
    intro i j hi hj hij
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 hDi i (List.mem_range.2 hi)) j
      (List.mem_range.2 hj)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 hij
    · exact h2
  have hsignR : ∀ j : ℕ, Equiv.Perm.sign (prodL (D.repW.getD j [])) = 1 := by
    intro j
    by_cases hj : j < D.repW.length
    · have hm := getD_mem_of_lt hj
      exact sign_prodL_even _
        (hvalid _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hm)))))
        (hpar _ (List.mem_append.2 (Or.inl hm)))
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [prodL]
  have hsignN : ∀ j : ℕ, Equiv.Perm.sign (prodL (D.nW.getD j [])) = 1 := by
    intro j
    by_cases hj : j < D.nW.length
    · have hm := getD_mem_of_lt hj
      exact sign_prodL_even _ (hvalid _ (List.mem_append.2 (Or.inr hm)))
        (hpar _ (List.mem_append.2 (Or.inr hm)))
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [prodL]
  refine ⟨?_, ?_⟩
  · intro x y hnx hny hnt
    obtain ⟨jx, hjx, hsx⟩ := OrbitData.cover_all D hClo h0 hlen0 x
    obtain ⟨jy, hjy, hsy⟩ := OrbitData.cover_all D hClo h0 hlen0 y
    have hrk0 : D.rk 0 = keyP D.S 1 := by
      rw [OrbitData.keyP_one]
      unfold OrbitData.rk OrbitData.K0
      rw [h0]
    have hjx0 : 1 ≤ jx := by
      by_contra hcon
      have h0' : jx = 0 := by omega
      subst h0'
      rw [hrk0] at hsx
      exact hnx (by simpa using nrm_inv ((keyEq_iff D.S x 1).1 hsx))
    have hjy0 : 1 ≤ jy := by
      by_contra hcon
      have h0' : jy = 0 := by omega
      subst h0'
      rw [hrk0] at hsy
      exact hny (by simpa using nrm_inv ((keyEq_iff D.S y 1).1 hsy))
    have htyeq : D.typ.getD jx false = D.typ.getD jy false := by
      have h1 := (htyp x jx hjx0 hjx hsx).symm.trans (hnt.trans (htyp y jy hjy0 hjy hsy))
      generalize D.typ.getD jx false = tx at h1 ⊢
      generalize D.typ.getD jy false = ty at h1 ⊢
      cases tx <;> cases ty <;> simp at h1 ⊢
    obtain ⟨hwx1, hwx2⟩ := hwit jx hjx0 hjx
    obtain ⟨hwy1, hwy2⟩ := hwit jy hjy0 hjy
    rw [← htyeq] at hwy2
    have hNx : Nrm D.S (prodL (D.nW.getD jx [])) := OrbitData.nrm_of_seteqb D _ hwx1
    have hNy : Nrm D.S (prodL (D.nW.getD jy [])) := OrbitData.nrm_of_seteqb D _ hwy1
    have kx : SetEq (keyP D.S (prodL (D.nW.getD jx [] ++
        D.repW.getD (D.base (D.typ.getD jx false)) []))) (keyP D.S x) := by
      rw [OrbitData.keyP_S]
      have h1 := seteqb_iff.1 hwx2
      exact fun c => (h1 c).trans (hsx c).symm
    have ky : SetEq (keyP D.S (prodL (D.nW.getD jy [] ++
        D.repW.getD (D.base (D.typ.getD jx false)) []))) (keyP D.S y) := by
      rw [OrbitData.keyP_S]
      have h1 := seteqb_iff.1 hwy2
      exact fun c => (h1 c).trans (hsy c).symm
    have mx := (keyEq_iff D.S _ _).1 kx
    have my := (keyEq_iff D.S _ _).1 ky
    refine ⟨prodL (D.nW.getD jy []) * (prodL (D.nW.getD jx []))⁻¹, ?_,
      nrm_mul hNy (nrm_inv hNx), ?_⟩
    · rw [map_mul, map_inv, hsignN, hsignN]; simp
    · have e : y⁻¹ * (prodL (D.nW.getD jy []) * (prodL (D.nW.getD jx []))⁻¹) * x =
          ((prodL (D.nW.getD jy [] ++ D.repW.getD (D.base (D.typ.getD jx false)) []))⁻¹
            * y)⁻¹ * ((prodL (D.nW.getD jx [] ++
              D.repW.getD (D.base (D.typ.getD jx false)) []))⁻¹ * x) := by
        rw [prodL_append, prodL_append]; group
      rw [e]
      exact nrm_mul (nrm_inv my) mx
  · refine ⟨fun i => prodL (D.repW.getD i.val []), fun i => hsignR i.val, ?_⟩
    intro i j hij hN
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hd := hdist i.val j.val (by omega) (by omega) hne
    have hkeq := (keyEq_iff D.S _ _).2 hN
    rw [OrbitData.keyP_rk, OrbitData.keyP_rk] at hkeq
    have := seteqb_iff.2 hkeq
    rw [hd] at this
    exact Bool.false_ne_true this

private def D0 : OrbitData where
  vws := [[(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 1), (2, 3), (0, 2), (1, 3)]]
  repW := [[], [(3, 4), (4, 5)], [(3, 5), (5, 4)], [(2, 3), (3, 4)], [(2, 3), (3, 5)],
    [(2, 4), (3, 5)], [(1, 2), (2, 3), (3, 4), (4, 5)], [(1, 2), (2, 3), (3, 5), (5, 4)],
    [(1, 2), (2, 4), (4, 3), (3, 5)], [(1, 3), (3, 5), (5, 2), (2, 4)],
    [(0, 1), (1, 2), (2, 3), (3, 4)], [(0, 1), (1, 2), (2, 3), (3, 5)],
    [(0, 1), (1, 2), (2, 4), (3, 5)], [(0, 1), (1, 3), (3, 5), (2, 4)],
    [(0, 2), (2, 4), (1, 3), (3, 5)]]
  typ := [false, false, false, false, false, true, false, false, true, true, false, false, true,
    true, true]
  nW := [[], [], [(1, 2), (4, 5)], [(1, 3), (3, 2)], [(2, 3), (4, 5)], [], [(1, 2), (2, 3)],
    [(1, 3), (4, 5)], [(1, 2), (4, 5)], [(1, 3), (3, 2)], [(0, 1), (1, 3)],
    [(0, 1), (1, 2), (2, 3), (4, 5)], [(0, 1), (1, 2)], [(0, 1), (1, 3), (3, 2), (4, 5)],
    [(0, 2), (1, 3)]]
  bF := 1
  bT := 5

private def D1 : OrbitData where
  vws := [[(0, 1), (2, 3)], [(0, 1), (4, 5)], [(0, 1), (2, 3), (0, 1), (4, 5)]]
  repW := [[], [(3, 4), (4, 5)], [(3, 5), (5, 4)], [(1, 2), (4, 5)], [(1, 2), (3, 4)],
    [(1, 2), (3, 5)], [(1, 3), (3, 2)], [(1, 3), (3, 4), (4, 5), (5, 2)],
    [(1, 3), (3, 5), (5, 4), (4, 2)], [(1, 4), (4, 5), (5, 3), (3, 2)], [(1, 4), (4, 2)],
    [(1, 4), (4, 3), (3, 5), (5, 2)], [(1, 5), (5, 4), (4, 3), (3, 2)], [(1, 5), (5, 2)],
    [(1, 5), (5, 3), (3, 4), (4, 2)]]
  typ := [false, true, true, true, false, false, true, false, false, false, false, true, false,
    false, true]
  nW := [[], [], [(0, 1), (4, 5)], [(0, 4), (4, 2), (1, 5), (5, 3)], [],
    [(0, 1), (2, 5), (5, 3), (3, 4)], [(0, 5), (5, 2), (1, 4), (4, 3)],
    [(0, 1), (2, 4), (4, 3), (3, 5)], [(2, 3), (4, 5)], [(2, 4), (3, 5)], [(0, 1), (2, 3)],
    [(0, 2), (1, 3)], [(0, 1), (4, 5)], [(2, 5), (3, 4)], [(0, 3), (3, 1), (1, 2), (4, 5)]]
  bF := 4
  bT := 1

private theorem D0_ok : D0.ok = true := by decide +kernel

private theorem D1_ok : D1.ok = true := by decide +kernel

private def a0w : Wd := [(0, 1), (2, 3)]

private def b0w : Wd := [(0, 2), (1, 3)]

private def b1w : Wd := [(0, 1), (4, 5)]

private def a0 : P6 := prodL a0w

private def b0 : P6 := prodL b0w

private def b1 : P6 := prodL b1w

private def eqW (u v : Wd) : Bool := encW u == encW v

private def sqW (w : Wd) : Bool := eqW (w ++ w) []

private def commW (u v : Wd) : Bool := eqW (u ++ v) (v ++ u)

private theorem eqW_iff {u v : Wd} : eqW u v = true ↔ prodL u = prodL v := by
  unfold eqW
  rw [beq_iff_eq, ← enc_prodL, ← enc_prodL]
  exact ⟨fun h => enc_injective h, fun h => by rw [h]⟩

private theorem sqW_iff {w : Wd} : sqW w = true ↔ prodL w * prodL w = 1 := by
  unfold sqW
  rw [eqW_iff, prodL_append]
  rfl

private theorem commW_iff {u v : Wd} :
    commW u v = true ↔ prodL u * prodL v = prodL v * prodL u := by
  unfold commW
  rw [eqW_iff, prodL_append, prodL_append]

private def tblC : List Wd :=
  [[(0, 4), (4, 2), (1, 5), (5, 3)], [(0, 4), (4, 1), (1, 5), (5, 2)],
   [(0, 4), (4, 3), (3, 2), (1, 5)], [(0, 4), (4, 2), (2, 1), (3, 5)],
   [(0, 4), (4, 3), (3, 2), (2, 1)], [(0, 4), (4, 5), (5, 2), (2, 1)],
   [(0, 4), (4, 3), (3, 1), (2, 5)], [(0, 4), (4, 2), (2, 3), (3, 1)],
   [(0, 4), (4, 5), (5, 3), (3, 1)], [(0, 4), (4, 1), (2, 5), (5, 3)], [(0, 4), (4, 1)],
   [(0, 4), (4, 1), (2, 3), (3, 5)], [(0, 4), (4, 2), (2, 5), (5, 1)],
   [(0, 4), (4, 5), (5, 1), (2, 3)], [(0, 4), (4, 3), (3, 5), (5, 1)], [(2, 4), (3, 5)],
   [(2, 4), (4, 3)], [(2, 4), (4, 5)], [], [(3, 5), (5, 4)], [(3, 4), (4, 5)],
   [(1, 4), (4, 3), (3, 5), (5, 2)], [(1, 4), (4, 2)], [(1, 4), (4, 5), (5, 3), (3, 2)],
   [(1, 2), (4, 5)], [(1, 2), (3, 4)], [(1, 2), (3, 5)], [(1, 4), (4, 2), (2, 5), (5, 3)],
   [(1, 4), (4, 3)], [(1, 4), (4, 5), (5, 2), (2, 3)], [(1, 2), (2, 3)],
   [(1, 2), (2, 5), (5, 4), (4, 3)], [(1, 2), (2, 4), (4, 5), (5, 3)], [(1, 4), (2, 5)],
   [(1, 4), (2, 3)], [(1, 4), (3, 5)], [(1, 2), (2, 3), (3, 5), (5, 4)], [(1, 2), (2, 4)],
   [(1, 2), (2, 5), (5, 3), (3, 4)], [(1, 4), (4, 3), (3, 2), (2, 5)], [(1, 4), (4, 5)],
   [(1, 4), (4, 2), (2, 3), (3, 5)], [(1, 2), (2, 3), (3, 4), (4, 5)], [(1, 2), (2, 5)],
   [(1, 2), (2, 4), (4, 3), (3, 5)]]

private def e0W : List Wd :=
  [[], [(2, 3), (4, 5)], [(0, 1), (4, 5)], [(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 3), (1, 2)]]

private def stdOk1 : Bool :=
  tblC.all (fun c => validB c && c.length % 2 == 0) &&
    evW.all fun w => !(sqW w) || eqW w [] || tblC.any fun c => eqW (cjW c w) a0w

private def stdOk2 : Bool :=
  evW.all fun w => !(sqW w) || eqW w [] || eqW w a0w || !(commW a0w w) ||
    [b0w, a0w ++ b0w, b1w, a0w ++ b1w].any (eqW w)

private def stdOk3 : Bool :=
  evW.all fun w => !(sqW w) || !(commW a0w w) || e0W.any (eqW w)

private def stdOk4 : Bool :=
  [b0w, a0w ++ b0w, b1w, a0w ++ b1w].all fun b =>
    e0W.all fun u => !(commW b u) || [[], a0w, b, a0w ++ b].any (eqW u)

private theorem stdOk1_true : stdOk1 = true := by decide +kernel

private theorem stdOk2_true : stdOk2 = true := by decide +kernel

private theorem stdOk3_true : stdOk3 = true := by decide +kernel

private theorem stdOk4_true : stdOk4 = true := by decide +kernel

private theorem a0a0 : a0 * a0 = 1 := sqW_iff.1 (by decide +kernel : sqW a0w = true)

private theorem sign_cj (c s : P6) : Equiv.Perm.sign (cj c s) = Equiv.Perm.sign s := by
  simp only [cj, map_mul, map_inv, Int.units_inv_eq_self]
  rw [mul_comm (Equiv.Perm.sign c) (Equiv.Perm.sign s), mul_assoc, Int.units_mul_self, mul_one]

private theorem std1 {σ : P6} (hs : Equiv.Perm.sign σ = 1) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ c : P6, Equiv.Perm.sign c = 1 ∧ cj c σ = a0 := by
  obtain ⟨w, hw, rfl⟩ := exists_even_word σ hs
  have h := stdOk1_true
  simp only [stdOk1, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨htbl, hall⟩ := h
  have hw' := hall w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hw'
  rcases hw' with (hw' | hw') | hw'
  · exact absurd (sqW_iff.2 h2) (by simp [hw'])
  · exact absurd (eqW_iff.1 hw') h1
  · obtain ⟨c, hc, hce⟩ := List.any_eq_true.1 hw'
    have hcv := htbl c hc
    simp only [beq_iff_eq] at hcv
    refine ⟨prodL c, sign_prodL_even c hcv.1 hcv.2, ?_⟩
    rw [cj_prodL]
    exact eqW_iff.1 hce

private theorem std2 {τ : P6} (hs : Equiv.Perm.sign τ = 1) (h2 : τ * τ = 1) (h1 : τ ≠ 1)
    (h0 : τ ≠ a0) (hc : τ * a0 = a0 * τ) :
    τ = b0 ∨ τ = a0 * b0 ∨ τ = b1 ∨ τ = a0 * b1 := by
  obtain ⟨w, hw, rfl⟩ := exists_even_word τ hs
  have h := stdOk2_true
  simp only [stdOk2, List.all_eq_true] at h
  have hw' := h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hw'
  rcases hw' with (((hw' | hw') | hw') | hw') | hw'
  · exact absurd (sqW_iff.2 h2) (by simp [hw'])
  · exact absurd (eqW_iff.1 hw') h1
  · exact absurd (eqW_iff.1 hw') h0
  · exact absurd (commW_iff.2 (by simpa [a0] using hc.symm)) (by simp [hw'])
  · obtain ⟨u, hu, hue⟩ := List.any_eq_true.1 hw'
    have hu' := eqW_iff.1 hue
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Or.inl hu'
    · exact Or.inr (Or.inl (by rw [hu', prodL_append]; rfl))
    · exact Or.inr (Or.inr (Or.inl hu'))
    · exact Or.inr (Or.inr (Or.inr (by rw [hu', prodL_append]; rfl)))

private theorem stdE0 {e : P6} (hs : Equiv.Perm.sign e = 1) (h2 : e * e = 1)
    (hc : e * a0 = a0 * e) : ∃ u ∈ e0W, prodL u = e := by
  obtain ⟨w, hw, rfl⟩ := exists_even_word e hs
  have h := stdOk3_true
  simp only [stdOk3, List.all_eq_true] at h
  have hw' := h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hw'
  rcases hw' with (hw' | hw') | hw'
  · exact absurd (sqW_iff.2 h2) (by simp [hw'])
  · exact absurd (commW_iff.2 (by simpa [a0] using hc.symm)) (by simp [hw'])
  · obtain ⟨u, hu, hue⟩ := List.any_eq_true.1 hw'
    exact ⟨u, hu, (eqW_iff.1 hue).symm⟩

private theorem stdE0cl {b : Wd} (hb : b ∈ [b0w, a0w ++ b0w, b1w, a0w ++ b1w]) {u : Wd}
    (hu : u ∈ e0W) (hc : prodL u * prodL b = prodL b * prodL u) :
    prodL u = 1 ∨ prodL u = a0 ∨ prodL u = prodL b ∨ prodL u = a0 * prodL b := by
  have h := stdOk4_true
  simp only [stdOk4, List.all_eq_true] at h
  have h1 := h b hb u hu
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · exact absurd (commW_iff.2 hc.symm) (by simp [h1])
  · obtain ⟨v, hv, hve⟩ := List.any_eq_true.1 h1
    have hv' := eqW_iff.1 hve
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inl hv'
    · exact Or.inr (Or.inl hv')
    · exact Or.inr (Or.inr (Or.inl hv'))
    · exact Or.inr (Or.inr (Or.inr (by rw [hv', prodL_append]; rfl)))

@[expose] def kleinList (a b : P6) : List P6 := [1, a, b, a * b]

structure KleinPair (a b : P6) : Prop where
  ea : Equiv.Perm.sign a = 1
  eb : Equiv.Perm.sign b = 1
  a1 : a ≠ 1
  b1 : b ≠ 1
  ab : a ≠ b
  sa : a * a = 1
  sb : b * b = 1
  comm : a * b = b * a

private theorem klein_std {a b : P6} (h : KleinPair a b) :
    ∃ c : P6, Equiv.Perm.sign c = 1 ∧ cj c a = a0 ∧
      (cj c b = b0 ∨ cj c b = a0 * b0 ∨ cj c b = b1 ∨ cj c b = a0 * b1) := by
  obtain ⟨c, hc, hca⟩ := std1 h.ea h.sa h.a1
  refine ⟨c, hc, hca, std2 ?_ ?_ ?_ ?_ ?_⟩
  · rw [sign_cj]; exact h.eb
  · rw [← cj_cj_mul, h.sb, cj_cj_one]
  · intro h1
    exact h.b1 (cj_inj c (h1.trans (cj_cj_one c).symm))
  · intro h1
    rw [← hca] at h1
    exact h.ab (cj_inj c h1).symm
  · rw [← hca, ← cj_cj_mul, ← cj_cj_mul, h.comm]

private theorem cj_eq_one_iff (c e : P6) : cj c e = 1 ↔ e = 1 :=
  ⟨fun h => cj_inj c (h.trans (cj_cj_one c).symm), fun h => by rw [h, cj_cj_one]⟩

theorem klein_closed {a b : P6} (h : KleinPair a b) {e : P6} (he : Equiv.Perm.sign e = 1)
    (h2 : e * e = 1) (hea : e * a = a * e) (heb : e * b = b * e) : e ∈ kleinList a b := by
  obtain ⟨c, hc, hca, hcb⟩ := klein_std h
  have he' : Equiv.Perm.sign (cj c e) = 1 := by rw [sign_cj]; exact he
  have h2' : cj c e * cj c e = 1 := by rw [← cj_cj_mul, h2, cj_cj_one]
  have hea' : cj c e * a0 = a0 * cj c e := by
    rw [← hca, ← cj_cj_mul, ← cj_cj_mul, hea]
  obtain ⟨u, hu, hue⟩ := stdE0 he' h2' hea'
  have hb' : ∃ bw ∈ [b0w, a0w ++ b0w, b1w, a0w ++ b1w], prodL bw = cj c b := by
    rcases hcb with hb | hb | hb | hb
    · exact ⟨b0w, by simp, hb.symm⟩
    · exact ⟨a0w ++ b0w, by simp, by rw [prodL_append]; exact hb.symm⟩
    · exact ⟨b1w, by simp, hb.symm⟩
    · exact ⟨a0w ++ b1w, by simp, by rw [prodL_append]; exact hb.symm⟩
  obtain ⟨bw, hbw, hbwb⟩ := hb'
  have hcomm : prodL u * prodL bw = prodL bw * prodL u := by
    rw [hue, hbwb, ← cj_cj_mul, ← cj_cj_mul, heb]
  have key := stdE0cl hbw hu hcomm
  rw [hue, hbwb] at key
  have hab : a0 * cj c b = cj c (a * b) := by rw [cj_cj_mul, hca]
  simp only [kleinList, List.mem_cons, List.not_mem_nil, or_false]
  rcases key with k | k | k | k
  · exact Or.inl ((cj_eq_one_iff c e).1 k)
  · exact Or.inr (Or.inl (cj_inj c (k.trans hca.symm)))
  · exact Or.inr (Or.inr (Or.inl (cj_inj c k)))
  · exact Or.inr (Or.inr (Or.inr (cj_inj c (k.trans hab))))

private theorem nrm_congr {L₁ L₂ : List P6} (h : ∀ s, s ∈ L₁ ↔ s ∈ L₂) (σ : P6) :
    Nrm L₁ σ ↔ Nrm L₂ σ := by
  have : {s | s ∈ L₁} = {s | s ∈ L₂} := Set.ext h
  unfold Nrm
  rw [this]

private theorem ntP_congr' {L₁ L₂ : List P6} (h : ∀ s, s ∈ L₁ ↔ s ∈ L₂) (σ : P6) :
    ntP L₁ σ ↔ ntP L₂ σ := by
  unfold ntP
  constructor
  · rintro ⟨v, hv, hv1, hN⟩
    exact ⟨v, (h v).1 hv, hv1, (nrm_congr h _).1 hN⟩
  · rintro ⟨v, hv, hv1, hN⟩
    exact ⟨v, (h v).2 hv, hv1, (nrm_congr h _).2 hN⟩

private theorem transport_cj (L : List P6) (c : P6) :
    (∀ σ, Nrm L σ ↔ Nrm (L.map (cj c)) (cj c σ)) ∧
    (∀ σ, ntP L σ ↔ ntP (L.map (cj c)) (cj c σ)) := by
  have hN : ∀ σ, Nrm L σ ↔ Nrm (L.map (cj c)) (cj c σ) := by
    intro σ
    rw [nrm_map_cj, cj_inv_cj]
  refine ⟨hN, fun σ => ?_⟩
  have hc : ∀ v, (cj c σ)⁻¹ * cj c v * cj c σ = cj c (σ⁻¹ * v * σ) := by
    intro v
    simp only [cj]
    group
  unfold ntP
  constructor
  · rintro ⟨v, hv, hv1, hn⟩
    refine ⟨cj c v, List.mem_map.2 ⟨v, hv, rfl⟩,
      fun h => hv1 (cj_inj c (h.trans (cj_cj_one c).symm)), ?_⟩
    rw [hc]
    exact (hN _).1 hn
  · rintro ⟨v', hv', hv1, hn⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hv'
    refine ⟨v, hv, fun h => hv1 (by rw [h, cj_cj_one]), ?_⟩
    rw [hc] at hn
    exact (hN _).2 hn

private theorem kleinList_map (c a b : P6) :
    (kleinList a b).map (cj c) = kleinList (cj c a) (cj c b) := by
  simp [kleinList, cj_cj_one, cj_cj_mul]

private theorem D0_S : D0.S = kleinList a0 b0 := by
  have h : D0.S = [prodL [], prodL a0w, prodL b0w, prodL (a0w ++ b0w)] := rfl
  rw [h, prodL_append]
  rfl

private theorem D1_S : D1.S = kleinList a0 b1 := by
  have h : D1.S = [prodL [], prodL a0w, prodL b1w, prodL (a0w ++ b1w)] := rfl
  rw [h, prodL_append]
  rfl

private theorem a0_mul_a0_mul (b : P6) : a0 * (a0 * b) = b := by
  rw [← mul_assoc, a0a0, one_mul]

private theorem klein_D {a b : P6} (h : KleinPair a b) :
    ∃ c : P6, Equiv.Perm.sign c = 1 ∧ ∃ D : OrbitData, D.ok = true ∧
      ∀ s, s ∈ (kleinList a b).map (cj c) ↔ s ∈ D.S := by
  obtain ⟨c, hc, hca, hcb⟩ := klein_std h
  refine ⟨c, hc, ?_⟩
  rw [kleinList_map, hca]
  rcases hcb with hb | hb | hb | hb
  · exact ⟨D0, D0_ok, by rw [hb, D0_S]; exact fun s => Iff.rfl⟩
  · refine ⟨D0, D0_ok, ?_⟩
    rw [hb, D0_S]
    intro s
    simp only [kleinList, List.mem_cons, List.not_mem_nil, or_false, a0_mul_a0_mul]
    tauto
  · exact ⟨D1, D1_ok, by rw [hb, D1_S]; exact fun s => Iff.rfl⟩
  · refine ⟨D1, D1_ok, ?_⟩
    rw [hb, D1_S]
    intro s
    simp only [kleinList, List.mem_cons, List.not_mem_nil, or_false, a0_mul_a0_mul]
    tauto

private theorem klein_transfer {a b : P6} (h : KleinPair a b) :
    ∃ c : P6, Equiv.Perm.sign c = 1 ∧ ∃ D : OrbitData, D.ok = true ∧
      (∀ σ, Nrm (kleinList a b) σ ↔ Nrm D.S (cj c σ)) ∧
      (∀ σ, ntP (kleinList a b) σ ↔ ntP D.S (cj c σ)) := by
  obtain ⟨c, hc, D, hD, hset⟩ := klein_D h
  obtain ⟨hN, hnt⟩ := transport_cj (kleinList a b) c
  exact ⟨c, hc, D, hD, fun σ => (hN σ).trans (nrm_congr hset _),
    fun σ => (hnt σ).trans (ntP_congr' hset _)⟩

theorem klein_orbit {a b : P6} (h : KleinPair a b) {x y : P6}
    (hnx : ¬ Nrm (kleinList a b) x) (hny : ¬ Nrm (kleinList a b) y)
    (hnt : ntP (kleinList a b) x ↔ ntP (kleinList a b) y) :
    ∃ n : P6, Equiv.Perm.sign n = 1 ∧ Nrm (kleinList a b) n ∧
      Nrm (kleinList a b) (y⁻¹ * n * x) := by
  obtain ⟨c, hc, D, hD, hN, hnt'⟩ := klein_transfer h
  obtain ⟨n', hn'1, hn'2, hn'3⟩ := (OrbitData.orbit D hD).1 (cj c x) (cj c y)
    (fun h' => hnx ((hN x).2 h')) (fun h' => hny ((hN y).2 h'))
    (((hnt' x).symm.trans hnt).trans (hnt' y))
  refine ⟨cj c⁻¹ n', ?_, ?_, ?_⟩
  · rw [sign_cj]
    exact hn'1
  · rw [hN, cj_cj_inv]
    exact hn'2
  · rw [hN]
    have e : cj c (y⁻¹ * cj c⁻¹ n' * x) = (cj c y)⁻¹ * n' * cj c x := by
      simp only [cj]
      group
    rw [e]
    exact hn'3

end CFSG.CGT.Timmesfeld75.A6Model
