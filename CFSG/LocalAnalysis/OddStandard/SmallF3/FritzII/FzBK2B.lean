module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def FzbNorm {G : Type} [Group G] (P : Subgroup G) (g : G) : Prop :=
  ∀ p ∈ P, g * p * g⁻¹ ∈ P

section Norm

variable {G : Type} [Group G] {P : Subgroup G} {g g' : G}

theorem FzbNorm.one : FzbNorm P 1 := by
  intro p hp
  simpa using hp

theorem FzbNorm.mul (h : FzbNorm P g) (h' : FzbNorm P g') : FzbNorm P (g * g') := by
  intro p hp
  convert h (g' * p * g'⁻¹) (h' p hp) using 1
  group

theorem FzbNorm.pow (h : FzbNorm P g) (n : ℕ) : FzbNorm P (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact FzbNorm.one
  | succ n ih => rw [pow_succ]; exact FzbNorm.mul ih h

end Norm

namespace FzbCoding

private theorem range_map_getElem! (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  have hsize : i < ((Array.range n).map f).size := by
    simpa [Array.size_map, Array.size_range] using hi
  rw [getElem!_pos ((Array.range n).map f) i hsize, Array.getElem_map, Array.getElem_range]

private theorem gensU_lt {i : ℕ} (hi : i < 4) : gensU[i]! < 64 := by
  interval_cases i <;> decide

private theorem iterA_cons (f : Array ℕ) (n x : ℕ) :
    iterA f n (f[x]!) = f[iterA f n x]! := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show f[iterA f n (f[x]!)]! = f[f[iterA f n x]!]!
      rw [ih]

variable {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P) {g g' : G}

@[expose] def tab (g : G) : Array ℕ := (Array.range 64).map (fun x => C.enc (g * C.dec x * g⁻¹))

theorem tab_size (g : G) : (C.tab g).size = 64 := by
  rw [tab]
  simp [Array.size_map, Array.size_range]

theorem tab_getElem (g : G) {x : ℕ} (hx : x < 64) :
    (C.tab g)[x]! = C.enc (g * C.dec x * g⁻¹) := by
  rw [tab]
  exact range_map_getElem! (fun x => C.enc (g * C.dec x * g⁻¹)) hx

theorem tab_lt (hg : FzbNorm P g) {x : ℕ} (hx : x < 64) : (C.tab g)[x]! < 64 := by
  rw [tab_getElem C g hx]
  exact C.enc_lt _ (hg _ (C.dec_mem x hx))

theorem tab_enc (hg : FzbNorm P g) {p : G} (hp : p ∈ P) :
    (C.tab g)[C.enc p]! = C.enc (g * p * g⁻¹) := by
  rw [tab_getElem C g (C.enc_lt p hp), C.dec_enc p hp]

theorem tab_dec (hg : FzbNorm P g) {x : ℕ} (hx : x < 64) :
    g * C.dec x * g⁻¹ = C.dec ((C.tab g)[x]!) := by
  rw [tab_getElem C g hx]
  exact (C.dec_enc _ (hg _ (C.dec_mem x hx))).symm

private theorem tab_enc_mul (C : FzbCoding P) {g : G} (hg : FzbNorm P g) {x y : ℕ}
    (hx : x < 64) (hy : y < 64) :
    (C.tab g)[uMul x y]! = uMul ((C.tab g)[x]!) ((C.tab g)[y]!) := by
  have hxy : uMul x y < 64 := fzb_uMul_lt hx hy
  rw [tab_getElem C g hxy, tab_getElem C g hx, tab_getElem C g hy, C.dec_mul hx hy]
  have hgx : g * C.dec x * g⁻¹ ∈ P := hg _ (C.dec_mem x hx)
  have hgy : g * C.dec y * g⁻¹ ∈ P := hg _ (C.dec_mem y hy)
  have heq : g * (C.dec x * C.dec y) * g⁻¹ =
      (g * C.dec x * g⁻¹) * (g * C.dec y * g⁻¹) := by group
  rw [heq, C.enc_mul _ hgx _ hgy]

theorem tab_mul (hg : FzbNorm P g) (hg' : FzbNorm P g') {x : ℕ} (hx : x < 64) :
    (C.tab (g * g'))[x]! = (C.tab g)[(C.tab g')[x]!]! := by
  have hlt : (C.tab g')[x]! < 64 := tab_lt C hg' hx
  rw [tab_getElem C (g * g') hx, tab_getElem C g hlt, ← tab_dec C hg' hx]
  congr 1
  group

theorem tab_one {x : ℕ} (hx : x < 64) : (C.tab 1)[x]! = x := by
  rw [tab_getElem C 1 hx]
  simp only [one_mul, inv_one, mul_one]
  exact C.enc_dec x hx

theorem tab_pow (hg : FzbNorm P g) (n : ℕ) {x : ℕ} (hx : x < 64) :
    (C.tab (g ^ n))[x]! = iterA (C.tab g) n x := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, tab_one C hx]
      rfl
  | succ n ih =>
      rw [pow_succ, tab_mul C (FzbNorm.pow hg n) hg hx, ih (tab_lt C hg hx)]
      exact iterA_cons (C.tab g) n x

theorem tab_isAut (hg : FzbNorm P g) : isAutArr (C.tab g) = true := by
  have h1 : ((C.tab g).size == 64) = true := by
    rw [beq_iff_eq]
    exact tab_size C g
  have h2 : allBelow (fun x => (C.tab g)[x]! < 64) 64 = true :=
    (fzb_allBelow_iff _ 64).mpr (fun x hx => by simpa using tab_lt C hg hx)
  have h3 : ((C.tab g)[0]! == 0) = true := by
    rw [beq_iff_eq, tab_getElem C g (by norm_num), C.dec_zero]
    simp [C.enc_one]
  have h4 : allBelow (fun x => allBelow (fun y => (C.tab g)[x]! != (C.tab g)[y]!) x) 64
      = true := by
    rw [fzb_allBelow_iff]
    intro x hx
    rw [fzb_allBelow_iff]
    intro y hy
    rw [bne_iff_ne]
    intro hxy
    have hy64 : y < 64 := lt_trans hy hx
    have hdec : C.dec x = C.dec y := by
      have hconj : g * C.dec x * g⁻¹ = g * C.dec y * g⁻¹ := by
        rw [tab_dec C hg hx, tab_dec C hg hy64]
        exact congrArg C.dec hxy
      have hcancel : g * C.dec x = g * C.dec y := by
        have := congrArg (· * g) hconj
        simpa [mul_assoc] using this
      exact mul_left_cancel hcancel
    have hxy' : x = y := by
      have := congrArg C.enc hdec
      rwa [C.enc_dec x hx, C.enc_dec y hy64] at this
    omega
  have h5 : allBelow (fun i => allBelow (fun x =>
      (C.tab g)[uMul gensU[i]! x]! == uMul (C.tab g)[gensU[i]!]! (C.tab g)[x]!) 64) 4
      = true := by
    rw [fzb_allBelow_iff]
    intro i hi
    rw [fzb_allBelow_iff]
    intro x hx
    rw [beq_iff_eq]
    exact tab_enc_mul C hg (gensU_lt hi) hx
  rw [isAutArr, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem tab_comm (hg : FzbNorm P g) (hg' : FzbNorm P g') (hc : g * g' = g' * g) :
    commA (C.tab g) (C.tab g') = true := by
  rw [commA, fzb_allBelow_iff]
  intro x hx
  rw [beq_iff_eq]
  have hlt : (C.tab g')[x]! < 64 := tab_lt C hg' hx
  have hlt' : (C.tab g)[x]! < 64 := tab_lt C hg hx
  have hLP : (C.tab g)[(C.tab g')[x]!]! = C.enc (g * (g' * C.dec x * g'⁻¹) * g⁻¹) := by
    rw [tab_getElem C g hlt, ← tab_dec C hg' hx]
  have hRP : (C.tab g')[(C.tab g)[x]!]! = C.enc (g' * (g * C.dec x * g⁻¹) * g'⁻¹) := by
    rw [tab_getElem C g' hlt', ← tab_dec C hg hx]
  rw [hLP, hRP]
  congr 1
  calc g * (g' * C.dec x * g'⁻¹) * g⁻¹
      = (g * g') * C.dec x * (g * g')⁻¹ := by group
    _ = (g' * g) * C.dec x * (g' * g)⁻¹ := by rw [hc]
    _ = g' * (g * C.dec x * g⁻¹) * g'⁻¹ := by group

theorem tab_fix_count (hg : FzbNorm P g) :
    countBelow (fun x => (C.tab g)[x]! == x) 64 =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({g} : Set G)) := by
  rw [fzb_countBelow_eq]
  let F : Finset ℕ := (Finset.range 64).filter (fun x => (C.tab g)[x]! == x)
  change F.card = Nat.card ↥(P ⊓ Subgroup.centralizer ({g} : Set G))
  have hcard : F.card = Nat.card ↥F := by
    rw [← Fintype.card_coe F, Nat.card_eq_fintype_card]
  refine hcard.trans (Nat.card_congr ?_)
  refine ⟨fun x => ⟨C.dec x.1, ?_⟩, fun y => ⟨C.enc y.1, ?_⟩, ?_, ?_⟩
  · obtain ⟨hxr, hfix⟩ := Finset.mem_filter.mp x.2
    have hx : x.1 < 64 := Finset.mem_range.mp hxr
    have hf : (C.tab g)[x.1]! = x.1 := beq_iff_eq.mp hfix
    refine Subgroup.mem_inf.mpr ⟨C.dec_mem x.1 hx, ?_⟩
    have hconj : g * C.dec x.1 * g⁻¹ = C.dec x.1 := by
      rw [tab_dec C hg hx, hf]
    have hcomm : C.dec x.1 * g = g * C.dec x.1 := by
      have := congrArg (· * g) hconj
      simpa [mul_assoc] using this.symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  · obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp y.2
    have hycomm : y.1 * g = g * y.1 := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hcomm : g * y.1 * g⁻¹ = y.1 := by
      rw [hycomm.symm, mul_assoc, mul_inv_cancel, mul_one]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (C.enc_lt y.1 hyP), ?_⟩
    rw [beq_iff_eq, tab_enc C hg hyP, hcomm]
  · intro x
    exact Subtype.ext (C.enc_dec x.1 (Finset.mem_range.mp (Finset.mem_filter.mp x.2).1))
  · intro y
    exact Subtype.ext (C.dec_enc y.1 (Subgroup.mem_inf.mp y.2).1)

theorem tab_twist {words : Array (List ℕ)} (hw : wordsOK words = true) {g : Array ℕ}
    (hg : isAutArr g = true) {a : G} (ha : FzbNorm P a) {p0 : Array ℕ}
    (h : conjP g (C.tab a) p0 = true) {x : ℕ} (hx : x < 64) :
    (C.twist hw g hg).enc (a * (C.twist hw g hg).dec x * a⁻¹) = p0[x]! := by
  set C' : FzbCoding P := C.twist hw g hg with hC'
  have henc : ∀ p : G, C'.enc p = g[C.enc p]! := by
    intro p
    rw [hC']
    exact twist_enc C hw g hg p
  have hdecxP : C'.dec x ∈ P := C'.dec_mem x hx
  have hxenc : C.enc (C'.dec x) < 64 := C.enc_lt _ hdecxP
  have hgen : g[C.enc (C'.dec x)]! = x := by
    rw [← henc (C'.dec x), C'.enc_dec x hx]
  have hconj := h
  rw [conjP, fzb_allBelow_iff] at hconj
  have hh : g[(C.tab a)[C.enc (C'.dec x)]!]! = p0[g[C.enc (C'.dec x)]!]! :=
    beq_iff_eq.mp (hconj (C.enc (C'.dec x)) hxenc)
  calc
    C'.enc (a * C'.dec x * a⁻¹) = g[C.enc (a * C'.dec x * a⁻¹)]! := henc _
    _ = g[(C.tab a)[C.enc (C'.dec x)]!]! := by
      congr 1
      rw [tab_getElem C a hxenc, C.dec_enc (C'.dec x) hdecxP]
    _ = p0[g[C.enc (C'.dec x)]!]! := hh
    _ = p0[x]! := by rw [hgen]

theorem tab_twist_dec {words : Array (List ℕ)} (hw : wordsOK words = true) {g : Array ℕ}
    (hg : isAutArr g = true) {a : G} (ha : FzbNorm P a) {p0 : Array ℕ}
    (h : conjP g (C.tab a) p0 = true) {x : ℕ} (hx : x < 64) :
    a * (C.twist hw g hg).dec x * a⁻¹ = (C.twist hw g hg).dec (p0[x]!) := by
  set C' : FzbCoding P := C.twist hw g hg with hC'
  have hmem : a * C'.dec x * a⁻¹ ∈ P := ha _ (C'.dec_mem x hx)
  have htw : C'.enc (a * C'.dec x * a⁻¹) = p0[x]! := by
    rw [hC']
    exact tab_twist C hw hg ha h hx
  exact ((C'.dec_enc (a * C'.dec x * a⁻¹) hmem).symm.trans (congrArg C'.dec htw))

end FzbCoding

end CFSG.OddStandard.SmallF3.FritzII
