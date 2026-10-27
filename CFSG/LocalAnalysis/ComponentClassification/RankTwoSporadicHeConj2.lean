module

public import CFSG.Certificates.Kernel.Census.HeConj2Sound
public import CFSG.Sporadic.SuzOddCore.Restrict
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.Schreier.PairHeClassesBase

public section

namespace CFSG.KC.HeConj

open Subgroup CFSG.KC.Enum CFSG.KC.Census CFSG.KS CFSG.KS.SporSch
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier CFSG.ABGLocalTools CFSG.Open
open CFSG.Sporadic.SuzOddCore

theorem map_pcG {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∀ (l : List G) (m : ℕ), f (pcG l m) = pcG (l.map f) m
  | [], _ => map_one f
  | x :: l, m => by
    simp only [pcG, List.map_cons, map_mul, map_pcG f l]
    split_ifs <;> simp

theorem nbeq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  rw [Nat.beq_eq]
  exact h

theorem nbeq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem nodeH_map (φ : A →* B) (l : List A) (bm : List ℕ) :
    (nodeH l bm).map φ = nodeH (l.map φ) bm := by
  rw [nodeH, nodeH, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, map_pcG φ l m⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, map_pcG φ l m⟩

theorem facts_of_map (φ : A →* B) (hφ : Function.Injective φ) (l : List A) (N : Subgroup A) :
    ∀ wit : HW, wit.facts (l.map φ) (N.map φ) → wit.facts l N
  | .small, h => by
    simp only [HW.facts] at h ⊢
    rwa [card_map_of_injective hφ] at h
  | .order4 e gf _ _, h => by
    simp only [HW.facts, ← map_pcG, mem_map_iff_mem hφ, ne_eq,
      map_eq_one_iff φ hφ] at h ⊢
    exact h
  | .closing s t v .., h => by
    simp only [HW.facts, ← map_pcG, mem_map_iff_mem hφ, ne_eq,
      map_eq_one_iff φ hφ] at h ⊢
    exact h

theorem facts_map (φ : A →* B) (hφ : Function.Injective φ) (l : List A) (N : Subgroup A) :
    ∀ wit : HW, wit.facts l N → wit.facts (l.map φ) (N.map φ)
  | .small, h => by
    simp only [HW.facts] at h ⊢
    rwa [card_map_of_injective hφ]
  | .order4 e gf _ _, h => by
    simp only [HW.facts, ← map_pcG, mem_map_iff_mem hφ, ne_eq,
      map_eq_one_iff φ hφ] at h ⊢
    exact h
  | .closing s t v .., h => by
    simp only [HW.facts, ← map_pcG, mem_map_iff_mem hφ, ne_eq,
      map_eq_one_iff φ hφ] at h ⊢
    exact h

theorem isElemAbelian_of_map_le {N E : Subgroup A} {s : A}
    (h : N.map (MulAut.conj s).toMonoidHom ≤ E) (hE : IsElemAbelian 2 E) : IsElemAbelian 2 N := by
  have hE' := (CFSG.Open.IsElemAbelian.mono hE h).map (MulAut.conj s⁻¹).toMonoidHom
  rwa [CFSG.ComponentClassification.RankTwoSporadic.map_conj_map_conj, inv_mul_cancel,
    show (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A by ext; simp, map_id] at hE'

end Transport

section Generic

variable {n : ℕ} {X R : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} {uR : Equiv.Perm (Fin n)}
  {uf : ℕ → ℕ} {nfv : ℕ → Bool} {nfp : ℕ → ℕ → ℕ} {nfE : ℕ → Equiv.Perm (Fin n)}

@[expose] def InC (X : Subgroup (Equiv.Perm (Fin n))) (uR : Equiv.Perm (Fin n)) (a : Equiv.Perm (Fin n))
    (p : ℕ) : Prop :=
  if p = 0 then a ∈ X else uR * a ∈ X

@[expose] def xE (uR : Equiv.Perm (Fin n)) (nfE : ℕ → Equiv.Perm (Fin n)) (f F : ℕ) :
    Equiv.Perm (Fin n) :=
  (if f = 1 then uR else 1) * nfE F

@[expose] def xsE (uR : Equiv.Perm (Fin n)) (nfE : ℕ → Equiv.Perm (Fin n)) (fl xf : List ℕ) :
    List (Equiv.Perm (Fin n)) :=
  List.zipWith (xE uR nfE) fl xf

variable (hnf : ∀ F, nfv F = true → nfE F ∈ X ∧ RepF n (nfp F) (nfE F)) (huf : RepF n uf uR)
  (hu2 : uR * uR = 1) (hN : ∀ x ∈ X, uR * x * uR⁻¹ ∈ X)

include hnf huf in
theorem repF_xE {f F : ℕ} (hF : nfv F = true) : RepF n (xp nfp uf f F) (xE uR nfE f F) := by
  intro x hx
  have h := (huf.comp (hnf F hF).2) x hx
  have h1 := (hnf F hF).2 x hx
  simp only [xp, xE, strictN_val]
  by_cases hf : f = 1
  · subst hf
    simpa using h
  · simp only [nbeq_false hf, hf, if_false, one_mul]
    exact h1

include hnf hu2 in
theorem inC_xE {f F : ℕ} (hF : nfv F = true) (hf : f < 2) :
    InC X uR (xE uR nfE f F) f := by
  have hm := (hnf F hF).1
  unfold InC xE
  rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl
  · simpa using hm
  · simp only [one_ne_zero, if_false, if_true]
    rw [← mul_assoc, hu2, one_mul]
    exact hm

include hu2 hN in
theorem inC_mul {a b : Equiv.Perm (Fin n)} {p q : ℕ} (hp : p < 2) (hq : q < 2) (ha : InC X uR a p)
    (hb : InC X uR b q) : InC X uR (a * b) ((p + q) % 2) := by
  have hui : uR⁻¹ = uR := inv_eq_of_mul_eq_one_right hu2
  unfold InC at *
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;>
    rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;>
    simp only [↓reduceIte, one_ne_zero] at ha hb
  · rw [if_pos (by decide)]
    exact mul_mem ha hb
  · rw [if_neg (by decide)]
    have := mul_mem (hN a ha) hb
    rwa [hui, mul_assoc, mul_assoc, ← mul_assoc uR uR b, hu2, one_mul, ← mul_assoc] at this
  · rw [if_neg (by decide), ← mul_assoc]
    exact mul_mem ha hb
  · rw [if_pos (by decide)]
    have := mul_mem (hN _ ha) hb
    rwa [hui, ← mul_assoc uR uR a, hu2, one_mul, mul_assoc, ← mul_assoc uR uR b, hu2,
      one_mul] at this

theorem bpar_lt : ∀ (fl : List ℕ) (m : ℕ), bpar fl m < 2
  | [], _ => by simp [bpar]
  | f :: fl, m => Nat.mod_lt _ (by norm_num)

theorem bpar_cons (f : ℕ) (fl : List ℕ) (m : ℕ) :
    bpar (f :: fl) m = ((if m % 2 = 1 then f else 0) + bpar fl (m / 2)) % 2 := by
  change ((bif Nat.beq (m % 2) 1 then f else 0) + bpar fl (m / 2)) % 2 = _
  by_cases h : m % 2 = 1
  · rw [nbeq_true h, if_pos h]
    rfl
  · rw [nbeq_false h, if_neg h]
    rfl

theorem bpcOK_facts {bs : List ℕ} : ∀ {fl xf rs : List ℕ} {cs : List (List ℕ)},
    bpcOK nfv nfp uf bs fl xf rs cs = true → fl.length = xf.length ∧
      (∀ F ∈ xf, nfv F = true) ∧ ∀ f ∈ fl, f < 2
  | [], [], _, _, _ => by simp
  | f :: fl, F :: xf, r :: rs, c :: cs, h => by
    simp only [bpcOK, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hl, hF, hf⟩ := bpcOK_facts h.2
    refine ⟨by simp [hl], ?_, ?_⟩
    · intro G hG
      rcases List.mem_cons.1 hG with rfl | hG
      · exact h.1.1.1.1.1
      · exact hF G hG
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact h.1.1.1.1.2
      · exact hf g hg
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [bpcOK] at h
  | _ :: _, _ :: _, [], _, h | _ :: _, _ :: _, _ :: _, [], h => by simp [bpcOK] at h

include hnf huf in
theorem repF_bpcAt : ∀ {fl xf : List ℕ}, fl.length = xf.length → (∀ F ∈ xf, nfv F = true) →
    ∀ m, RepF n (bpcAt nfp uf fl xf m) (pcG (xsE uR nfE fl xf) m)
  | [], [], _, _, m => by
    intro x hx
    simp [bpcAt, xsE, pcG]
  | f :: fl, F :: xf, hl, hF, m => by
    have ih := repF_bpcAt (fl := fl) (xf := xf) (by simpa using hl)
      (fun G hG => hF G (List.mem_cons_of_mem F hG)) (m / 2)
    have hx := repF_xE hnf huf (f := f) (hF F List.mem_cons_self)
    intro x hx'
    change strictN (bpcAt nfp uf fl xf (m / 2) x) (fun y => nIf(Nat.beq (m % 2) 1,
      xp nfp uf f F y, y)) = _
    simp only [strictN_val, xsE, List.zipWith_cons_cons]
    rw [pcG]
    by_cases hm : m % 2 = 1
    · rw [nbeq_true hm, if_pos hm]
      exact (hx.comp ih) x hx'
    · rw [nbeq_false hm, if_neg hm, one_mul]
      exact ih x hx'
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => by simp at hl

include hnf hu2 hN in
theorem inC_pcG : ∀ {fl xf : List ℕ}, fl.length = xf.length → (∀ F ∈ xf, nfv F = true) →
    (∀ f ∈ fl, f < 2) → ∀ m, InC X uR (pcG (xsE uR nfE fl xf) m) (bpar fl m)
  | [], [], _, _, _, m => by simp [InC, xsE, pcG, bpar]
  | f :: fl, F :: xf, hl, hF, hf, m => by
    have ih := inC_pcG (fl := fl) (xf := xf) (by simpa using hl)
      (fun G hG => hF G (List.mem_cons_of_mem F hG)) (fun g hg => hf g (List.mem_cons_of_mem f hg))
      (m / 2)
    have hf2 := hf f List.mem_cons_self
    simp only [xsE, List.zipWith_cons_cons]
    rw [pcG, bpar_cons]
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_pos hm]
      exact inC_mul hu2 hN hf2 (bpar_lt _ _) (inC_xE hnf hu2 (hF F List.mem_cons_self) hf2) ih
    · rw [if_neg hm, if_neg hm, one_mul, Nat.zero_add, Nat.mod_eq_of_lt (bpar_lt _ _)]
      exact ih
  | [], _ :: _, hl, _, _, _ | _ :: _, [], hl, _, _, _ => by simp at hl

variable (hX : BaseFaithful X bs) (hbs : ∀ b ∈ bs, b < n)

include hX hbs huf hu2 in
theorem eq_of_inC {a b : Equiv.Perm (Fin n)} {fa fb : ℕ → ℕ} (hfa : RepF n fa a) (hfb : RepF n fb b)
    {p : ℕ} (ha : InC X uR a p) (hb : InC X uR b p) (h : eqOnL bs fa fb = true) : a = b := by
  unfold InC at ha hb
  split_ifs at ha hb
  · exact eq_of_eqOnL hX hfa hfb ha hb h
  · have h' : eqOnL bs (fun x => uf (fa x)) (fun x => uf (fb x)) = true := by
      rw [eqOnL_iff] at h ⊢
      intro x hx
      rw [h x hx]
    have := eq_of_eqOnL hX (huf.comp hfa) (huf.comp hfb) ha hb h'
    exact mul_left_cancel this

include hnf huf hu2 hN hX hbs in
theorem brel_spec {f F : ℕ} (hF : nfv F = true) (hf : f < 2) {fl xf : List ℕ}
    (hl : fl.length = xf.length) (hxf : ∀ F ∈ xf, nfv F = true) (hfl : ∀ f ∈ fl, f < 2) :
    ∀ {fys Fys cs : List ℕ}, (∀ F ∈ Fys, nfv F = true) → (∀ f ∈ fys, f < 2) →
      brelOK nfp uf bs f F fl xf fys Fys cs = true →
      ∀ y ∈ xsE uR nfE fys Fys, ∃ c, y * xE uR nfE f F = xE uR nfE f F * pcG (xsE uR nfE fl xf) c
  | [], [], [], _, _, _ => by simp [xsE]
  | fy :: fys, Fy :: Fys, c :: cs, hF', hf', h => by
    simp only [brelOK, Bool.and_eq_true] at h
    obtain ⟨⟨hpar, heq⟩, hrest⟩ := h
    intro y hy
    simp only [xsE, List.zipWith_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨c, ?_⟩
      have hFy := hF' Fy List.mem_cons_self
      have hfy := hf' fy List.mem_cons_self
      have hx := repF_xE hnf huf (f := f) hF
      have hy' := repF_xE hnf huf (f := fy) hFy
      have hp := repF_bpcAt hnf huf hl hxf c
      refine eq_of_inC huf hu2 hX hbs (hy'.comp hx) (hx.comp hp) (p := (fy + f) % 2)
        (inC_mul hu2 hN hfy hf (inC_xE hnf hu2 hFy hfy) (inC_xE hnf hu2 hF hf)) ?_ ?_
      · have h1 := inC_mul hu2 hN hf (bpar_lt fl c) (inC_xE hnf hu2 hF hf)
          (inC_pcG hnf hu2 hN hl hxf hfl c)
        rw [Nat.eq_of_beq_eq_true hpar, Nat.add_comm]
        exact h1
      · simpa only [eqB, strictN_val] using heq
    · exact brel_spec hF hf hl hxf hfl (fun G hG => hF' G (List.mem_cons_of_mem Fy hG))
        (fun g hg => hf' g (List.mem_cons_of_mem fy hg)) hrest y hy
  | [], _ :: _, _, _, _, h | [], [], _ :: _, _, _, h | _ :: _, [], _, _, _, h
  | _ :: _, _ :: _, [], _, _, h => by simp [brelOK] at h

include hnf huf hu2 hN hX hbs in
theorem pcRel_of_bpcOK : ∀ {fl xf rs : List ℕ} {cs : List (List ℕ)},
    bpcOK nfv nfp uf bs fl xf rs cs = true → PcRel (xsE uR nfE fl xf)
  | [], [], _, _, _ => by simp [xsE, PcRel]
  | f :: fl, F :: xf, r :: rs, c :: cs, h => by
    have h' := h
    simp only [bpcOK, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨⟨⟨⟨hF, hf⟩, hpar⟩, hsq⟩, hrel⟩, hrest⟩ := h'
    obtain ⟨hl, hxf, hfl⟩ := bpcOK_facts hrest
    have hx := repF_xE hnf huf (f := f) hF
    simp only [xsE, List.zipWith_cons_cons, PcRel]
    refine ⟨⟨r, ?_⟩, brel_spec hnf huf hu2 hN hX hbs hF hf hl hxf hfl hxf hfl hrel,
      pcRel_of_bpcOK hrest⟩
    have hp := repF_bpcAt hnf huf hl hxf r
    refine eq_of_inC huf hu2 hX hbs (hx.comp hx) hp (p := (f + f) % 2)
      (inC_mul hu2 hN hf hf (inC_xE hnf hu2 hF hf) (inC_xE hnf hu2 hF hf)) ?_ ?_
    · have h1 := inC_pcG hnf hu2 hN hl hxf hfl r
      rw [Nat.eq_of_beq_eq_true hpar] at h1
      rw [show (f + f) % 2 = 0 by omega]
      exact h1
    · simpa only [eqB, strictN_val] using hsq
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [bpcOK] at h
  | _ :: _, _ :: _, [], _, h | _ :: _, _ :: _, _ :: _, [], h => by simp [bpcOK] at h

theorem distinct_nodup : ∀ {l : List ℕ}, distinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [distinct, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
      Nat.beq_eq_true_eq] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, distinct_nodup h.2⟩
    have := h.1 a ha
    simp at this

theorem xsE_length (fl xf : List ℕ) (hl : fl.length = xf.length) :
    (xsE uR nfE fl xf).length = fl.length := by
  simp [xsE, hl]

theorem mem_xsE : ∀ {fl xf : List ℕ} {y : Equiv.Perm (Fin n)}, y ∈ xsE uR nfE fl xf →
    ∃ f ∈ fl, ∃ F ∈ xf, y = xE uR nfE f F
  | [], _, _, h => by simp [xsE] at h
  | _ :: _, [], _, h => by simp [xsE] at h
  | f :: fl, F :: xf, y, h => by
    simp only [xsE, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨f, List.mem_cons_self, F, List.mem_cons_self, rfl⟩
    · obtain ⟨g, hg, G, hG, rfl⟩ := mem_xsE h
      exact ⟨g, List.mem_cons_of_mem f hg, G, List.mem_cons_of_mem F hG, rfl⟩

theorem xsE_get {fl xf : List ℕ} (hl : fl.length = xf.length) {k : ℕ} (hk : k < fl.length) :
    (xsE uR nfE fl xf)[k]! = xE uR nfE fl[k]! xf[k]! := by
  have hk' : k < (xsE uR nfE fl xf).length := by rw [xsE_length fl xf hl]; exact hk
  rw [getElem!_pos _ k hk', getElem!_pos _ k hk, getElem!_pos _ k (hl ▸ hk)]
  simp [xsE]

theorem rep_pperm {n w P : ℕ} (hw : n ≤ 2 ^ w) (hc : canonP n w P = true)
    (hv : pvalid n w P = true) (i : Fin n) : (pperm n w P i : ℕ) = at' w P i := by
  have hva : CFSG.RankThree.Native.validA n (unpackP n w P) = true :=
    (CFSG.KC.Census.SP.validA_unpack hw hc).trans hv
  have := CFSG.RankThree.Native.rep_of_validA hva i
  rw [pperm, ← this, CFSG.KC.Census.SP.unpackP_get, if_pos i.2]

include hnf huf hu2 hX hbs in
theorem witness_of_heConjOK (hR : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X) (huR : uR ∈ R)
    (hXR : X ≤ R) {d : HeD} (h : heConjOK n 32 6 bs nfv nfp uf d = true) :
    closure {g | g ∈ xsE uR nfE d.fl d.xf} ≤ R ∧
      Nat.card (closure {g | g ∈ xsE uR nfE d.fl d.xf}) = 2 ^ d.xs.length ∧
      ∀ E ≤ closure {g | g ∈ xsE uR nfE d.fl d.xf}, IsElemAbelian 2 E → 4 ≤ Nat.card E →
        YWitness X E ∨ (UWitness X E ∧ E ≤ X) := by
  have hN : ∀ x ∈ X, uR * x * uR⁻¹ ∈ X := hR uR huR
  simp only [heConjOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ht, hn⟩, hb⟩, hw⟩ := h
  obtain ⟨hrel32, hsep32, hfacts, htree⟩ := tree32_sound (n := 32) (w := 6) (by norm_num)
    (by norm_num) ht hn
  simp only [bridgeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hdl, hdlt⟩, hdist⟩, hfl⟩, hxf⟩, hdelta⟩, hbpc⟩ := hb
  obtain ⟨hl, hnfv, hf2⟩ := bpcOK_facts hbpc
  set xs8 := xsE uR nfE d.fl d.xf with hxs8
  set S := closure {g | g ∈ xs8}
  have hlen8 : xs8.length = d.xs.length := by rw [xsE_length _ _ hl, ← Nat.eq_of_beq_eq_true hfl]
  have hrep8 : ∀ k < d.xs.length, RepF n (xp nfp uf d.fl[k]! d.xf[k]!) xs8[k]! := by
    intro k hk
    have hk' : k < d.fl.length := by rw [Nat.eq_of_beq_eq_true hfl]; exact hk
    rw [xsE_get hl hk']
    refine repF_xE hnf huf (hnfv _ ?_)
    rw [getElem!_pos d.xf k (by rw [← hl]; exact hk')]
    exact List.getElem_mem _
  have hmemR : ∀ y ∈ xs8, y ∈ R := by
    intro y hy
    obtain ⟨f, -, F, hF, rfl⟩ := mem_xsE hy
    refine mul_mem ?_ (hXR (hnf F (hnfv F hF)).1)
    split_ifs
    · exact huR
    · exact one_mem _
  have hSR : S ≤ R := (closure_le R).2 hmemR
  have hrel8 : PcRel xs8 := pcRel_of_bpcOK hnf huf hu2 hN hX hbs hbpc
  have hcard8 : Nat.card S ≤ 2 ^ d.xs.length := by
    have hsurj : ∀ g : S, ∃ m : Fin (2 ^ xs8.length), pcG xs8 m = g := by
      intro g
      obtain ⟨m, hm, hg⟩ := exists_pcG_of_pcRel hrel8 g g.2
      exact ⟨⟨m, hm⟩, hg⟩
    have := Nat.card_le_card_of_surjective (fun m : Fin (2 ^ xs8.length) =>
      (⟨pcG xs8 m, pcG_mem xs8 m⟩ : S)) fun g => by
        obtain ⟨m, hm⟩ := hsurj g
        exact ⟨m, Subtype.ext hm⟩
    rw [Nat.card_eq_fintype_card (α := Fin (2 ^ xs8.length)), Fintype.card_fin, hlen8] at this
    exact this
  have hL : PointsList n 32 d.dl := ⟨Nat.eq_of_beq_eq_true hdl, fun x hx => by
    simpa using hdlt x hx, distinct_nodup hdist⟩
  have hcan := ht
  simp only [tree32OK, canonD, Bool.and_eq_true, List.all_eq_true] at hcan
  have hxsv : ∀ X ∈ d.xs, canonP 32 6 X = true ∧ pvalid 32 6 X = true := fun X hX =>
    Bool.and_eq_true _ _ ▸ hcan.1.1.1.1.1.1.1.1.1.1.1.1.1 X hX
  have hfl' : d.fl.length = d.xs.length := Nat.eq_of_beq_eq_true hfl
  have hxf' : d.xf.length = d.xs.length := Nat.eq_of_beq_eq_true hxf
  have hdk : ∀ k < d.xs.length, deltaOK nfp uf 32 6 d.dl d.xs[k]! d.fl[k]! d.xf[k]! = true := by
    intro k hk
    have := hdelta _ (mem_zip_of_lt hk (by simp [hfl', hxf', hk]))
    rw [getElem!_pos d.xs k hk, getElem!_pos d.fl k (by omega), getElem!_pos d.xf k (by omega)]
    simpa using this
  have hval : ∀ k < d.xs.length, ∀ j < 32, at' 6 d.xs[k]! j < 32 := by
    intro k hk j hj
    have hmk : d.xs[k]! ∈ d.xs := by rw [getElem!_pos d.xs k hk]; exact List.getElem_mem _
    have := rep_pperm (n := 32) (w := 6) (by norm_num) (hxsv _ hmk).1 (hxsv _ hmk).2 ⟨j, hj⟩
    rw [← this]
    exact (pperm 32 6 _ _).2
  have hpt : ∀ k < d.xs.length, ∀ j < 32, ∀ hj : d.dl[j]! < n,
      ((xs8[k]! : Equiv.Perm (Fin n)) ⟨d.dl[j]!, hj⟩ : ℕ) = d.dl[at' 6 d.xs[k]! j]! := by
    intro k hk j hj hjn
    rw [← hrep8 k hk _ hjn]
    have := (List.all_eq_true.1 (hdk k hk)) j (List.mem_range.2 hj)
    rw [Nat.beq_eq] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    rw [getElem!_pos d.dl j (by rw [Nat.eq_of_beq_eq_true hdl]; exact hj),
      getElem!_pos d.dl _ (by rw [Nat.eq_of_beq_eq_true hdl]; exact hval k hk j hj)]
    rw [List.getElem?_eq_getElem (by rw [Nat.eq_of_beq_eq_true hdl]; exact hj),
      List.getElem?_eq_getElem (by rw [Nat.eq_of_beq_eq_true hdl]; exact hval k hk j hj)] at this
    exact this
  have hdlen : d.dl.length = 32 := Nat.eq_of_beq_eq_true hdl
  have hgen8 : ∀ y ∈ xs8, ∃ k < d.xs.length, y = xs8[k]! := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    exact ⟨k, hlen8 ▸ hk, (getElem!_pos xs8 k hk).symm⟩
  have hpres : ∀ g ∈ S, ∀ x : Fin n, (x : ℕ) ∈ d.dl → (g x : ℕ) ∈ d.dl := by
    intro g hg x hx
    have hF : ({x : Fin n | (x : ℕ) ∈ d.dl} : Set (Fin n)).Finite := Set.toFinite _
    refine CFSG.Perm.smul_mem_of_finite_of_mem_closure hF (x := x) (g := g) ?_ hg hx
    intro y hy z hz
    obtain ⟨k, hk, rfl⟩ := hgen8 y hy
    obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem (show (z : ℕ) ∈ d.dl from hz)
    have hj32 : j < 32 := hdlen ▸ hj
    have hz' : z = ⟨d.dl[j]!, by rw [getElem!_pos d.dl j hj, hjz]; exact z.2⟩ :=
      Fin.ext (by
        change (z : ℕ) = d.dl[j]!
        rw [getElem!_pos d.dl j hj, hjz])
    change ((xs8[k]! : Equiv.Perm (Fin n)) z : ℕ) ∈ d.dl
    rw [hz', hpt k hk j hj32, getElem!_pos d.dl _ (by rw [hdlen]; exact hval k hk j hj32)]
    exact List.getElem_mem _
  let ρ := hL.restrHom S hpres
  have hρx : ∀ k (hk : k < d.xs.length),
      ρ ⟨xs8[k]!, subset_closure (by
        rw [getElem!_pos xs8 k (hlen8 ▸ hk)]; exact List.getElem_mem _)⟩ =
        pperm 32 6 d.xs[k]! := by
    intro k hk
    have hgS : xs8[k]! ∈ S := subset_closure (by
      rw [getElem!_pos xs8 k (hlen8 ▸ hk)]; exact List.getElem_mem _)
    change hL.restrPerm (xs8[k]!) (PointsList.mem_iff_of_mem S hpres hgS) = _
    refine (hL.restrPerm_eq_iff _ _ _).2 fun i => Fin.ext ?_
    have hmk : d.xs[k]! ∈ d.xs := by rw [getElem!_pos d.xs k hk]; exact List.getElem_mem _
    have hpti : ∀ j : Fin 32, (hL.pt j : ℕ) = d.dl[j.val]! := fun j => by
      rw [hL.pt_val, getElem!_pos d.dl _ _]
    have e : hL.pt i = ⟨d.dl[i.val]!, by rw [← hpti i]; exact (hL.pt i).2⟩ := Fin.ext (hpti i)
    have h1 := hpt k hk i.val i.2 (by rw [← hpti i]; exact (hL.pt i).2)
    rw [hpti, rep_pperm (by norm_num) (hxsv _ hmk).1 (hxsv _ hmk).2, ← h1, ← e]
  set S32 := closure {g | g ∈ d.xs.map (pperm 32 6)}
  have hcard32 : Nat.card S32 = 2 ^ d.xs.length := by
    rw [card_closure_of_pc hrel32 hsep32, List.length_map]
  have hS32 : S32 ≤ ρ.range := by
    rw [closure_le]
    intro g hg
    obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨k, hk, hkX⟩ := List.getElem_of_mem hX0
    refine ⟨_, hρx k hk |>.trans ?_⟩
    rw [getElem!_pos d.xs k hk, hkX]
  have hrange : Nat.card ρ.range ≤ Nat.card S :=
    Nat.card_le_card_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hcS : Nat.card S = 2 ^ d.xs.length := by
    have := card_le_of_le hS32
    omega
  have hcR : Nat.card ρ.range = Nat.card S := by
    have := card_le_of_le hS32
    omega
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← card_eq_one]
    have h1 := card_ker_mul_card_range ρ
    rw [hcR] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have hrng : ρ.range = S32 := (eq_of_le_of_card_ge hS32 (by omega)).symm
  let xsS : List S := xs8.attach.map fun y => ⟨y.1, subset_closure y.2⟩
  have hxsS : xsS.map S.subtype = xs8 := by
    exact List.ext_getElem (by simp [xsS]) fun k _ _ => by simp [xsS]
  have hxsρ : xsS.map ρ = d.xs.map (pperm 32 6) := by
    refine List.ext_getElem (by simp [xsS, hlen8]) fun k h1 h2 => ?_
    have hk : k < d.xs.length := by simpa using h2
    simp only [xsS, List.getElem_map, List.getElem_attach]
    have := hρx k hk
    rw [getElem!_pos d.xs k hk] at this
    rw [← this]
    congr 2
    exact (getElem!_pos xs8 k (hlen8 ▸ hk)).symm
  have hnodeS : ∀ bm : List ℕ, (nodeH xsS bm).map S.subtype = nodeH xs8 bm := fun bm => by
    rw [nodeH_map, hxsS]
  have hnodeρ : ∀ bm : List ℕ, (nodeH xsS bm).map ρ = nodeH (d.xs.map (pperm 32 6)) bm :=
    fun bm => by rw [nodeH_map, hxsρ]
  have hconjX : ∀ s ∈ S, X.map (MulAut.conj s).toMonoidHom = X := by
    intro s hs
    refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hR s (hSR hs) x hx
    · simpa using hR s⁻¹ (R.inv_mem (hSR hs)) x hx
    · simp [MulAut.conj_apply, mul_assoc]
  refine ⟨hSR, hcS, fun E hES hE hE4 => ?_⟩
  set ES := E.subgroupOf S
  have hESmap : ES.map S.subtype = E := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hES]
  have hcardES : Nat.card ES = Nat.card E := by
    rw [← card_map_of_injective S.subtype_injective, hESmap]
  have hEab : IsElemAbelian 2 ES := CFSG.Open.IsElemAbelian.subgroupOf hE S
  have hE32 : ES.map ρ ≤ S32 := hrng ▸ map_le_range ρ ES
  obtain ⟨i, hi, s', hs', hle, halt⟩ := htree (ES.map ρ) hE32 (hEab.map ρ)
    (by rwa [card_map_of_injective hinj, hcardES])
  obtain ⟨s, rfl⟩ : s' ∈ ρ.range := by rw [hrng]; exact hs'
  set N8 := nodeH xs8 d.nm[i]!
  set NS := nodeH xsS d.nm[i]!
  have hNS : NS.map S.subtype = N8 := hnodeS _
  have hconjS : (NS.map (MulAut.conj s).toMonoidHom).map ρ =
      (nodeH (d.xs.map (pperm 32 6)) d.nm[i]!).map (MulAut.conj (ρ s)).toMonoidHom := by
    rw [← hnodeρ, map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hleS : NS.map (MulAut.conj s).toMonoidHom ≤ ES := by
    rw [← map_le_map_iff_of_injective hinj, hconjS]
    exact hle
  have hmapS : ∀ K : Subgroup S, (K.map (MulAut.conj s).toMonoidHom).map S.subtype =
      (K.map S.subtype).map (MulAut.conj (s : Equiv.Perm (Fin n))).toMonoidHom := by
    intro K
    rw [map_map, map_map]
    rfl
  have hle8 : N8.map (MulAut.conj (s : Equiv.Perm (Fin n))).toMonoidHom ≤ E := by
    rw [← hNS, ← hmapS, ← hESmap]
    exact map_mono hleS
  have hN8ab : IsElemAbelian 2 N8 := isElemAbelian_of_map_le hle8 hE
  have hf8 : (d.wits[i]!).facts xs8 N8 := by
    have h1 := (hfacts i hi).1
    rw [← hnodeρ, ← hxsρ] at h1
    have h2 := facts_of_map ρ hinj xsS NS _ h1
    have h3 := facts_map S.subtype S.subtype_injective xsS NS _ h2
    rwa [hNS, hxsS] at h3
  have hwi : hwOK nfv nfp uf bs d.fl d.xf d.nm[i]! d.wits[i]! = true := by
    have := List.all_eq_true.1 hw i (List.mem_range.2 hi)
    exact this
  obtain ⟨hmono, hclos⟩ := hwOK_sound hX hbs (fun F hF => ⟨nfE F, (hnf F hF).1, (hnf F hF).2⟩)
    (hfl'.trans hlen8.symm) (hxf'.trans hlen8.symm) (fun k hk => hrep8 k (hlen8 ▸ hk))
    (fun y hy x hx => hR y (hmemR y hy) x hx) hwi hN8ab hf8
  have hsR : (s : Equiv.Perm (Fin n)) ∈ R := hSR s.2
  set ι := (MulAut.conj (s : Equiv.Perm (Fin n))).toMonoidHom
  have hι : Function.Injective ι := (MulAut.conj _).injective
  rcases halt with hm | ⟨hc, heq⟩
  · obtain ⟨y, hy, h4⟩ := hmono hm
    refine Or.inl (yWitness_of_le_of_orderOf hle8 ⟨ι y, ?_, ?_⟩)
    · have := mem_map_of_mem ι hy
      rwa [map_nE ι hι, hconjX _ s.2] at this
    · rwa [orderOf_injective ι hι]
  ·
    have heq8 : N8.map ι = E := by
      refine le_antisymm hle8 ?_
      have h1 : (NS.map (MulAut.conj s).toMonoidHom).map ρ = ES.map ρ := by rw [hconjS]; exact heq
      have h2 := map_injective hinj h1
      rw [← hESmap, ← h2, hmapS, hNS]
    have hN8X : N8 ≤ X := by
      change closure {g | ∃ m ∈ d.nm[i]!, g = pcG xs8 m} ≤ X
      rw [closure_le]
      rintro _ ⟨m, hm, rfl⟩
      have h0 := (hfacts i hi).2 hc m hm
      have := inC_pcG hnf hu2 hN hl hnfv hf2 m
      rw [h0] at this
      simpa [InC] using this
    obtain hU := hclos hc hN8X
    refine Or.inr ⟨?_, ?_⟩
    · rw [← heq8, ← hconjX _ s.2]
      exact (uWitness_map_iff ι hι X N8).2 hU
    · rw [← heq8, ← hconjX _ s.2]
      exact map_mono hN8X

end Generic

section He

open CFSG.Sporadic.HeldB CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native

variable
  {d : HeD} {U w kS BP NS CH NR NL NT BT NQ BQ : ℕ} {PS PSI LR Ts LT PT QT : ℕ → ℕ}

theorem witness_he_of_heConjOK (hU : heUArr = unpack 8330 14 U)
    (hT : TabChain 8330 w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT heStrongArrs
      heBase.toArray heBase) (hlen : d.xs.length = 11)
    (h : heConjOK 8330 32 6 heBase (nfValidK 5 LR) (nfPtT w NR NL LT PT 5) (pg 14 (mask 14) U) d =
      true) :
    ∃ S : Subgroup ↥heAutGroup, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (heP.subgroupOf heAutGroup) E ∨
        (UWitness (heP.subgroupOf heAutGroup) E ∧ E ≤ heP.subgroupOf heAutGroup) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnf : ∀ F, nfValidK 5 LR F = true →
      nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 F) ∈ heP ∧
        RepF 8330 (nfPtT w NR NL LT PT 5 F) (nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 F)) :=
    fun F hF => ⟨heP_eq_originalSubgroup ▸ nfElt_mem heChainArrays
      (chainCheckFacts heChain_check.1) heChain_valid.1 (nfPtT_sound hT hF).1,
      (nfPtT_sound hT hF).2⟩
  have huf : RepF 8330 (pg 14 (mask 14) U) heAutU := by
    intro x hx
    have := rep_heU ⟨x, hx⟩
    rw [hU, unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn] at this
    exact this
  have hu2 : heAutU * heAutU = 1 := by
    rw [← sq, ← orderOf_heAutU, pow_orderOf_eq_one]
  have hR : ∀ r ∈ heAutGroup, ∀ x ∈ heP, r * x * r⁻¹ ∈ heP := fun r hr x hx =>
    (mem_normalizer_iff.1 (heAutGroup_le_normalizer hr) x).1 hx
  have hX : BaseFaithful heP heBase := by
    have := he_baseFaithful
    rw [← heP_eq_originalSubgroup] at this
    exact this
  obtain ⟨hSR, hcS, hw⟩ := witness_of_heConjOK hnf huf hu2 hX (by decide) hR
    heAutU_mem_heAutGroup heP_le_heAutGroup h
  set S' := closure {g | g ∈ xsE heAutU (fun F => nfElt 8330 heStrongArrs heBase.toArray
    (nfArr 5 F)) d.fl d.xf}
  have hS'le : S' ≤ heAutGroup.subtype.range := by rwa [range_subtype]
  set S := S'.comap heAutGroup.subtype
  have hSmap : S.map heAutGroup.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ 11 := by
    rw [← card_map_of_injective heAutGroup.subtype_injective, hSmap, hcS, hlen]
  have hmap : (heP.subgroupOf heAutGroup).map heAutGroup.subtype = heP := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr heP_le_heAutGroup]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, card_heAutGroup, show (8060774400 : ℕ) = 2 ^ 11 * 3935925 by norm_num] at h1
    have hidx : S.index = 3935925 := Nat.eq_of_mul_eq_mul_left (by norm_num) h1
    rw [hidx] at h2
    exact absurd h2 (by decide)
  · have hES' : E.map heAutGroup.subtype ≤ S' := hSmap ▸ map_mono hES
    rcases hw _ hES' (isElemAbelian_map hE _)
        (by rwa [card_map_of_injective heAutGroup.subtype_injective]) with hY | ⟨hU', hle⟩
    · left
      rw [← hmap] at hY
      exact (yWitness_map_iff _ heAutGroup.subtype_injective _ _).mp hY
    · right
      rw [← hmap] at hU' hle
      exact ⟨(uWitness_map_iff _ heAutGroup.subtype_injective _ _).mp hU',
        (map_le_map_iff_of_injective heAutGroup.subtype_injective).mp hle⟩

theorem he_yCensusII_of_heConjOK (hU : heUArr = unpack 8330 14 U)
    (hT : TabChain 8330 w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT heStrongArrs
      heBase.toArray heBase) (hlen : d.xs.length = 11)
    (h : heConjOK 8330 32 6 heBase (nfValidK 5 LR) (nfPtT w NR NL LT PT 5) (pg 14 (mask 14) U) d =
      true) :
    YCensus (heP.subgroupOf heAutGroup) (· ≤ heP.subgroupOf heAutGroup) := by
  obtain ⟨S, hS, hw⟩ := witness_he_of_heConjOK hU hT hlen h
  refine yCensus_of_le_sylow heP_normal_heAutGroup hS (fun E w hle x hx => ?_)
    fun E hES hE hE4 hnot => ?_
  · have hx' : w * x * w⁻¹ ∈ heP.subgroupOf heAutGroup := hle ⟨x, hx, rfl⟩
    have := heP_normal_heAutGroup.conj_mem _ hx' w⁻¹
    simpa [mul_assoc] using this
  · rcases hw E hES hE hE4 with h | ⟨-, h⟩
    · exact h
    · exact absurd h hnot

theorem he_yCensus17U_of_heConjOK (hU : heUArr = unpack 8330 14 U)
    (hT : TabChain 8330 w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT heStrongArrs
      heBase.toArray heBase) (hlen : d.xs.length = 11)
    (h : heConjOK 8330 32 6 heBase (nfValidK 5 LR) (nfPtT w NR NL LT PT 5) (pg 14 (mask 14) U) d =
      true) :
    YCensus17U (heP.subgroupOf heAutGroup) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_he_of_heConjOK hU hT hlen h
  refine yCensus17U_of_le_sylow heP_normal_heAutGroup hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

end He

end CFSG.KC.HeConj

end
