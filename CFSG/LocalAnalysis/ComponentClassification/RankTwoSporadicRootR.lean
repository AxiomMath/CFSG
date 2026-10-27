module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjT
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.Certificates.Kernel.Census.PerfSound
public import CFSG.Certificates.Kernel.Census.RestrictSound
public import CFSG.Certificates.Kernel.Census.ToMainConj
public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.RootR

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Census CFSG.KC.Census.Base CFSG.KC.Census.Restrict
open scoped commutatorElement

@[expose] noncomputable def rootTreeR (n w h : ℕ) (L : ℕ → ℕ) (bs : List ℕ) (m wr : ℕ)
    (r : RootR) : Bool :=
  conjTreeOKW m r.ps (fun a => eqA m a (idA m)) (r.d.toMain m wr) #[] &&
    r.ps.all (fun p => Nat.blt p m) &&
    (List.range m).all (fun q => Nat.blt (at' w r.O q) n && Nat.beq (at' wr r.ix (at' w r.O q)) q) &&
    Nat.beq r.xw.length r.d.xs.length && r.xw.all (fun x => x.all fun k => Nat.blt k (2 * h)) &&
    pcRelB w L bs r.xw r.d.rs r.d.cjs &&
    (r.xw.zip r.d.xs).all (fun p => resB w L wr m r.O r.ix p.1 p.2)

@[expose] noncomputable def rootClsR (w : ℕ) (L : ℕ → ℕ) (bs : List ℕ) (m wr : ℕ) (r : RootR) :
    Bool :=
  Nat.beq r.mb.length r.d.nodes.size && Nat.beq r.mxb.length r.d.nodes.size &&
    (List.range r.d.nodes.size).all fun j =>
      Nat.beq r.d.nodes[j]!.basis.size 1 &&
      eqA m (unpackP m wr r.d.nodes[j]!.basis[0]!) (pcA m (r.d.xs.map (unpackP m wr)) (r.mb.getD j 0)) &&
      bs.any (fun b => !(Nat.beq (pcwPt w L r.xw (r.mb.getD j 0) b) b)) &&
      bs.all (fun b => Nat.beq (pcwPt w L r.xw (r.mxb.getD j 0) b)
        (pcwPt w L r.xw r.mx (pcwPt w L r.xw (r.mb.getD j 0) b)))

@[expose] noncomputable def rootCheckR (n w h : ℕ) (L : ℕ → ℕ) (bs : List ℕ) (m wr : ℕ)
    (pxs : List ℕ) (i : ℕ) (r : RootR) : Bool :=
  rootTreeR n w h L bs m wr r && rootXR w L bs (pxs.getD i 0) r && rootClsR w L bs m wr r &&
    rootLeafR w h L bs pxs i r

theorem map_pcG {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    ∀ (l : List G) (m : ℕ), φ (pcG l m) = pcG (l.map φ) m
  | [], _ => map_one φ
  | x :: l, m => by
    rw [pcG, List.map_cons, pcG, map_mul, map_pcG φ l (m / 2)]
    split_ifs
    · rfl
    · rw [map_one]

theorem map_conj_self {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {v : Equiv.Perm (Fin n)}
    (hv : v ∈ P) : P.map (MulAut.conj v).toMonoidHom = P := by
  refine le_antisymm ?_ fun x hx => ⟨v⁻¹ * x * v, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hv hx) (inv_mem hv)
  · exact mul_mem (mul_mem (inv_mem hv) hx) hv
  · simp [MulAut.conj_apply, mul_assoc]

variable {n w h : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)} {bs : List ℕ}
  {P : Subgroup (Equiv.Perm (Fin n))}

set_option maxHeartbeats 1000000 in
theorem root_of_rootCheckR (hB : BaseOf P bs) (HL : Letters n w h L ℓ)
    (hℓ : ∀ k < 2 * h, ℓ k ∈ P) {m wr : ℕ} {pxs : List ℕ} {i : ℕ}
    {X₀ : ℕ → Equiv.Perm (Fin n)}
    (hX₀ : ∀ j ≤ i, ∀ p (hp : p < n), at' w (pxs.getD j 0) p = (X₀ j ⟨p, hp⟩ : ℕ))
    (hX₀P : ∀ j ≤ i, X₀ j ∈ P) {r : RootR} (h : rootCheckR n w h L bs m wr pxs i r = true) :
    ∃ T : Subgroup (Equiv.Perm (Fin n)), T ≤ P ⊓ centralizer {X₀ i} ∧
      Nat.card T = 2 ^ r.d.xs.length ∧
      ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ X₀ i →
        MonoW P true (closure {X₀ i, b}) ∨
          ∃ j < i, ∃ g ∈ P, g * b * g⁻¹ = X₀ j ∨ g * (X₀ i * b) * g⁻¹ = X₀ j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rootCheckR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨htr, hxr⟩, hcl⟩, hlf⟩ := h
  unfold rootTreeR at htr
  simp only [Bool.and_eq_true] at htr
  obtain ⟨⟨⟨⟨⟨⟨htree, hps⟩, hpts⟩, hxwl⟩, hxwk⟩, hrel⟩, hres⟩ := htr
  have hbn : ∀ b ∈ bs, b < n := hB.1
  have hps' : ∀ p ∈ r.ps, p < m := fun p hp => Nat.blt_eq.mp (List.all_eq_true.1 hps p hp)
  have hxwl' : r.xw.length = r.d.xs.length := Nat.eq_of_beq_eq_true hxwl
  have hwok : ∀ x : List ℕ, (x.all fun k => Nat.blt k (2 * h)) = true → WordOK h x :=
    fun x hx k hk => Nat.blt_eq.mp (List.all_eq_true.1 hx k hk)
  have hxw : ∀ x ∈ r.xw, WordOK h x := fun x hx => hwok x (List.all_eq_true.1 hxwk x hx)
  obtain ⟨X, hXdef⟩ : ∃ X, X = r.xw.map (wordPerm ℓ) := ⟨_, rfl⟩
  have hXl : X.length = r.d.xs.length := by rw [hXdef, List.length_map, hxwl']
  have hXP : ∀ g ∈ X, g ∈ P := fun g hg => by
    rw [hXdef] at hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    exact wordPerm_mem HL hℓ (hxw x hx)
  have hpcP : ∀ k, pcG X k ∈ P := pcG_mem_of hXP
  have hpcw : ∀ k p (hp : p < n), pcwPt w L r.xw k p = (pcG X k ⟨p, hp⟩ : ℕ) := fun k p hp => by
    rw [hXdef]
    exact pcwPt_eq HL r.xw hxw k p hp
  have hrelX : PcRel X := hXdef ▸ pcRel_of_pcRelB HL hB hℓ r.xw r.d.rs r.d.cjs hxw hrel
  obtain ⟨S4, hS4def⟩ : ∃ S4 : Subgroup (Equiv.Perm (Fin n)), S4 = closure {a | a ∈ X} :=
    ⟨_, rfl⟩
  have hS4P : S4 ≤ P := hS4def ▸ (closure_le P).2 fun g hg => hXP g hg
  obtain ⟨xsU, hxsU⟩ : ∃ xsU, xsU = r.d.xs.map (unpackP m wr) := ⟨_, rfl⟩
  have htm : (r.d.toMain m wr).xs = xsU := by rw [hxsU]; rfl
  obtain ⟨hxv, hrelU, hsepU⟩ := pc_of_conjTreeOKW htree
  rw [htm] at hxv hrelU hsepU
  obtain ⟨S', hS'def⟩ : ∃ S', S' = pcSub m xsU := ⟨_, rfl⟩
  have hS'card : Nat.card S' = 2 ^ r.d.xs.length := by
    rw [hS'def, pcSub, card_closure_of_pc hrelU hsepU, List.length_map, hxsU, List.length_map]
  have hroots := roots_of_conjTreeOKW htree
  rw [htm, ← hS'def] at hroots
  have hpt : ∀ q < m, at' w r.O q < n ∧ at' wr r.ix (at' w r.O q) = q := by
    intro q hq
    have := List.all_eq_true.1 hpts q (List.mem_range.2 hq)
    simp only [Bool.and_eq_true] at this
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩
  let Of : Fin m → Fin n := fun q => ⟨at' w r.O q, (hpt q q.2).1⟩
  have hOf : Function.Injective Of := fun a b hab => by
    have := congrArg (fun x : Fin n => at' wr r.ix x.val) hab
    simp only [Of, (hpt a a.2).2, (hpt b b.2).2] at this
    exact Fin.ext this
  have hgen : ∀ j (hj : j < r.d.xs.length), ∃ hs : wordPerm ℓ r.xw[j] ∈ stab Of,
      resHom hOf ⟨_, hs⟩ = permOfArr m (unpackP m wr r.d.xs[j]) := by
    intro j hj
    have hj1 : j < r.xw.length := by omega
    have hr := List.all_eq_true.1 hres (r.xw[j], r.d.xs[j]) (mem_zip_of_lt hj1 hj)
    unfold resB at hr
    have hv := hxv _ (by rw [hxsU]; exact List.mem_map_of_mem (List.getElem_mem hj))
    have hlt : ∀ q : Fin m, at' wr r.d.xs[j] q < m := by
      intro q
      have h1 := (rep_of_validA hv).lt q.2
      rw [SP.unpackP_get, if_pos q.2] at h1
      exact h1
    have hq : ∀ q : Fin m, (wordPerm ℓ r.xw[j]) (Of q) = Of ⟨at' wr r.d.xs[j] q, hlt q⟩ := by
      intro q
      have hq := List.all_eq_true.1 hr q.val (List.mem_range.2 q.2)
      simp only [Bool.and_eq_true] at hq
      have hw := wPt_eq HL r.xw[j] (hxw _ (List.getElem_mem hj1)) _ (hpt q q.2).1
      rw [hw] at hq
      apply Fin.ext
      change _ = at' w r.O (at' wr r.d.xs[j] q)
      rw [Nat.eq_of_beq_eq_true hq.2]
      exact (Nat.eq_of_beq_eq_true hq.1).symm
    have hs : wordPerm ℓ r.xw[j] ∈ stab Of := mem_stab_of_maps hOf fun q => ⟨_, hq q⟩
    refine ⟨hs, resHom_eq hOf fun q => ?_⟩
    have hrep := rep_of_validA hv
    rw [hq q]
    congr 1
    apply Fin.ext
    rw [← hrep.apply q.2, SP.unpackP_get, if_pos q.2]
  have hmemX : ∀ j (hj : j < r.xw.length), wordPerm ℓ r.xw[j] ∈ S4 := fun j hj => by
    have hx : wordPerm ℓ r.xw[j] ∈ X := by
      rw [hXdef]
      exact List.mem_map_of_mem (List.getElem_mem _)
    rw [hS4def]
    exact subset_closure hx
  have hS4stab : S4 ≤ stab Of := by
    rw [hS4def, closure_le]
    intro g hg
    rw [Set.mem_setOf_eq, hXdef] at hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_map]
    exact (hgen j (by simp at hj; omega)).1
  let f : ↥S4 →* Equiv.Perm (Fin m) := (resHom hOf).comp (inclusion hS4stab)
  let XW : List ↥S4 := List.ofFn (n := r.d.xs.length) fun j => ⟨_, hmemX j.1 (by omega)⟩
  have hXW : XW.map S4.subtype = X := by
    rw [hXdef]
    apply List.ext_getElem
    · simp [XW, hxwl']
    · intro i h1 h2
      simp only [XW, List.getElem_map, List.getElem_ofFn]
      rfl
  have hfXW : XW.map f = xsU.map (permOfArr m) := by
    apply List.ext_getElem
    · simp [XW, hxsU]
    · intro i h1 h2
      have hi : i < r.d.xs.length := by simpa [XW] using h1
      simp only [XW, List.getElem_map, List.getElem_ofFn]
      have e : f ⟨_, hmemX i (by omega)⟩ = permOfArr m (unpackP m wr r.d.xs[i]) := (hgen i hi).2
      rw [e]
      simp [hxsU]
  have hpcS : ∀ k, pcG X k = ((pcG XW k : ↥S4) : Equiv.Perm (Fin n)) := fun k => by
    rw [← hXW]
    exact (map_pcG S4.subtype XW k).symm
  have hfpc : ∀ k, f (pcG XW k) = pcG (xsU.map (permOfArr m)) k := fun k => by
    rw [map_pcG, hfXW]
  have hXWgen : closure {a | a ∈ XW} = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨k, -, hk⟩ := exists_pcG_of_pcRel hrelX g (hS4def ▸ g.2)
    have : g = pcG XW k := Subtype.ext (by rw [← hpcS, hk])
    rw [this]
    exact pcG_mem XW k
  have hrange : f.range = S' := by
    rw [MonoidHom.range_eq_map, ← hXWgen, MonoidHom.map_closure, hS'def, pcSub, ← hfXW]
    congr 1
    ext b
    simp
  have hcardS4 : Nat.card ↥S4 ≤ 2 ^ r.d.xs.length := by
    have hsurj : Function.Surjective
        (fun k : Fin (2 ^ r.d.xs.length) => (pcG XW k : ↥S4)) := by
      intro g
      obtain ⟨k, hk, he⟩ := exists_pcG_of_pcRel hrelX g (hS4def ▸ g.2)
      exact ⟨⟨k, hXl ▸ hk⟩, Subtype.ext (by rw [← hpcS]; exact he)⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  have hinj : Function.Injective f :=
    injective_of_card_le_range f (by rw [hrange, hS'card]; exact hcardS4)
  have hS4card : Nat.card ↥S4 = 2 ^ r.d.xs.length := by
    have := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥S4)) (f := f) hinj
    rw [← MonoidHom.range_eq_map, hrange, hS'card, card_top] at this
    exact this.symm
  unfold rootXR at hxr
  simp only [Bool.and_eq_true, List.all_eq_true] at hxr
  obtain ⟨⟨hxb, hx1⟩, hxc⟩ := hxr
  have hX0 : pcG X r.mx = X₀ i := by
    refine eq_of_base hB (hpcP _) (hX₀P i le_rfl) fun b hb hbs => ?_
    have e := Nat.eq_of_beq_eq_true (hxb b hbs)
    rwa [hpcw _ b hb, hX₀ i le_rfl b hb] at e
  have hS4C : S4 ≤ P ⊓ centralizer {X₀ i} := by
    rw [hS4def, closure_le]
    intro g hg
    refine ⟨hXP g hg, mem_centralizer_singleton_iff.2 ?_⟩
    rw [Set.mem_setOf_eq, hXdef] at hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    rw [← hX0]
    refine eq_of_base hB (P.mul_mem (hXP _ (hXdef ▸ List.mem_map_of_mem hx)) (hpcP _))
      (P.mul_mem (hpcP _) (hXP _ (hXdef ▸ List.mem_map_of_mem hx))) fun b hb hbs => ?_
    have e := Nat.eq_of_beq_eq_true (hxc x hx b hbs)
    rw [wPt_eq HL x (hxw x hx) b hb, hpcw _ _ (Fin.isLt _), hpcw _ b hb,
      wPt_eq HL x (hxw x hx) _ (Fin.isLt _)] at e
    simpa [Equiv.Perm.mul_apply] using e.symm
  refine ⟨S4, hS4C, hS4card, fun b hb hb2 hb1 hbx => ?_⟩
  set b4 : ↥S4 := ⟨b, hb⟩
  have hfb2 : f b4 ^ 2 = 1 := by
    rw [← map_pow]
    have : b4 ^ 2 = 1 := Subtype.ext (by simpa [b4] using hb2)
    rw [this, map_one]
  have hfb1 : f b4 ≠ 1 := fun h1 => hb1 (by
    have := hinj (h1.trans (map_one f).symm)
    simpa [b4] using congrArg Subtype.val this)
  have hfbS : f b4 ∈ S' := hrange ▸ ⟨b4, rfl⟩
  obtain ⟨j, hj, s', hs', hsb⟩ := hroots _ hfbS hfb2 hfb1
  have hnodes : (r.d.toMain m wr).nodes = r.d.nodes.map (NodeP.toMain m wr) := rfl
  have hj' : j < r.d.nodes.size := by simpa [hnodes] using hj
  unfold rootClsR at hcl
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hcl
  obtain ⟨⟨hmbl, hmxbl⟩, hcls⟩ := hcl
  obtain ⟨⟨⟨hb1s, hbas⟩, hbmv⟩, hxbj⟩ := hcls j hj'
  have hbasis : (r.d.toMain m wr).nodes[j]!.basis = r.d.nodes[j]!.basis.map (unpackP m wr) := by
    rw [hnodes, SP.map_get _ _ hj']
    rfl
  have hbsz : (r.d.toMain m wr).nodes[j]!.basis.size = 1 := by
    rw [hbasis, Array.size_map]
    exact Nat.eq_of_beq_eq_true hb1s
  set B := pcG X (r.mb.getD j 0) with hBdef
  have hBP : B ∈ P := hpcP _
  have hB1 : B ≠ 1 := by
    intro h1
    obtain ⟨b', hb', hbm⟩ := List.any_eq_true.1 hbmv
    rw [hpcw _ b' (hbn b' hb'), ← hBdef, h1, Equiv.Perm.one_apply] at hbm
    simp at hbm
  have hrepB : Rep m (r.d.toMain m wr).nodes[j]!.basis[0]! (f (pcG XW (r.mb.getD j 0))) := by
    rw [hfpc, hbasis, SP.map_get _ _ (by rw [Nat.eq_of_beq_eq_true hb1s]; norm_num)]
    exact rep_of_eqA (rep_pcA hxv _) (by
      unfold eqA at hbas ⊢
      rw [allLt_iff] at hbas ⊢
      intro x hx
      have := hbas x hx
      rw [beq_iff_eq] at this ⊢
      rw [hxsU]
      exact this.symm)
  obtain ⟨s4, rfl⟩ : ∃ s4, f s4 = s' := by
    rw [← hrange] at hs'
    exact hs'
  have hBs : pcG XW (r.mb.getD j 0) = s4 * b4 * s4⁻¹ := by
    rcases hsb 0 (by rw [hbsz]; norm_num) _ hrepB with he | he
    · apply hinj
      rw [he, map_mul, map_mul, map_inv]
    · exfalso
      apply hB1
      rw [hBdef, hpcS, (map_eq_one_iff f hinj).1 he]
      rfl
  have hBs' : B = (s4 : Equiv.Perm (Fin n)) * b * (s4 : Equiv.Perm (Fin n))⁻¹ := by
    rw [hBdef, hpcS, hBs]
    rfl
  have hs4P : (s4 : Equiv.Perm (Fin n)) ∈ P := hS4P s4.2
  have hs4x : (s4 : Equiv.Perm (Fin n)) * X₀ i * (s4 : Equiv.Perm (Fin n))⁻¹ = X₀ i := by
    rw [mem_centralizer_singleton_iff.1 (hS4C s4.2).2, mul_assoc, mul_inv_cancel, mul_one]
  have hXB : pcG X (r.mxb.getD j 0) = X₀ i * B := by
    refine eq_of_base hB (hpcP _) (P.mul_mem (hX₀P i le_rfl) hBP) fun b' hb' hbs => ?_
    have e := Nat.eq_of_beq_eq_true (hxbj b' hbs)
    rw [hpcw _ b' hb', hpcw _ b' hb', hpcw _ _ (Fin.isLt _), hX0] at e
    simpa [Equiv.Perm.mul_apply, hBdef] using e
  set σ := (MulAut.conj (s4 : Equiv.Perm (Fin n))).toMonoidHom
  have hσ : Function.Injective σ := (MulAut.conj (s4 : Equiv.Perm (Fin n))).injective
  have hmap : closure ({X₀ i, B} : Set (Equiv.Perm (Fin n))) =
      (closure ({X₀ i, b} : Set (Equiv.Perm (Fin n)))).map σ := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [σ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs4x, hBs']
  have hmono : MonoW P true (closure {X₀ i, B}) → MonoW P true (closure {X₀ i, b}) := by
    intro hM
    rw [hmap, ← map_conj_self hs4P] at hM
    exact (monoW_map_iff σ hσ P _ true).1 hM
  have hxE : X₀ i ∈ closure ({X₀ i, B} : Set (Equiv.Perm (Fin n))) :=
    subset_closure (Set.mem_insert _ _)
  have hBE : B ∈ closure ({X₀ i, B} : Set (Equiv.Perm (Fin n))) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hpair : ∀ e, inPair r j e = true → pcG X e ∈ closure ({X₀ i, B} : Set (Equiv.Perm (Fin n))) := by
    intro e he
    simp only [inPair, Bool.or_eq_true] at he
    rcases he with (he | he) | he
    · rw [Nat.eq_of_beq_eq_true he, hX0]
      exact hxE
    · rw [Nat.eq_of_beq_eq_true he]
      exact hBE
    · rw [Nat.eq_of_beq_eq_true he, hXB]
      exact mul_mem hxE hBE
  unfold rootLeafR at hlf
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hlf
  obtain ⟨⟨⟨⟨hcov, hwits⟩, hskips⟩, hperfs⟩, hperfB⟩ := hlf
  have hc := hcov j hj'
  simp only [Bool.or_eq_true, List.any_eq_true] at hc
  rcases hc with ((hself | ⟨t, ht, htj⟩) | ⟨s, hs, hsj⟩) | ⟨pf, hpf, hpfj⟩
  ·
    exfalso
    apply hbx
    have hBm : r.mb.getD j 0 = r.mx := Nat.eq_of_beq_eq_true hself
    have e : B = X₀ i := by rw [hBdef, hBm, hX0]
    rw [hBs'] at e
    have hc : (s4 : Equiv.Perm (Fin n)) * X₀ i = X₀ i * (s4 : Equiv.Perm (Fin n)) :=
      mem_centralizer_singleton_iff.1 (hS4C s4.2).2
    have e2 : b = (s4 : Equiv.Perm (Fin n))⁻¹ * (X₀ i * (s4 : Equiv.Perm (Fin n))) := by
      rw [← e]
      group
    rw [e2, ← hc, inv_mul_cancel_left]
  ·
    have htj' : t.1 = j := Nat.eq_of_beq_eq_true htj
    obtain ⟨⟨hme, hfs⟩, hwb⟩ := hwits t ht
    have hfac : FacOK h t.2.2.1 := fun g hg => by
      have := hfs g hg
      exact ⟨fun k hk => Nat.blt_eq.mp (this.1.2 k hk), fun k hk => Nat.blt_eq.mp (this.2 k hk)⟩
    obtain ⟨y, hy, hyo⟩ := exists_order4_of_witB HL hB hℓ hxw hfac hwb
    rw [← hXdef] at hy
    left
    apply hmono
    refine Or.inl ⟨y, nE_mono P ?_ hy, by rw [hyo]⟩
    rw [closure_le]
    rintro g (rfl | hg)
    · exact hpair _ (htj' ▸ hme)
    · simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      exact hpair _ (htj' ▸ (hfs g' hg').1.1)
  ·
    have hsj' : s.1 = j := Nat.eq_of_beq_eq_true hsj
    have hsk := hskips s hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hsk
    obtain ⟨⟨⟨hsa, hsl⟩, hsw⟩, hsb⟩ := hsk
    have hjr : s.2.2.2 < i := Nat.blt_eq.mp hsl
    have hgw : WordOK h s.2.2.1 := fun k hk => Nat.blt_eq.mp (hsw k hk)
    have hGP := wordPerm_mem HL hℓ hgw
    set G := wordPerm ℓ s.2.2.1
    have hconj : G * pcG X s.2.1 * G⁻¹ = X₀ s.2.2.2 := by
      have hc : G * pcG X s.2.1 = X₀ s.2.2.2 * G := by
        refine eq_of_base hB (P.mul_mem hGP (hpcP _)) (P.mul_mem (hX₀P _ (by omega)) hGP)
          fun b' hb' hbs => ?_
        have e := Nat.eq_of_beq_eq_true (hsb b' hbs)
        rw [hpcw _ b' hb', wPt_eq HL _ hgw _ (Fin.isLt _), wPt_eq HL _ hgw b' hb',
          hX₀ _ (by omega) _ (Fin.isLt _)] at e
        simpa [Equiv.Perm.mul_apply] using e
      rw [hc, mul_inv_cancel_right]
    right
    refine ⟨s.2.2.2, hjr, G * s4, P.mul_mem hGP hs4P, ?_⟩
    rcases hsa with hsa | hsa
    · left
      rw [Nat.eq_of_beq_eq_true hsa, hsj', ← hBdef, hBs'] at hconj
      rw [← hconj]
      simp only [mul_inv_rev, Subgroup.coe_inv]
      group
    · right
      rw [Nat.eq_of_beq_eq_true hsa, hsj', hXB, hBs'] at hconj
      rw [← hconj]
      conv_rhs => rw [← hs4x]
      simp only [mul_inv_rev]
      group
  ·
    have hpfj' : pf.1 = j := Nat.eq_of_beq_eq_true hpfj
    obtain ⟨hpl, hnc⟩ := hperfs pf hpf
    have hne : r.perfs.isEmpty = false := by
      cases hr : r.perfs with
      | nil => rw [hr] at hpf; simp at hpf
      | cons _ _ => rfl
    rw [hne, Bool.false_or] at hperfB
    have hx1' : bs.any (fun b => !(Nat.beq (pcwPt w L r.xw r.mx b) b)) = true := hx1
    left
    apply hmono
    refine Or.inr ⟨rfl, pWitness_of_perfB HL hB hℓ hxw (E := closure {X₀ i, B})
      (by rw [← hXdef, hX0]; exact hxE) hx1' (me := r.mb.getD pf.1 0)
      (by rw [← hXdef, hpfj']; exact hBE) hperfB (Nat.blt_eq.mp hpl) hnc⟩

end CFSG.ComponentClassification.RankTwoSporadic.RootR
