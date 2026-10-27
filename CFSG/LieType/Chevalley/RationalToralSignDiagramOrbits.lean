module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs
public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

theorem maskPairing_single (b : Fin τ.rank → Bool) (j : Fin τ.rank) :
    maskPairing b (Pi.single j 1) = if b j then 1 else 0 := by
  rw [maskPairing, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem maskChar_single (b : Fin τ.rank → Bool) (j : Fin τ.rank) :
    maskChar b (Multiplicative.ofAdd (Pi.single j 1)) = if b j then -1 else 1 := by
  rw [maskChar_apply, maskPairing_single]
  split_ifs <;> simp

theorem maskChar_injective : Function.Injective (maskChar (τ := τ)) := by
  intro b b' h
  funext j
  have h' := congrArg (fun χ => χ (Multiplicative.ofAdd (Pi.single j 1))) h
  simp only [maskChar_single] at h'
  cases hb : b j <;> cases hb' : b' j <;> simp only [hb, hb'] at h' ⊢ <;>
    exact absurd h' (by decide)

theorem permChar_maskChar (ρ : Equiv.Perm (Fin τ.rank)) (b : Fin τ.rank → Bool) :
    permChar ρ (maskChar b) = maskChar (b ∘ ρ.symm) := by
  refine MonoidHom.ext fun x => ?_
  change permChar ρ (maskChar b) (Multiplicative.ofAdd (Multiplicative.toAdd x)) =
    maskChar (b ∘ ρ.symm) (Multiplicative.ofAdd (Multiplicative.toAdd x))
  rw [permChar_apply, maskChar_apply, maskChar_apply]
  congr 1
  simp only [maskPairing, permLattice, Function.comp_apply, Equiv.symm_symm]
  rw [← Equiv.sum_comp ρ (fun j => if b (ρ.symm j) = true then Multiplicative.toAdd x j else 0)]
  simp

theorem listMask_ofFn (b : Fin τ.rank → Bool) : listMask (List.ofFn b) = b := by
  funext j
  simp [listMask]

theorem ofFn_listMask {l : List Bool} (h : l.length = τ.rank) :
    List.ofFn (listMask (τ := τ) l) = l :=
  List.ext_getElem (by simp [h]) fun i _ h₂ => by
    simp [listMask, List.getElem?_eq_getElem h₂]

theorem eq_of_ofFn_eq {b b' : Fin τ.rank → Bool} (h : List.ofFn b = List.ofFn b') : b = b' :=
  List.ofFn_injective h

theorem exists_maskChar_of_closed
    {S : Set (Fin τ.rank → Bool)}
    (hS : ∀ b ∈ S, ∀ i, maskReflect i b ∈ S) {b₀ : Fin τ.rank → Bool} (h₀ : b₀ ∈ S)
    (t : WeylGroup τ) : ∃ b ∈ S, ∀ v : Fin τ.rank → ℤ,
      maskChar b₀ (Multiplicative.ofAdd (t⁻¹ • v)) = maskChar b (Multiplicative.ofAdd v) := by
  induction t using (coxeterSystem τ).simple_induction_left with
  | one => exact ⟨b₀, h₀, fun v => by rw [inv_one, one_smul]⟩
  | mul_simple_left w i ih =>
    obtain ⟨b, hb, e⟩ := ih
    refine ⟨maskReflect i b, hS b hb i, fun v => ?_⟩
    rw [maskChar_maskReflect, _root_.mul_inv_rev, mul_smul, (coxeterSystem τ).inv_simple, e]

theorem charOrbit_subset_image
    {S : Set (Fin τ.rank → Bool)}
    (hS : ∀ b ∈ S, ∀ i, maskReflect i b ∈ S) {b₀ : Fin τ.rank → Bool} (h₀ : b₀ ∈ S) :
    charOrbit (maskChar b₀) ⊆ maskChar '' S := by
  rintro χ' ⟨t, ht⟩
  obtain ⟨b, hb, e⟩ := exists_maskChar_of_closed hS h₀ t
  refine ⟨b, hb, MonoidHom.ext fun x => ?_⟩
  change maskChar b (Multiplicative.ofAdd (Multiplicative.toAdd x)) =
    χ' (Multiplicative.ofAdd (Multiplicative.toAdd x))
  rw [ht, e]

theorem maskChar_maskAct_mem_charOrbit
    (b₀ : Fin τ.rank → Bool) (ω : List (Fin τ.rank)) :
    maskChar (maskAct ω b₀) ∈ charOrbit (maskChar b₀) :=
  ⟨(coxeterSystem τ).wordProd ω, fun v => maskChar_maskAct ω b₀ v⟩

theorem charOrbit_subset_of_mem
    {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (h : χ' ∈ charOrbit χ) : charOrbit χ' ⊆ charOrbit χ := by
  rintro χ'' ⟨u, hu⟩
  obtain ⟨t, ht⟩ := h
  exact ⟨u * t, fun v => by rw [hu, ht, _root_.mul_inv_rev, mul_smul]⟩

theorem natCard_setOf_ofFn_mem {L : List (List Bool)} (hlen : ∀ l ∈ L, l.length = τ.rank)
    (hnd : L.Nodup) : Nat.card {b : Fin τ.rank → Bool | List.ofFn b ∈ L} = L.length := by
  classical
  let e : {b : Fin τ.rank → Bool | List.ofFn b ∈ L} ≃ {l // l ∈ L} :=
    { toFun := fun b => ⟨List.ofFn b.1, b.2⟩
      invFun := fun l => ⟨listMask l.1, by
        change List.ofFn (listMask l.1) ∈ L
        rw [ofFn_listMask (hlen _ l.2)]
        exact l.2⟩
      left_inv := fun b => Subtype.ext (listMask_ofFn b.1)
      right_inv := fun l => Subtype.ext (ofFn_listMask (hlen _ l.2)) }
  rw [Nat.card_congr e, ← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun l => List.mem_toFinset.symm)

abbrev OrbitEntries : Type := List (List Bool × List ℕ)

namespace OrbitEntries

@[expose] def head (o : OrbitEntries) : List Bool :=
  (o.headD ([], [])).1

@[expose] def bits (o : OrbitEntries) : List (List Bool) :=
  o.map Prod.fst

variable (τ) in
@[expose] def check (o : OrbitEntries) : Bool :=
  !o.isEmpty &&
  o.all (fun e => e.1.length == τ.rank &&
    List.ofFn (maskAct (toFinWord (τ := τ) e.2) (listMask (τ := τ) o.head)) == e.1) &&
  o.all fun e => (List.finRange τ.rank).all fun i =>
    o.bits.contains (List.ofFn (maskReflect i (listMask (τ := τ) e.1)))

@[expose] def bitSet (o : OrbitEntries) : Set (Fin τ.rank → Bool) :=
  {b | List.ofFn b ∈ o.bits}

variable {o : OrbitEntries}

theorem mem_bits {l : List Bool} : l ∈ o.bits ↔ ∃ e ∈ o, e.1 = l := by
  simp [bits]

theorem length_of_mem (h : check τ o = true) {l : List Bool} (hl : l ∈ o.bits) :
    l.length = τ.rank := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, rfl⟩ := mem_bits.1 hl
  exact (h.1.2 e he).1

theorem head_mem (h : check τ o = true) : o.head ∈ o.bits := by
  simp only [check, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, -⟩, -⟩ := h
  obtain ⟨e, o', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact List.mem_map_of_mem (List.mem_cons_self ..)

theorem listMask_head_mem (h : check τ o = true) : listMask (τ := τ) o.head ∈ bitSet o := by
  change List.ofFn (listMask o.head) ∈ o.bits
  rw [ofFn_listMask (length_of_mem h (head_mem h))]
  exact head_mem h

theorem maskReflect_mem (h : check τ o = true) {b : Fin τ.rank → Bool} (hb : b ∈ bitSet o)
    (i : Fin τ.rank) : maskReflect i b ∈ bitSet o := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨e, he, he'⟩ := mem_bits.1 hb
  have := h.2 e he i (List.mem_finRange i)
  rwa [he', listMask_ofFn] at this

theorem exists_maskAct (h : check τ o = true) {b : Fin τ.rank → Bool} (hb : b ∈ bitSet o) :
    ∃ ω : List (Fin τ.rank), maskAct ω (listMask o.head) = b := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, he'⟩ := mem_bits.1 hb
  exact ⟨_, eq_of_ofFn_eq ((h.1.2 e he).2.trans he')⟩

theorem charOrbit_eq
    (h : check τ o = true) :
    charOrbit (maskChar (listMask (τ := τ) o.head)) = maskChar '' bitSet o := by
  refine (charOrbit_subset_image (fun b hb i => maskReflect_mem h hb i)
    (listMask_head_mem h)).antisymm ?_
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨ω, rfl⟩ := exists_maskAct h hb
  exact maskChar_maskAct_mem_charOrbit _ ω

theorem maskChar_mem_charOrbit_iff
    (h : check τ o = true) {b : Fin τ.rank → Bool} :
    maskChar b ∈ charOrbit (maskChar (listMask (τ := τ) o.head)) ↔ b ∈ bitSet o := by
  rw [charOrbit_eq h]
  exact maskChar_injective.mem_set_image

theorem natCard_charOrbit
    (h : check τ o = true) (hnd : o.bits.Nodup) :
    Nat.card (charOrbit (maskChar (listMask (τ := τ) o.head))) = o.bits.length := by
  rw [charOrbit_eq h, Nat.card_image_of_injective maskChar_injective]
  exact natCard_setOf_ofFn_mem (fun l hl => length_of_mem h hl) hnd

end OrbitEntries

structure OrbitCert (τ : Tag) where
  stable : List (SignRep τ × OrbitEntries)
  other : List OrbitEntries

namespace OrbitCert

variable (P : OrbitCert τ)

@[expose] def stableCheck (ρ : Equiv.Perm (Fin τ.rank)) (e : SignRep τ × OrbitEntries) : Bool :=
  OrbitEntries.check τ e.2 && decide (e.1.mask < 2 ^ τ.rank) &&
    List.ofFn (natBits (τ := τ) e.1.mask) == e.2.head &&
    e.2.bits.length == e.1.orbitSize && decide e.2.bits.Nodup &&
    List.ofFn (listMask (τ := τ) e.2.head ∘ ρ.symm) == e.2.head &&
    e.2.all fun x => e.2.bits.contains (List.ofFn (listMask (τ := τ) x.1 ∘ ρ.symm)) &&
      e.2.bits.contains (List.ofFn (listMask (τ := τ) x.1 ∘ ρ))

@[expose] def otherCheck (ρ : Equiv.Perm (Fin τ.rank)) (o : OrbitEntries) : Bool :=
  OrbitEntries.check τ o &&
    o.all fun x => !o.bits.contains (List.ofFn (listMask (τ := τ) x.1 ∘ ρ.symm))

@[expose] def check (ρ : Equiv.Perm (Fin τ.rank)) : Bool :=
  P.stable.all (stableCheck ρ) && P.other.all (otherCheck ρ) &&
    decide (P.stable.Pairwise fun e e' => e.2.bits.contains e'.2.head = false)

@[expose] def Covers : Prop :=
  ∀ b : Fin τ.rank → Bool, ∃ o ∈ P.stable.map Prod.snd ++ P.other, List.ofFn b ∈ o.bits

@[expose] def reps : List (SignRep τ) :=
  P.stable.map Prod.fst

variable {P} {ρ : Equiv.Perm (Fin τ.rank)}

theorem stableCheck_of_mem (h : P.check ρ = true) {e : SignRep τ × OrbitEntries}
    (he : e ∈ P.stable) : stableCheck ρ e = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1 e he

theorem otherCheck_of_mem (h : P.check ρ = true) {o : OrbitEntries} (ho : o ∈ P.other) :
    otherCheck ρ o = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 o ho

section Stable

variable {e : SignRep τ × OrbitEntries} (h : stableCheck ρ e = true)
include h

theorem stable_check : OrbitEntries.check τ e.2 = true := by
  simp only [stableCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem stable_mask_lt : e.1.mask < 2 ^ τ.rank := by
  simp only [stableCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

theorem stable_natBits : natBits (τ := τ) e.1.mask = listMask e.2.head := by
  have hh := h
  simp only [stableCheck, Bool.and_eq_true, beq_iff_eq] at hh
  refine eq_of_ofFn_eq (hh.1.1.1.1.2.trans ?_)
  exact (ofFn_listMask (OrbitEntries.length_of_mem (stable_check h)
    (OrbitEntries.head_mem (stable_check h)))).symm

theorem stable_signMaskChar : signMaskChar τ e.1.mask = maskChar (listMask e.2.head) := by
  rw [signMaskChar, stable_natBits h]

theorem stable_length : e.2.bits.length = e.1.orbitSize := by
  simp only [stableCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem stable_nodup : e.2.bits.Nodup := by
  simp only [stableCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem stable_head_comp : listMask (τ := τ) e.2.head ∘ ρ.symm = listMask e.2.head := by
  have hh := h
  simp only [stableCheck, Bool.and_eq_true, beq_iff_eq] at hh
  refine eq_of_ofFn_eq (hh.1.2.trans ?_)
  exact (ofFn_listMask (OrbitEntries.length_of_mem (stable_check h)
    (OrbitEntries.head_mem (stable_check h)))).symm

theorem stable_comp_mem {b : Fin τ.rank → Bool} (hb : b ∈ OrbitEntries.bitSet e.2) :
    b ∘ ρ.symm ∈ OrbitEntries.bitSet e.2 ∧ b ∘ ρ ∈ OrbitEntries.bitSet e.2 := by
  simp only [stableCheck, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨x, hx, hx'⟩ := OrbitEntries.mem_bits.1 hb
  have := h.2 x hx
  rw [hx', listMask_ofFn] at this
  exact this

theorem stable_permChar_eq :
    permChar ρ (signMaskChar τ e.1.mask) = signMaskChar τ e.1.mask := by
  rw [stable_signMaskChar h, permChar_maskChar, stable_head_comp h]

theorem stable_image_charOrbit :
    permChar ρ '' charOrbit (signMaskChar τ e.1.mask) = charOrbit (signMaskChar τ e.1.mask) := by
  rw [stable_signMaskChar h, OrbitEntries.charOrbit_eq (stable_check h), Set.image_image]
  ext χ
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨_, (stable_comp_mem h hb).1, ?_⟩
    change maskChar (b ∘ ρ.symm) = permChar ρ (maskChar b)
    rw [permChar_maskChar]
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b ∘ ρ, (stable_comp_mem h hb).2, ?_⟩
    change permChar ρ (maskChar (b ∘ ρ)) = maskChar b
    rw [permChar_maskChar, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

theorem stable_card_charOrbit :
    Nat.card (charOrbit (signMaskChar τ e.1.mask)) = e.1.orbitSize := by
  rw [stable_signMaskChar h, OrbitEntries.natCard_charOrbit (stable_check h) (stable_nodup h),
    stable_length h]

end Stable

theorem other_not_mem {o : OrbitEntries} (h : otherCheck ρ o = true) {b : Fin τ.rank → Bool}
    (hb : b ∈ OrbitEntries.bitSet o) : b ∘ ρ.symm ∉ OrbitEntries.bitSet o := by
  simp only [otherCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨x, hx, hx'⟩ := OrbitEntries.mem_bits.1 hb
  have h2 := h.2 x hx
  rw [hx', listMask_ofFn] at h2
  intro hmem
  have h3 : o.bits.contains (List.ofFn (b ∘ ρ.symm)) = true := List.contains_iff_mem.2 hmem
  rw [h3] at h2
  exact absurd h2 (by decide)

theorem other_check {o : OrbitEntries} (h : otherCheck ρ o = true) :
    OrbitEntries.check τ o = true := by
  simp only [otherCheck, Bool.and_eq_true] at h
  exact h.1

variable (h : P.check ρ = true)
include h

theorem mask_lt : ∀ e ∈ P.reps, e.mask < 2 ^ τ.rank := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact stable_mask_lt (stableCheck_of_mem h hx)

theorem permChar_eq : ∀ e ∈ P.reps,
    permChar ρ (signMaskChar τ e.mask) = signMaskChar τ e.mask := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact stable_permChar_eq (stableCheck_of_mem h hx)

theorem image_charOrbit : ∀ e ∈ P.reps,
    permChar ρ '' charOrbit (signMaskChar τ e.mask) = charOrbit (signMaskChar τ e.mask) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact stable_image_charOrbit (stableCheck_of_mem h hx)

theorem card_charOrbit : ∀ e ∈ P.reps,
    Nat.card (charOrbit (signMaskChar τ e.mask)) = e.orbitSize := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact stable_card_charOrbit (stableCheck_of_mem h hx)

theorem pairwise_not_mem
    : P.reps.Pairwise fun e e' =>
    signMaskChar τ e'.mask ∉ charOrbit (signMaskChar τ e.mask) := by
  have hp := h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hp
  rw [reps, List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => ?_) hp.2
  have hxs := stableCheck_of_mem h hx
  have hys := stableCheck_of_mem h hy
  rw [stable_signMaskChar hxs, stable_signMaskChar hys,
    OrbitEntries.maskChar_mem_charOrbit_iff (stable_check hxs)]
  intro hmem
  change List.ofFn (listMask (τ := τ) y.2.head) ∈ x.2.bits at hmem
  rw [ofFn_listMask (OrbitEntries.length_of_mem (stable_check hys)
    (OrbitEntries.head_mem (stable_check hys)))] at hmem
  simp [hmem] at hxy

theorem exists_rep
    (hcov : P.Covers) : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ,
    permChar ρ χ ∈ charOrbit χ → ∃ e ∈ P.reps, χ ∈ charOrbit (signMaskChar τ e.mask) := by
  intro χ hχ
  rw [eq_maskChar χ] at hχ ⊢
  set b : Fin τ.rank → Bool := fun j => decide (χ (Multiplicative.ofAdd (Pi.single j 1)) = -1)
  obtain ⟨o, ho, hbo⟩ := hcov b
  rcases List.mem_append.1 ho with ho | ho
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
    have hxs := stableCheck_of_mem h hx
    refine ⟨x.1, List.mem_map_of_mem hx, ?_⟩
    rw [stable_signMaskChar hxs, OrbitEntries.maskChar_mem_charOrbit_iff (stable_check hxs)]
    exact hbo
  · exfalso
    have hos := otherCheck_of_mem h ho
    have hmem : maskChar b ∈ charOrbit (maskChar (listMask (τ := τ) o.head)) :=
      (OrbitEntries.maskChar_mem_charOrbit_iff (other_check hos)).2 hbo
    have h2 := charOrbit_subset_of_mem hmem hχ
    rw [permChar_maskChar, OrbitEntries.maskChar_mem_charOrbit_iff (other_check hos)] at h2
    exact other_not_mem hos hbo h2

end OrbitCert

theorem natCard_kernelPosStabilizer_le_of_stabCert
    {C : RootCertificate τ} (hC : C.check = true)
    {S : StabCert} (hS : S.check C = true) {m : ℕ} (hm : List.ofFn (natBits (τ := τ) m) = S.mask) :
    Nat.card (kernelPosStabilizer (signMaskChar τ m)) ≤ (S.passing C).length := by
  have h := StabCert.card_kernelPosStabilizer_le hC hS
  rwa [← hm, listMask_ofFn] at h

theorem RationalToralSignDiagram.of_cert
    {P : OrbitCert τ} {ρ : Equiv.Perm (Fin τ.rank)} {p : ℕ}
    (hP : P.check ρ = true) (hcov : P.Covers)
    (hrep : ∀ e ∈ P.reps, Nat.card (kernelPosStabilizer (signMaskChar τ e.mask)) = e.omegaOrder ∧
      (kernelPosStabilizer (signMaskChar τ e.mask) : Set (WeylGroup τ)) =
        {w | ∃ l ∈ e.omegaWords, wordElt τ l = w} ∧
      ∀ l ∈ e.omegaWords, ThetaProperties ρ p (signMaskChar τ e.mask) (wordElt τ l)) :
    RationalToralSignDiagram τ ρ p P.reps where
  mask_lt := OrbitCert.mask_lt hP
  permChar_eq := OrbitCert.permChar_eq hP
  image_charOrbit := OrbitCert.image_charOrbit hP
  card_charOrbit := OrbitCert.card_charOrbit hP
  pairwise_not_mem := OrbitCert.pairwise_not_mem hP
  exists_rep := OrbitCert.exists_rep hP hcov
  card_kernelPosStabilizer := fun e he => (hrep e he).1
  coe_kernelPosStabilizer := fun e he => (hrep e he).2.1
  theta := fun e he => (hrep e he).2.2

end CFSG.LieType.Chevalley.ToralSign
