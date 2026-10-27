module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native

@[expose] def blk1 (n : ℕ) (p : Array ℕ) : Array ℕ := Array.ofFn (n := n) fun i => p[i.val]!

@[expose] def blk2 (n m : ℕ) (p : Array ℕ) : Array ℕ :=
  Array.ofFn (n := m) fun j => p[n + j.val]!

@[expose] def pairArr (n m : ℕ) (a b : Array ℕ) : Array ℕ :=
  Array.ofFn (n := n + m) fun i => if i.val < n then a[i.val]! else b[i.val - n]!

theorem blk1_pairArr {n m : ℕ} {a b : Array ℕ} (ha : a.size = n) :
    blk1 n (pairArr n m a b) = a := by
  apply Array.ext (by simp [blk1, ha])
  intro i hi _
  have hi' : i < n := by simpa [blk1] using hi
  simp only [blk1, Array.getElem_ofFn]
  rw [pairArr, getElem!_ofFn_nat _ (show i < n + m by omega)]
  simp only [ite_eq_left hi']
  rw [getElem!_pos a i (by omega)]

theorem blk2_pairArr {n m : ℕ} {a b : Array ℕ} (hb : b.size = m) :
    blk2 n m (pairArr n m a b) = b := by
  apply Array.ext (by simp [blk2, hb])
  intro j hj _
  have hj' : j < m := by simpa [blk2] using hj
  simp only [blk2, Array.getElem_ofFn]
  rw [pairArr, getElem!_ofFn_nat _ (show n + j < n + m by omega)]
  simp only [ite_eq_right (show ¬ n + j < n by omega), Nat.add_sub_cancel_left]
  rw [getElem!_pos b j (by omega)]

theorem size_compA {n : ℕ} {t u : Array ℕ} : (compA n t u).size = n := by
  simp [compA]

theorem size_idA {n : ℕ} : (idA n).size = n := by
  simp [idA]

@[expose] def prodAct (n m : ℕ) (gs ms : Array (Array ℕ)) (k : ℕ) (p : Array ℕ) : Array ℕ :=
  pairArr n m (compA n gs[k]! (blk1 n p)) (compA m ms[k]! (blk2 n m p))

@[expose] def prodValid (n m : ℕ) (p : Array ℕ) : Bool :=
  validA n (blk1 n p) && validA m (blk2 n m p)

@[expose] def prodKey (n : ℕ) (ps : List ℕ) (p : Array ℕ) : ℕ := keyA n ps (blk1 n p)

@[expose] def prodRoot (n m : ℕ) : Array ℕ := pairArr n m (idA n) (idA m)

@[expose] def prodOK (n m : ℕ) (gs ms : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) : Bool :=
  ms.size == gs.size && allLt gs.size (fun k => validA n gs[k]! && validA m ms[k]!) &&
    arrCertOK (prodAct n m gs ms) gs.size (prodValid n m) (prodKey n ps) (prodRoot n m) c

@[expose] def prodBfs (n m : ℕ) (gs ms : Array (Array ℕ)) (ps : List ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (prodAct n m gs ms) gs.size (prodKey n ps) (prodRoot n m) fuel

@[expose] noncomputable def prodGens (n m : ℕ) (gs ms : Array (Array ℕ)) (k : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin m) :=
  (permOfArr n gs[k]!, permOfArr m ms[k]!)

@[expose] noncomputable def prodDec (n m : ℕ) (p : Array ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin m) :=
  (permOfArr n (blk1 n p), permOfArr m (blk2 n m p))

section Spec

variable {n m : ℕ} {gs ms : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}

theorem prodOK_spec (hps : ∀ q ∈ ps, q < n) (h : prodOK n m gs ms ps c = true) :
    (∀ x, x ∈ Subgroup.closure (prodGens n m gs ms '' {k | k < gs.size}) ↔
      ∃ i < c.pts.size, prodDec n m c.pts[i]! = x) ∧
    Nat.card (Subgroup.closure (prodGens n m gs ms '' {k | k < gs.size})) = c.pts.size := by
  simp only [prodOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsz, hgs⟩, hc⟩ := h
  have hact : ∀ k < gs.size, ∀ a, prodValid n m a = true →
      prodDec n m (prodAct n m gs ms k a) = prodGens n m gs ms k * prodDec n m a := by
    intro k hk a ha
    simp only [prodValid, Bool.and_eq_true] at ha
    have hv := allLt_spec hgs hk
    simp only [Bool.and_eq_true] at hv
    have h1 := rep_compA (rep_of_validA hv.1) (rep_of_validA ha.1)
    have h2 := rep_compA (rep_of_validA hv.2)
      (rep_of_validA ha.2)
    simp only [prodDec, prodAct, prodGens, blk1_pairArr size_compA, blk2_pairArr size_compA,
      permOfArr_eq_of_rep h1, permOfArr_eq_of_rep h2, Prod.mk_mul_mk]
  have hkey : ∀ a b, prodValid n m a = true → prodValid n m b = true →
      prodDec n m a = prodDec n m b → prodKey n ps a = prodKey n ps b := by
    intro a b ha hb hab
    simp only [prodValid, Bool.and_eq_true] at ha hb
    exact keyA_eq hps ha.1 hb.1 (congrArg Prod.fst hab)
  have hroot : prodDec n m (prodRoot n m) = 1 := by
    simp only [prodDec, prodRoot, blk1_pairArr size_idA, blk2_pairArr size_idA,
      permOfArr_eq_of_rep rep_idA]
    rfl
  exact card_closure_of_arrCertOK (G := Equiv.Perm (Fin n) × Equiv.Perm (Fin m)) hc hact hkey hroot

end Spec


section Graph

variable {G H : Type*} [Group G] [Group H]

theorem exists_graph_hom [Finite G] [Finite H] (Γ : Subgroup (G × H)) (A : Subgroup G)
    (hmap : Γ.map (MonoidHom.fst G H) = A) (hcard : Nat.card Γ = Nat.card A) :
    ∃ φ : A →* H, (∀ a : A, ((a : G), φ a) ∈ Γ) ∧ (∀ (a : A) (b : H), ((a : G), b) ∈ Γ → φ a = b) ∧
      φ.range = Γ.map (MonoidHom.snd G H) := by
  let f : Γ →* A := ((MonoidHom.fst G H).comp Γ.subtype).codRestrict A fun γ => by
    rw [← hmap]
    exact ⟨γ, γ.2, rfl⟩
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : G) ∈ Γ.map (MonoidHom.fst G H) := hmap ▸ a.2
    obtain ⟨γ, hγ, hγa⟩ := ha
    exact ⟨⟨γ, hγ⟩, Subtype.ext hγa⟩
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hcard.le
  let e : Γ ≃* A := MulEquiv.ofBijective f hbij
  have he : ∀ γ : Γ, ((e γ : A) : G) = γ.1.1 := fun γ => rfl
  refine ⟨((MonoidHom.snd G H).comp Γ.subtype).comp e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro a
    have h1 : ((e (e.symm a) : A) : G) = (a : G) := by rw [MulEquiv.apply_symm_apply]
    rw [he] at h1
    have := (e.symm a).2
    rw [← h1]
    exact this
  · intro a b hab
    have h1 : (((e.symm a : Γ) : G × H).1) = (a : G) := by
      have := he (e.symm a)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    let γ' : Γ := ⟨((a : G), b), hab⟩
    have h2 : e γ' = a := Subtype.ext rfl
    have h3 : e.symm a = γ' := by rw [← h2, MulEquiv.symm_apply_apply]
    show ((e.symm a : Γ) : G × H).2 = b
    rw [h3]
  · ext b
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MonoidHom.coe_snd, mem_map]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (e.symm a).2, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨e ⟨γ, hγ⟩, by rw [MulEquiv.symm_apply_apply]⟩

end Graph

end CFSG.EvenSporadicStandard.RuStd.S2
