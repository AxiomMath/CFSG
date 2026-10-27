module

public import CFSG.LocalAnalysis.SectionRank.SignLift

public section

namespace CFSG.SectionRank.OddCover

open CFSG.Open CFSG.SectionRank Matrix
open scoped commutatorElement

@[expose] def symTwo (p : ℕ) : AddSubgroup (Matrix (Fin 2) (Fin 2) (ZMod p)) where
  carrier := {B | Bᵀ = B}
  add_mem' {B C} hB hC := by
    change (B + C)ᵀ = B + C
    rw [Matrix.transpose_add, hB, hC]
  zero_mem' := Matrix.transpose_zero
  neg_mem' {B} hB := by
    change (-B)ᵀ = -B
    rw [Matrix.transpose_neg, hB]

theorem mem_symTwo {p : ℕ} {B : Matrix (Fin 2) (Fin 2) (ZMod p)} : B ∈ symTwo p ↔ Bᵀ = B :=
  Iff.rfl

@[expose] def symOfCoords (p : ℕ) : (Fin 3 → ZMod p) →+ symTwo p where
  toFun v := ⟨!![v 0, v 1; v 1, v 2], by
    rw [mem_symTwo]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  map_zero' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem coe_symOfCoords {p : ℕ} (v : Fin 3 → ZMod p) :
    ((symOfCoords p v : symTwo p) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![v 0, v 1; v 1, v 2] :=
  rfl

theorem symOfCoords_injective (p : ℕ) : Function.Injective (symOfCoords p) := by
  intro v w h
  have h' := congrArg (fun B : symTwo p => (B : Matrix (Fin 2) (Fin 2) (ZMod p))) h
  simp only [coe_symOfCoords] at h'
  funext i
  fin_cases i
  · exact congrFun (congrFun h' 0) 0
  · exact congrFun (congrFun h' 0) 1
  · exact congrFun (congrFun h' 1) 1

theorem symOfCoords_surjective (p : ℕ) : Function.Surjective (symOfCoords p) := by
  intro B
  refine ⟨![(B : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0, (B : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1,
    (B : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1], Subtype.ext ?_⟩
  have hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p))ᵀ = B := B.2
  have h10 : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 =
      (B : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 := by
    have := congrFun (congrFun hB 0) 1
    rwa [Matrix.transpose_apply] at this
  rw [coe_symOfCoords]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10]

@[expose] def coordMat {p : ℕ} (v : Fin 3 → ZMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![v 0, v 1; v 1, v 2]

theorem coordMat_injective {p : ℕ} : Function.Injective (coordMat (p := p)) := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 1) 1

theorem coordMat_add {p : ℕ} (v w : Fin 3 → ZMod p) :
    coordMat (v + w) = coordMat v + coordMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coordMat_neg {p : ℕ} (v : Fin 3 → ZMod p) : coordMat (-v) = -coordMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coordMat_single_zero {p : ℕ} :
    coordMat (Pi.single 0 1 : Fin 3 → ZMod p) = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coordMat_single_one {p : ℕ} :
    coordMat (Pi.single 1 1 : Fin 3 → ZMod p) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coordMat_single_two {p : ℕ} :
    coordMat (Pi.single 2 1 : Fin 3 → ZMod p) = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

abbrev symD (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![-1, 0; 0, 1]

abbrev symS (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 1; 1, 0]

abbrev symT (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 0; 1, 1]

section Conj

variable {p : ℕ}

theorem symD_conj_zero :
    symD p * coordMat (Pi.single 0 1) * (symD p)ᵀ = coordMat (Pi.single 0 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symD]

theorem symD_conj_one :
    symD p * coordMat (Pi.single 1 1) * (symD p)ᵀ = coordMat (-Pi.single 1 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symD]

theorem symD_conj_two :
    symD p * coordMat (Pi.single 2 1) * (symD p)ᵀ = coordMat (Pi.single 2 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symD]

theorem symS_conj_zero :
    symS p * coordMat (Pi.single 0 1) * (symS p)ᵀ = coordMat (Pi.single 2 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symS]

theorem symS_conj_two :
    symS p * coordMat (Pi.single 2 1) * (symS p)ᵀ = coordMat (Pi.single 0 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symS]

theorem symT_conj_zero :
    symT p * coordMat (Pi.single 0 1) * (symT p)ᵀ =
      coordMat (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coordMat, Matrix.mul_apply, symT]

end Conj

section Splitting

variable {P : Type*} [Group P] {p : ℕ} [hp : Fact p.Prime]

theorem commute_of_fix_of_inv (hp2 : p ≠ 2) (A : Subgroup P) (hAZ : A ≤ Subgroup.center P)
    (hcommA : ∀ x y : P, ⁅x, y⁆ ∈ A) (hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1) (σ : P ≃* P)
    (hσA : ∀ a ∈ A, σ a = a) {g h : P} (hg : g⁻¹ * σ g ∈ A) (hh : h * σ h ∈ A) :
    Commute g h := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hc : ∀ x y z : P, Commute ⁅x, y⁆ z := fun x y z =>
    (Subgroup.mem_center_iff.1 (hAZ (hcommA x y)) z).symm
  set a := g⁻¹ * σ g
  set b := h * σ h
  have hσg : σ g = g * a := by simp [a]
  have hσh : σ h = h⁻¹ * b := by simp [b]
  have hfix := hσA _ (hcommA g h)
  rw [map_commutatorElement, hσg, hσh, commutatorElement_mul_central_left (hAZ hg),
    commutatorElement_mul_central_right (hAZ hh)] at hfix
  have hinv : ⁅g, h⁻¹⁆ = ⁅g, h⁆⁻¹ := by
    have := commutatorElement_mul_right_of_central hc g h⁻¹ h
    rw [inv_mul_cancel, commutatorElement_one_right] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  rw [hinv] at hfix
  set c := ⁅g, h⁆
  have hc2 : c ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hfix]
    exact inv_mul_cancel c
  have hc1 : c = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    have := hcp g h
    rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at this
    exact this
  exact commutatorElement_eq_one_iff_mul_comm.1 hc1

theorem exists_pow_eq_of_inv (hp2 : p ≠ 2) (A : Subgroup P) (hAZ : A ≤ Subgroup.center P)
    (σ : P ≃* P) (hσA : ∀ a ∈ A, σ a = a) {g : P} (hgp : g ^ p ∈ A) (hg : g * σ g ∈ A) :
    ∃ d ∈ A, g ^ p = d ^ p := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hcen : ∀ a ∈ A, ∀ x : P, Commute a x := fun a ha x =>
    (Subgroup.mem_center_iff.1 (hAZ ha) x).symm
  set a := g * σ g
  have hσg : σ g = g⁻¹ * a := by simp [a]
  set c := g ^ p
  have hfix := hσA c hgp
  rw [map_pow, hσg, (hcen a hg _).symm.mul_pow, inv_pow] at hfix
  have hcc : c * c = a ^ p := by
    calc c * c = c * (c⁻¹ * a ^ p) := by rw [hfix]
      _ = a ^ p := mul_inv_cancel_left c _
  refine ⟨a ^ ((p + 1) / 2) * c⁻¹, A.mul_mem (A.pow_mem hg _) (A.inv_mem hgp), ?_⟩
  have hac : Commute (a ^ ((p + 1) / 2)) c⁻¹ := ((hcen a hg c).pow_left _).inv_right
  rw [hac.mul_pow, ← pow_mul, mul_comm, pow_mul, ← hcc, inv_pow, (Commute.refl c).mul_pow,
    ← pow_add]
  have : (p + 1) / 2 + (p + 1) / 2 = p + 1 := by omega
  rw [this, pow_succ, ((Commute.refl c).pow_left p).eq, mul_inv_cancel_right]

theorem symmetric_square_central_extension_splitting (hp2 : p ≠ 2) (A : Subgroup P) [A.Normal]
    (hAZ : A ≤ Subgroup.center P) (θ : P ⧸ A ≃* Multiplicative (symTwo p))
    (αd αs αt : P ≃* P) (hdA : ∀ a ∈ A, αd a = a) (hsA : ∀ a ∈ A, αs a = a)
    (htA : ∀ a ∈ A, αt a = a)
    (hd : ∀ x : P, ((Multiplicative.toAdd (θ (αd x : P ⧸ A)) : symTwo p) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
        symD p * (Multiplicative.toAdd (θ (x : P ⧸ A)) : symTwo p) * (symD p)ᵀ)
    (hs : ∀ x : P, ((Multiplicative.toAdd (θ (αs x : P ⧸ A)) : symTwo p) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
        symS p * (Multiplicative.toAdd (θ (x : P ⧸ A)) : symTwo p) * (symS p)ᵀ)
    (ht : ∀ x : P, ((Multiplicative.toAdd (θ (αt x : P ⧸ A)) : symTwo p) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
        symT p * (Multiplicative.toAdd (θ (x : P ⧸ A)) : symTwo p) * (symT p)ᵀ) :
    ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ A ⊔ E = ⊤ ∧ A ⊓ E = ⊥ := by
  have hp' := hp.out
  let ι : Multiplicative (Fin 3 → ZMod p) ≃* Multiplicative (symTwo p) :=
    AddEquiv.toMultiplicative (AddEquiv.ofBijective (symOfCoords p)
      ⟨symOfCoords_injective p, symOfCoords_surjective p⟩)
  have hι : ∀ v, ((Multiplicative.toAdd (ι v) : symTwo p) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      coordMat (Multiplicative.toAdd v) := fun v => rfl
  set τ : P →* Multiplicative (Fin 3 → ZMod p) :=
    (θ.trans ι.symm).toMonoidHom.comp (QuotientGroup.mk' A) with hτdef
  have hτ : ∀ x, ι (τ x) = θ (x : P ⧸ A) := fun x => by
    change ι (ι.symm (θ (x : P ⧸ A))) = _
    rw [MulEquiv.apply_symm_apply]
  have hact : ∀ (σ : P ≃* P) (R : Matrix (Fin 2) (Fin 2) (ZMod p)),
      (∀ x : P, ((Multiplicative.toAdd (θ (σ x : P ⧸ A)) : symTwo p) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
          R * (Multiplicative.toAdd (θ (x : P ⧸ A)) : symTwo p) * Rᵀ) →
      ∀ x : P, coordMat (Multiplicative.toAdd (τ (σ x))) =
        R * coordMat (Multiplicative.toAdd (τ x)) * Rᵀ := by
    intro σ R hσ x
    have h1 := hσ x
    rw [← hτ, ← hτ, hι, hι] at h1
    exact h1
  have hker : ∀ x, τ x = 1 ↔ x ∈ A := fun x => by
    rw [hτdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hτeq : ∀ x y, τ x = τ y → x⁻¹ * y ∈ A := fun x y h =>
    (hker _).1 (by rw [map_mul, map_inv, h]; exact inv_mul_cancel _)
  have hcen : ∀ a ∈ A, ∀ g : P, Commute a g := fun a ha g =>
    (Subgroup.mem_center_iff.1 (hAZ ha) g).symm
  have hcommA : ∀ x y : P, ⁅x, y⁆ ∈ A := fun x y => by
    rw [← hker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hpA : ∀ x : P, x ^ p ∈ A := fun x => by
    rw [← hker, map_pow]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, toAdd_one,
      Pi.zero_apply]
  have hc : ∀ x y z : P, Commute ⁅x, y⁆ z := fun x y z => hcen _ (hcommA x y) z
  have hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1 := fun x y => by
    rw [← commutatorElement_pow_left_of_central hc, commutatorElement_def,
      (hcen _ (hpA x) y).eq]
    group
  have hτsurj : Function.Surjective τ := fun v => by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective ((θ.trans ι.symm).symm v)
    refine ⟨q, ?_⟩
    change (θ.trans ι.symm) (q : P ⧸ A) = v
    rw [hq, MulEquiv.apply_symm_apply]
  set e : Fin 3 → Multiplicative (Fin 3 → ZMod p) := fun i =>
    Multiplicative.ofAdd (Pi.single i 1) with he
  choose g hg using fun i => hτsurj (e i)
  have himg : ∀ (σ : P ≃* P) (R : Matrix (Fin 2) (Fin 2) (ZMod p)),
      (∀ x : P, ((Multiplicative.toAdd (θ (σ x : P ⧸ A)) : symTwo p) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
          R * (Multiplicative.toAdd (θ (x : P ⧸ A)) : symTwo p) * Rᵀ) →
      ∀ (i : Fin 3) (w : Multiplicative (Fin 3 → ZMod p)),
      R * coordMat (Pi.single i 1) * Rᵀ = coordMat (Multiplicative.toAdd w) →
        τ (σ (g i)) = w := by
    intro σ R hσ i w hw
    apply Multiplicative.toAdd.injective
    apply coordMat_injective
    rw [hact σ R hσ, hg i, ← hw]
    rfl
  have hdX : τ (αd (g 0)) = τ (g 0) := himg αd _ hd 0 _ (by
    rw [hg 0, he, toAdd_ofAdd]; exact symD_conj_zero)
  have hdY : τ (αd (g 1)) = (τ (g 1))⁻¹ := himg αd _ hd 1 _ (by
    rw [hg 1, he, toAdd_inv, toAdd_ofAdd]; exact symD_conj_one)
  have hdZ : τ (αd (g 2)) = τ (g 2) := himg αd _ hd 2 _ (by
    rw [hg 2, he, toAdd_ofAdd]; exact symD_conj_two)
  have hsX : τ (αs (g 0)) = τ (g 2) := himg αs _ hs 0 _ (by
    rw [hg 2, he, toAdd_ofAdd]; exact symS_conj_zero)
  have hsZ : τ (αs (g 2)) = τ (g 0) := himg αs _ hs 2 _ (by
    rw [hg 0, he, toAdd_ofAdd]; exact symS_conj_two)
  have hxyz : τ (g 0 * g 1 * g 2) = e 0 * e 1 * e 2 := by rw [map_mul, map_mul, hg, hg, hg]
  have htX : τ (αt (g 0)) = τ (g 0 * g 1 * g 2) := himg αt _ ht 0 _ (by
    rw [hxyz, he, toAdd_mul, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    exact symT_conj_zero)
  have hY : g 1 * αd (g 1) ∈ A := (hker _).1 (by rw [map_mul, hdY]; exact mul_inv_cancel _)
  have c01 : Commute (g 0) (g 1) := commute_of_fix_of_inv hp2 A hAZ hcommA hcp αd hdA
    (hτeq _ _ hdX.symm) hY
  have c21 : Commute (g 2) (g 1) := commute_of_fix_of_inv hp2 A hAZ hcommA hcp αd hdA
    (hτeq _ _ hdZ.symm) hY
  have c02 : Commute (g 0) (g 2) := by
    obtain ⟨a₁, ha₁, h₁⟩ : ∃ a ∈ A, αs (g 0) = g 2 * a :=
      ⟨_, hτeq _ _ hsX.symm, by group⟩
    obtain ⟨a₂, ha₂, h₂⟩ : ∃ a ∈ A, αs (g 2) = g 0 * a :=
      ⟨_, hτeq _ _ hsZ.symm, by group⟩
    have hfix := hsA _ (hcommA (g 0) (g 2))
    rw [map_commutatorElement, h₁, h₂, commutatorElement_mul_central_left (hAZ ha₁),
      commutatorElement_mul_central_right (hAZ ha₂), ← commutatorElement_inv] at hfix
    set c := ⁅g 0, g 2⁆
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
    have hc2 : c ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [← hfix]
      exact mul_inv_cancel c
    have hc1 : c = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
      have := hcp (g 0) (g 2)
      rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at this
      exact this
    exact commutatorElement_eq_one_iff_mul_comm.1 hc1
  obtain ⟨dY, hdYA, hdYp⟩ := exists_pow_eq_of_inv hp2 A hAZ αd hdA (hpA (g 1)) hY
  obtain ⟨a₁, ha₁, h₁⟩ : ∃ a ∈ A, αs (g 0) = g 2 * a := ⟨_, hτeq _ _ hsX.symm, by group⟩
  obtain ⟨a₂, ha₂, h₂⟩ : ∃ a ∈ A, αt (g 0) = g 0 * g 1 * g 2 * a :=
    ⟨_, hτeq _ _ htX.symm, by group⟩
  have hsp : g 0 ^ p = g 2 ^ p * a₁ ^ p := by
    have := hsA _ (hpA (g 0))
    rw [map_pow, h₁, (hcen a₁ ha₁ _).symm.mul_pow] at this
    exact this.symm
  have htp : g 1 ^ p * g 2 ^ p * a₂ ^ p = 1 := by
    have := htA _ (hpA (g 0))
    rw [map_pow, h₂, (hcen a₂ ha₂ _).symm.mul_pow, (c02.mul_left c21.symm).mul_pow,
      c01.mul_pow] at this
    have h3 : g 0 ^ p * (g 1 ^ p * g 2 ^ p * a₂ ^ p) = g 0 ^ p * 1 := by
      rw [mul_one]; simpa only [mul_assoc] using this
    exact mul_left_cancel h3
  have hcomm' : ∀ a ∈ A, ∀ b ∈ A, Commute a b := fun a ha b _ => hcen a ha b
  set bZ := (dY * a₂)⁻¹ with hbZ
  have hbZA : bZ ∈ A := A.inv_mem (A.mul_mem hdYA ha₂)
  have hZp : g 2 ^ p = bZ ^ p := by
    have h5 : dY ^ p * g 2 ^ p * a₂ ^ p = 1 := by rw [← hdYp]; exact htp
    have h6 : g 2 ^ p = (dY ^ p)⁻¹ * (a₂ ^ p)⁻¹ := by
      calc g 2 ^ p = (dY ^ p)⁻¹ * (dY ^ p * g 2 ^ p * a₂ ^ p) * (a₂ ^ p)⁻¹ := by group
        _ = (dY ^ p)⁻¹ * (a₂ ^ p)⁻¹ := by rw [h5, mul_one]
    have hc1 : Commute (dY ^ p) (a₂ ^ p) :=
      hcomm' _ (A.pow_mem hdYA p) _ (A.pow_mem ha₂ p)
    rw [h6, hbZ, inv_pow, (hcomm' dY hdYA a₂ ha₂).mul_pow, _root_.mul_inv_rev,
      ← hc1.inv_inv.eq]
  set bX := bZ * a₁ with hbX
  have hbXA : bX ∈ A := A.mul_mem hbZA ha₁
  have hXp : g 0 ^ p = bX ^ p := by
    rw [hsp, hZp, hbX, (hcomm' bZ hbZA a₁ ha₁).mul_pow]
  set b : Fin 3 → P := ![bX, dY, bZ] with hbdef
  have hb : ∀ i, b i ∈ A := fun i => by fin_cases i <;> assumption
  have hbp : ∀ i, g i ^ p = b i ^ p := fun i => by fin_cases i <;> assumption
  set g' : Fin 3 → P := fun i => g i * (b i)⁻¹ with hg'def
  have hg'p : ∀ i, g' i ^ p = 1 := fun i => by
    rw [hg'def, (hcen _ (A.inv_mem (hb i)) (g i)).symm.mul_pow, hbp, inv_pow, mul_inv_cancel]
  have hτg' : ∀ i, τ (g' i) = e i := fun i => by
    rw [hg'def, map_mul, (hker _).2 (A.inv_mem (hb i)), mul_one, hg i]
  have hcomm'' : ∀ i j, Commute (g' i) (g' j) := by
    have hbase : ∀ i j, Commute (g i) (g j) := by
      intro i j
      fin_cases i <;> fin_cases j
      all_goals first
        | exact Commute.refl _
        | assumption
        | exact Commute.symm (by assumption)
    intro i j
    exact ((hbase i j).mul_right (hcen _ (A.inv_mem (hb j)) (g i)).symm).mul_left
      (hcen _ (A.inv_mem (hb i)) _)
  have : NeZero p := ⟨hp'.ne_zero⟩
  let ψ : Fin 3 → Multiplicative (ZMod p) →* P := fun i => zmodPowHom (g' i) (hg'p i)
  have hψcomm : Pairwise fun i j => ∀ (x y : Multiplicative (ZMod p)), Commute (ψ i x) (ψ j y) :=
    fun i j _ x y => (hcomm'' i j).pow_pow _ _
  let Ψ : (Fin 3 → Multiplicative (ZMod p)) →* P := MonoidHom.noncommPiCoprod ψ hψcomm
  have hτΨ : τ.comp Ψ = piToMultiplicative (Fin 3) (ZMod p) := by
    refine MonoidHom.functions_ext _ _ _ fun i x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_mulSingle]
    change τ (g' i ^ (Multiplicative.toAdd x).val) = _
    rw [map_pow, hτg']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    funext j
    by_cases hj : j = i
    · subst hj
      simp [he, piToMultiplicative]
    · simp [he, piToMultiplicative, hj]
  have hΨinj : Function.Injective Ψ := fun f f' h => piToMultiplicative_injective _ _ (by
    have h' := congrArg τ h
    rwa [← MonoidHom.comp_apply τ Ψ, ← MonoidHom.comp_apply τ Ψ, hτΨ] at h')
  refine ⟨Ψ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : P) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hxp : x ^ p = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero,
        zero_mul]
    rw [← map_pow, hxp, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv, Nat.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · rw [eq_top_iff]
    intro x _
    obtain ⟨f, hf⟩ := piToMultiplicative_surjective (Fin 3) (ZMod p) (τ x)
    have h1 : τ (Ψ f) = τ x := by rw [← MonoidHom.comp_apply, hτΨ, hf]
    have hx : Ψ f * ((Ψ f)⁻¹ * x) ∈ Ψ.range ⊔ A :=
      Subgroup.mul_mem_sup ⟨f, rfl⟩ (hτeq _ _ h1)
    rw [mul_inv_cancel_left, sup_comm] at hx
    exact hx
  · rw [eq_bot_iff]
    rintro x ⟨hxA, ⟨f, rfl⟩⟩
    have h1 : τ (Ψ f) = 1 := (hker _).2 hxA
    rw [← MonoidHom.comp_apply, hτΨ] at h1
    have hf : f = 1 := piToMultiplicative_injective _ _ (by rw [h1, map_one])
    rw [hf, map_one]
    exact one_mem _

end Splitting

section Lift

@[expose] def symConj {p : ℕ} (R : Matrix (Fin 2) (Fin 2) (ZMod p)) : symTwo p →+ symTwo p where
  toFun B := ⟨R * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) * Rᵀ, by
    rw [mem_symTwo, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      B.2, Matrix.mul_assoc]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' B C := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])

theorem coe_symConj {p : ℕ} (R : Matrix (Fin 2) (Fin 2) (ZMod p)) (B : symTwo p) :
    ((symConj R B : symTwo p) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      R * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) * Rᵀ :=
  rfl

theorem inv_conj_mem_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
  let φ : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hφ : Function.Injective φ := fun x y hxy => by
    have := congrArg Subtype.val hxy
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  intro x hx
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨x, hx⟩
  have hy' : g * y * g⁻¹ = x := congrArg Subtype.val hy
  rw [← hy']
  simp [mul_assoc]

variable {G Q : Type*} [Group G] [Group Q] {p : ℕ} [hp : Fact p.Prime]

theorem three_le_pRank_of_symmetric_square [Finite G] (hp2 : p ≠ 2) (A : Subgroup G) [A.Normal]
    (hAZ : A ≤ Subgroup.center G) (ρ : G →* Q) (hρ : Function.Surjective ρ) (hker : ρ.ker = A)
    (ψ : Multiplicative (symTwo p) →* Q) (hψ : Function.Injective ψ) (dd ds dt : Q)
    (hdd : ∀ B, dd * ψ B * dd⁻¹ =
      ψ (Multiplicative.ofAdd (symConj (symD p) (Multiplicative.toAdd B))))
    (hds : ∀ B, ds * ψ B * ds⁻¹ =
      ψ (Multiplicative.ofAdd (symConj (symS p) (Multiplicative.toAdd B))))
    (hdt : ∀ B, dt * ψ B * dt⁻¹ =
      ψ (Multiplicative.ofAdd (symConj (symT p) (Multiplicative.toAdd B)))) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set P : Subgroup G := ψ.range.comap ρ with hPdef
  have hmemP : ∀ x : G, x ∈ P ↔ ρ x ∈ ψ.range := fun x => Iff.rfl
  let ρP : P →* ψ.range := (ρ.comp P.subtype).codRestrict ψ.range fun x => x.2
  let τ : P →* Multiplicative (symTwo p) :=
    (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp ρP
  have hψτ : ∀ x : P, ψ (τ x) = ρ x := fun x => by
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hψ).apply_symm_apply (ρP x))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hτsurj : Function.Surjective τ := fun v => by
    obtain ⟨g, hg⟩ := hρ (ψ v)
    exact ⟨⟨g, (hmemP g).2 ⟨v, hg.symm⟩⟩, hψ ((hψτ _).trans hg)⟩
  set A' : Subgroup P := A.subgroupOf P with hA'def
  have hkerτ : A' = τ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker, ← hψτ,
      ← map_one ψ]
    exact hψ.eq_iff
  have hA'Z : A' ≤ Subgroup.center P := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    have hc := Subgroup.mem_center_iff.1 (hAZ (Subgroup.mem_subgroupOf.1 hx)) (y : G)
    exact Subtype.ext hc
  let θ : P ⧸ A' ≃* Multiplicative (symTwo p) :=
    (QuotientGroup.quotientMulEquivOfEq hkerτ).trans
      (QuotientGroup.quotientKerEquivOfSurjective τ hτsurj)
  have hθ : ∀ x : P, θ (x : P ⧸ A') = τ x := fun x => rfl
  have haut : ∀ (R : Matrix (Fin 2) (Fin 2) (ZMod p)) (d : Q),
      (∀ B, d * ψ B * d⁻¹ = ψ (Multiplicative.ofAdd (symConj R (Multiplicative.toAdd B)))) →
      ∃ α : P ≃* P, (∀ a ∈ A', α a = a) ∧
        ∀ x : P, ((Multiplicative.toAdd (θ (α x : P ⧸ A')) : symTwo p) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) =
            R * (Multiplicative.toAdd (θ (x : P ⧸ A')) : symTwo p) * Rᵀ := by
    intro R d hd
    obtain ⟨g, hg⟩ := hρ d
    have h₁ : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx => by
      obtain ⟨v, hv⟩ := (hmemP x).1 hx
      exact (hmemP _).2 ⟨Multiplicative.ofAdd (symConj R (Multiplicative.toAdd v)), by
        rw [← hd, hv, ← hg]
        simp only [map_mul, map_inv]⟩
    have : Finite P := inferInstance
    have h₂ : ∀ x ∈ P, g⁻¹ * x * g ∈ P := inv_conj_mem_of_conj_mem (H := P) h₁
    refine ⟨conjRestrict P g h₁ h₂, fun a ha => Subtype.ext ?_, fun x => ?_⟩
    · rw [conjRestrict_apply]
      have hc := Subgroup.mem_center_iff.1 (hAZ (Subgroup.mem_subgroupOf.1 ha)) g
      rw [hc]
      group
    · rw [hθ, hθ]
      have : τ (conjRestrict P g h₁ h₂ x) =
          Multiplicative.ofAdd (symConj R (Multiplicative.toAdd (τ x))) := by
        apply hψ
        rw [← hd, hψτ, hψτ, conjRestrict_apply, ← hg]
        simp only [map_mul, map_inv]
      rw [this, toAdd_ofAdd, coe_symConj]
  obtain ⟨αd, hαd, hd⟩ := haut _ dd hdd
  obtain ⟨αs, hαs, hs⟩ := haut _ ds hds
  obtain ⟨αt, hαt, ht⟩ := haut _ dt hdt
  obtain ⟨E, hE, hcard, -, -⟩ := symmetric_square_central_extension_splitting hp2 A' hA'Z θ
    αd αs αt hαd hαs hαt hd hs ht
  refine le_pRank hp.out.one_lt le_top (isElemAbelian_map hE P.subtype) ?_
  rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]

end Lift

end CFSG.SectionRank.OddCover
