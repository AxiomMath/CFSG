module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81CLin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

open CFSG.Open Matrix Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K] {n : ℕ}

private theorem eq_one_of_sq [CharP K 2] {x : K} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (x - 1) ^ 2 = 0 := by
    linear_combination hx + (1 - x) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

private theorem card_four (h : UnitaryFieldData 2 1 K) : Nat.card K = 4 :=
  h.card.trans (by norm_num)

private theorem pow_three_unit (h : UnitaryFieldData 2 1 K) (u : Kˣ) : u ^ 3 = 1 := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card Kˣ = 3 := by
    have e1 := Fintype.card_units (α := K)
    rw [← Nat.card_eq_fintype_card (α := K), card_four h] at e1
    exact e1
  rw [← hcard]
  exact pow_card_eq_one

private theorem eq_one_of_bar_eq (h : UnitaryFieldData 2 1 K) {x : K} (hx : h.bar x = x)
    (hx0 : x ≠ 0) : x = 1 := by
  rw [h.bar_apply, pow_one] at hx
  have h0 : x * (x - 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hx0
  · exact sub_eq_zero.1 h1

private theorem mem_statedSU_of_mem_uU (h : UnitaryFieldData 2 1 K) (hn : 1 ≤ n)
    {B : GL (Fin n) K} (hB : B ∈ uU h n) (hdet : (B : Matrix (Fin n) (Fin n) K).det = 1) :
    B ∈ StatedSU n (2 ^ 1) K := by
  have hK : Nat.card K = (2 ^ 1) ^ 2 := (card_four h).trans (by norm_num)
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn).1
  have hmem : B ∈ (StatedSU n (2 ^ 1) K : Set (GL (Fin n) K)) := by
    rw [hset]
    refine ⟨hdet, ?_⟩
    have hu := (mem_uU h).1 hB
    have hbar : (⇑h.bar : K → K) = fun c => c ^ 2 ^ 1 := funext fun c => h.bar_apply c
    rw [hbar] at hu
    exact hu
  exact hmem

theorem exists_conj_of_uConjAut (h : UnitaryFieldData 2 1 K) (hn : 4 ≤ n) (A : uU h n)
    (ht : (uConjAut h (by omega) A) ^ 2 = 1) :
    ∃ g : StatedProj (StatedSU n (2 ^ 1) K), uConjAut h (by omega) A = MulAut.conj g := by
  haveI := h.charP
  have hA2 : uConjAut h (by omega) (A ^ 2) = 1 := by rw [map_pow]; exact ht
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h (by omega) (A ^ 2)).1 hA2
  have hB2 : ((A ^ 3 : uU h n) : GL (Fin n) K) ^ 2 = 1 := by
    have e : ((A ^ 3 : uU h n) : GL (Fin n) K) ^ 2 = ((A ^ 2 : uU h n) : GL (Fin n) K) ^ 3 := by
      simp only [Subgroup.coe_pow]
      rw [← pow_mul, ← pow_mul]
    rw [e, hc, ← map_pow, pow_three_unit h c, map_one]
  have hdet : (((A ^ 3 : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    apply eq_one_of_sq
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hB2, Units.val_one, Matrix.det_one]
  have hBSU := mem_statedSU_of_mem_uU h (by omega) (A ^ 3).2 hdet
  have htB : uConjAut h (by omega) (A ^ 3) = uConjAut h (by omega) A := by
    rw [map_pow, pow_succ (uConjAut h (by omega) A) 2, ht, one_mul]
  refine ⟨projH _ ⟨_, hBSU⟩, ?_⟩
  rw [← htB]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := projH_surjective x
  rw [uConjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

private theorem scalar_map (φ : K ≃+* K) (x : K) :
    (Matrix.scalar (Fin n) x).map φ = Matrix.scalar (Fin n) (φ x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem mul_scalar_comm (M : Matrix (Fin n) (Fin n) K) (x : K) :
    M * Matrix.scalar (Fin n) x = Matrix.scalar (Fin n) x * M :=
  (Matrix.scalar_commute x (fun r' => Commute.all _ r') M).eq.symm

private theorem conj_scalar (g : GL (Fin n) K) (x : K) :
    (g : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) x *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) x := by
  rw [mul_scalar_comm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

private theorem phi_mulVec (φ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (fun i => φ ((M *ᵥ v) i)) = M.map φ *ᵥ (fun i => φ (v i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

private theorem bar_bar' (h : UnitaryFieldData 2 1 K) {φ : K ≃+* K} (hφ : ∀ c, φ c = h.bar c)
    (c : K) : φ (φ c) = c := by
  rw [hφ, hφ, h.bar_bar]

private theorem uLift_uLift (h : UnitaryFieldData 2 1 K) (A : uU h n) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c) (g : StatedSU n (2 ^ 1) K) :
    ((uLift h A φ (uLift h A φ g) : StatedSU n (2 ^ 1) K) : GL (Fin n) K) =
      ((A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K)) * (g : GL (Fin n) K) *
        ((A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K))⁻¹ := by
  have hφφ : φ * φ = 1 := RingEquiv.ext fun c => bar_bar' h hφ c
  have hgg : glAut φ (glAut φ (g : GL (Fin n) K)) = (g : GL (Fin n) K) := by
    rw [← MulAut.mul_apply, ← map_mul, hφφ, map_one, MulAut.one_apply]
  change (A : GL (Fin n) K) * glAut φ ((A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) *
    (A : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K)⁻¹ = _
  rw [map_mul, map_mul, map_inv, hgg]
  group

private theorem mul_glAut_mem_uU (h : UnitaryFieldData 2 1 K) (A : uU h n) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c) : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) ∈ uU h n := by
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hA : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  have hA' : Amᵀ * Am.map h.bar = 1 := by
    have e := congrArg Matrix.transpose hA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at e
  have hφm : Am.map φ = Am.map h.bar := by
    ext i j
    simp only [Matrix.map_apply, hφ]
  have hbb : (Am.map h.bar).map h.bar = Am := by
    ext i j
    simp only [Matrix.map_apply, h.bar_bar]
  rw [mem_uU, Units.val_mul, coe_glAut, ← hAm]
  calc ((Am * Am.map φ).map h.bar)ᵀ * (Am * Am.map φ)
      = (Am.map h.bar * Am)ᵀ * (Am * Am.map h.bar) := by rw [Matrix.map_mul, hφm, hbb]
    _ = Amᵀ * (((Am.map h.bar)ᵀ * Am) * Am.map h.bar) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.one_mul, hA']

private theorem coe_uLift_scalar (h : UnitaryFieldData 2 1 K) (A : uU h n) (φ : K ≃+* K)
    {g : StatedSU n (2 ^ 1) K} {μ : Kˣ}
    (hg : (g : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) μ) :
    (((uLift h A φ g : StatedSU n (2 ^ 1) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) (φ (μ : K)) := by
  rw [coe_uLift, hg, Matrix.GeneralLinearGroup.coe_scalar, scalar_map, conj_scalar]

private def liftSub (h : UnitaryFieldData 2 1 K) (A : uU h n) (φ : K ≃+* K)
    (E : Subgroup (StatedProj (StatedSU n (2 ^ 1) K))) : Subgroup (StatedSU n (2 ^ 1) K) where
  carrier := {g | projH _ g ∈ E ∧ uLift h A φ g = g}
  mul_mem' {a b} ha hb := ⟨by rw [map_mul]; exact E.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨by rw [map_one]; exact E.one_mem, map_one _⟩
  inv_mem' {a} ha := ⟨by rw [map_inv]; exact E.inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem false_of_bar (h : UnitaryFieldData 2 1 K) (A : uU h n) {φ : K ≃+* K} (hn4 : 4 ≤ n)
    (hn7 : n ≤ 7) (hφ : ∀ c, φ c = h.bar c)
    (ht : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1)
    (E : Subgroup (StatedProj (StatedSU n (2 ^ 1) K))) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4)
    (hfix : ∀ e ∈ E, (uConjAut h (by omega) A * uFieldAut h (by omega) φ :
      MulAut (StatedProj (StatedSU n (2 ^ 1) K))) e = e) : False := by
  haveI := h.charP
  haveI := h.finite
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hn1 : 1 ≤ n := by omega
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hφφ : ∀ c, φ (φ c) = c := bar_bar' h hφ
  set t := uConjAut h hn1 A * uFieldAut h hn1 φ with htdef
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set Ainv : Matrix (Fin n) (Fin n) K := (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) with hAinv
  have hinvA : Ainv * Am = 1 := by rw [hAinv, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM := mul_glAut_mem_uU h A hφ
  have hMone : uConjAut h hn1 ⟨_, hM⟩ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ := projH_surjective x
    have h2 : t (t (projH _ g)) = projH _ g := by
      have e := congrArg (fun s : MulAut (StatedProj (StatedSU n (2 ^ 1) K)) => s (projH _ g)) ht
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using e
    rw [htdef, uLift_proj, uLift_proj] at h2
    rw [uConjAut_proj, MulAut.one_apply, ← h2]
    exact congrArg (projH _) (Subtype.ext (uLift_uLift h A hφ g).symm)
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h (by omega) ⟨_, hM⟩).1 hMone
  have hcM : Am * Am.map φ = Matrix.scalar (Fin n) (c : K) := by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simpa only [Units.val_mul, coe_glAut, Matrix.GeneralLinearGroup.coe_scalar] using e
  have h1 : Am.map φ * Am = Matrix.scalar (Fin n) (c : K) := by
    calc Am.map φ * Am = Ainv * (Am * Am.map φ) * Am := by
          rw [← Matrix.mul_assoc Ainv Am, hinvA, Matrix.one_mul]
      _ = Matrix.scalar (Fin n) (c : K) := by
          rw [hcM, mul_scalar_comm, Matrix.mul_assoc, hinvA, Matrix.mul_one]
  have h2 : (Am * Am.map φ).map φ = Am.map φ * Am := by
    have e := map_mul (φ.mapMatrix : Matrix (Fin n) (Fin n) K ≃+* Matrix (Fin n) (Fin n) K) Am
      (Am.map φ)
    simp only [RingEquiv.mapMatrix_apply] at e
    rw [e]
    congr 1
    ext i j
    simp only [Matrix.map_apply, hφφ]
  have hcφ : Matrix.scalar (Fin n) (φ (c : K)) = Matrix.scalar (Fin n) (c : K) :=
    calc Matrix.scalar (Fin n) (φ (c : K)) = (Matrix.scalar (Fin n) (c : K)).map φ :=
          (scalar_map φ _).symm
      _ = (Am * Am.map φ).map φ := by rw [hcM]
      _ = Am.map φ * Am := h2
      _ = Matrix.scalar (Fin n) (c : K) := h1
  have hc1 : (c : K) = 1 :=
    eq_one_of_bar_eq h (by rw [← hφ]; exact Matrix.scalar_inj.1 hcφ) c.ne_zero
  have hAA : Am * Am.map φ = 1 := by rw [hcM, hc1, map_one]
  set Ehat := liftSub h A φ E with hEhat
  have hker : ∀ g ∈ Ehat, projH _ g = 1 → g = 1 := by
    intro g hg hg1
    have hmem := (QuotientGroup.eq_one_iff g).1 hg1
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    have e1 := coe_uLift_scalar h A φ hμ.symm
    rw [hg.2, ← hμ, Matrix.GeneralLinearGroup.coe_scalar] at e1
    have hμ1 : (μ : K) = 1 :=
      eq_one_of_bar_eq h (by rw [← hφ]; exact (Matrix.scalar_inj.1 e1).symm) μ.ne_zero
    have hμ1' : μ = 1 := Units.ext hμ1
    apply Subtype.ext
    rw [← hμ, hμ1', map_one, Subgroup.coe_one]
  have hinj : ∀ a ∈ Ehat, ∀ b ∈ Ehat, projH _ a = projH _ b → a = b := by
    intro a ha b hb hab
    have h1 := hker (a⁻¹ * b) (Ehat.mul_mem (Ehat.inv_mem ha) hb)
      (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    rw [← mul_inv_cancel_left a b, h1, mul_one]
  have hsurj : ∀ x ∈ E, ∃ g ∈ Ehat, projH _ g = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := projH_surjective x
    have hty : projH _ (uLift h A φ y) = projH _ y := by
      rw [← uLift_proj]
      exact hfix _ hx
    have hz := (projH_eq_projH_iff).1 hty.symm
    set z := y⁻¹ * uLift h A φ y with hzdef
    have hz1 : projH _ z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨μ, hμ⟩ := hz
    have hμ3 : μ ^ 3 = 1 := pow_three_unit h μ
    have hLz : uLift h A φ z = z⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_uLift_scalar h A φ hμ.symm, Subgroup.coe_inv, ← hμ, ← map_inv,
        Matrix.GeneralLinearGroup.coe_scalar]
      congr 1
      rw [hφ, h.bar_apply, pow_one]
      have hsq : μ ^ 2 = μ⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hμ3)
      rw [← Units.val_pow_eq_pow_val, hsq]
    have hz3 : z ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hμ, ← map_pow, hμ3, map_one, Subgroup.coe_one]
    have hy : uLift h A φ y = y * z := by rw [hzdef, mul_inv_cancel_left]
    have hproj : projH _ (y * z⁻¹) = projH _ y := by
      rw [map_mul, map_inv, hz1, inv_one, mul_one]
    refine ⟨y * z⁻¹, ⟨by rw [hproj]; exact hx, ?_⟩, hproj⟩
    rw [map_mul, map_inv, hLz, inv_inv, hy, mul_assoc]
    congr 1
    rw [← pow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hz3)
  have hEab : IsElemAbelian 3 Ehat := by
    have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · refine hinj _ (Ehat.mul_mem a.2 b.2) _ (Ehat.mul_mem b.2 a.2) ?_
      change projH _ ((a : StatedSU n (2 ^ 1) K) * (b : StatedSU n (2 ^ 1) K)) =
        projH _ ((b : StatedSU n (2 ^ 1) K) * (a : StatedSU n (2 ^ 1) K))
      rw [map_mul, map_mul]
      exact hEc _ a.2.1 _ b.2.1
    · refine hker _ (Ehat.pow_mem hx 3) ?_
      rw [map_pow]
      exact hE.2 _ hx.1
  have hEhcard : Nat.card Ehat = 3 ^ 4 := by
    rw [← hcard]
    refine Nat.card_congr (Equiv.ofBijective (fun g : Ehat => (⟨projH _ g, g.2.1⟩ : E)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hinj _ a.2 _ b.2 (congrArg Subtype.val hab))
    · rintro ⟨x, hx⟩
      obtain ⟨g, hg, hgx⟩ := hsurj x hx
      exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  set G : Subgroup (GL (Fin n) K) := Ehat.map (StatedSU n (2 ^ 1) K).subtype with hGdef
  have hGcard : Nat.card G = 3 ^ 4 := by
    rw [hGdef, Subgroup.card_map_of_injective (StatedSU n (2 ^ 1) K).subtype_injective, hEhcard]
  have hGab : IsElemAbelian 3 G := by
    obtain ⟨hc', hp'⟩ := hEab
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      have h1 := congrArg Subtype.val (hc'.is_comm.comm (⟨a', ha'⟩ : Ehat) ⟨b', hb'⟩)
      change (a : GL (Fin n) K) * b = b * a
      rw [← hae, ← hbe]
      exact congrArg Subtype.val h1
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow, hp' x' hx', map_one]
  have hcomm : ∀ x ∈ Ehat, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Am =
      Am * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ := by
    intro x hx
    have e := congrArg (fun g : StatedSU n (2 ^ 1) K => ((g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) hx.2
    simp only [coe_uLift] at e
    rw [← hAm, ← hAinv] at e
    calc ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Am
        = (Am * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ * Ainv) * Am := by rw [e]
      _ = Am * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ := by
        rw [Matrix.mul_assoc _ Ainv Am, hinvA, Matrix.mul_one]
  set τ : (Fin n → K) → (Fin n → K) := fun v => Am *ᵥ (fun i => φ (v i)) with hτ
  have τadd : ∀ a b, τ (a + b) = τ a + τ b := fun a b => by
    simp only [hτ, Pi.add_apply, map_add]
    rw [← Matrix.mulVec_add]
    rfl
  have τsmul : ∀ (c : K) v, τ (c • v) = φ c • τ v := fun c v => by
    simp only [hτ, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have τneg : ∀ a, τ (-a) = -τ a := fun a => by
    simp only [hτ, Pi.neg_apply, map_neg]
    rw [← Matrix.mulVec_neg]
    rfl
  have ττ : ∀ v, τ (τ v) = v := fun v => by
    simp only [hτ]
    rw [phi_mulVec, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    funext i
    exact hφφ (v i)
  have τg : ∀ x ∈ Ehat, ∀ v, τ (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ τ v := fun x hx v => by
    simp only [hτ]
    rw [phi_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x hx]
  let Vτ : AddSubgroup (Fin n → K) :=
    { carrier := {v | τ v = v}
      add_mem' := fun {a b} ha hb => by
        change τ (a + b) = a + b
        rw [τadd, show τ a = a from ha, show τ b = b from hb]
      zero_mem' := by
        change τ 0 = 0
        simp only [hτ, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      neg_mem' := fun {a} ha => by
        change τ (-a) = -a
        rw [τneg, show τ a = a from ha] }
  have hmemV : ∀ v, v ∈ Vτ ↔ τ v = v := fun v => Iff.rfl
  set W : Submodule (ZMod 2) (Fin n → K) := AddSubgroup.toZModSubmodule 2 Vτ with hWdef
  have hmemW : ∀ v, v ∈ W ↔ τ v = v := fun v => by
    rw [hWdef, AddSubgroup.mem_toZModSubmodule]
    exact hmemV v
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  have hωφ : φ ω ≠ ω := by rw [hφ]; exact hω
  have hs0 : φ ω + ω ≠ 0 := fun h0 => hωφ (CharTwo.add_eq_zero.1 h0)
  have hsub0 : ω - φ ω ≠ 0 := fun h0 => hωφ (sub_eq_zero.1 h0).symm
  have hW : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    rw [hmemW] at hw ⊢
    change τ (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = _
    rw [τg x hx, hw]
    rfl
  have hplus : ∀ v, v + τ v ∈ W := fun v => by
    rw [hmemW, τadd, ττ, add_comm]
  have hfaith : ∀ g ∈ G, (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w) → g = 1 := by
    rintro _ ⟨x, hx, rfl⟩ hfixW
    refine eq_one_of_mulVec fun v => ?_
    set gm : Matrix (Fin n) (Fin n) K := (((StatedSU n (2 ^ 1) K).subtype x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) with hgm
    have hv : (φ ω + ω) • v = φ ω • (v + τ v) + (ω • v + τ (ω • v)) := by
      rw [τsmul]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(φ ω * τ v i)) * h2K
    have hgv : gm *ᵥ ((φ ω + ω) • v) = (φ ω + ω) • v := by
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, hfixW _ (hplus v), hfixW _ (hplus (ω • v))]
    rw [Matrix.mulVec_smul] at hgv
    exact smul_right_injective (Fin n → K) hs0 hgv
  have hdim : finrank (ZMod 2) W ≤ n := by
    have hpair : Function.Injective (fun p : W × W => (p.1 : Fin n → K) + ω • (p.2 : Fin n → K)) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      simp only at hab
      have ha := (hmemW a).1 a.2
      have hb := (hmemW b).1 b.2
      have ha' := (hmemW a').1 a'.2
      have hb' := (hmemW b').1 b'.2
      have hcd : (a : Fin n → K) - a' = ω • ((b' : Fin n → K) - b) := by
        rw [smul_sub]
        linear_combination (exp := 1) hab
      have hτc : τ ((a : Fin n → K) - a') = (a : Fin n → K) - a' := by
        rw [sub_eq_add_neg, τadd, τneg, ha, ha']
      have hτd : τ ((b' : Fin n → K) - b) = (b' : Fin n → K) - b := by
        rw [sub_eq_add_neg, τadd, τneg, hb, hb']
      have hd0 : (b' : Fin n → K) - b = 0 := by
        have e1 : (ω - φ ω) • ((b' : Fin n → K) - b) = 0 := by
          rw [sub_smul, ← hcd, ← hτd, ← τsmul, ← hcd, hτc, sub_self]
        exact (smul_eq_zero.1 e1).resolve_left hsub0
      have hc0 : (a : Fin n → K) - a' = 0 := by rw [hcd, hd0, smul_zero]
      have hbb : b = b' := Subtype.ext (sub_eq_zero.1 hd0).symm
      have haa : a = a' := Subtype.ext (sub_eq_zero.1 hc0)
      rw [haa, hbb]
    have hle := Nat.card_le_card_of_injective _ hpair
    rw [Nat.card_prod, ← FiniteField.pow_finrank_eq_natCard 2 W, Nat.card_fun, Nat.card_fin,
      card_four h] at hle
    have h4 : 2 ^ (2 * finrank (ZMod 2) W) ≤ 2 ^ (2 * n) := by
      calc 2 ^ (2 * finrank (ZMod 2) W) = 2 ^ finrank (ZMod 2) W * 2 ^ finrank (ZMod 2) W := by
            ring
        _ ≤ 4 ^ n := hle
        _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
    omega
  have hbound := card_le_of_faithful G hGab W hW hfaith
  rw [hGcard] at hbound
  have h3 : 3 ^ (finrank (ZMod 2) W / 2) ≤ 3 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (3 : ℕ) ^ 4 ≤ 3 ^ 3 := hbound.trans h3
  norm_num at this

theorem innerOfFix_unitary (h : UnitaryFieldData 2 1 K) (hn4 : 4 ≤ n) (hn7 : n ≤ 7) :
    InnerOfFix (StatedProj (StatedSU n (2 ^ 1) K)) := by
  intro E hE hcard t ht hfix
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by
    rintro ⟨h3, -⟩
    omega
  obtain ⟨A, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h (by omega) hq t
  rcases uFieldAut_eq_or_of_sq h (by omega) hq ht with hφ | hφ
  · subst hφ
    rw [map_one, mul_one] at ht ⊢
    exact exists_conj_of_uConjAut h hn4 A ht
  · exact (false_of_bar h A hn4 hn7 hφ ht E hE hcard hfix).elim

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

end
