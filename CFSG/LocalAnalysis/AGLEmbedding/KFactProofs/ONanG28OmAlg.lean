module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmSpec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSylow

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28

attribute [local irreducible] txL tU tZ tO tzc

theorem neg_mat (A : Matrix (Fin 6) (Fin 6) GF8) : -A = A := by
  ext i j
  rfl

theorem add_self_mat (A : Matrix (Fin 6) (Fin 6) GF8) : A + A = 0 := by
  have h : ∀ a : GF8, a + a = 0 := by decide
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact h _

theorem getElem!_invDiag (u : Array ℕ) {t : ℕ} (ht : t < 36) :
    (invDiag u)[t]! = if t % 7 = 0 then u[t]! ^^^ 1 else u[t]! := by
  rw [invDiag, getElem!_ofFn_nat' _ ht]

theorem valid_invDiag {u : Array ℕ} (hu : Valid u) : Valid (invDiag u) := by
  refine ⟨by simp [invDiag], fun t ht => ?_⟩
  rw [getElem!_invDiag u ht]
  split_ifs
  · exact xor_lt8' (hu.2 t ht) (by norm_num)
  · exact hu.2 t ht

theorem decode_invDiag {u : Array ℕ} (hu : Valid u) : decode (invDiag u) = decode u + 1 := by
  ext i j
  have hlt : 6 * i.val + j.val < 36 := by omega
  have hi := i.2
  have hj := j.2
  simp only [decode, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]
  rw [getElem!_invDiag u hlt]
  have hdiag : (6 * i.val + j.val) % 7 = 0 ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst h
      omega
  by_cases h : i = j
  · have h7 : (6 * i.val + j.val) % 7 = 0 := hdiag.mpr h
    rw [ite_eq_left h7, ite_eq_left h, ofNat'_xor' (hu.2 _ hlt) (by norm_num)]
    rfl
  · have h7 : ¬ (6 * i.val + j.val) % 7 = 0 := fun h7 => h (hdiag.mp h7)
    rw [ite_eq_right h7, ite_eq_right h]
    exact (add_zero _).symm

theorem invDiag_invDiag {u : Array ℕ} (hu : Valid u) : invDiag (invDiag u) = u := by
  apply eq_of_decode_eq (valid_invDiag (valid_invDiag hu)) hu
  rw [decode_invDiag (valid_invDiag hu), decode_invDiag hu, add_assoc, add_self_mat, add_zero]

theorem xor_one_mod_two : ∀ a : Fin 8, ((a : ℕ) ^^^ 1) % 2 = ((a : ℕ) % 2 + 1) % 2 := by decide

theorem canon_eq_or (u : Array ℕ) : canonCode u = u ∨ canonCode u = invDiag u := by
  unfold canonCode
  split_ifs <;> simp

theorem valid_canonCode {u : Array ℕ} (hu : Valid u) : Valid (canonCode u) := by
  rcases canon_eq_or u with h | h <;> rw [h]
  · exact hu
  · exact valid_invDiag hu

theorem getElem!_invDiag_zero (u : Array ℕ) : (invDiag u)[0]! = u[0]! ^^^ 1 := by
  rw [getElem!_invDiag u (by norm_num)]
  simp

theorem canon_even {u : Array ℕ} (hu : Valid u) : (canonCode u)[0]! % 2 = 0 := by
  unfold canonCode
  by_cases h : u[0]! % 2 = 0
  · rw [ite_eq_left h]
    exact h
  · rw [ite_eq_right h, getElem!_invDiag_zero]
    have hx := xor_one_mod_two ⟨u[0]!, hu.2 0 (by norm_num)⟩
    simp only at hx
    omega

section IsCC


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] def IsCC (c : Array ℕ) (x : adjointGroup .G2 K) : Prop :=
  M.rho (x * zE M * x⁻¹) = decode c ∨ M.rho (x * (zE M)⁻¹ * x⁻¹) = decode c

theorem rho_mul_inv (g : adjointGroup .G2 K) : M.rho g * M.rho g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem rho_inv_mul (g : adjointGroup .G2 K) : M.rho g⁻¹ * M.rho g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem quad_rho_zE (hq : quadOK tzc = true) :
    M.rho (zE M) * M.rho (zE M) + M.rho (zE M) + 1 = 0 := by
  have h := quadOK_spec hq
  rw [rho_zE, ← decode_mulCode valid_tzc valid_tzc, ← decode_idCode]
  ext i j
  have hlt : 6 * i.val + j.val < 36 := by omega
  have hv := valid_mulCode valid_tzc valid_tzc
  simp only [decode, Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
  rw [← ofNat'_xor' (hv.2 _ hlt) (valid_tzc.2 _ hlt), ← ofNat'_xor' (by
    exact xor_lt8' (hv.2 _ hlt) (valid_tzc.2 _ hlt)) (valid_idCode.2 _ hlt), h _ hlt]
  rfl

theorem conj_quad_aux {R : Type*} [Ring R] (X Xi Z : R) (h1 : Xi * X = 1) (h2 : X * Xi = 1) :
    (X * Z * Xi) * (X * Z * Xi) + X * Z * Xi + 1 = X * (Z * Z + Z + 1) * Xi := by
  calc (X * Z * Xi) * (X * Z * Xi) + X * Z * Xi + 1
      = X * Z * (Xi * X) * Z * Xi + X * Z * Xi + X * Xi := by
        rw [h2]; simp only [mul_assoc]
    _ = X * (Z * Z + Z + 1) * Xi := by rw [h1]; noncomm_ring

theorem quad_conj (hq : quadOK tzc = true) (x : adjointGroup .G2 K) :
    M.rho (x * zE M * x⁻¹) * M.rho (x * zE M * x⁻¹) + M.rho (x * zE M * x⁻¹) + 1 = 0 := by
  have h := quad_rho_zE M hq
  have e1 : M.rho (x * zE M * x⁻¹) = M.rho x * M.rho (zE M) * M.rho x⁻¹ := by
    rw [map_mul, map_mul]
  rw [e1, conj_quad_aux _ _ _ (rho_inv_mul M x) (rho_mul_inv M x), h]
  simp

theorem rho_conj_zinv (hq : quadOK tzc = true) (x : adjointGroup .G2 K) :
    M.rho (x * (zE M)⁻¹ * x⁻¹) = M.rho (x * zE M * x⁻¹) + 1 := by
  have hw3 : (x * zE M * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, zE_pow_three]
    group
  have hinv : x * (zE M)⁻¹ * x⁻¹ = (x * zE M * x⁻¹) * (x * zE M * x⁻¹) := by
    have : (x * zE M * x⁻¹)⁻¹ = (x * zE M * x⁻¹) * (x * zE M * x⁻¹) := by
      apply inv_eq_of_mul_eq_one_right
      have e : (x * zE M * x⁻¹) * ((x * zE M * x⁻¹) * (x * zE M * x⁻¹)) =
          (x * zE M * x⁻¹) ^ 3 := (pow_three _).symm
      rw [e, hw3]
    rw [← this]
    group
  rw [hinv, map_mul]
  have h := quad_conj M hq x
  rw [add_assoc] at h
  have := eq_neg_of_add_eq_zero_left h
  rw [neg_add, neg_mat, neg_mat] at this
  exact this

theorem isCC_inv {u : Array ℕ} (hu : Valid u) (hq : quadOK tzc = true)
    {x : adjointGroup .G2 K} (h : IsCC M u x) : IsCC M (invDiag u) x := by
  rw [IsCC, decode_invDiag hu]
  rcases h with h | h
  · right
    rw [rho_conj_zinv M hq, h]
  · left
    have := rho_conj_zinv M hq x
    rw [h] at this
    rw [this, add_assoc, add_self_mat, add_zero]
  
theorem isCC_canon {u : Array ℕ} (hu : Valid u) (hq : quadOK tzc = true)
    {x : adjointGroup .G2 K} (h : IsCC M u x) : IsCC M (canonCode u) x := by
  rcases canon_eq_or u with h' | h' <;> rw [h']
  · exact h
  · exact isCC_inv M hu hq h

theorem isCC_step {c G Gi : Array ℕ} (hc : Valid c) (hG : Valid G) (hGi : Valid Gi)
    {g x : adjointGroup .G2 K} (hg : M.rho g = decode G) (hgi : M.rho g⁻¹ = decode Gi)
    (h : IsCC M c x) : IsCC M (conjCode G Gi c) (g * x) := by
  have key : ∀ w : adjointGroup .G2 K,
      M.rho (x * w * x⁻¹) = decode c →
        M.rho (g * x * w * (g * x)⁻¹) = decode (conjCode G Gi c) := by
    intro w hw
    have e : g * x * w * (g * x)⁻¹ = g * (x * w * x⁻¹) * g⁻¹ := by group
    rw [e, map_mul, map_mul, hw, hg, hgi, conjCode,
      decode_mulCode (valid_mulCode hG hc) hGi, decode_mulCode hG hc]
  rcases h with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

theorem tree_sem (hq : quadOK tzc = true) (D : TreeData) (hok : D.ok = true)
    (gE rE : ℕ → adjointGroup .G2 K)
    (hgens : ∀ s < D.gens.size, Valid D.gens[s]! ∧ Valid D.ginvs[s]! ∧
      M.rho (gE s) = decode D.gens[s]! ∧ M.rho (gE s)⁻¹ = decode D.ginvs[s]!)
    (hroots : ∀ k < D.R, Valid D.roots[k]! ∧ (D.roots[k]!)[0]! % 2 = 0 ∧
      IsCC M D.roots[k]! (rE k)) :
    ∀ n < D.N, (D.build[n]!).2 < D.R ∧ Valid (D.build[n]!).1 ∧ (D.build[n]!).1[0]! % 2 = 0 ∧
      ∃ p ∈ Subgroup.closure {x | ∃ s < D.gens.size, x = gE s},
        IsCC M (D.build[n]!).1 (p * rE (D.build[n]!).2) := by
  obtain ⟨-, hspec⟩ := TreeData.build_spec D hok
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨hroot, hnon⟩ := hspec n hn
    by_cases hnR : n < D.R
    · rw [hroot hnR]
      obtain ⟨hv, he, hc⟩ := hroots n hnR
      exact ⟨hnR, hv, he, 1, Subgroup.one_mem _, by simpa using hc⟩
    · obtain ⟨hp, hs, hbuild⟩ := hnon (not_lt.mp hnR)
      obtain ⟨hr, hv, -, p, hpmem, hc⟩ := ih (D.par n) hp (lt_trans hp hn)
      obtain ⟨hg1, hg2, hg3, hg4⟩ := hgens (D.sym n) hs
      have e1 : (D.build[n]!).1 = canonCode (conjCode D.gens[D.sym n]! D.ginvs[D.sym n]!
          (D.build[D.par n]!).1) := by rw [hbuild]
      have e2 : (D.build[n]!).2 = (D.build[D.par n]!).2 := by rw [hbuild]
      rw [e1, e2]
      have hvv := valid_mulCode (valid_mulCode hg1 hv) hg2
      refine ⟨hr, valid_canonCode hvv, canon_even hvv,
        gE (D.sym n) * p, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨D.sym n, hs, rfl⟩) hpmem,
        ?_⟩
      have := isCC_step M hv hg1 hg2 hg3 hg4 hc
      rw [← mul_assoc] at this
      exact isCC_canon M hvv hq this

end IsCC

end CFSG.AGLEmbedding.KFactProofs.G28
