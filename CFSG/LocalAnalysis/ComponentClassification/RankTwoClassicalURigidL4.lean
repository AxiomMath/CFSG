module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidBarW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped commutatorElement

section BarW

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ}

theorem noNormalTwo_of_uBarL_le (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) (hk : 2 ≤ k)
    {M : Subgroup (StatedProj (StatedSU (2 + k) (2 ^ f) K))} (hLM : uBarL K k f ≤ M)
    (hMW : M ≤ centralizer (uBarW K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K)))) :
    NoNormalTwo M := by
  have := h.finite
  have hK := h.card_eq_sq
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  intro Q hQ hQ2 hN
  set L := Q.subgroupOf (uBarL K k f)
  have hLn : L.Normal :=
    ⟨fun n hn l => (mem_normalizer_iff.mp (hN (hLM l.2)) n.1).mp hn⟩
  have hL2 : IsPGroup 2 ↥L := fun g => by
    obtain ⟨n, hn⟩ := hQ2 ⟨g.1.1, g.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h' := congrArg (Subtype.val : ↥Q → StatedProj (StatedSU (2 + k) (2 ^ f) K)) hn
    simpa using h'
  have hLbot := eq_bot_of_normal_isPGroup_two_of_quasisimple (isQuasisimple_uBarL hK hf hk)
    (odd_card_center_uBarL hK hf hk) L hL2
  have hQW : ∀ x ∈ Q, ∀ w ∈ uBarW K k f, x * w = w * x := fun x hx w hw =>
    (mem_centralizer_iff.mp (hMW (hQ hx)) w hw).symm
  have hQL : ∀ x ∈ Q, ∀ l ∈ uBarL K k f, x * l = l * x := by
    intro x hx l hl
    have h1 : ⁅x, l⁆ ∈ Q := by
      have hl' : l * x⁻¹ * l⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp (hN (hLM hl)) x⁻¹).mp (inv_mem hx)
      rw [commutatorElement_def, mul_assoc x, mul_assoc x]
      exact mul_mem hx hl'
    have h2 : ⁅x, l⁆ ∈ uBarL K k f := by
      obtain ⟨g, rfl, a, D, hg⟩ := exists_blk_of_commute_uBarW (by omega) hζ hζ1 (hQW x hx)
      obtain ⟨S, rfl⟩ := hl
      obtain ⟨S', hS'⟩ := commutatorElement_mem_range_uL h hg (coe_uL S)
        (show a • (1 : Matrix (Fin 2) (Fin 2) K) * 1 = 1 * a • 1 by
          rw [Matrix.mul_one, Matrix.one_mul])
      exact ⟨S', by simp only [MonoidHom.comp_apply]; rw [hS', map_commutatorElement]⟩
    have h3 : (⟨⁅x, l⁆, h2⟩ : ↥(uBarL K k f)) ∈ L := h1
    rw [hLbot, mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h3)
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hpow := pow_eq_one_of_commute_uBarW_uBarL h hk hζ hζ1 (hQW x hx) (hQL x hx)
  obtain ⟨n, hn⟩ := hQ2 ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have h2 : orderOf x ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hpow
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop : Nat.Coprime (2 ^ n) (2 ^ f + 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

end BarW

section Pow

variable {K : Type} [Field K] {k f : ℕ}

theorem semi_pow {τ : K ≃+* K} {B : GL (Fin (2 + k)) K}
    {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
    (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : B * glAut τ (g : GL (Fin (2 + k)) K) * B⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
        α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩)
    {X : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K} (hB : B.val = blk X D)
    (n : ℕ) :
    ∃ (Bn : GL (Fin (2 + k)) K) (Xn : Matrix (Fin 2) (Fin 2) K) (Dn : Matrix (Fin k) (Fin k) K),
      Bn.val = blk Xn Dn ∧ ∀ g : StatedSU (2 + k) (2 ^ f) K,
        ∃ hg : Bn * glAut (τ ^ n) (g : GL (Fin (2 + k)) K) * Bn⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
          (α ^ n) (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩ := by
  induction n with
  | zero =>
    refine ⟨1, 1, 1, by rw [Units.val_one, blk_one], fun g => ⟨?_, ?_⟩⟩
    · simp only [pow_zero, map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
      exact g.2
    · simp only [pow_zero, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      simp only [map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  | succ n ih =>
    obtain ⟨Bn, Xn, Dn, hBn, hαn⟩ := ih
    refine ⟨B * glAut τ Bn, X * Xn.map τ, D * Dn.map τ, ?_, fun g => ?_⟩
    · rw [Units.val_mul, coe_glAut, hB, hBn, blk_map_fun _ (map_zero τ), blk_mul]
    · obtain ⟨hgn, hαgn⟩ := hαn g
      obtain ⟨hg', hαg'⟩ := hα ⟨_, hgn⟩
      have e1 : glAut (τ ^ (n + 1)) (g : GL (Fin (2 + k)) K) =
          glAut τ (glAut (τ ^ n) (g : GL (Fin (2 + k)) K)) := by
        rw [pow_succ', map_mul, MulAut.mul_apply]
      have heq : B * glAut τ (Bn * glAut (τ ^ n) (g : GL (Fin (2 + k)) K) * Bn⁻¹) * B⁻¹ =
          B * glAut τ Bn * glAut (τ ^ (n + 1)) (g : GL (Fin (2 + k)) K) *
            (B * glAut τ Bn)⁻¹ := by
        rw [e1, map_mul (glAut τ) (Bn * glAut (τ ^ n) (g : GL (Fin (2 + k)) K)) Bn⁻¹,
          map_mul (glAut τ) Bn, map_inv (glAut τ) Bn]
        group
      refine ⟨heq ▸ hg', ?_⟩
      rw [pow_succ', MulAut.mul_apply, hαgn, hαg']
      congr 1
      exact Subtype.ext heq

theorem inner_pow {B : GL (Fin (2 + k)) K}
    {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
    (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : B * (g : GL (Fin (2 + k)) K) * B⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
        α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩) (n : ℕ) :
    ∀ g : StatedSU (2 + k) (2 ^ f) K,
      ∃ hg : B ^ n * (g : GL (Fin (2 + k)) K) * (B ^ n)⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
        (α ^ n) (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩ := by
  induction n with
  | zero =>
    intro g
    refine ⟨by simp, ?_⟩
    simp only [pow_zero, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp
  | succ n ih =>
    intro g
    obtain ⟨hgn, hαgn⟩ := ih g
    obtain ⟨hg', hαg'⟩ := hα ⟨_, hgn⟩
    have heq : B * (B ^ n * (g : GL (Fin (2 + k)) K) * (B ^ n)⁻¹) * B⁻¹ =
        B ^ (n + 1) * (g : GL (Fin (2 + k)) K) * (B ^ (n + 1))⁻¹ := by
      rw [pow_succ']
      group
    refine ⟨heq ▸ hg', ?_⟩
    rw [pow_succ', MulAut.mul_apply, hαgn, hαg']
    congr 1
    exact Subtype.ext heq

end Pow

section Four

variable {K : Type} [Field K] [CharP K 2] {f : ℕ}

omit [CharP K 2] in
theorem map_one_add_onesM (τ : K ≃+* K) :
    (1 + (onesM : Matrix (Fin 2) (Fin 2) K)).map τ = 1 + onesM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onesM]

omit [CharP K 2] in
theorem onesM_apply (i j : Fin 2) : (onesM : Matrix (Fin 2) (Fin 2) K) i j = 1 := by
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP K 2] in
theorem eq_of_commute_onesM {D : Matrix (Fin 2) (Fin 2) K} (hD : D * onesM = onesM * D) :
    D 0 1 = D 1 0 ∧ D 1 1 = D 0 0 := by
  have h00 := congrFun (congrFun hD 0) 0
  have h01 := congrFun (congrFun hD 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, onesM_apply, mul_one, one_mul] at h00 h01
  exact ⟨add_left_cancel h00, by linear_combination h01.symm⟩

theorem mul_self_of_symm {D : Matrix (Fin 2) (Fin 2) K} (h1 : D 0 1 = D 1 0)
    (h2 : D 1 1 = D 0 0) : D * D = (D 0 0 * D 0 0 + D 0 1 * D 0 1) • 1 := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] <;>
    simp only [one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero]
  · rw [← h1]
  · rw [h2, h1]
    linear_combination (D 0 0 * D 1 0) * h2'
  · rw [h2]
    linear_combination (D 1 0 * D 0 0) * h2'
  · rw [h2, h1]
    ring

theorem eq_smul_one_of_pow {D : Matrix (Fin 2) (Fin 2) K} (h1 : D 0 1 = D 1 0)
    (h2 : D 1 1 = D 0 0) (hdet : D 0 0 * D 0 0 + D 0 1 * D 0 1 ≠ 0) {m : ℕ} (hm : Odd m)
    {d : K} (hd : D ^ m = d • 1) : D = D 0 0 • 1 := by
  obtain ⟨j, rfl⟩ := hm
  have hDm : D ^ (2 * j + 1) = (D 0 0 * D 0 0 + D 0 1 * D 0 1) ^ j • D := by
    rw [pow_succ, pow_mul, sq, mul_self_of_symm h1 h2, smul_pow, one_pow, Matrix.smul_mul,
      Matrix.one_mul]
  rw [hDm] at hd
  have h01 : D 0 1 = 0 := by
    have := congrFun (congrFun hd 0) 1
    simp only [Matrix.smul_apply, smul_eq_mul, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hdet)
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.smul_apply, smul_eq_mul, one_apply_eq,
      one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero]
  · exact h01
  · rw [← h1, h01]
  · exact h2

omit [CharP K 2] in
theorem vecMulVec_uw₀_two (hk : 2 ≤ 2) : vecMulVec (uw₀ (K := K) hk) (uw₀ hk) = onesM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uw₀, onesM, vecMulVec_apply]

end Four

section FourFix

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ}

theorem fix_uBarL_of_fix_four (h : UnitaryFieldData 2 f K)
    {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))} {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) (hW : ∀ w ∈ uBarW K 2 f, α w = w)
    (hN : ∀ S : StatedSU 2 (2 ^ f) K, (S : GL (Fin 2) K).val = 1 + onesM →
      α (uProj K (2 + 2) f (uL K 2 f S)) = uProj K (2 + 2) f (uL K 2 f S)) :
    ∀ l ∈ uBarL K 2 f, α l = l := by
  have hK := h.card_eq_sq
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  obtain ⟨τ, B, -, hB⟩ := exists_unitary_semilinear_statedProj h (n := 2 + 2) (by omega)
    (fun h' => absurd h'.1 (by omega)) α
  have hα : ∀ g : StatedSU (2 + 2) (2 ^ f) K,
      ∃ hg : B * glAut τ (g : GL (Fin (2 + 2)) K) * B⁻¹ ∈ StatedSU (2 + 2) (2 ^ f) K,
        α (uProj K (2 + 2) f g) = uProj K (2 + 2) f ⟨_, hg⟩ := hB
  obtain ⟨A₁, D, hBD⟩ := exists_blk_of_fix_uBarW hα hζ hζ1 hW
  obtain ⟨SN, hSN⟩ := exists_statedSU_eq_of_bar h (det_one_add_smul_onesM (1 : K)) (by
    rw [map_one_add_smul_onesM, map_one, transpose_one_add_smul_onesM,
      one_add_smul_onesM_mul_self])
  have hSN' : (SN : GL (Fin 2) K).val = 1 + onesM := by rw [hSN, one_smul]
  have hDN : D * onesM = onesM * D := by
    have e := mul_eq_of_fix_uL hα hBD (hN SN hSN')
    rw [hSN', map_one_add_onesM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one] at e
    exact (add_left_cancel e).symm
  obtain ⟨hD1, hD2⟩ := eq_of_commute_onesM hDN
  have hdet : D 0 0 * D 0 0 + D 0 1 * D 0 1 ≠ 0 := by
    have h1 := (det_ne_zero_of_blk hBD).2
    rw [det_fin_two, hD2, ← hD1] at h1
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    intro h0
    apply h1
    linear_combination h0 - (D 0 1 * D 0 1) * h2'
  rcases eq_refl_or_bar_of_fix_uBarW hα h hBD hW with hτ | hτ
  ·
    subst hτ
    have hgl : ∀ g : GL (Fin (2 + 2)) K, glAut (RingEquiv.refl K) g = g := fun g => by
      rw [show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one]
      rfl
    have hα1 : ∀ g : StatedSU (2 + 2) (2 ^ f) K,
        ∃ hg : B * (g : GL (Fin (2 + 2)) K) * B⁻¹ ∈ StatedSU (2 + 2) (2 ^ f) K,
          α (uProj K (2 + 2) f g) = uProj K (2 + 2) f ⟨_, hg⟩ := hα
    have hαm' := inner_pow hα1 m
    have hαm'' : ∀ g : StatedSU (2 + 2) (2 ^ f) K,
        ∃ hg : B ^ m * glAut (RingEquiv.refl K) (g : GL (Fin (2 + 2)) K) * (B ^ m)⁻¹ ∈
          StatedSU (2 + 2) (2 ^ f) K,
            (α ^ m) (uProj K (2 + 2) f g) = uProj K (2 + 2) f ⟨_, hg⟩ := fun g => by
      obtain ⟨hg, hαg⟩ := hαm' g
      simp only [hgl]
      exact ⟨hg, hαg⟩
    have hBm : (B ^ m).val = blk (A₁ ^ m) (D ^ m) := by
      rw [Units.val_pow_eq_pow_val, hBD, blk_pow]
    have hDm : ∀ S : StatedSU 2 (2 ^ f) K,
        D ^ m * (S : GL (Fin 2) K).val = (S : GL (Fin 2) K).val * D ^ m := fun S => by
      have e := mul_eq_of_fix_uL hαm'' hBm (S := S) (by rw [hαm]; rfl)
      have hmap : (S : GL (Fin 2) K).val.map (RingEquiv.refl K) = (S : GL (Fin 2) K).val := by
        ext i j
        rfl
      rw [hmap] at e
      exact e.symm
    have hDs := eq_smul_one_of_commute_statedSU (le_refl 2) hζ hζ1 hDm
    have hD := eq_smul_one_of_pow hD1 hD2 hdet hm hDs
    rintro _ ⟨S, rfl⟩
    simp only [MonoidHom.comp_apply]
    obtain ⟨hgS, hαS⟩ := hα1 (uL K 2 f S)
    rw [hαS]
    congr 1
    obtain ⟨hBi, hA₁', -, hD', -⟩ := inv_val_of_blk hBD
    have hcomm : D * (S : GL (Fin 2) K).val = (S : GL (Fin 2) K).val * D := by
      rw [hD, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    apply Subtype.ext
    apply Units.ext
    change B.val * ((uL K 2 f S : StatedSU (2 + 2) (2 ^ f) K) : GL (Fin (2 + 2)) K).val *
      (B⁻¹ : GL (Fin (2 + 2)) K).val =
        ((uL K 2 f S : StatedSU (2 + 2) (2 ^ f) K) : GL (Fin (2 + 2)) K).val
    rw [hBD, hBi, coe_uL, blk_mul, blk_mul, Matrix.mul_one, hA₁', hcomm, Matrix.mul_assoc, hD',
      Matrix.mul_one]
  ·
    exfalso
    obtain ⟨Bm, Xm, Dm, hBm, hαm'⟩ := semi_pow hα hBD m
    obtain ⟨c, -, hc⟩ := exists_rootsOfUnity_ne_one hζ hζ1
    have hτ2 : τ ^ 2 = 1 := RingEquiv.ext fun x => by
      rw [pow_two, RingAut.mul_apply, hτ, hτ, h.bar_bar]
      rfl
    have hτm : ∀ x, (τ ^ m) x = h.bar x := by
      obtain ⟨j, rfl⟩ := hm
      intro x
      rw [pow_succ, pow_mul, hτ2, one_pow, one_mul, hτ]
    exact false_of_fix_torus_bar h hαm' hτm hBm hc (by rw [hαm]; rfl)

end FourFix

end CFSG.ComponentClassification.RankTwoClassical.URigid
