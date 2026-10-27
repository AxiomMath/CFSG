module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem charP_two_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p', hp'⟩ := CharP.exists F
  have hp'prime : p'.Prime := CharP.char_is_prime F p'
  obtain ⟨m, -, hcard⟩ := FiniteField.card F p'
  have hcard' : Nat.card F = 2 ^ (2 * n) := by
    rw [hF, ← pow_mul, Nat.mul_comm n 2]
  have hdvd : p' ∣ 2 ^ (2 * n) := by
    rw [← hcard', Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p' m.pos.ne'
  have h2 : p' ∣ 2 := hp'prime.dvd_of_dvd_pow hdvd
  have : p' = 2 := (Nat.prime_dvd_prime_iff_eq hp'prime Nat.prime_two).mp h2
  subst this
  exact hp'

private theorem hasEnoughRootsOfUnity_of_dvd_card_sub_one {F : Type} [Field F] [Finite F]
    {n : ℕ} [NeZero n] (hn : n ∣ Nat.card F - 1) : HasEnoughRootsOfUnity F n := by
  set N := Nat.card F - 1 with hN
  have hNu : Nat.card Fˣ = N := Nat.card_units F
  have hNpos : 0 < N := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : NeZero N := ⟨by omega⟩
  have htop : rootsOfUnity N F = ⊤ := by
    ext x
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    rw [← hNu]
    exact pow_card_eq_one'
  have hNcard : N ≤ Nat.card (rootsOfUnity N F) := by
    rw [htop, Subgroup.card_top, hNu]
  haveI : HasEnoughRootsOfUnity F N := HasEnoughRootsOfUnity.of_card_le hNcard
  exact HasEnoughRootsOfUnity.of_dvd F hn

private theorem dvd_card_sub_one {p n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) : p ∣ Nat.card F - 1 := by
  have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    have h := Nat.sq_sub_sq (2 ^ n) 1
    simpa using h
  rw [hF, h1]
  exact dvd_mul_of_dvd_left hpq _

private theorem rootsOfUnity_pow_card_add_one {p q : ℕ} {F : Type} [Field F]
    (hpq : p ∣ q + 1) (c : rootsOfUnity p F) : ((c : Fˣ) : F) ^ (q + 1) = 1 := by
  obtain ⟨k, hk⟩ := hpq
  have hc : ((c : Fˣ) : F) ^ p = 1 := (mem_rootsOfUnity' p (c : Fˣ)).mp c.2
  rw [hk, pow_mul, hc, one_pow]

private noncomputable def uniDiagHom (p d : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* GL (Fin d) F where
  toFun v := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal fun i => ((v i : Fˣ) : F)) (by
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (v i : Fˣ).ne_zero)
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  map_mul' v w := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.diagonal_mul_diagonal]
    simp

private theorem uniDiagHom_val (p d : ℕ) (F : Type) [Field F]
    (v : Fin d → rootsOfUnity p F) :
    ((uniDiagHom p d F v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => ((v k : Fˣ) : F)) := by
  change (Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal fun k => ((v k : Fˣ) : F)) _ :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal _
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private def uniProdHom (p d : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* rootsOfUnity p F where
  toFun v := ∏ i, v i
  map_one' := by simp
  map_mul' v w := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]

private def uniPairHom (p d : ℕ) (F : Type) [Field F] (i j : Fin d) :
    (Fin d → rootsOfUnity p F) →* rootsOfUnity p F × rootsOfUnity p F where
  toFun v := (∏ t, v t, v i * (v j)⁻¹)
  map_one' := by
    apply Prod.ext <;> simp
  map_mul' v w := by
    apply Prod.ext
    · show (∏ t, (v * w) t) = (∏ t, v t) * (∏ t, w t)
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib]
    · show (v * w) i * ((v * w) j)⁻¹ = (v i * (v j)⁻¹) * (w i * (w j)⁻¹)
      simp only [Pi.mul_apply, mul_inv_rev]
      simp [mul_assoc, mul_comm, mul_left_comm]

private theorem card_ker_uniPairHom {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hd : 3 ≤ d) (hμ : Nat.card (rootsOfUnity p F) = p)
    {i j k : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (uniPairHom p d F i j).ker = p ^ (d - 2) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsurj : Function.Surjective (uniPairHom p d F i j) := by
    rintro ⟨α, β⟩
    let v : Fin d → rootsOfUnity p F := fun t =>
      if t = i then β else if t = k then α * β⁻¹ else 1
    refine ⟨v, ?_⟩
    apply Prod.ext
    · show (∏ t, v t) = α
      have hsupp : ∀ t ∈ (Finset.univ : Finset (Fin d)),
          t ∉ ({i, k} : Finset (Fin d)) → v t = 1 := by
        intro t _ ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        simp [v, ht.1, ht.2]
      rw [← Finset.prod_subset (s₁ := ({i, k} : Finset (Fin d))) (s₂ := Finset.univ)
        (Finset.subset_univ _) hsupp]
      rw [Finset.prod_insert (by simpa using hik), Finset.prod_singleton]
      have hvi : v i = β := by simp [v]
      have hvk : v k = α * β⁻¹ := by simp [v, hik, Ne.symm hik]
      rw [hvi, hvk, ← mul_assoc, mul_comm β α, mul_assoc, mul_inv_cancel, mul_one]
    · show v i * (v j)⁻¹ = β
      have hvi : v i = β := by simp [v]
      have hvj : v j = 1 := by
        have hji : j ≠ i := Ne.symm hij
        have hjk' : j ≠ k := hjk
        simp [v, hji, hjk']
      rw [hvi, hvj, inv_one, mul_one]
  have hrange : (uniPairHom p d F i j).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have h := Subgroup.card_ker_mul_card_range (uniPairHom p d F i j)
  rw [hrange, Subgroup.card_top, Nat.card_prod, hμ, Nat.card_fun, Nat.card_fin, hμ] at h
  have hpd : p ^ d = p ^ (d - 2) * (p * p) := by
    conv_lhs => rw [show d = (d - 2) + 2 from by omega]
    rw [pow_add, pow_two]
  rw [hpd] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hp.pos) h

private noncomputable def uniConstHom (p d : ℕ) (F : Type) [Field F] (hpd : p ∣ d)
    (i j : Fin d) : rootsOfUnity p F →* (uniPairHom p d F i j).ker where
  toFun c := ⟨fun _ => c, by
    rw [MonoidHom.mem_ker]
    apply Prod.ext
    · show (∏ _t : Fin d, c) = 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      obtain ⟨m, rfl⟩ := hpd
      rw [pow_mul]
      have hcp : c ^ p = 1 := Subtype.ext c.2
      rw [hcp, one_pow]
    · show c * c⁻¹ = 1
      simp⟩
  map_one' := Subtype.ext (funext fun _ => rfl)
  map_mul' c c' := Subtype.ext (funext fun _ => rfl)

private theorem uniConstHom_injective (p d : ℕ) (F : Type) [Field F] (hpd : p ∣ d)
    (i j : Fin d) : Function.Injective (uniConstHom p d F hpd i j) := by
  intro c c' h
  have h2 := congrArg (fun a : (uniPairHom p d F i j).ker =>
    (a : Fin d → rootsOfUnity p F) i) h
  simpa [uniConstHom] using h2

private theorem card_uniConstSub {p d : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hpd : p ∣ d) (i j : Fin d) (hμ : Nat.card (rootsOfUnity p F) = p) :
    Nat.card (uniConstHom p d F hpd i j).range = p := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (uniConstHom_injective p d F hpd i j), Subgroup.card_top, hμ]

private theorem isElemAbelian_top_fun (p d : ℕ) (F : Type) [Field F] :
    IsElemAbelian p (⊤ : Subgroup (Fin d → rootsOfUnity p F)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (funext fun i => mul_comm _ _)⟩⟩, ?_⟩
  · intro x hx
    funext i
    exact Subtype.ext (x i).2

private theorem uniDiagHom_mem_SU {p n d : ℕ} {F : Type} [Field F]
    (hpq : p ∣ 2 ^ n + 1) {v : Fin d → rootsOfUnity p F}
    (hv : v ∈ (uniProdHom p d F).ker) :
    uniDiagHom p d F v ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [uniDiagHom_val, Matrix.det_diagonal]
    have h : (∏ i, v i : rootsOfUnity p F) = 1 := MonoidHom.mem_ker.mp hv
    have h2 : (((∏ i, v i : rootsOfUnity p F) : Fˣ) : F) = 1 := by simp [h]
    have h3 : (∏ i, ((v i : Fˣ) : F)) =
        (((∏ i, v i : rootsOfUnity p F) : Fˣ) : F) := by simp
    rw [h3, h2]
  · rw [uniDiagHom_val, Matrix.diagonal_map (f := fun x : F => x ^ (2 ^ n))
        (zero_pow (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    rw [← pow_succ]
    exact rootsOfUnity_pow_card_add_one (q := 2 ^ n) hpq (v i)

private noncomputable def uniDiagHomSU (p n d : ℕ) (F : Type) [Field F]
    (hpq : p ∣ 2 ^ n + 1) (i j : Fin d) :
    (uniPairHom p d F i j).ker →* ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) :=
  ((uniDiagHom p d F).comp (uniPairHom p d F i j).ker.subtype).codRestrict _ fun v =>
    uniDiagHom_mem_SU hpq (by
      show (uniProdHom p d F) (v : Fin d → rootsOfUnity p F) = 1
      exact congrArg Prod.fst (MonoidHom.mem_ker.mp v.2))

private noncomputable def uniPermGL {d : ℕ} {F : Type} [Field F]
    (σ : Equiv.Perm (Fin d)) : GL (Fin d) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp] private theorem uniCoePermGL {d : ℕ} {F : Type} [Field F]
    (σ : Equiv.Perm (Fin d)) :
    ((uniPermGL σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl

private theorem uniPermMatrix_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (i j : Fin d) : σ.permMatrix F i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

private theorem uniPermMatrix_map_pow {n d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (hq0 : 2 ^ n ≠ 0) : (σ.permMatrix F).map (· ^ (2 ^ n)) = σ.permMatrix F := by
  ext i j
  rw [Matrix.map_apply, uniPermMatrix_apply']
  by_cases h : σ i = j
  · simp [h]
  · rw [if_neg h]
    exact zero_pow hq0

private theorem uniSwap_mem_SU {n d : ℕ} {F : Type} [Field F] [CharP F 2]
    (hq0 : 2 ^ n ≠ 0) {i j : Fin d} (hij : i ≠ j) :
    uniPermGL (Equiv.swap i j) ∈ LargeEvenSUGroup (Fin d) F (2 ^ n) := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [uniCoePermGL, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
    have : ((-1 : ℤˣ) : F) = (-1 : F) := by simp
    rw [this]
    exact CharTwo.neg_eq 1
  · rw [uniCoePermGL, uniPermMatrix_map_pow (Equiv.swap i j) hq0,
      Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private theorem uniPermGL_swap_not_scalar {d : ℕ} {F : Type} [Field F] {i j : Fin d}
    (hij : i ≠ j) : uniPermGL (Equiv.swap i j) ∉ LargeEvenScalars (Fin d) F := by
  intro h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h
  have h1 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i j) hc
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
    if_neg hij, uniCoePermGL, uniPermMatrix_apply', Equiv.swap_apply_left, if_pos rfl] at h1
  exact zero_ne_one h1

private theorem uniDiagHom_comm_swap {p d : ℕ} {F : Type} [Field F]
    {i j : Fin d} (hij : i ≠ j) {v : Fin d → rootsOfUnity p F} (hv : v i = v j) :
    uniDiagHom p d F v * uniPermGL (Equiv.swap i j) =
      uniPermGL (Equiv.swap i j) * uniDiagHom p d F v := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, uniDiagHom_val, uniCoePermGL]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, uniPermMatrix_apply']
  by_cases h : Equiv.swap i j a = b
  · rw [if_pos h]
    have hab : v a = v b := by
      by_cases hai : a = i
      · subst hai
        rw [Equiv.swap_apply_left] at h
        rw [← h, hv]
      · by_cases haj : a = j
        · subst haj
          rw [Equiv.swap_apply_right] at h
          rw [← h, hv]
        · rw [Equiv.swap_apply_of_ne_of_ne hai haj] at h
          rw [h]
    rw [hab, mul_one, one_mul]
  · rw [if_neg h, mul_zero, zero_mul]

private theorem uniDiagHom_scalar_const {p d : ℕ} {F : Type} [Field F] (hd : 1 ≤ d)
    {v : Fin d → rootsOfUnity p F}
    (h : uniDiagHom p d F v ∈ LargeEvenScalars (Fin d) F) :
    ∃ c : rootsOfUnity p F, v = fun _ => c := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h
  let i0 : Fin d := ⟨0, by omega⟩
  have entry : ∀ i : Fin d, c = (v i : Fˣ) := by
    intro i
    apply Units.ext
    have h2 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i i) hc
    simpa [uniDiagHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h2
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rw [entry i0]
    exact (v i0).2
  · funext i
    apply Subtype.ext
    exact (entry i).symm

private theorem scalar_of_psi_eq_one {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {U : Subgroup (GL (Fin d) F)}
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U}
    {ψ : ↥U →* ↥S} (hψ : GLifts θ ψ) {u : ↥U} (hu : ψ u = 1) :
    (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  have h1 : LargeEvenProjMk U u = 1 := by
    have h2 := hψ u
    rw [hu] at h2
    have h3 : (QuotientGroup.mk (1 : ↥S) : ↥S ⧸ Subgroup.center ↥S) = 1 :=
      map_one (QuotientGroup.mk' (Subgroup.center ↥S))
    rw [h3, map_one] at h2
    exact h2.symm
  have h3 : u ∈ (LargeEvenProjMk U).ker := h1
  rw [QuotientGroup.ker_mk'] at h3
  exact Subgroup.mem_subgroupOf.1 h3

private theorem card_sup_mul_card_inf_of_commute {G : Type*} [Group G] [Finite G]
    (L R : Subgroup G) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R := by
  let f : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hf : ∀ x : L × R, f x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : f.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hf]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hf]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hf]; simp⟩)
  have hker : Nat.card f.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hf, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hf]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hf, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, Nat.card_prod] at h
  simpa [mul_comm] using h

theorem uni_rank_bmax {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : MCfg p S B N D K x) (hbmax : GLAIsBmax p B) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S) (hψ : GLifts θ ψ) :
    p ^ (d - 2) ≤ Nat.card B := by
  classical
  have hp : p.Prime := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : CharP F 2 := charP_two_of_card_sq hn hF
  haveI : HasEnoughRootsOfUnity F p :=
    hasEnoughRootsOfUnity_of_dvd_card_sub_one (dvd_card_sub_one hF hpq)
  have hμ : Nat.card (rootsOfUnity p F) = p :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity F p
  have hq0 : 2 ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  set i2 : Fin d := ⟨2, by omega⟩ with hi2
  have hi01 : i0 ≠ i1 := by simp [hi0, hi1]
  have hi02 : i0 ≠ i2 := by simp [hi0, hi2]
  have hi12 : i1 ≠ i2 := by simp [hi1, hi2]
  let A := (uniPairHom p d F i0 i1).ker
  have hcardA : Nat.card A = p ^ (d - 2) := card_ker_uniPairHom hp hd hμ hi01 hi02 hi12
  let SU := LargeEvenSUGroup (Fin d) F (2 ^ n)
  let diagSU := uniDiagHomSU p n d F hpq i0 i1
  let φA : A →* Ω := S.subtype.comp (ψ.comp diagSU)
  let τ : ↥SU := ⟨uniPermGL (Equiv.swap i0 i1), uniSwap_mem_SU hq0 hi01⟩
  let g : Ω := S.subtype (ψ τ)
  let U : Subgroup Ω := Subgroup.zpowers g
  let E : Subgroup Ω := φA.range ⊔ Subgroup.zpowers x
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hAtop : IsElemAbelian p (⊤ : Subgroup A) := by
    have h := IsElemAbelian.comap (p := p) (isElemAbelian_top_fun p d F)
      (f := A.subtype) Subtype.coe_injective
    simpa using h
  have hEA : IsElemAbelian p φA.range := by
    have h := hAtop.map φA
    rwa [← MonoidHom.range_eq_map] at h
  have hEx : IsElemAbelian p (Subgroup.zpowers x) :=
    isElemAbelian_zpowers (hcfg.elem.2 x hcfg.mem)
  have hcommφx : ∀ a ∈ φA.range, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, rfl⟩ := MonoidHom.mem_range.mp ha
    have haS : φA a₀ ∈ S := (ψ (diagSU a₀)).2
    have hxca : φA a₀ * x = x * φA a₀ :=
      (Subgroup.mem_centralizer_iff.mp hxcent) (φA a₀) haS
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right hxca m).eq
  have hE : IsElemAbelian p E := IsElemAbelian.sup_of_commute hEA hEx hcommφx
  have hψτ_ne : ψ τ ≠ 1 := by
    intro h1
    exact uniPermGL_swap_not_scalar hi01 (scalar_of_psi_eq_one hψ h1)
  have hg_ne : g ≠ 1 := by
    intro h1
    exact hψτ_ne (Subtype.ext h1)
  have hU_ne : U ≠ ⊥ := by
    intro hbot
    have : g ∈ (⊥ : Subgroup Ω) := by rw [← hbot]; exact Subgroup.mem_zpowers g
    exact hg_ne (Subgroup.mem_bot.mp this)
  have hτ2 : τ ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one, sq,
      uniCoePermGL, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  have hg2 : g ^ 2 = 1 := by
    show (S.subtype (ψ τ)) ^ 2 = 1
    rw [← map_pow (S.subtype) (ψ τ) 2, ← map_pow ψ τ 2, hτ2]
    simp
  have hU2 : IsPGroup 2 U := by
    have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg_ne
    have hcard : Nat.card U = 2 := by
      show Nat.card (Subgroup.zpowers g) = 2
      rw [Nat.card_zpowers, hord]
    exact IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hE_N : E ≤ Subgroup.normalizer (U : Set Ω) := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      refine Subgroup.centralizer_le_normalizer (U : Set Ω) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcomm_g : g * φA a = φA a * g := by
        have hcommSU : diagSU a * τ = τ * diagSU a := by
          apply Subtype.ext
          exact uniDiagHom_comm_swap hi01 (by
            have h2 := congrArg Prod.snd (MonoidHom.mem_ker.mp a.2)
            exact mul_inv_eq_one.mp h2)
        have h1 : ψ (diagSU a) * ψ τ = ψ τ * ψ (diagSU a) := by
          rw [← map_mul, ← map_mul, hcommSU]
        exact (congrArg S.subtype h1).symm
      exact (Commute.zpow_left hcomm_g m).eq
    · refine Subgroup.zpowers_le.mpr ?_
      refine Subgroup.centralizer_le_normalizer (U : Set Ω) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hgS : g ∈ S := (ψ τ).2
      have hxg : g * x = x * g := (Subgroup.mem_centralizer_iff.mp hxcent) g hgS
      exact (Commute.zpow_left hxg m).eq
  let constHom := uniConstHom p d F hpd i0 i1
  have hconst_card : Nat.card constHom.range = p := card_uniConstSub hp hpd i0 i1 hμ
  have hconst_of_center : ∀ (a : A) (y : ↥S), S.subtype y = (φA a : Ω) →
      y ∈ Subgroup.center ↥S → ∃ c, (a : Fin d → rootsOfUnity p F) = fun _ => c := by
    intro a y hy hyZ
    have hmk : QuotientGroup.mk y = 1 := (QuotientGroup.eq_one_iff y).mpr hyZ
    have hproj : LargeEvenProjMk SU (diagSU a) = 1 := by
      have h := hψ (diagSU a)
      rw [show ψ (diagSU a) = y from (Subtype.ext hy).symm, hmk, map_one] at h
      exact h.symm
    have hscal : (diagSU a : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      have hmem : (diagSU a : ↥SU) ∈ (LargeEvenProjMk SU).ker := hproj
      rw [QuotientGroup.ker_mk'] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    exact uniDiagHom_scalar_const (d := d) (by omega) hscal
  have hker_le_const : φA.ker ≤ constHom.range := by
    intro a ha
    have hy : (1 : ↥S) ∈ Subgroup.center ↥S := Subgroup.one_mem _
    obtain ⟨c, hc⟩ := hconst_of_center a 1 (by rw [map_one, MonoidHom.mem_ker.mp ha]) hy
    refine MonoidHom.mem_range.mpr ⟨c, Subtype.ext ?_⟩
    exact hc.symm
  have hker_dvd : Nat.card φA.ker ∣ p := by
    have h := Subgroup.card_dvd_of_le hker_le_const
    rwa [hconst_card] at h
  have hker_le_p : Nat.card φA.ker ≤ p := Nat.le_of_dvd hp.pos hker_dvd
  have hcardker : Nat.card φA.ker * Nat.card φA.range = p ^ (d - 2) := by
    have h := Subgroup.card_ker_mul_card_range φA
    rw [hcardA] at h
    exact h
  have hxord : orderOf x = p :=
    orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
  have hxorder : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hEcard : p ^ (d - 2) ≤ Nat.card E := by
    by_cases hx : x ∈ φA.range
    · have hEeq : E = φA.range := by
        show φA.range ⊔ Subgroup.zpowers x = φA.range
        rw [sup_eq_left]
        exact Subgroup.zpowers_le.mpr hx
      have hk1 : Nat.card φA.ker = 1 := by
        by_contra hne
        have hk_p : Nat.card φA.ker = p := by
          rcases (Nat.dvd_prime hp).mp hker_dvd with h | h
          · exact absurd h hne
          · exact h
        have heq : φA.ker = constHom.range :=
          Subgroup.eq_of_le_of_card_ge hker_le_const (by rw [hconst_card, hk_p])
        obtain ⟨a, hxa⟩ := MonoidHom.mem_range.mp hx
        have hxS : x ∈ S := hxa ▸ (ψ (diagSU a)).2
        have hxZ : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
          rw [Subgroup.mem_center_iff]
          intro s
          apply Subtype.ext
          exact (Subgroup.mem_centralizer_iff.mp hxcent) (s : Ω) s.2
        obtain ⟨c, hc⟩ := hconst_of_center a ⟨x, hxS⟩ (by simp [hxa]) hxZ
        have hmem : a ∈ constHom.range := by
          refine MonoidHom.mem_range.mpr ⟨c, Subtype.ext ?_⟩
          exact hc.symm
        have : a ∈ φA.ker := heq ▸ hmem
        rw [MonoidHom.mem_ker] at this
        exact hcfg.ne_one (by rw [← hxa]; exact this)
      rw [hEeq]
      have hrange_card : Nat.card φA.range = p ^ (d - 2) := by
        rw [← hcardker, hk1, one_mul]
      rw [hrange_card]
    · have hIcard : Nat.card (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) = 1 := by
        have hdvd : Nat.card (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) ∣ p := by
          have h := Subgroup.card_dvd_of_le
            (inf_le_right : (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) ≤
              Subgroup.zpowers x)
          rwa [hxorder] at h
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        · exact h
        · exfalso
          have heq : (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) = Subgroup.zpowers x :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hxorder])
          have : x ∈ (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) := by
            rw [heq]; exact Subgroup.mem_zpowers x
          exact hx this.1
      have hdisj : (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω) = ⊥ :=
        Subgroup.eq_bot_of_card_eq (H := (φA.range ⊓ Subgroup.zpowers x : Subgroup Ω)) hIcard
      have hcardE : Nat.card E = Nat.card φA.range * p := by
        have h := card_sup_mul_card_inf_of_commute φA.range (Subgroup.zpowers x) hcommφx
        rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxord] at h
        exact h
      rw [hcardE]
      calc p ^ (d - 2) = Nat.card φA.ker * Nat.card φA.range := hcardker.symm
        _ ≤ p * Nat.card φA.range := Nat.mul_le_mul_right _ hker_le_p
        _ = Nat.card φA.range * p := Nat.mul_comm _ _
  have hleB : Nat.card E ≤ Nat.card B := by
    have h := card_le_pow_glaTwoLocalRank hp hE hU_ne hU2 hE_N
    rwa [← hbmax.2.1] at h
  exact hEcard.trans hleB

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
