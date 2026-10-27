module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryBasis
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial Matrix CFSG.ClassicalGroups.Unitary TorusU CFSG.Open
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.LieType.Universal.Unitary (conjTr SUid)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Torus

variable {K : Type} [Field K] {n p : ℕ}

@[expose] def odProdHom (p n : ℕ) :
    (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) where
  toFun c := ∏ i, c i
  map_one' := by simp
  map_mul' c d := by simp [Finset.prod_mul_distrib]

@[expose] def odDelta (p n : ℕ) : Subgroup (Fin n → Multiplicative (ZMod p)) :=
  MonoidHom.ker (odProdHom p n)

theorem mem_odDelta {c : Fin n → Multiplicative (ZMod p)} :
    c ∈ odDelta p n ↔ ∏ i, c i = 1 :=
  Iff.rfl

theorem isElemAbelian_odDelta [Fact p.Prime] :
    IsElemAbelian p (⊤ : Subgroup (odDelta p n)) :=
  ⟨⟨⟨fun a b => Subtype.ext (mul_comm a.1 b.1)⟩⟩,
    fun c _ => Subtype.ext (od_torus_pow (c : Fin n → Multiplicative (ZMod p)))⟩

@[expose] def odKappaFun (r n : ℕ) (c : Fin r → Multiplicative (ZMod p)) :
    Fin n → Multiplicative (ZMod p) :=
  fun i => if h : (i : ℕ) < r then c ⟨i, h⟩ else if (i : ℕ) = r then (∏ j, c j)⁻¹ else 1

theorem odKappaFun_one (r n : ℕ) : odKappaFun (p := p) r n 1 = 1 := by
  funext i
  simp [odKappaFun]

theorem odKappaFun_mul (r n : ℕ) (c d : Fin r → Multiplicative (ZMod p)) :
    odKappaFun r n (c * d) = odKappaFun r n c * odKappaFun r n d := by
  funext i
  by_cases h1 : (i : ℕ) < r
  · simp [odKappaFun, h1]
  · by_cases h2 : (i : ℕ) = r
    · simp [odKappaFun, h1, h2, Finset.prod_mul_distrib]
      exact mul_comm _ _
    · simp [odKappaFun, h1, h2]

theorem prod_odKappaFun {r n : ℕ} (hr : r < n) (c : Fin r → Multiplicative (ZMod p)) :
    ∏ i, odKappaFun r n c i = 1 := by
  set c' : ℕ → Multiplicative (ZMod p) := fun k => if h : k < r then c ⟨k, h⟩ else 1 with hc'
  set g : ℕ → Multiplicative (ZMod p) :=
    fun k => if k < r then c' k else if k = r then (∏ j, c j)⁻¹ else 1 with hg
  have h1 : ∀ i : Fin n, odKappaFun r n c i = g (i : ℕ) := by
    intro i
    by_cases h : (i : ℕ) < r
    · simp [odKappaFun, hg, hc', h]
    · simp [odKappaFun, hg, h]
  simp_rw [h1]
  rw [Fin.prod_univ_eq_prod_range g n]
  have hsub : Finset.range (r + 1) ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.prod_subset hsub (fun x hx hx' => by
    rw [Finset.mem_range] at hx hx'
    simp [hg, show ¬ x < r by omega, show x ≠ r by omega]), Finset.prod_range_succ]
  have h2 : ∏ k ∈ Finset.range r, g k = ∏ j : Fin r, c j := by
    have h3 : ∏ k ∈ Finset.range r, g k = ∏ k ∈ Finset.range r, c' k :=
      Finset.prod_congr rfl fun k hk => by
        have := Finset.mem_range.1 hk
        simp [hg, this]
    rw [h3, ← Fin.prod_univ_eq_prod_range c' r]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hc', j.2]
  rw [h2]
  simp [hg]

@[expose] def odKappaHom (r n : ℕ) (hr : r < n) :
    (Fin r → Multiplicative (ZMod p)) →* odDelta p n where
  toFun c := ⟨odKappaFun r n c, mem_odDelta.2 (prod_odKappaFun hr c)⟩
  map_one' := Subtype.ext (odKappaFun_one r n)
  map_mul' c d := Subtype.ext (odKappaFun_mul r n c d)


theorem od_monomial_diag (u : Fin n → K) (π : Equiv.Perm (Fin n)) (s : Fin n → K) :
    (Matrix.of fun i j => if i = π j then u j else 0) * diagonal s =
      diagonal (fun i => s (π.symm i)) * (Matrix.of fun i j => if i = π j then u j else 0) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : i = π j
  · subst h
    simp [mul_comm]
  · simp [h]

theorem od_mul_colMatrix_mono {Bm : Matrix (Fin n) (Fin n) K} {b : Fin n → Fin n → K}
    {u : Fin n → K} {π : Equiv.Perm (Fin n)} (hb : ∀ a, Bm *ᵥ b a = u a • b (π a)) :
    Bm * colMatrix b = colMatrix b * (Matrix.of fun i j => if i = π j then u j else 0) := by
  ext k j
  have h1 : (Bm * colMatrix b) k j = (Bm *ᵥ b j) k := by
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  rw [h1, hb j, Matrix.mul_apply]
  simp [colMatrix, Pi.smul_apply, mul_comm]

theorem od_mono_conj {M P Q N : Matrix (Fin n) (Fin n) K} {π : Equiv.Perm (Fin n)}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hMP : M * P = P * N)
    (hN : ∀ s : Fin n → K, N * diagonal s = diagonal (fun i => s (π.symm i)) * N)
    (a : Fin n → K) :
    M * (P * diagonal a * Q) = (P * diagonal (fun i => a (π.symm i)) * Q) * M := by
  have hNQ : N * Q = Q * M := by
    have h1 : Q * M * P = N := by
      rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    calc N * Q = (Q * M * P) * Q := by rw [h1]
      _ = Q * M * (P * Q) := by rw [Matrix.mul_assoc]
      _ = Q * M := by rw [hPQ, Matrix.mul_one]
  calc M * (P * diagonal a * Q) = (M * P) * diagonal a * Q := by simp only [Matrix.mul_assoc]
    _ = P * (N * diagonal a) * Q := by rw [hMP]; simp only [Matrix.mul_assoc]
    _ = P * (diagonal (fun i => a (π.symm i)) * N) * Q := by rw [hN]
    _ = P * diagonal (fun i => a (π.symm i)) * (N * Q) := by simp only [Matrix.mul_assoc]
    _ = P * diagonal (fun i => a (π.symm i)) * (Q * M) := by rw [hNQ]
    _ = (P * diagonal (fun i => a (π.symm i)) * Q) * M := by simp only [Matrix.mul_assoc]

theorem od_torus_of_basis [Finite K] [Fact p.Prime] [NeZero p] (hn : p + 3 ≤ n) {σ : K ≃+* K}
    (hσσ : ∀ x, σ (σ x) = x) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hσζ : σ ζ = ζ⁻¹)
    {B : GL (Fin n) K} {b : Fin n → Fin n → K} {u : Fin n → K} {π : Equiv.Perm (Fin n)}
    (hb : ∀ a a', herm σ (b a) (b a') = if a = a' then 1 else 0)
    (hBb : ∀ a, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b a = u a • b (π a)) :
    ∃ T : Subgroup (SUid σ n), IsElemAbelian p T ∧
      p ^ (p + 1) ≤ Nat.card (T.map (QuotientGroup.mk'
        ((StatedScalars (Fin n) K).subgroupOf (SUid σ n)))) ∧
      ∀ g ∈ T, ∃ g' ∈ T, B * (g : GL (Fin n) K) * B⁻¹ = (g' : GL (Fin n) K) := by
  set P := colMatrix b with hPdef
  have hP : conjTr σ P * P = 1 := conjTr_colMatrix_mul_self hb
  have hPQ : P * conjTr σ P = 1 := mul_conjTr_self hP
  have hBP : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P =
      P * (Matrix.of fun i j => if i = π j then u j else 0) := od_mul_colMatrix_mono hBb
  have hNd := od_monomial_diag u π
  let T0 : odDelta p n →* (Fin n → K) :=
    (MonoidHom.pi fun j => (charHom hζ).comp
      (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) j)).comp (odDelta p n).subtype
  have hT0 : ∀ g j, T0 g j = charHom hζ ((g : Fin n → Multiplicative (ZMod p)) j) :=
    fun g j => rfl
  have hT : ∀ g j, σ (T0 g j) * T0 g j = 1 := fun g j => by
    rw [hT0]
    exact norm_charHom hζ hσζ _
  have hdet : ∀ g, ∏ j, T0 g j = 1 := fun g => by
    simp only [hT0]
    rw [← map_prod, mem_odDelta.1 g.2, map_one]
  obtain ⟨F, hF⟩ := exists_hom_conjDiag hσσ hP T0 hT hdet
  have hkap : ∀ x : Fin (p + 1) → Multiplicative (ZMod p),
      ((F (odKappaHom (p + 1) n (by omega) x) : SUid σ n) : GL (Fin n) K) ∈
        StatedScalars (Fin n) K → x = 1 := by
    intro x hx
    obtain ⟨c0, hc0⟩ := MonoidHom.mem_range.1 hx
    have hc0' : P * diagonal (fun j => charHom hζ (odKappaFun (p + 1) n x j)) * conjTr σ P =
        Matrix.scalar (Fin n) (c0 : K) := by
      have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc0
      simp only [GeneralLinearGroup.coe_scalar] at h1
      rw [hF] at h1
      exact h1.symm
    have hent : ∀ j, charHom hζ (odKappaFun (p + 1) n x j) = (c0 : K) := fun j =>
      entries_eq_of_conj_eq_scalar P (conjTr σ P) hP _ c0 hc0' j
    have h1 : (c0 : K) = 1 := by
      have h2 := hent ⟨p + 2, by omega⟩
      have h3 : odKappaFun (p + 1) n x ⟨p + 2, by omega⟩ = 1 := by simp [odKappaFun]
      rw [h3, map_one] at h2
      exact h2.symm
    funext i
    have h2 := hent ⟨i, by omega⟩
    rw [h1] at h2
    have h3 : odKappaFun (p + 1) n x ⟨i, by omega⟩ = 1 := eq_one_of_charHom_eq_one hζ h2
    have h4 : odKappaFun (p + 1) n x ⟨i, by omega⟩ = x i := by
      unfold odKappaFun
      rw [dif_pos i.2]
    rw [← h4]
    exact h3
  refine ⟨F.range, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact IsElemAbelian.map isElemAbelian_odDelta _
  · set f' : (Fin (p + 1) → Multiplicative (ZMod p)) →* SUid σ n :=
      F.comp (odKappaHom (p + 1) n (by omega)) with hf'
    set g := (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (SUid σ n))).comp f'
      with hg
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : f' x ∈ (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (SUid σ n))).ker := hx
      rw [QuotientGroup.ker_mk'] at h1
      exact hkap x (Subgroup.mem_subgroupOf.1 h1)
    have hle : g.range ≤ F.range.map (QuotientGroup.mk'
        ((StatedScalars (Fin n) K).subgroupOf (SUid σ n))) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨f' x, ⟨odKappaHom (p + 1) n (by omega) x, rfl⟩, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv, od_card_torus] at h1
    exact h1
  · rintro _ ⟨a, rfl⟩
    let a' : odDelta p n := ⟨fun i => (a : Fin n → Multiplicative (ZMod p)) (π.symm i), by
      rw [mem_odDelta, Equiv.prod_comp π.symm (a : Fin n → Multiplicative (ZMod p))]
      exact mem_odDelta.1 a.2⟩
    refine ⟨F a', ⟨a', rfl⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    simp only [Units.val_mul]
    rw [hF a, hF a']
    exact od_mono_conj hPQ hP hBP hNd (T0 a)

end Torus

section Final

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {r e0 p n : ℕ} [Fact r.Prime] [CharP K r]
  [hpf : Fact p.Prime] {c : K} [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]
  {σ : K ≃+* K} {B : GL (Fin n) K}

theorem odBv_succ (j : ℕ) (y : Fin n → K) :
    odBv B ((j + 1 : ℕ) : ℤ) y =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ odBv B (j : ℤ) y := by
  rw [odBv_natCast, odBv_natCast, pow_succ', ← Matrix.mulVec_mulVec]

theorem od_basis_of_family (S : OdSetup r e0 p c σ B) {m : ℕ} (hm : p * m = n)
    {w : Fin m → Fin n → K}
    (hw : ∀ (i i' : Fin m) (j j' : Fin p),
      herm σ (odBv B ((j : ℕ) : ℤ) (w i)) (odBv B ((j' : ℕ) : ℤ) (w i')) =
        if (i, j) = (i', j') then 1 else 0) :
    ∃ (b : Fin n → Fin n → K) (u : Fin n → K) (π : Equiv.Perm (Fin n)),
      (∀ a a', herm σ (b a) (b a') = if a = a' then 1 else 0) ∧
      ∀ a, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b a = u a • b (π a) := by
  haveI : NeZero p := ⟨hpf.out.ne_zero⟩
  have hcard : Fintype.card (Fin m × Fin p) = n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm, hm]
  let e : Fin m × Fin p ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let π : Equiv.Perm (Fin n) := e.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin m)) (Equiv.addRight (1 : Fin p))).trans e)
  refine ⟨fun a => odBv B (((e.symm a).2 : ℕ) : ℤ) (w (e.symm a).1),
    fun a => if ((e.symm a).2 : ℕ) + 1 < p then 1 else c, π, ?_, ?_⟩
  · intro a a'
    rw [hw]
    simp [e.symm.injective.eq_iff]
  · intro a
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective a
    have hπ : π (e (i, j)) = e (i, j + 1) := by simp [π]
    simp only [hπ, Equiv.symm_apply_apply]
    have hval : ((j + 1 : Fin p) : ℕ) = ((j : ℕ) + 1) % p := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hpf.out.one_lt]
    by_cases hj : (j : ℕ) + 1 < p
    · rw [if_pos hj, one_smul, hval, Nat.mod_eq_of_lt hj, odBv_succ]
    · have hjp : (j : ℕ) + 1 = p := by have := j.2; omega
      rw [if_neg hj, hval, hjp, Nat.mod_self, Nat.cast_zero, odBv_zero, ← odBv_succ, hjp,
        odBv_p S.hBp]

theorem od_exists_zeta {f : ℕ} (hp : p.Prime) (hK : Nat.card K = (r ^ f) ^ 2)
    (hpq : p ∣ r ^ f + 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p ∧ unitaryInvolution K r f ζ = ζ⁻¹ := by
  have hq : 1 < r ^ f := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hK
  have hcard : p ∣ Nat.card Kˣ := by
    rw [CFSG.ClassicalGroups.Unitary.card_units_of_card hK, sq_sub_one_eq _ hq.le]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζu, hζu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hcard
  refine ⟨(ζu : K), IsPrimitiveRoot.coe_units_iff.mpr (hζu ▸ IsPrimitiveRoot.orderOf ζu), ?_⟩
  rw [unitaryInvolution_apply]
  have h1 : ζu ^ (r ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hζu]; exact hpq)
  have h2 : ζu ^ (r ^ f) = ζu⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
  have h3 := congrArg (fun u : Kˣ => (u : K)) h2
  simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using h3

theorem od_exists_dim [NeZero p] (hp : p.Prime) (hnp : ∀ b : K, b ^ p ≠ c)
    {M : Matrix (Fin n) (Fin n) K} (hM : M ^ p = Matrix.scalar (Fin n) c) :
    ∃ m, p * m = n := by
  have hT : (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    have hc := AlgEquiv.commutes (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)) c
    rw [show (Matrix.toLin' M) = Matrix.toLinAlgEquiv' M from rfl, ← map_pow, hM]
    exact hc
  obtain ⟨m, b, -, -⟩ := exists_monomial_basis hp hnp hT
  refine ⟨m, ?_⟩
  have h1 := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun] at h1
  simpa using h1.symm

end Final

end I294OD

open Polynomial Matrix CFSG.Open I294OD CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)

theorem i294ODUnitaryMonomial_holds : I294ODUnitaryMonomial := by
  intro p n r f _ K _ _ _ hp hp2 hK hpq hn B hB c hBp hnp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Irreducible (X ^ p - C (c : K) : K[X])) :=
    ⟨X_pow_sub_C_irreducible_of_prime hp hnp⟩
  have hn1 : 1 ≤ n := by omega
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hBpm := od_unitary_matrix_pow hBp
  have hcu : c ^ (r ^ f + 1) = 1 := by
    have hsc : GeneralLinearGroup.scalar (Fin n) c ∈ Uid (unitaryInvolution K r f) n := by
      rw [← hBp]
      exact pow_mem hB p
    exact l212in_scalar_unitary hn1 hsc
  have S : OdSetup r f p (c : K) (unitaryInvolution K r f) B :=
    ⟨hB, c.ne_zero, hBpm, fun k => unitaryInvolution_apply K r f k,
      unitaryInvolution_involutive hK, hK, hp.odd_of_ne_two hp2, hpq,
      by rw [← Units.val_pow_eq_pow_val, hcu, Units.val_one]⟩
  obtain ⟨m, hm⟩ := od_exists_dim hp hnp hBpm
  obtain ⟨w, hw⟩ := od_exists_orbit_family S hσ m hm
  obtain ⟨b, u, π, hb, hBb⟩ := od_basis_of_family S hm hw
  obtain ⟨ζ, hζ, hσζ⟩ := od_exists_zeta hp hK hpq
  have main : ∀ H : Subgroup (GL (Fin n) K), H = SUid (unitaryInvolution K r f) n →
      ∃ T : Subgroup H, IsElemAbelian p T ∧
        p ^ (p + 1) ≤ Nat.card (T.map (QuotientGroup.mk'
          ((StatedScalars (Fin n) K).subgroupOf H))) ∧
        ∀ g ∈ T, ∃ g' ∈ T, B * (g : GL (Fin n) K) * B⁻¹ = (g' : GL (Fin n) K) := by
    intro H hH
    subst hH
    exact od_torus_of_basis (by omega) (unitaryInvolution_involutive hK) hζ hσζ hb hBb
  exact main _ (SUid_eq_statedSU hK n).symm

end CFSG.LocalAnalysis.RankFourTheoremC
