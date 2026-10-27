module

public import CFSG.GroupTheory.PowTorsionQuotient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryTwoLocal
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainDet

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module CFSG.ClassicalGroups.Orthogonal

theorem scalars_le_center (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] :
    CFSG.ClassicalGroups.Orthogonal.scalars K V ≤ Subgroup.center (V ≃ₗ[K] V) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact (CFSG.ClassicalGroups.Orthogonal.commute_of_mem_scalars hx y).symm

instance scalars_inf_normal (K : Type*) [Field K] (V : Type*) [AddCommGroup V]
    [Module K V] (R : Subgroup (V ≃ₗ[K] V)) :
    (R ⊓ CFSG.ClassicalGroups.Orthogonal.scalars K V).Normal :=
  Subgroup.normal_of_le_center (inf_le_right.trans (scalars_le_center K V))

theorem card_quotient_scalar_le_of_card_le {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [Finite (V ≃ₗ[K] V)] {r n : ℕ} (R : Subgroup (V ≃ₗ[K] V))
    (h : Nat.card R ≤ r ^ n * Nat.card {x : R // ∃ a : K, ∀ v, (x : V ≃ₗ[K] V) v = a • v}) :
    Nat.card (R ⧸ (R ⊓ CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf R) ≤ r ^ n := by
  classical
  let S : Subgroup R := (R ⊓ CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf R
  have hS : Nat.card {x : R // ∃ a : K, ∀ v, (x : V ≃ₗ[K] V) v = a • v} = Nat.card S := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1, by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨x.1.2, mem_scalars.mpr x.2⟩⟩
        invFun := fun y => ⟨y.1, mem_scalars.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp y.2)).2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  have hcard : Nat.card R = Nat.card (R ⧸ S) * Nat.card S :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup S
  have hle : Nat.card (R ⧸ S) * Nat.card S ≤ r ^ n * Nat.card S := by
    calc Nat.card (R ⧸ S) * Nat.card S = Nat.card R := hcard.symm
      _ ≤ r ^ n * Nat.card {x : R // ∃ a : K, ∀ v, (x : V ≃ₗ[K] V) v = a • v} := h
      _ = r ^ n * Nat.card S := by rw [hS]
  exact Nat.le_of_mul_le_mul_right hle (Nat.card_pos (α := S))

theorem eq_one_of_fixes_flag_of_odd {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {H : Type} [Group H] [Finite H]
    (F : CFSG.LieType.BorelTits.ReflForm K V) (ρ : H →* Module.End K V)
    (hρ : CFSG.LieType.BorelTits.IsIsometric F ρ) (hinj : Function.Injective ρ) {g : H}
    (hodd : Odd (orderOf g)) {W : Submodule K V} (hW : ∀ w ∈ W, ρ g w = w)
    (hM : ∀ v ∈ F.perp W, ρ g v - v ∈ W) : g = 1 := by
  classical
  have hnpos : 0 < orderOf g := orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)
  by_contra hg
  have hn1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hpodd : Odd p := hodd.of_dvd_nat hpdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ Odd 2) hpodd
  have hWinv : ∀ w ∈ W, ρ g⁻¹ w = w := by
    intro w hw
    calc ρ g⁻¹ w = ρ g⁻¹ (ρ g w) := by rw [hW w hw]
      _ = w := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hPres : ∀ k : ℕ, ∀ v ∈ F.perp W, ρ (g ^ k) v ∈ F.perp W := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
        intro v hv
        rw [pow_succ', map_mul, Module.End.mul_apply]
        exact hρ.apply_mem_perp_of_forall (fun w hw => by rw [hWinv w hw]; exact hw) (ih v hv)
  have hfix : ∀ k : ℕ, (∀ w ∈ W, ρ (g ^ k) w = w) ∧
      (∀ v ∈ F.perp W, ρ (g ^ k) v - v ∈ W) := by
    intro k
    induction k with
    | zero => exact ⟨fun w hw => by simp, fun v hv => by simp⟩
    | succ k ih =>
        constructor
        · intro w hw
          rw [pow_succ', map_mul, Module.End.mul_apply, ih.1 w hw, hW w hw]
        · intro v hv
          have hkv : ρ (g ^ k) v ∈ F.perp W := hPres k v hv
          have h1 : ρ g (ρ (g ^ k) v) - ρ (g ^ k) v ∈ W := hM _ hkv
          have h2 : ρ (g ^ k) v - v ∈ W := ih.2 v hv
          rw [pow_succ', map_mul, Module.End.mul_apply]
          have h3 : ρ g (ρ (g ^ k) v) - v ∈ W := by
            have := W.add_mem h1 h2
            convert this using 1
            abel
          exact h3
  have hhp : (g ^ (orderOf g / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hpdvd, pow_orderOf_eq_one]
  have hh1 : g ^ (orderOf g / p) = 1 :=
    @CFSG.RankThree.PartOne.KFU.FlagSplit.eq_one_of_fixes_flag K _ _ V _ _ H _ F ρ hρ hinj
      p hp hp2 (g ^ (orderOf g / p)) hhp W (hfix (orderOf g / p)).1
      (hfix (orderOf g / p)).2
  have hgn : g ^ (orderOf g / p) = 1 := hh1
  have hdvd : orderOf g ∣ orderOf g / p := orderOf_dvd_iff_pow_eq_one.mpr hgn
  have hge : p ≤ orderOf g := Nat.le_of_dvd hnpos hpdvd
  have hpos : 0 < orderOf g / p := Nat.div_pos hge hp.pos
  have hlt : orderOf g / p < orderOf g := Nat.div_lt_self hnpos hp.one_lt
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)



theorem card_le_pow_sub_two_of_factor_bounds {r d k m A B C : ℕ} (hr : r.Prime) (hd : 3 ≤ d)
    (hk : 1 ≤ k) (h2k : 2 * k ≤ d) (hm : m = d - 2 * k)
    (hA : A ≤ r ^ (k - 1) * r ^ (m - 1))
    (hB2 : m ≠ 0 → B ≤ r ^ 2) (hB1 : (m = 0 ∨ k = 1) → B ≤ r)
    (hfac : C = A * B) : C ≤ r ^ (d - 2) := by
  rw [hfac]
  rcases eq_or_ne m 0 with hm0 | hmne
  · calc A * B ≤ (r ^ (k - 1) * r ^ (m - 1)) * r :=
        Nat.mul_le_mul hA (hB1 (Or.inl hm0))
      _ = r ^ k := by
          simp only [hm0, Nat.sub_zero, Nat.zero_sub, pow_zero, mul_one]
          rw [← pow_succ]
          congr 1
          omega
      _ ≤ r ^ (d - 2) := Nat.pow_le_pow_right hr.pos (by omega)
  · rcases eq_or_ne k 1 with hk1 | hkne
    · calc A * B ≤ (r ^ (k - 1) * r ^ (m - 1)) * r :=
          Nat.mul_le_mul hA (hB1 (Or.inr hk1))
        _ = r ^ m := by
            rw [hk1, Nat.sub_self, pow_zero, one_mul]
            rw [← pow_succ]
            congr 1
            omega
        _ = r ^ (d - 2) := by rw [hm, hk1]
    · have hk2 : 2 ≤ k := by omega
      calc A * B ≤ (r ^ (k - 1) * r ^ (m - 1)) * r ^ 2 :=
            Nat.mul_le_mul hA (hB2 hmne)
        _ = r ^ (k - 1 + (m - 1) + 2) := by rw [← pow_add, ← pow_add]
        _ = r ^ (d - k) := by
            have h : k - 1 + (m - 1) + 2 = d - k := by omega
            rw [h]
        _ ≤ r ^ (d - 2) := Nat.pow_le_pow_right hr.pos (by omega)

theorem card_quotient_le_pow_two_of_scalar_pair {N : Type*} [CommGroup N] [Finite N]
    {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime] (Cr : Subgroup N)
    (hNr : ∀ x : N, x ^ r ∈ Cr) (f g : N → F)
    (hpair : Function.Injective fun x => (f x, g x))
    (hf : ∀ x : N, x ^ r = 1 → f x ^ r = 1)
    (hg : ∀ x : N, x ^ r = 1 → g x ^ r = 1) :
    Nat.card (N ⧸ Cr) ≤ r ^ 2 := by
  have h1 := CFSG.GroupTheory.card_quotient_le_card_pow_torsion (A := N) (r := r) Cr hNr
  refine h1.trans ?_
  let ψ : MonoidHom.ker (powMonoidHom r : N →* N) → Fin 2 → F :=
    fun x j => if j = 0 then f (x : N) else g (x : N)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hpair
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 1
    simp only [ψ] at h0 h1
    exact Prod.ext h0 h1
  have hroot : ∀ (x : MonoidHom.ker (powMonoidHom r : N →* N)) (j : Fin 2),
      ψ x j ^ r = 1 := by
    intro x j
    have hx : (x : N) ^ r = 1 := x.2
    fin_cases j
    · exact hf _ hx
    · exact hg _ hx
  have h := CFSG.RankThree.PartOne.KFU.card_le_pow_card_of_injective_rootsOfUnity
    (K := F) ψ hψ hroot
  calc Nat.card (MonoidHom.ker (powMonoidHom r : N →* N)) ≤ r ^ Fintype.card (Fin 2) := h
    _ = r ^ 2 := by norm_num

theorem card_quotient_le_prime_of_scalar {N : Type*} [CommGroup N] [Finite N]
    {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime] (Cr : Subgroup N)
    (hNr : ∀ x : N, x ^ r ∈ Cr) (f : N → F) (hf : Function.Injective f)
    (hroot : ∀ x : N, x ^ r = 1 → f x ^ r = 1) :
    Nat.card (N ⧸ Cr) ≤ r := by
  have h1 := CFSG.GroupTheory.card_quotient_le_card_pow_torsion (A := N) (r := r) Cr hNr
  refine h1.trans ?_
  let ψ : MonoidHom.ker (powMonoidHom r : N →* N) → Fin 1 → F :=
    fun x _ => f (x : N)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    have h0 := congrFun hxy 0
    simpa [ψ] using h0
  have hroot' : ∀ (x : MonoidHom.ker (powMonoidHom r : N →* N)) (j : Fin 1),
      ψ x j ^ r = 1 := by
    intro x j
    exact hroot _ x.2
  have h := CFSG.RankThree.PartOne.KFU.card_le_pow_card_of_injective_rootsOfUnity
    (K := F) ψ hψ hroot'
  calc Nat.card (MonoidHom.ker (powMonoidHom r : N →* N)) ≤ r ^ Fintype.card (Fin 1) := h
    _ = r := by norm_num

theorem card_quotient_le_prime_of_pair_det {N : Type*} [CommGroup N] [Finite N]
    {F : Type} [Field F] [Finite F] [CharP F 2] {r m : ℕ} [Fact r.Prime] (Cr : Subgroup N)
    (hNr : ∀ x : N, x ^ r ∈ Cr) (f g : N → F)
    (hpair : Function.Injective fun x => (f x, g x))
    (hf : ∀ x : N, x ^ r = 1 → f x ^ r = 1)
    (hg : ∀ x : N, x ^ r = 1 → g x ^ r = 1)
    (hdet : ∀ x : N, x ^ r = 1 → f x ^ 2 * g x ^ m = 1) :
    Nat.card (N ⧸ Cr) ≤ r := by
  have h1 := CFSG.GroupTheory.card_quotient_le_card_pow_torsion (A := N) (r := r) Cr hNr
  refine h1.trans ?_
  let ψ : MonoidHom.ker (powMonoidHom r : N →* N) → Fin 1 → F :=
    fun x _ => g (x : N)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hpair
    have h0 := congrFun hxy 0
    simp only [ψ] at h0
    have hx : (x : N) ^ r = 1 := x.2
    have hy : (y : N) ^ r = 1 := y.2
    have hdx := hdet _ hx
    have hdy := hdet _ hy
    have hgx : g (x : N) ≠ 0 := by
      intro h0'
      have hthis := hg _ hx
      rw [h0', zero_pow (Fact.out : r.Prime).ne_zero] at hthis
      exact zero_ne_one hthis
    have hsq : f (x : N) ^ 2 = f (y : N) ^ 2 := by
      have hx2 : f (x : N) ^ 2 = (g (x : N) ^ m)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by rwa [mul_comm] at hdx)
      have hy2 : f (y : N) ^ 2 = (g (y : N) ^ m)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by rwa [mul_comm] at hdy)
      rw [h0] at hx2
      exact hx2.trans hy2.symm
    have hfxy : f (x : N) = f (y : N) := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    exact Prod.ext hfxy h0
  have hroot' : ∀ (x : MonoidHom.ker (powMonoidHom r : N →* N)) (j : Fin 1),
      ψ x j ^ r = 1 := by
    intro x j
    exact hg _ x.2
  have h := CFSG.RankThree.PartOne.KFU.card_le_pow_card_of_injective_rootsOfUnity
    (K := F) ψ hψ hroot'
  calc Nat.card (MonoidHom.ker (powMonoidHom r : N →* N)) ≤ r ^ Fintype.card (Fin 1) := h
    _ = r := by norm_num


theorem perpEnd_eq_smul_one {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (F : CFSG.LieType.BorelTits.ReflForm K V)
    {W : Submodule K V} (hWiso : F.IsTotallyIsotropic W)
    (g : LinearMap.GeneralLinearGroup K V)
    (hg : g ∈ CFSG.HardMathSupport.Curtis.UnitaryLevi.isoStab F.toDual W) (μ : K)
    (hμ : ∀ v ∈ F.perp W, (g : Module.End K V) v - μ • v ∈ W) :
    CFSG.HardMathSupport.Curtis.UnitaryLevi.perpEnd (B := F.toDual) (P := W) ⟨g, hg⟩ =
      μ • 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H v =>
      have hv : (v : V) ∈ F.perp W := v.2
      have hgv : (g : Module.End K V) (v : V) ∈ W.orthogonalBilin F.toDual :=
        CFSG.HardMathSupport.Curtis.UnitaryLevi.apply_mem_orthogonalBilin hg v.2
      have hmv : μ • (v : V) ∈ W.orthogonalBilin F.toDual := by
        rw [Submodule.mem_orthogonalBilin]
        intro w hw
        have h1 : (g : Module.End K V) (v : V) - μ • (v : V) ∈ W := hμ (v:V) hv
        have h2 : (g : Module.End K V) (v : V) ∈ W.orthogonalBilin F.toDual := hgv
        rw [Submodule.mem_orthogonalBilin] at h2
        have h1perp : (g : Module.End K V) (v : V) - μ • (v : V) ∈ F.perp W := hWiso h1
        have h1perp' : (g : Module.End K V) (v : V) - μ • (v : V) ∈
            W.orthogonalBilin F.toDual := h1perp
        rw [Submodule.mem_orthogonalBilin] at h1perp'
        have h3 := h2 w hw
        have h4 := h1perp' w hw
        rw [map_sub, h3, zero_sub, neg_eq_zero] at h4
        exact h4
      rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.perpEnd_mk ⟨g, hg⟩ v
        ⟨(g : Module.End K V) (v : V), hgv⟩ rfl]
      rw [LinearMap.smul_apply, Module.End.one_apply, ← Submodule.Quotient.mk_smul]
      rw [Submodule.Quotient.eq]
      exact hμ (v:V) hv

theorem det_scalar_action {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (F : CFSG.LieType.BorelTits.ReflForm K V)
    {W : Submodule K V} (hWiso : F.IsTotallyIsotropic W)
    (g : LinearMap.GeneralLinearGroup K V)
    (hg : g ∈ CFSG.HardMathSupport.Curtis.UnitaryLevi.isoStab F.toDual W)
    (hdet : LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1)
    (lam μ : K) (hlam : ∀ w ∈ W, (g : Module.End K V) w = lam • w)
    (hμ : ∀ v ∈ F.perp W, (g : Module.End K V) v - μ • v ∈ W)
    {q : ℕ} (hσ : ((F.σ : K →+* K) lam) = lam ^ q) (hq : lam ^ (q + 1) = 1) :
    lam ^ (2 * finrank K W) * μ ^ finrank K
        (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot F.toDual W) = 1 := by
  have hperp : CFSG.HardMathSupport.Curtis.UnitaryLevi.perpEnd (B := F.toDual) (P := W)
      ⟨g, hg⟩ = μ • 1 := perpEnd_eq_smul_one F hWiso g hg μ hμ
  have hdetperp : LinearMap.det (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpEnd
      (B := F.toDual) (P := W) ⟨g, hg⟩) =
      μ ^ finrank K (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot F.toDual W) := by
    rw [hperp]
    exact CFSG.HardMathSupport.Curtis.UnitaryLevi.det_eq_pow_of_forall _ μ
      (fun m => by rw [LinearMap.smul_apply, Module.End.one_apply])
  have hmain := CFSG.HardMathSupport.Curtis.UnitaryLevi.det_eq_of_isoStab
    ((F.σ : K →+* K)).surjective (fun u h => F.nondeg u h) hWiso ⟨g, hg⟩ lam hlam
  rw [hdet, hdetperp] at hmain
  have hmul : lam ^ q * lam = 1 := by rw [← pow_succ, hq]
  have hσinv : ((F.σ : K →+* K) lam)⁻¹ = lam := by
    rw [hσ]
    exact inv_eq_of_mul_eq_one_right hmul
  rw [hσinv] at hmain
  have halg : lam ^ finrank K W * μ ^ finrank K
        (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot F.toDual W) * lam ^ finrank K W =
      lam ^ (2 * finrank K W) * μ ^ finrank K
        (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot F.toDual W) := by
    rw [mul_right_comm, ← pow_add, two_mul]
  rw [halg] at hmain
  exact hmain.symm

end CFSG.LocalAnalysis.GLTheoremA
