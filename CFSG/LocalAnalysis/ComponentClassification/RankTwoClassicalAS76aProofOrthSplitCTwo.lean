module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

section Vectors

variable {Q : QuadraticForm K (ι → K)} [CharP K 2]

omit [DecidableEq ι] in
theorem exists_singular_partner (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {z y : ι → K}
    (hz0 : z ≠ 0) (hQz : Q z = 0) (hQy : Q y = 1) :
    ∃ g, Q g = 0 ∧ Q.polarBilin g z = 0 ∧ Q.polarBilin g y = 1 := by
  obtain ⟨T, hT3, hTs⟩ := hT
  have hS2 : 2 ≤ finrank K ↥(T ⊓ LinearMap.ker (Q.polarBilin.flip z)) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Q.polarBilin.flip z)
    have h2 : finrank K (LinearMap.range (Q.polarBilin.flip z)) ≤ 1 := by
      have h := Submodule.finrank_le (LinearMap.range (Q.polarBilin.flip z))
      rwa [Module.finrank_self] at h
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker (Q.polarBilin.flip z))
    have h4 := Submodule.finrank_le (T ⊔ LinearMap.ker (Q.polarBilin.flip z))
    omega
  have hmem : ∀ t ∈ T ⊓ LinearMap.ker (Q.polarBilin.flip z), Q t = 0 ∧ Q.polarBilin t z = 0 :=
    fun t ht => ⟨hTs t (Submodule.mem_inf.mp ht).1, by
      have h := LinearMap.mem_ker.mp (Submodule.mem_inf.mp ht).2
      rwa [LinearMap.flip_apply] at h⟩
  have hnle : ¬ T ⊓ LinearMap.ker (Q.polarBilin.flip z) ≤ K ∙ z := fun hle => by
    have h := Submodule.finrank_mono hle
    rw [finrank_span_singleton hz0] at h
    omega
  obtain ⟨h, hhS, hhz⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  by_cases hA : ∃ t ∈ T ⊓ LinearMap.ker (Q.polarBilin.flip z), Q.polarBilin t y ≠ 0
  · obtain ⟨t, htS, hty⟩ := hA
    obtain ⟨hQt, htz⟩ := hmem t htS
    refine ⟨(Q.polarBilin t y)⁻¹ • t, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_smul, hQt, smul_zero]
    · rw [map_smul, LinearMap.smul_apply, htz, smul_zero]
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hty]
  obtain ⟨hQh, hhz'⟩ := hmem h hhS
  have hhy : Q.polarBilin h y = 0 := by
    by_contra hne
    exact hA ⟨h, hhS, hne⟩
  have hli : LinearIndependent K ![h, z, y] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three] at hc
    have hc' : c 0 • h + c 1 • z + c 2 • y = 0 := by simpa using hc
    have e1 : c 0 • h + c 1 • z = c 2 • y := by
      have h1 := eq_neg_of_add_eq_zero_left hc'
      rwa [← neg_smul, CharTwo.neg_eq] at h1
    have e2 : c 2 = 0 := by
      have hl : Q (c 0 • h + c 1 • z) = 0 := by
        rw [quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQh, hQz]
        simp only [map_smul, LinearMap.smul_apply, hhz', smul_zero, add_zero]
      rw [e1, QuadraticMap.map_smul, hQy, smul_eq_mul, mul_one] at hl
      exact mul_self_eq_zero.mp hl
    have e4 : c 0 • h = c 1 • z := by
      rw [e2, zero_smul] at e1
      have h1 := eq_neg_of_add_eq_zero_left e1
      rwa [← neg_smul, CharTwo.neg_eq] at h1
    have e3 : c 0 = 0 := by
      by_contra hc0
      apply hhz
      rw [Submodule.mem_span_singleton]
      exact ⟨(c 0)⁻¹ * c 1, by rw [mul_smul, ← e4, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
    have e5 : c 1 = 0 := by
      rw [e3, zero_smul] at e4
      exact (smul_eq_zero.mp e4.symm).resolve_right hz0
    intro i
    fin_cases i
    exacts [e3, e5, e2]
  obtain ⟨w, hw⟩ := exists_polar_dual Q hQ ![h, z, y] hli
  have a0 : Q.polarBilin h (w 0) = 1 := by simpa using hw 0 0
  have a2 : Q.polarBilin h (w 2) = 0 := by simpa using hw 0 2
  have b0 : Q.polarBilin z (w 0) = 0 := by simpa using hw 1 0
  have b2 : Q.polarBilin z (w 2) = 0 := by simpa using hw 1 2
  have c0 : Q.polarBilin y (w 0) = 0 := by simpa using hw 2 0
  have c2 : Q.polarBilin y (w 2) = 1 := by simpa using hw 2 2
  have hxh : Q.polarBilin (w 0 + w 2) h = 1 := by
    rw [polarBilin_comm, map_add, a0, a2, add_zero]
  have hxz : Q.polarBilin (w 0 + w 2) z = 0 := by
    rw [polarBilin_comm, map_add, b0, b2, add_zero]
  have hxy : Q.polarBilin (w 0 + w 2) y = 1 := by
    rw [polarBilin_comm, map_add, c0, c2, zero_add]
  refine ⟨(w 0 + w 2) + Q (w 0 + w 2) • h, ?_, ?_, ?_⟩
  · rw [quad_add Q (w 0 + w 2) (Q (w 0 + w 2) • h), QuadraticMap.map_smul, hQh, smul_zero,
      add_zero, map_smul, hxh, smul_eq_mul, mul_one, CharTwo.add_self_eq_zero]
  · rw [map_add, LinearMap.add_apply, hxz, map_smul, LinearMap.smul_apply, hhz', smul_zero,
      add_zero]
  · rw [map_add, LinearMap.add_apply, hxy, map_smul, LinearMap.smul_apply, hhy, smul_zero,
      add_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_singular_dual_vector {z y g f₀ : ι → K} (hQz : Q z = 0) (hQy : Q y = 1)
    (hyz : Q.polarBilin y z = 0) (hgz : Q.polarBilin g z = 0) (hgy : Q.polarBilin g y = 1)
    (hQf₀ : Q f₀ = 0) (hzf₀ : Q.polarBilin z f₀ = 1) (hyf₀ : Q.polarBilin y f₀ = 0) :
    ∃ f, Q f = 0 ∧ Q.polarBilin z f = 1 ∧ Q.polarBilin g f = 0 ∧ Q.polarBilin y f = 0 := by
  obtain ⟨β, hβ⟩ : ∃ β, Q.polarBilin g f₀ = β := ⟨_, rfl⟩
  have hzy : Q.polarBilin z y = 0 := by rw [polarBilin_comm]; exact hyz
  have hf₀y : Q.polarBilin f₀ y = 0 := by rw [polarBilin_comm]; exact hyf₀
  have hf₀z : Q.polarBilin f₀ z = 1 := by rw [polarBilin_comm]; exact hzf₀
  refine ⟨f₀ + β • y + β ^ 2 • z, ?_, ?_, ?_, ?_⟩
  · rw [quad_add Q (f₀ + β • y) (β ^ 2 • z), quad_add Q f₀ (β • y), QuadraticMap.map_smul,
      QuadraticMap.map_smul, hQf₀, hQy, hQz]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hf₀y,
      hf₀z, hyz, mul_zero, mul_one, add_zero, zero_add]
    linear_combination β ^ 2 * CharTwo.two_eq_zero (R := K)
  · simp only [map_add, map_smul, smul_eq_mul, hzf₀, hzy, TypeCData.pol_self, mul_zero, add_zero]
  · simp only [map_add, map_smul, smul_eq_mul, hβ, hgy, hgz, mul_zero, mul_one, add_zero]
    exact CharTwo.add_self_eq_zero β
  · simp only [map_add, map_smul, smul_eq_mul, hyf₀, TypeCData.pol_self, hyz, mul_zero, add_zero]

end Vectors

section Matrices

variable {Q : QuadraticForm K (ι → K)} [CharP K 2]

omit [CharP K 2] in
theorem cTwoX_mulVec (u z v : ι → K) :
    cTwoX Q u z *ᵥ v = Q.polarBilin v u • z + Q.polarBilin v z • u := by
  rw [cTwoX, add_mulVec, polMat_mulVec, polMat_mulVec]

omit [CharP K 2] in
theorem cTwoX_add (u w z : ι → K) : cTwoX Q u z + cTwoX Q w z = cTwoX Q (u + w) z :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [add_mulVec, cTwoX_mulVec, cTwoX_mulVec, cTwoX_mulVec, map_add, add_smul, smul_add]
    abel

theorem cTwoX_mul {u w z : ι → K} (huz : Q.polarBilin u z = 0) (hwz : Q.polarBilin w z = 0) :
    cTwoX Q u z * cTwoX Q w z = Q.polarBilin w u • polMat Q z z :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hzu : Q.polarBilin z u = 0 := by rw [polarBilin_comm]; exact huz
    rw [← mulVec_mulVec, cTwoX_mulVec w z v, mulVec_add, mulVec_smul, mulVec_smul,
      cTwoX_mulVec u z z, cTwoX_mulVec u z w, smul_mulVec, polMat_mulVec, hzu,
      TypeCData.pol_self, hwz]
    simp only [zero_smul, add_zero, smul_zero, zero_add]
    rw [smul_smul, smul_smul, mul_comm]

theorem cTwoX_mul_self {u z : ι → K} (huz : Q.polarBilin u z = 0) :
    cTwoX Q u z * cTwoX Q u z = 0 := by
  rw [cTwoX_mul huz huz, TypeCData.pol_self, zero_smul]

omit [CharP K 2] in
theorem quad_cTwoX {u z : ι → K} (hQu : Q u = 0) (hQz : Q z = 0)
    (huz : Q.polarBilin u z = 0) (v : ι → K) : Q (cTwoX Q u z *ᵥ v) = 0 := by
  have hzu : Q.polarBilin z u = 0 := by rw [polarBilin_comm]; exact huz
  rw [cTwoX_mulVec, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQz, hQu]
  simp only [map_smul, LinearMap.smul_apply, hzu, smul_zero, add_zero]

theorem pol_cTwoX (u z v : ι → K) : Q.polarBilin v (cTwoX Q u z *ᵥ v) = 0 := by
  rw [cTwoX_mulVec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm,
    CharTwo.add_self_eq_zero]

theorem cTwoX_isometry {u z : ι → K} (hQu : Q u = 0) (hQz : Q z = 0)
    (huz : Q.polarBilin u z = 0) (a : K) (v : ι → K) :
    Q ((1 + a • cTwoX Q u z) *ᵥ v) = Q v := by
  rw [add_mulVec, one_mulVec, smul_mulVec, quad_add, QuadraticMap.map_smul,
    quad_cTwoX hQu hQz huz, smul_zero, add_zero, map_smul, smul_eq_mul, pol_cTwoX, mul_zero,
    add_zero]

omit [CharP K 2] in
theorem rank_cTwoX {u z p₁ p₂ : ι → K} (hz0 : z ≠ 0) (h₁u : Q.polarBilin p₁ u = 1)
    (h₁z : Q.polarBilin p₁ z = 0) (h₂u : Q.polarBilin p₂ u = 0) (h₂z : Q.polarBilin p₂ z = 1) :
    (cTwoX Q u z).rank = 2 := by
  refine rank_eq_two_of (u := z) (w := u) (fun a b h => ?_)
    (fun v => ⟨_, _, cTwoX_mulVec u z v⟩)
    ⟨p₁, by rw [cTwoX_mulVec, h₁u, h₁z, one_smul, zero_smul, add_zero]⟩
    ⟨p₂, by rw [cTwoX_mulVec, h₂u, h₂z, one_smul, zero_smul, zero_add]⟩
  have h1 := congrArg (Q.polarBilin p₁) h
  rw [map_add, map_smul, map_smul, h₁z, h₁u, map_zero, smul_zero, smul_eq_mul, mul_one,
    zero_add] at h1
  subst h1
  rw [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right hz0, rfl⟩

omit [CharP K 2] in
theorem conj_cTwoX {D : GL ι K} (hD : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) (u z : ι → K) :
    ((D⁻¹ : GL ι K) : Matrix ι ι K) * cTwoX Q u z * D =
      cTwoX Q (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u)
        (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z) := by
  rw [cTwoX, mul_add, add_mul, conj_polMat Q hD, conj_polMat Q hD, cTwoX]

omit [CharP K 2] in
theorem cTwoX_smul (a b : K) (u z : ι → K) :
    cTwoX Q (a • u) (b • z) = (a * b) • cTwoX Q u z :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [cTwoX_mulVec, smul_mulVec, cTwoX_mulVec, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    module

theorem hypMat_mulVec_left {z f : ι → K} (hzf : Q.polarBilin z f = 1) (α : K) :
    hypMat Q z f α *ᵥ z = α • z := by
  rw [hypMat_mulVec, hzf, TypeCData.pol_self, mul_one, mul_zero, zero_smul, add_zero, sub_smul,
    one_smul, add_sub_cancel]

theorem hypMat_mulVec_right {z f : ι → K} (hzf : Q.polarBilin z f = 1) (α : K) :
    hypMat Q z f α *ᵥ f = α⁻¹ • f := by
  rw [hypMat_mulVec, TypeCData.pol_self, polarBilin_comm Q f z, hzf, mul_zero, zero_smul,
    add_zero, mul_one, sub_smul, one_smul, add_sub_cancel]

omit [CharP K 2] in
theorem hypMat_mulVec_of_perp {z f v : ι → K} (hvz : Q.polarBilin v z = 0)
    (hvf : Q.polarBilin v f = 0) (α : K) : hypMat Q z f α *ᵥ v = v := by
  rw [hypMat_mulVec, hvz, hvf, mul_zero, mul_zero, zero_smul, zero_smul, add_zero, add_zero]

end Matrices

section Main

variable [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem splitAt_of_singular_pair (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega ⇑Q)} (hZ : Odd (Nat.card (center ↥A)))
    {z y g f : ι → K} (hQz : Q z = 0) (hQy : Q y = 1) (hyz : Q.polarBilin y z = 0)
    (hQg : Q g = 0) (hgz : Q.polarBilin g z = 0) (hgy : Q.polarBilin g y = 1) (hQf : Q f = 0)
    (hzf : Q.polarBilin z f = 1) (hgf : Q.polarBilin g f = 0) (hyf : Q.polarBilin y f = 0)
    {J : Subgroup G} (W : K → GL ι K) (hWc : ∀ d, (W d : Matrix ι ι K) = 1 + cTwoT Q y z d)
    (hJ : ∀ j, j ∈ J ↔ ∃ d, j ^ 2 = 1 ∧ Represents e j (W d)) :
    SplitAt A J (Nat.card K)
      (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2)
      (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2) := by
  have hz0 : z ≠ 0 := fun h => by
    rw [h, map_zero, LinearMap.zero_apply] at hzf
    exact zero_ne_one hzf
  have hzy : Q.polarBilin z y = 0 := by rw [polarBilin_comm]; exact hyz
  have hzg : Q.polarBilin z g = 0 := by rw [polarBilin_comm]; exact hgz
  have hyg : Q.polarBilin y g = 1 := by rw [polarBilin_comm]; exact hgy
  have hfz : Q.polarBilin f z = 1 := by rw [polarBilin_comm]; exact hzf
  have hfg : Q.polarBilin f g = 0 := by rw [polarBilin_comm]; exact hgf
  have huz : Q.polarBilin (y + g) z = 0 := by
    rw [map_add, LinearMap.add_apply, hyz, hgz, add_zero]
  have hQu : Q (y + g) = 0 := by
    rw [quad_add, hQy, hQg, hyg, add_zero, CharTwo.add_self_eq_zero]
  have hgu : Q.polarBilin g (y + g) = 1 := by rw [map_add, hgy, TypeCData.pol_self, add_zero]
  have hug : Q.polarBilin (y + g) g = 1 := by rw [polarBilin_comm]; exact hgu
  have hfu : Q.polarBilin f (y + g) = 0 := by
    rw [map_add, polarBilin_comm Q f y, hyf, hfg, add_zero]
  have huf : Q.polarBilin (y + g) f = 0 := by rw [polarBilin_comm]; exact hfu
  have hzu : Q.polarBilin z (y + g) = 0 := by rw [polarBilin_comm]; exact huz
  have hX₁sq := cTwoX_mul_self (Q := Q) hgz
  have hX₂sq := cTwoX_mul_self (Q := Q) huz
  have hX₁₂ : cTwoX Q g z * cTwoX Q (y + g) z = polMat Q z z := by
    rw [cTwoX_mul hgz huz, hug, one_smul]
  have hX₂₁ : cTwoX Q (y + g) z * cTwoX Q g z = polMat Q z z := by
    rw [cTwoX_mul huz hgz, hgu, one_smul]
  have hsum : cTwoX Q g z + cTwoX Q (y + g) z = cTwoX Q y z := by
    rw [cTwoX_add, add_comm y g, ← add_assoc, add_self_vec, zero_add]
  have hfac : ∀ d : K, (1 + d • cTwoX Q g z) * (1 + d • cTwoX Q (y + g) z) =
      1 + cTwoT Q y z d := fun d => by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hX₁₂, cTwoT, ← hsum, smul_add,
      pow_two]
    abel
  have hsq₁ : ∀ a : K, (a • cTwoX Q g z) * (a • cTwoX Q g z) = 0 := fun a => by
    rw [smul_mul_smul_comm, hX₁sq, smul_zero]
  have hsq₂ : ∀ a : K, (a • cTwoX Q (y + g) z) * (a • cTwoX Q (y + g) z) = 0 := fun a => by
    rw [smul_mul_smul_comm, hX₂sq, smul_zero]
  have hX₁y : cTwoX Q g z *ᵥ y = z := by
    rw [cTwoX_mulVec, hyg, hyz, one_smul, zero_smul, add_zero]
  have hX₁z : cTwoX Q g z *ᵥ z = 0 := by
    rw [cTwoX_mulVec, hzg, TypeCData.pol_self, zero_smul, zero_smul, add_zero]
  have hX₁g : cTwoX Q g z *ᵥ g = 0 := by
    rw [cTwoX_mulVec, TypeCData.pol_self, hgz, zero_smul, zero_smul, add_zero]
  have hX₂g : cTwoX Q (y + g) z *ᵥ g = z := by
    rw [cTwoX_mulVec, hgu, hgz, one_smul, zero_smul, add_zero]
  have hX₂z : cTwoX Q (y + g) z *ᵥ z = 0 := by
    rw [cTwoX_mulVec, hzu, TypeCData.pol_self, zero_smul, zero_smul, add_zero]
  have hX₁0 : cTwoX Q g z ≠ 0 := fun h => hz0 (by rw [← hX₁y, h, zero_mulVec])
  have hX₂0 : cTwoX Q (y + g) z ≠ 0 := fun h => hz0 (by rw [← hX₂g, h, zero_mulVec])
  have hr₁ : (cTwoX Q g z).rank = 2 := rank_cTwoX hz0 hyg hyz hfg hfz
  have hr₂ : (cTwoX Q (y + g) z).rank = 2 := rank_cTwoX hz0 hgu hgz hfu hfz
  have hrk₁ : ∀ a : K, a ≠ 0 → (a • cTwoX Q g z).rank = 2 := fun a ha => by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha), hr₁]
  have hrk₂ : ∀ a : K, a ≠ 0 → (a • cTwoX Q (y + g) z).rank = 2 := fun a ha => by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha), hr₂]
  set W₁ : K → GL ι K := fun a => sqZeroGL (a • cTwoX Q g z) (hsq₁ a) with hW₁
  set W₂ : K → GL ι K := fun a => sqZeroGL (a • cTwoX Q (y + g) z) (hsq₂ a) with hW₂
  have hW₁c : ∀ a, (W₁ a : Matrix ι ι K) = 1 + a • cTwoX Q g z := fun a => rfl
  have hW₂c : ∀ a, (W₂ a : Matrix ι ι K) = 1 + a • cTwoX Q (y + g) z := fun a => rfl
  refine splitAt_of_lifts (e := e) hZ W₁ W₂ (fun a => ?_) (fun a => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a => sqZeroGL_sq _ _) (fun a => sqZeroGL_sq _ _) (fun a b => ?_)
    (fun a c h => ?_) (fun a c h => ?_) (fun a b c h => ?_) (fun j => ?_) (fun c hc => ?_) _ _
    (fun a ha x hx2 hx => ?_) (fun a ha x hx2 hx => ?_)
  ·
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hW₁c]
      exact cTwoX_isometry hQg hQz hgz a v
    · rw [commRank_sqZeroGL]
      by_cases ha : a = 0
      · rw [ha, zero_smul, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hrk₁ a ha]
        exact even_two
  ·
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hW₂c]
      exact cTwoX_isometry hQu hQz huz a v
    · rw [commRank_sqZeroGL]
      by_cases ha : a = 0
      · rw [ha, zero_smul, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hrk₂ a ha]
        exact even_two
  ·
    apply Units.ext
    rw [Units.val_mul, hW₁c, hW₁c, hW₁c]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hX₁sq, smul_zero,
      add_zero, add_smul]
    abel
  ·
    apply Units.ext
    rw [Units.val_mul, hW₂c, hW₂c, hW₂c]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hX₂sq, smul_zero,
      add_zero, add_smul]
    abel
  ·
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hW₁c, hW₂c]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hX₁₂, hX₂₁]
    rw [mul_comm a b]
    abel
  ·
    have h0 := eq_zero_of_sqZeroGL_eq_scalar (hsq₁ a) h
    exact (smul_eq_zero.mp h0).resolve_right hX₁0
  ·
    have h0 := eq_zero_of_sqZeroGL_eq_scalar (hsq₂ a) h
    exact (smul_eq_zero.mp h0).resolve_right hX₂0
  ·
    have hm := congrArg (fun X : GL ι K => (X : Matrix ι ι K)) h
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hW₁c, hW₂c,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one] at hm
    have hcz : z = (c : K) • z := by
      have h1 := congrArg (· *ᵥ z) hm
      simp only [add_mulVec, one_mulVec, smul_mulVec, hX₁z, hX₂z, smul_zero, add_zero] at h1
      exact h1
    have hc1 : (c : K) = 1 := by
      by_contra hne
      have h4 : ((c : K) - 1) • z = 0 := by rw [sub_smul, one_smul, ← hcz, sub_self]
      exact hz0 ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne))
    rw [hc1, one_smul, add_right_inj] at hm
    have h5 := congrArg (· *ᵥ g) hm
    simp only [smul_mulVec, hX₂g, hX₁g, smul_zero] at h5
    have hb : b = 0 := (smul_eq_zero.mp h5).resolve_right hz0
    rw [hb, zero_smul] at hm
    exact (smul_eq_zero.mp hm.symm).resolve_right hX₁0
  ·
    rw [hJ]
    refine exists_congr fun d => and_congr_right fun _ => ?_
    have hWd : W d = W₁ d * W₂ d := by
      apply Units.ext
      rw [Units.val_mul, hWc, hW₁c, hW₂c, hfac]
    rw [hWd]
  ·
    obtain ⟨μ, hμ2⟩ : ∃ μ : K, μ ^ 2 = c := ⟨(frobeniusEquiv K 2).symm c, by
      have h := frobenius_apply_frobeniusEquiv_symm K 2 c
      rwa [frobenius_def] at h⟩
    have hμ : μ ≠ 0 := fun h0 => hc (by rw [← hμ2, h0, zero_pow two_ne_zero])
    have hiso₁ : ∀ v, Q (((hypGL hzf (inv_ne_zero hμ) : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v :=
      fun v => by
        rw [coe_hypGL]
        exact hypMat_isometry hzf hQz hQf (inv_ne_zero hμ) v
    have hiso₂ : ∀ v, Q (((hypGL hgu hμ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
      rw [coe_hypGL]
      exact hypMat_isometry hgu hQg hQu hμ v
    have hDiso : ∀ v, Q (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ : GL ι K) :
        Matrix ι ι K) *ᵥ v) = Q v := fun v => by
      rw [Units.val_mul, ← mulVec_mulVec, hiso₁, hiso₂]
    have hDinv : ∀ v, (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) :
        Matrix ι ι K) *ᵥ v = hypMat Q g (y + g) μ⁻¹ *ᵥ (hypMat Q z f μ⁻¹⁻¹ *ᵥ v) := fun v => by
      rw [_root_.mul_inv_rev, Units.val_mul, coe_hypGL_inv, coe_hypGL_inv, mulVec_mulVec]
    have hDz : (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z =
        μ • z := by
      rw [hDinv, hypMat_mulVec_left hzf, inv_inv, mulVec_smul, hypMat_mulVec_of_perp hzg hzu]
    have hDg : (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ g =
        μ⁻¹ • g := by
      rw [hDinv, hypMat_mulVec_of_perp hgz hgf, hypMat_mulVec_left hgu]
    have hDu : (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ
        (y + g) = μ • (y + g) := by
      rw [hDinv, hypMat_mulVec_of_perp huz huf, hypMat_mulVec_right hgu, inv_inv]
    have hc₁ : (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) : Matrix ι ι K) *
        cTwoX Q g z * ((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ : GL ι K) : Matrix ι ι K) =
        cTwoX Q g z := by
      rw [conj_cTwoX hDiso, hDg, hDz, cTwoX_smul, inv_mul_cancel₀ hμ, one_smul]
    have hc₂ : (((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ)⁻¹ : GL ι K) : Matrix ι ι K) *
        cTwoX Q (y + g) z * ((hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ : GL ι K) :
          Matrix ι ι K) = c • cTwoX Q (y + g) z := by
      rw [conj_cTwoX hDiso, hDu, hDz, cTwoX_smul, ← pow_two, hμ2]
    refine ⟨hypGL hzf (inv_ne_zero hμ) * hypGL hgu hμ, mul_mem ?_ ?_, fun x => ⟨?_, ?_⟩⟩
    · exact mem_statedOmega_of Q hQ hT hiso₁ (hypGL_even_commRank hzf (inv_ne_zero hμ))
    · exact mem_statedOmega_of Q hQ hT hiso₂ (hypGL_even_commRank hgu hμ)
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hW₁c, mul_add, mul_one, add_mul, Units.inv_mul,
        mul_smul_comm, smul_mul_assoc, hc₁]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, hW₂c, hW₂c, mul_add, mul_one, add_mul, Units.inv_mul,
        mul_smul_comm, smul_mul_assoc, hc₂, smul_smul, mul_comm x c]
  ·
    refine ⟨hx2, W₁ a, hx, orderOf_sqZeroGL (hsq₁ a) (fun h => ha ?_), ?_, even_two,
      fun v => ?_⟩
    · exact (smul_eq_zero.mp h).resolve_right hX₁0
    · rw [commRank_sqZeroGL, hrk₁ a ha]
    · show Q (((W₁ a : Matrix ι ι K) - 1) *ᵥ v) = 0
      rw [hW₁c, add_sub_cancel_left, smul_mulVec, QuadraticMap.map_smul,
        quad_cTwoX hQg hQz hgz, smul_zero]
  ·
    refine ⟨hx2, W₂ a, hx, orderOf_sqZeroGL (hsq₂ a) (fun h => ha ?_), ?_, even_two,
      fun v => ?_⟩
    · exact (smul_eq_zero.mp h).resolve_right hX₂0
    · rw [commRank_sqZeroGL, hrk₂ a ha]
    · show Q (((W₂ a : Matrix ι ι K) - 1) *ᵥ v) = 0
      rw [hW₂c, add_sub_cancel_left, smul_mulVec, QuadraticMap.map_smul,
        quad_cTwoX hQu hQz huz, smul_zero]

theorem splitAt_jGroup_of_typeCTwo (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K)
    (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .c 2)
    (hreg : RegularOn A (jGroup A p) (nonidentity (jGroup A p)))
    (haut : AutCyclic A (jGroup A p) (Nat.card K - 1)) :
    SplitAt A (jGroup A p) (Nat.card K)
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2)
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2) := by
  subst hq
  obtain ⟨hp2, M, hpM, hM2, hr, ⟨hev, hc⟩⟩ := hp
  have hMiso : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v := statedOmega_isometry hpM.2.1
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    have h1 : v + ((M : Matrix ι ι K) - 1) *ᵥ v = (M : Matrix ι ι K) *ᵥ v := by
      rw [sub_mulVec, one_mulVec, add_sub_cancel]
    rw [h1]
    exact hMiso v
  have hev' : Even (commRank M) := hr ▸ hev
  have hN := sub_one_mul_self_eq_zero hM2
  obtain ⟨z, z', y', hd⟩ := exists_typeCData hQ hMiso hM2 hev' hc
  obtain ⟨W, hWc, hJ⟩ := exists_beta_jGroup Q hQ hT hZ hp2 hpM hM2 hev' hd.sq hreg haut
  have he₁ : TypeCData.e₁ Q ((M : Matrix ι ι K) - 1) z y' = 0 := by
    apply eq_zero_of_rank_eq_zero
    rw [hd.rank_e₁ hN hiso]
    exact Nat.sub_eq_zero_of_le hr.le
  have hW : ∀ d, (W d : Matrix ι ι K) =
      1 + cTwoT Q (((M : Matrix ι ι K) - 1) *ᵥ y') z d := fun d => by
    rw [hWc, ← hd.factor hN hiso d, he₁, smul_zero, add_zero, one_mul]
  have hz0 : z ≠ 0 := fun h => by
    have h1 := hd.pol_y'z
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨g, hQg, hgz, hgy⟩ := exists_singular_partner hQ hT hz0 hd.quad_z hd.quad_y
  obtain ⟨f, hQf, hzf, hgf, hyf⟩ := exists_singular_dual_vector hd.quad_z hd.quad_y
    (hd.pol_y_z hN) hgz hgy (hd.quad_f hiso) (hd.pol_z_f hiso) (hd.pol_y_f hN hiso)
  exact splitAt_of_singular_pair Q hQ hT hZ hd.quad_z hd.quad_y (hd.pol_y_z hN) hQg hgz hgy hQf
    hzf hgf hyf W hW hJ

end Main

theorem orthPlusSplitCTwo : OrthPlusSplitCTwo := by
  intro G _ _ A D hD _ hZ _ p hp hcase
  have hJ := regularOn_autCyclic_of_case hcase
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hreg, haut⟩ := hJ
    have haut' : AutCyclic A (jGroup A p) (Nat.card K - 1) := by
      rw [hK]
      exact haut
    have hsplit := splitAt_jGroup_of_typeCTwo (CFSG.LieType.Universal.Spin.quadPlus n K)
      (StatedQuadPlus n K) (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K) hZ hp hreg haut'
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem orthMinusSplitCTwo : OrthMinusSplitCTwo := by
  intro G _ _ A D hD _ hZ _ p hp hcase
  have hJ := regularOn_autCyclic_of_case hcase
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨hreg, haut⟩ := hJ
    have haut' : AutCyclic A (jGroup A p) (Nat.card K - 1) := by
      rw [hK]
      exact haut
    have hsplit := splitAt_jGroup_of_typeCTwo (CFSG.LieType.Universal.Spin.quadMinus n K b c)
      (StatedQuadMinus n K b c) (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) hZ hp hreg haut'
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

theorem classicalSplit : ClassicalSplit :=
  classicalSplit_of orthPlusSplitC orthMinusSplitC orthPlusSplitCTwo orthMinusSplitCTwo

end CFSG.ComponentClassification.RankTwoClassical
