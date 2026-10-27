module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnKey
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnAut
public import CFSG.GH74.GLS.Stage2.OddAut.FixStep

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer.Odd87


section Model

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem hermGram_hyp (r ε : ℕ) : HermGram h (hypGram r ε K) where
  herm := by rw [hypGram_map, hypGram_transpose]
  det_ne := det_hypGram_ne_zero
  map_eq := fun σ => hypGram_map_ringEquiv σ

section Sign

variable [Fact p.Prime] [CharP K p] [Nonempty (HypIndex r ε)]

theorem scalar_eq_one_of_pow (c : Kˣ) (hc : GeneralLinearGroup.scalar (HypIndex r ε) c ^ p = 1) :
    c = 1 := by
  have h1 : ((GeneralLinearGroup.scalar (HypIndex r ε) (c ^ p) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [map_pow, hc, Units.val_one]
  obtain ⟨i0⟩ : Nonempty (HypIndex r ε) := inferInstance
  have h2 := congrFun (congrFun h1 i0) i0
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Matrix.one_apply_eq, Units.val_pow_eq_pow_val] at h2
  have h3 : (c : K) = 1 := by
    apply frobenius_inj K p
    rw [frobenius_def, map_one]
    exact h2
  exact Units.ext h3

theorem eq_of_proj_eq_of_pow {x y : hypSU h r ε} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : hypProj h r ε x = hypProj h r ε y) : x = y := by
  have hmem : x⁻¹ * y ∈ hypScalars h r ε := QuotientGroup.eq.mp hxy
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hmem
  have hcen : x⁻¹ * y ∈ Subgroup.center (hypSU h r ε) :=
    normOneScalars_le_center h _ _ hmem
  have hcomm : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp hcen x
  have hyx : y = x * (x⁻¹ * y) := by group
  have hsp : (x⁻¹ * y) ^ p = 1 := by
    have h1 : y ^ p = x ^ p * (x⁻¹ * y) ^ p := by
      conv_lhs => rw [hyx]
      exact hcomm.mul_pow p
    rw [hy, hx, one_mul] at h1
    exact h1.symm
  have hc1 : c = 1 := by
    refine scalar_eq_one_of_pow (p := p) (r := r) (ε := ε) c ?_
    have := congrArg (fun g : hypSU h r ε => (g : GL (HypIndex r ε) K)) hsp
    simpa [hc] using this
  have hs1 : x⁻¹ * y = 1 := by
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  exact mul_left_cancel (a := x⁻¹) (by rw [hs1, inv_mul_cancel])

end Sign

section Conj

@[expose] noncomputable def cfHom (X : semilinearSimilitudes h r ε) :
    hypSU h r ε →* hypSU h r ε where
  toFun x := ⟨(X : SemiGL (HypIndex r ε) K).left * glAut (X : SemiGL (HypIndex r ε) K).right
    (x : GL (HypIndex r ε) K) * (X : SemiGL (HypIndex r ε) K).left⁻¹, conj_mem_hypSU X.2 x⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]
    group

theorem coe_cfHom (X : semilinearSimilitudes h r ε) (x : hypSU h r ε) :
    ((cfHom h X x : hypSU h r ε) : GL (HypIndex r ε) K) =
      (X : SemiGL (HypIndex r ε) K).left * glAut (X : SemiGL (HypIndex r ε) K).right
        (x : GL (HypIndex r ε) K) * (X : SemiGL (HypIndex r ε) K).left⁻¹ := rfl

theorem aut_proj (hr : 1 ≤ r) (hε : ε ≤ 1) (X : semilinearSimilitudes h r ε) (x : hypSU h r ε) :
    semilinearAutHom h hr hε X (hypProj h r ε x) = hypProj h r ε (cfHom h X x) :=
  semilinearAutHom_apply h hr hε X x

theorem act_semi_of_conj {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι K}
    (A : GL ι K) (σ : K ≃+* K) (x y : gramSU h G)
    (hxy : mx (y : GL ι K) = mx A * (mx (x : GL ι K)).map σ * mx A⁻¹) (w : ι → K) :
    act y (semi A σ w) = semi A σ (act x w) := by
  unfold act semi
  rw [hxy, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  have h1 : mx A⁻¹ * mx A = 1 := by
    simp only [mx]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  have := RingHom.map_mulVec (σ : K →+* K) (mx (x : GL ι K)) w i
  simpa using this.symm

theorem act_cfHom (X : semilinearSimilitudes h r ε) (x : hypSU h r ε)
    (w : HypIndex r ε → K) :
    act (cfHom h X x) (semi (X : SemiGL (HypIndex r ε) K).left
      (X : SemiGL (HypIndex r ε) K).right w) =
      semi (X : SemiGL (HypIndex r ε) K).left (X : SemiGL (HypIndex r ε) K).right (act x w) :=
  act_semi_of_conj h _ _ x _ (by simp only [mx, coe_cfHom, Units.val_mul, coe_glAut]) w

end Conj

end Model

section CaseA

variable {Y : Type} [Group Y]

theorem fix_of_commute_conj (hcen : Subgroup.center Y = ⊥) {z : MulAut Y} {g : Y}
    (hzg : MulAut.conj g * z = z * MulAut.conj g) : z g = g := by
  have hinj := mulAut_conj_injective_of_center_bot hcen
  apply hinj
  have h1 := mulAut_conj_conj z g
  rw [← h1, ← hzg, mul_assoc, mul_inv_cancel, mul_one]

end CaseA

section CaseA2

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}

theorem isPGroup_map_QE [Fact p.Prime] [CharP K p] [Nonempty (HypIndex r ε)] (hp : p ≠ 2)
    (E : Submodule K (HypIndex r ε → K)) :
    IsPGroup p ↥((QE (hermGram_hyp h r ε) E).map (hypProj h r ε)) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : hypPSU h r ε) ^ p ^ 1 = 1
  rw [pow_one, ← hxg, ← map_pow, InQ.pow_eq_one (hermGram_hyp h r ε) hx hp, map_one]

theorem un_caseA (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hp2 : p ≠ 2)
    (hcen : Subgroup.center (hypPSU h r ε) = ⊥) {V Z : Subgroup (MulAut (hypPSU h r ε))}
    (h2 : N2Cfg (hypPSU h r ε) p V Z) (h3 : N3Full (hypPSU h r ε) V Z) : False := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have : Nonempty (HypIndex r ε) := ⟨Sum.inl ⟨0, hr⟩⟩
  have hG := hermGram_hyp h r ε
  have hVe : IsElementaryAbelian p ↥V := h2.2.2.1
  have hVc : Nat.card ↥V = p ^ 2 := h2.2.2.2.1
  obtain ⟨v, hvV, hv1, g, hgp, hgv⟩ := un_exists_inner_of_elem h hr hε hn hp2 hVe hVc
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hv1
    rw [← hgv, map_one, map_one]
  have hzu : ∀ z ∈ Z, z (hypProj h r ε g) = hypProj h r ε g := fun z hz =>
    fix_of_commute_conj hcen (by rw [hgv]; exact h2.2.2.2.2.2.2.2.2 v hvV z hz)
  set M : Subgroup (hypPSU h r ε) := (QE hG (fixU g)).map (hypProj h r ε) with hM
  have hMle : M ≤ fixSub v := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hgv, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
      ← commute_of_inQ hG hx, mul_assoc, mul_inv_cancel, mul_one]
  have hΦ : ∀ z : MulAut (hypPSU h r ε), ∀ X : semilinearSimilitudes h r ε,
      semilinearAutHom h hr hε X = z → ∀ x : hypSU h r ε,
      z (hypProj h r ε x) = hypProj h r ε (cfHom h X x) := fun z X hX x => by
    rw [← hX]
    exact aut_proj h hr hε X x
  have hcf : ∀ z : MulAut (hypPSU h r ε), ∀ X : semilinearSimilitudes h r ε,
      semilinearAutHom h hr hε X = z → ∀ y : hypSU h r ε, y ^ p = 1 →
      z (hypProj h r ε y) = hypProj h r ε y → cfHom h X y = y := by
    intro z X hX y hy hzy
    refine eq_of_proj_eq_of_pow h ?_ hy ?_
    · rw [← map_pow, hy, map_one]
    · rw [← hΦ z X hX y, hzy]
  have hMinv : ∀ z ∈ Z, ∀ c ∈ M, z c ∈ M := by
    intro z hz c hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨X, hX⟩ := semilinearAutHom_surjective h hr hε hp2 hn z
    obtain ⟨μ, hμ0, hμ, hA⟩ := X.2
    have hcfg : cfHom h X g = g := hcf z X hX g hgp (hzu z hz)
    have hΦE : ∀ w ∈ fixU g, semi (X : SemiGL (HypIndex r ε) K).left
        (X : SemiGL (HypIndex r ε) K).right w ∈ fixU g := by
      intro w hw
      rw [mem_fixU] at hw ⊢
      have := act_cfHom h X g w
      rw [hcfg, hw] at this
      exact this
    refine ⟨cfHom h X x, inQ_conj hG _ _ hA hΦE (fun w => act_cfHom h X x w) hx, ?_⟩
    rw [hΦ z X hX x]
  have hMp : NoOddNormal M p := noOddNormal_of_isPGroup (isPGroup_map_QE h hp2 _)
  have hfix := fix_step hcen h2 h3 hvV hv1 hMle hMinv hMp
  obtain ⟨-, -, -, -, -, hZodd, hZcop, hZbot, -⟩ := h2
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hdvd : orderOf (z : MulAut (hypPSU h r ε)) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime (orderOf (z : MulAut (hypPSU h r ε))) p :=
    Nat.Coprime.coprime_dvd_left hdvd hZcop
  have hsp : ¬ p ∣ orderOf (z : MulAut (hypPSU h r ε)) := by
    intro h'
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h')
  have hsodd : Odd (orderOf (z : MulAut (hypPSU h r ε))) := Odd.of_dvd_nat hZodd hdvd
  set s := orderOf (z : MulAut (hypPSU h r ε)) with hs
  have hzs : (z : MulAut (hypPSU h r ε)) ^ s = 1 := pow_orderOf_eq_one _
  obtain ⟨X, hX⟩ := semilinearAutHom_surjective h hr hε hp2 hn (z : MulAut (hypPSU h r ε))
  obtain ⟨μ, hμ0, hμ, hA⟩ := X.2
  set A : GL (HypIndex r ε) K := (X : SemiGL (HypIndex r ε) K).left with hAdef
  set σ : K ≃+* K := (X : SemiGL (HypIndex r ε) K).right with hσdef
  have hXs := (semilinearAutHom_eq_one_iff h hr hε hn (X ^ s)).mp (by rw [map_pow, hX, hzs])
  have hσs : σ ^ s = 1 := by
    have h1 : (((X ^ s : semilinearSimilitudes h r ε)) : SemiGL (HypIndex r ε) K).right =
        σ ^ s := by
      rw [Subgroup.coe_pow]
      exact map_pow (SemidirectProduct.rightHom : SemiGL (HypIndex r ε) K →* (K ≃+* K))
        (X : SemiGL (HypIndex r ε) K) s
    rw [← h1]
    exact hXs.1
  have hAs : σ = 1 → ∃ c : K, (mx A) ^ s = c • (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    intro hσ1
    obtain ⟨c, hc⟩ := hXs.2
    have hxinl : (X : SemiGL (HypIndex r ε) K) = SemidirectProduct.inl A :=
      SemidirectProduct.ext (by simp [hAdef]) (by simpa [hσdef] using hσ1)
    have h1 : (((X ^ s : semilinearSimilitudes h r ε)) : SemiGL (HypIndex r ε) K) =
        SemidirectProduct.inl (A ^ s) := by
      rw [Subgroup.coe_pow, hxinl, map_pow]
    rw [h1, SemidirectProduct.left_inl] at hc
    refine ⟨(c : K), ?_⟩
    have := congrArg (fun g : GL (HypIndex r ε) K => mx g) hc
    simp only [mx, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at this
    rw [mx, this, Matrix.smul_one_eq_diagonal]
    rfl
  have hΦu : ∀ w, semi A σ (act g w) = act g (semi A σ w) := by
    intro w
    have hcfg : cfHom h X g = g := hcf z X hX g hgp (hzu z z.2)
    have := act_cfHom h X g w
    rw [hcfg] at this
    exact this.symm
  have hΦQ : ∀ x : hypSU h r ε, InQ (fixU g) x → ∀ w, semi A σ (act x w) = act x (semi A σ w) := by
    intro x hx w
    have hcfx : cfHom h X x = x :=
      hcf z X hX x (InQ.pow_eq_one hG hx hp2) (hfix z z.2 _ ⟨x, hx, rfl⟩)
    have := act_cfHom h X x w
    rw [hcfx] at this
    exact this.symm
  obtain ⟨hσ1, l, hl0, hAl⟩ := key_prop hG hp2 hgp hg1 A σ hA hΦu hΦQ hsodd hsp hσs hAs
  have hz : (z : MulAut (hypPSU h r ε)) = 1 := by
    rw [← hX]
    refine (semilinearAutHom_eq_one_iff h hr hε hn X).mpr ⟨hσ1, Units.mk0 l hl0, ?_⟩
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    exact hAl
  exact hz1 (Subtype.ext hz)

end CaseA2

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
