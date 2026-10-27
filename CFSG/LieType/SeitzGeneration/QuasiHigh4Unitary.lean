module

public import CFSG.LieType.SeitzGeneration.HeisTorusUGen
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LieType.SeitzGeneration.QuasiHigh3Linear

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh4

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LieType.SeitzGeneration.QuasiHigh3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.LieType.Chevalley
open scoped commutatorElement

section SubfieldGU

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K}
  (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (n : ℕ)

include hbar in
theorem subfieldGL_mem_primeFormUnitary {g : GL (Fin n) k}
    (hg : g ∈ primeFormUnitary h₀ (idGram k n)) :
    subfieldGL k n g ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul, hg,
    Matrix.map_one _ (map_zero _) (map_one _)]

include hbar in
theorem mem_primeFormUnitary_of_subfieldGL {g : GL (Fin n) k}
    (hg : subfieldGL k n g ∈ primeFormUnitary h (idGram K n)) :
    g ∈ primeFormUnitary h₀ (idGram k n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul] at hg
  refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
  change (((g : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g).map k.subtype =
    (1 : Matrix (Fin n) (Fin n) k).map k.subtype
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def subfieldGU :
    primeFormUnitary h₀ (idGram k n) →* primeFormUnitary h (idGram K n) :=
  ((subfieldGL k n).comp (primeFormUnitary h₀ (idGram k n)).subtype).codRestrict _ fun g =>
    subfieldGL_mem_primeFormUnitary h h₀ hbar n g.2

theorem coe_subfieldGU (g : primeFormUnitary h₀ (idGram k n)) :
    ((subfieldGU h h₀ hbar n g : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      subfieldGL k n g :=
  rfl

theorem subfieldGU_injective : Function.Injective (subfieldGU h h₀ hbar n) := fun _ _ hgg' =>
  Subtype.ext (subfieldGL_injective k n (congrArg Subtype.val hgg'))

end SubfieldGU

theorem glAut_subfieldGL {K : Type} [Field K] (σ : K ≃+* K) (n : ℕ)
    (g : GL (Fin n) (fixSubfield σ)) :
    glAut σ (subfieldGL (fixSubfield σ) n g) = subfieldGL (fixSubfield σ) n g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

section Split

open CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2
  (card_inf_eq_sq_of_decomp exists_zpow_mul_mem_primeFormD relIndex_closure_pair_of_indep)

theorem eq_one_or_exists_pow_mul_eq_one {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) {r₁ r₂ : F}
    (h₁ : r₁ ^ p = 1) (h₂ : r₂ ^ p = 1) : r₁ = 1 ∨ ∃ a : ℕ, r₁ ^ a * r₂ = 1 := by
  by_cases hr : r₁ = 1
  · exact Or.inl hr
  · right
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hprim : IsPrimitiveRoot r₁ p := isPrimitiveRoot_of_pow_eq_one_ne_one hp h₁ hr
    have hr₂ : r₂ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at h₂
      exact zero_ne_one h₂
    obtain ⟨a, -, ha⟩ := hprim.eq_pow_of_pow_eq_one (ξ := r₂⁻¹) (by rw [inv_pow, h₂, inv_one])
    exact ⟨a, by rw [ha, inv_mul_cancel₀ hr₂]⟩

theorem range_le_closure_hyperLiftSet_of_perfect {G P : Type*} [Group G] [Group P]
    [Group.IsPerfect G] (β : G →* P) {p : ℕ} {E H : Subgroup (MulAut P)} (hHE : H ≤ E)
    (hH : H.relIndex E = p) (hfix : ∀ g, β g ∈ fixedPoints H) :
    β.range ≤ Subgroup.closure (hyperLiftSet p E) := by
  rw [← commutator_range_eq_of_perfect β, Subgroup.commutator_le]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact Subgroup.subset_closure (commutator_mem_hyperLiftSet hHE hH (hfix x) (hfix y))

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem primeFormConjHom_subfieldGU_mk_eq (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K}
    (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {n : ℕ}
    (x₀ : primeFormUnitary h₀ (idGram k n))
    (Y : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (hxY : (x₀ : GL (Fin n) k) * Y = Y * x₀) :
    primeFormConjHom h (idGram K n) (subfieldGU h h₀ hbar n x₀)
        ((subfieldSU h h₀ hbar n Y : gramSU h _) : primeFormP h (idGram K n)) =
      ((subfieldSU h h₀ hbar n Y : gramSU h _) : primeFormP h (idGram K n)) := by
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change subfieldGL k n (x₀ : GL (Fin n) k) * subfieldGL k n (Y : GL (Fin n) k) *
      (subfieldGL k n (x₀ : GL (Fin n) k))⁻¹ = subfieldGL k n (Y : GL (Fin n) k)
  rw [← map_mul, hxY, map_mul, mul_inv_cancel_right]

theorem commute_conj_blockGL {k : Type*} [Field k] {n : ℕ} (Pg x : GL (Fin (n + 1)) k)
    (i : Fin n) (hi : (i : ℕ) + 2 ≤ n + 1) (v : Fin (n + 1) → k) (hv : ∀ c, v c ≠ 0)
    (hx : ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      diagonal v)
    (hvv : v i.castSucc = v i.succ) (g : GL (Fin 2) k) :
    x * (Pg * blockGL (n + 1) (i : ℕ) hi g * Pg⁻¹) =
      (Pg * blockGL (n + 1) (i : ℕ) hi g * Pg⁻¹) * x := by
  have hDB : (Pg⁻¹ * x * Pg) * blockGL (n + 1) (i : ℕ) hi g =
      blockGL (n + 1) (i : ℕ) hi g * (Pg⁻¹ * x * Pg) := by
    apply Units.ext
    change ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        ((blockGL (n + 1) (i : ℕ) hi g : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      ((blockGL (n + 1) (i : ℕ) hi g : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        ((Pg⁻¹ * x * Pg : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    rw [coe_blockGL, hx]
    exact (blockMat_mul_diagonal_comm hi _ hv i.castSucc i.succ (by simp) (by simp) hvv _).symm
  calc x * (Pg * blockGL (n + 1) (i : ℕ) hi g * Pg⁻¹)
      = Pg * ((Pg⁻¹ * x * Pg) * blockGL (n + 1) (i : ℕ) hi g) * Pg⁻¹ := by group
    _ = Pg * (blockGL (n + 1) (i : ℕ) hi g * (Pg⁻¹ * x * Pg)) * Pg⁻¹ := by rw [hDB]
    _ = (Pg * blockGL (n + 1) (i : ℕ) hi g * Pg⁻¹) * x := by group

theorem map_suSub_le_closure_hyperLiftSet (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 2 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hq₀ : ℓ ^ (f / p) ≠ 2)
    {E : Subgroup (MulAut (primeFormP h (idGram K (n + 1))))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ ∈ E)
    (hlift : ∀ y ∈ E, y ∈ primeFormD h (idGram K (n + 1)) →
      ∃ x : primeFormUnitary h (idGram K (n + 1)), primeFormConjHom h _ x = y ∧
        glAut σ (x : GL (Fin (n + 1)) K) = x)
    (hcomm : ∀ x y : primeFormUnitary h (idGram K (n + 1)),
      glAut σ (x : GL (Fin (n + 1)) K) = x → glAut σ (y : GL (Fin (n + 1)) K) = y →
      primeFormConjHom h _ x ∈ E → primeFormConjHom h _ y ∈ E → x * y = y * x)
    (hpow : ∀ x : primeFormUnitary h (idGram K (n + 1)), glAut σ (x : GL (Fin (n + 1)) K) = x →
      primeFormConjHom h _ x ∈ E → x ^ (ℓ ^ (f / p) + 1) = 1) :
    (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) (n + 1)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K)) (n + 1))) ≤
      Subgroup.closure (hyperLiftSet p E) := by
  classical
  have hfin : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : 3 ≤ n + 1 := by omega
  have : Finite (MulAut (primeFormP h (idGram K (n + 1)))) := MulEquiv.finite_left
  set k : Subfield K := fixSubfield σ with hkdef
  set h₀ : UnitaryFieldData ℓ (f / p) k := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  set e := f / p with he
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfe : f = p * e := (Nat.mul_div_cancel' hpf).symm
  have hℓ := h.prime
  have hq₀1 : 1 < ℓ ^ e := h₀.one_lt_pow
  have hqq : ℓ ^ f = (ℓ ^ e) ^ p := by rw [hfe, pow_mul']
  have hpq₀ : p ∣ ℓ ^ e + 1 := by
    have h1 : (((ℓ ^ e) ^ p + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).2 (by rw [← hqq]; exact hpq)
    push_cast at h1
    rw [ZMod.pow_card] at h1
    exact (ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h1)
  have hq₀3 : ℓ ^ e ≠ 3 := by
    intro h3
    rw [h3] at hpq₀
    have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpq₀
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hq₀4 : 4 ≤ ℓ ^ e := by omega
  have hq3 : 3 < ℓ ^ f := by
    rw [hqq]
    calc 3 < ℓ ^ e := by omega
      _ = (ℓ ^ e) ^ 1 := (pow_one _).symm
      _ ≤ (ℓ ^ e) ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hne : ¬(n + 1 = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hC : IsPrimeFormGram (1 : GL (Fin (n + 1)) K) := isPrimeFormGram_one
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ with hfσ
  have hισ : primeFormFieldFactor h hC hN hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hN hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : fσ ∉ primeFormD h (idGram K (n + 1)) := by
    rw [← ker_primeFormFieldFactor h hC hN hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have hBc := card_inf_eq_sq_of_decomp hp hE hcard hσE hσD
    (fun x hx => exists_zpow_mul_mem_primeFormD h hN hne hp hσ hE hx)
  obtain ⟨b₁, hb₁B, hb₁1⟩ : ∃ b ∈ E ⊓ primeFormD h (idGram K (n + 1)), b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E ⊓ primeFormD h (idGram K (n + 1)) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hBc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hb₁ord : orderOf b₁ = p := orderOf_eq_prime (hE.2 _ hb₁B.1) hb₁1
  obtain ⟨b₂, hb₂B, hb₂⟩ : ∃ b ∈ E ⊓ primeFormD h (idGram K (n + 1)),
      b ∉ Subgroup.zpowers b₁ := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ primeFormD h (idGram K (n + 1)) ≤ Subgroup.zpowers b₁ := hcon
    have hfz : Finite (Subgroup.zpowers b₁) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hb₁ord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hBc, Nat.card_zpowers, hb₁ord] at h1
    nlinarith [hp.two_le]
  have hlift₀ : ∀ y ∈ E, y ∈ primeFormD h (idGram K (n + 1)) →
      ∃ x₀ : primeFormUnitary h₀ (idGram k (n + 1)),
        primeFormConjHom h _ (subfieldGU h h₀ hbar (n + 1) x₀) = y := by
    intro y hyE hyD
    obtain ⟨x, hxy, hxσ⟩ := hlift y hyE hyD
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed (n := n + 1) hxσ
    have hg₀U : g₀ ∈ primeFormUnitary h₀ (idGram k (n + 1)) :=
      mem_primeFormUnitary_of_subfieldGL h h₀ hbar (n + 1) (by rw [hg₀]; exact x.2)
    refine ⟨⟨g₀, hg₀U⟩, ?_⟩
    have hx : subfieldGU h h₀ hbar (n + 1) ⟨g₀, hg₀U⟩ = x := Subtype.ext hg₀
    rw [hx, hxy]
  set ψ : primeFormUnitary h₀ (idGram k (n + 1)) →* MulAut (primeFormP h (idGram K (n + 1))) :=
    (primeFormConjHom h (idGram K (n + 1))).comp (subfieldGU h h₀ hbar (n + 1)) with hψ
  set G := E.comap ψ with hG
  have hσfix : ∀ x₀ : primeFormUnitary h₀ (idGram k (n + 1)),
      glAut σ ((subfieldGU h h₀ hbar (n + 1) x₀ : primeFormUnitary h (idGram K (n + 1))) :
        GL (Fin (n + 1)) K) = (subfieldGU h h₀ hbar (n + 1) x₀ : GL (Fin (n + 1)) K) :=
    fun x₀ => glAut_subfieldGL σ (n + 1) x₀
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    apply subfieldGU_injective h h₀ hbar (n + 1)
    rw [map_mul, map_mul]
    exact hcomm _ _ (hσfix x) (hσfix y) hx hy
  have hGpow : ∀ x ∈ G, x ^ (ℓ ^ e + 1) = 1 := by
    intro x hx
    apply subfieldGU_injective h h₀ hbar (n + 1)
    rw [map_pow, map_one]
    exact hpow _ (hσfix x) hx
  have hfink : Finite k := h₀.finite
  have hdvd : ℓ ^ e + 1 ∣ Nat.card k - 1 := by
    have h1 : Nat.card k - 1 = (ℓ ^ e - 1) * (ℓ ^ e + 1) := by
      rw [h₀.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ e) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvd
  haveI : NeZero (ℓ ^ e + 1) := ⟨by omega⟩
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h₀ hζ₀ dvd_rfl G hGcomm hGpow
  set Pg : GL (Fin (n + 1)) k := (P₀ : GL (Fin (n + 1)) k) with hPg
  let Dg : primeFormUnitary h₀ (idGram k (n + 1)) → GL (Fin (n + 1)) k := fun x =>
    Pg⁻¹ * (x : GL (Fin (n + 1)) k) * Pg
  have hdiag : ∀ x : G,
      ((Dg x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).IsDiag :=
    fun x => hP₀ x x.2
  have hDmul : ∀ x y : primeFormUnitary h₀ (idGram k (n + 1)), Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → G →* k := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hχ : ∀ (x : G) (c : Fin (n + 1)),
      χ c x = ((Dg x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c c :=
    fun _ _ => rfl
  have hnz : ∀ (x : G) (c : Fin (n + 1)), χ c x ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hscal : ∀ x : G, ψ x = 1 → ∀ a b : Fin (n + 1), χ a x = χ b x := by
    intro x hx a b
    have h1 := (primeFormConjHom_eq_one_iff (h := h) hN hq3 (subfieldGU h h₀ hbar (n + 1) x)).1 hx
    obtain ⟨c, -, hc⟩ := h1
    have h2 : subfieldGL k (n + 1) (Dg x) = GeneralLinearGroup.scalar (Fin (n + 1)) c := by
      have hx' : subfieldGL k (n + 1) ((x : primeFormUnitary h₀ (idGram k (n + 1))) :
          GL (Fin (n + 1)) k) = GeneralLinearGroup.scalar (Fin (n + 1)) c := hc
      simp only [Dg, map_mul, map_inv, hx']
      rw [(commute_scalar c (subfieldGL k (n + 1) Pg)⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
    have ha := congrArg
      (fun g : GL (Fin (n + 1)) K => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) a a) h2
    have hb := congrArg
      (fun g : GL (Fin (n + 1)) K => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) b b) h2
    simp only [coe_subfieldGL, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
      Matrix.map_apply] at ha hb
    exact Subtype.val_injective (ha.trans hb.symm)
  have hgood : ∀ i : Fin n, ∃ x : G, ψ x ≠ 1 ∧ χ i.castSucc x = χ i.succ x := by
    intro i
    obtain ⟨x₁, hx₁⟩ := hlift₀ b₁ hb₁B.1 hb₁B.2
    obtain ⟨x₂, hx₂⟩ := hlift₀ b₂ hb₂B.1 hb₂B.2
    have hx₁G : x₁ ∈ G := show ψ x₁ ∈ E by rw [hψ, MonoidHom.comp_apply, hx₁]; exact hb₁B.1
    have hx₂G : x₂ ∈ G := show ψ x₂ ∈ E by rw [hψ, MonoidHom.comp_apply, hx₂]; exact hb₂B.1
    have hψ₁ : ψ (⟨x₁, hx₁G⟩ : G) = b₁ := hx₁
    have hψ₂ : ψ (⟨x₂, hx₂G⟩ : G) = b₂ := hx₂
    set ρ : G →* kˣ := (χ i.castSucc).toHomUnits / (χ i.succ).toHomUnits with hρ
    have hρ1 : ∀ x : G, (ρ x : k) = 1 → χ i.castSucc x = χ i.succ x := fun x hx =>
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
        (χ i.castSucc) (χ i.succ) x).1 (Units.ext hx)
    have hρp : ∀ x : G, ψ x ^ p = 1 → (ρ x : k) ^ p = 1 := by
      intro x hx
      rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have h1 : ψ (x ^ p : G) = 1 := by rw [Subgroup.coe_pow, map_pow]; exact hx
      have h2 :=
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
          (χ i.castSucc) (χ i.succ) (x ^ p)).2
        (hscal _ h1 i.castSucc i.succ)
      rw [h2, Units.val_one]
    have h1p : ψ (⟨x₁, hx₁G⟩ : G) ^ p = 1 := by rw [hψ₁]; exact hE.2 _ hb₁B.1
    have h2p : ψ (⟨x₂, hx₂G⟩ : G) ^ p = 1 := by rw [hψ₂]; exact hE.2 _ hb₂B.1
    rcases eq_one_or_exists_pow_mul_eq_one hp (hρp _ h1p) (hρp _ h2p) with h1 | ⟨a, ha⟩
    · exact ⟨⟨x₁, hx₁G⟩, by rw [hψ₁]; exact hb₁1, hρ1 _ h1⟩
    · refine ⟨⟨x₁, hx₁G⟩ ^ a * ⟨x₂, hx₂G⟩, ?_, hρ1 _ ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow]
        change ψ (⟨x₁, hx₁G⟩ : G) ^ a * ψ (⟨x₂, hx₂G⟩ : G) ≠ 1
        rw [hψ₁, hψ₂]
        intro h12
        apply hb₂
        have : b₂ = (b₁ ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h12
        rw [this, ← zpow_natCast, ← _root_.zpow_neg]
        exact Subgroup.zpow_mem_zpowers _ _
      · rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
        exact ha
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP k ℓ := h₀.charP
  haveI : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ e) k) :=
    CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two h₀.card_eq_sq hq₀4
  let ε₂ : Su k ℓ e 2 ≃* CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ e) k :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h₀.card_eq_sq 2)
  haveI : Group.IsPerfect (Su k ℓ e 2) :=
    Group.IsPerfect.ofSurjective (f := ε₂.symm.toMonoidHom) ε₂.symm.surjective
  let ε₀ : Su k ℓ e (n + 1) ≃* unitarySU ℓ e k (n + 1) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h₀.card_eq_sq (n + 1))
  let incl : unitarySU ℓ e k (n + 1) →*
      gramSU h₀ ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h₀ (n + 1)))
  have hincl : Function.Surjective incl := by
    intro y
    refine ⟨⟨(y : GL (Fin (n + 1)) k), ?_⟩, rfl⟩
    rw [unitarySU_eq_gramSU h₀ (n + 1)]
    exact y.2
  set Q := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K)) (n + 1)) with hQ
  let R : Su k ℓ e (n + 1) →*
      gramSU h₀ ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    incl.comp ((conjSU h₀ P₀).toMonoidHom.comp ε₀.toMonoidHom)
  have hR : Function.Surjective R :=
    hincl.comp ((conjSU h₀ P₀).surjective.comp ε₀.surjective)
  let Γ : Su k ℓ e (n + 1) →* primeFormP h (idGram K (n + 1)) :=
    Q.comp ((subfieldSU h h₀ hbar (n + 1)).comp R)
  have hΓ : (suSub h h₀ hbar (n + 1)).map Q = Γ.range := by
    show ((subfieldSU h h₀ hbar (n + 1)).range).map Q =
      (Q.comp ((subfieldSU h h₀ hbar (n + 1)).comp R)).range
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_map R,
      Subgroup.map_top_of_surjective R hR, MonoidHom.range_eq_map]
  have hblock : ∀ i : Fin n, (Γ.comp (blockEmb2 k ℓ e n i)).range ≤
      Subgroup.closure (hyperLiftSet p E) := by
    intro i
    obtain ⟨x, hxψ, hxχ⟩ := hgood i
    have hbE : ψ x ∈ E := x.2
    have hbD : ψ x ∈ primeFormD h (idGram K (n + 1)) := ⟨_, rfl⟩
    have hσb : fσ ∉ Subgroup.zpowers (ψ x) := fun h' => hσD ((Subgroup.zpowers_le.2 hbD) h')
    have hrel := (relIndex_closure_pair_of_indep hp hE hcard hbE hσE hxψ hσb).2
    have hdD : ((Dg x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        Matrix.diagonal (fun c => χ c x) := ((hdiag x).diagonal_diag).symm
    refine range_le_closure_hyperLiftSet_of_perfect _ (closure_pair_le hbE hσE) hrel fun g => ?_
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    have hYc : ((R (blockEmb2 k ℓ e n i g) : gramSU h₀ _) : GL (Fin (n + 1)) k) =
        Pg * blockGL (n + 1) (i : ℕ) (by omega) (g : GL (Fin 2) k) * Pg⁻¹ := rfl
    have hcomm' := commute_conj_blockGL Pg ((x : primeFormUnitary h₀ (idGram k (n + 1))) :
      GL (Fin (n + 1)) k) i (by omega) (fun c => χ c x) (hnz x) hdD hxχ (g : GL (Fin 2) k)
    rintro φ (rfl | rfl)
    · exact primeFormConjHom_subfieldGU_mk_eq h h₀ hbar (x : primeFormUnitary h₀ _)
        (R (blockEmb2 k ℓ e n i g)) (by rw [hYc]; exact hcomm')
    · exact range_subfieldPSU_le h (n + 1) h₀ hbar
        ⟨((R (blockEmb2 k ℓ e n i g) : gramSU h₀ _) : primeFormP h₀ _), rfl⟩
  rw [hΓ, MonoidHom.range_eq_map, ← iSup_range_blockEmb2 h₀.card_eq_sq hq₀ n, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  rw [← MonoidHom.range_comp]
  exact hblock i

theorem map_congr_map_congr_inv {P : Type*} [Group P] (τ : MulAut P) (E : Subgroup (MulAut P)) :
    (E.map (MulAut.congr τ⁻¹).toMonoidHom).map (MulAut.congr τ).toMonoidHom = E :=
  map_congr_symm_map_congr τ⁻¹ E

theorem closure_hyperLiftSet_eq_top_of_split
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 2 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hq₀ : ℓ ^ (f / p) ≠ 2)
    {E : Subgroup (MulAut (primeFormP h (idGram K (n + 1))))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ ∈ E)
    (hlift : ∀ y ∈ E, y ∈ primeFormD h (idGram K (n + 1)) →
      ∃ x : primeFormUnitary h (idGram K (n + 1)), primeFormConjHom h _ x = y ∧
        glAut σ (x : GL (Fin (n + 1)) K) = x)
    (hcomm : ∀ x y : primeFormUnitary h (idGram K (n + 1)),
      glAut σ (x : GL (Fin (n + 1)) K) = x → glAut σ (y : GL (Fin (n + 1)) K) = y →
      primeFormConjHom h _ x ∈ E → primeFormConjHom h _ y ∈ E → x * y = y * x)
    (hpow : ∀ x : primeFormUnitary h (idGram K (n + 1)), glAut σ (x : GL (Fin (n + 1)) K) = x →
      primeFormConjHom h _ x ∈ E → x ^ (ℓ ^ (f / p) + 1) = 1) :
    Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  have hfin : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : 3 ≤ n + 1 := by omega
  have : Finite (MulAut (primeFormP h (idGram K (n + 1)))) := MulEquiv.finite_left
  have hC : IsPrimeFormGram (1 : GL (Fin (n + 1)) K) := isPrimeFormGram_one
  set κ := primeFormConjHom h (idGram K (n + 1)) with hκ
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ with hfσ
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hℓ := h.prime
  have hq₀1 : 1 < ℓ ^ (f / p) := h₀.one_lt_pow
  have hqq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [hfeq, pow_mul', Nat.mul_div_cancel_left _ hp.pos]
  have hq3 : 3 < ℓ ^ f := by
    rw [hqq]
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ (ℓ ^ (f / p)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (ℓ ^ (f / p)) ^ p := Nat.pow_le_pow_right (by omega) hp.two_le
  have hne : ¬(n + 1 = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hq₀' : ¬(n + 1 = 3 ∧ ℓ ^ (f / p) = 2) := fun h' => hq₀ h'.2
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hισ : primeFormFieldFactor h hC hN hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hN hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : fσ ∉ primeFormD h (idGram K (n + 1)) := by
    rw [← ker_primeFormFieldFactor h hC hN hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have h1 := map_suSub_le_closure_hyperLiftSet h hn hp hp2 hpq hσ hq₀ hE hcard hσE hlift hcomm
    hpow
  have hBc := card_inf_eq_sq_of_decomp hp hE hcard hσE hσD
    (fun x hx => exists_zpow_mul_mem_primeFormD h hN hne hp hσ hE hx)
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ E ⊓ primeFormD h (idGram K (n + 1)), b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E ⊓ primeFormD h (idGram K (n + 1)) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hBc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨w, hwb, hwσ⟩ := hlift b hbB.1 hbB.2
  have hιb : primeFormFieldFactor h hC hN hne b = 1 := by
    rw [← MonoidHom.mem_ker, ker_primeFormFieldFactor]
    exact hbB.2
  have hbσE : b * fσ ∈ E := E.mul_mem hbB.1 hσE
  have hbσι : primeFormFieldFactor h hC hN hne (b * fσ) = σ := by
    rw [map_mul, hιb, one_mul, hισ]
  have hbσ1 : b * fσ ≠ 1 := fun h1 => hσ1 (by rw [← hbσι, h1, map_one])
  have hbσord : orderOf (b * fσ) = p := orderOf_eq_prime (hE.2 _ hbσE) hbσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hN hne hp hp2 hpℓ
      (b * fσ) hbσord σ hbσι hσ
  have hconj : (b * fσ) * κ M = κ M * fσ := by
    calc (b * fσ) * κ M = κ M * ((κ M)⁻¹ * (b * fσ) * κ M) := by group
      _ = κ M * fσ := by rw [hM]
  set Mσ : primeFormUnitary h (idGram K (n + 1)) := primeFormFieldU h hC σ M with hMσ
  have hfield : fσ * κ M * fσ⁻¹ = κ Mσ := primeFormField_conj_eq h hC σ M
  have hfM : fσ * κ M = κ Mσ * fσ := by
    rw [← hfield]
    group
  have hκ1 : κ (M⁻¹ * w * Mσ) = 1 := by
    have h2 : κ w * κ Mσ * fσ = κ M * fσ := by
      rw [mul_assoc, ← hfM, ← mul_assoc, hwb, hconj]
    have h3 : κ w * κ Mσ = κ M := mul_right_cancel h2
    rw [map_mul, map_mul, map_inv, mul_assoc, h3, inv_mul_cancel]
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (h := h) hN hq3 _).1 hκ1
  have hMσc : ((Mσ : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
      (w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c := by
    have h2 : (M : GL (Fin (n + 1)) K)⁻¹ * (w : GL (Fin (n + 1)) K) *
        (Mσ : GL (Fin (n + 1)) K) = GeneralLinearGroup.scalar (Fin (n + 1)) c := hc
    rw [← h2]
    group
  have hglM : glAut σ (M : GL (Fin (n + 1)) K) =
      (w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c := hMσc
  have hwcomm : ∀ x : primeFormUnitary h (idGram K (n + 1)), κ x ∈ E →
      κ x ∈ primeFormD h (idGram K (n + 1)) →
      (x : GL (Fin (n + 1)) K) * (w : GL (Fin (n + 1)) K) =
        (w : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) := by
    intro x hxE hxD
    obtain ⟨z, hzx, hzσ⟩ := hlift (κ x) hxE hxD
    have hz1 : κ (z⁻¹ * x) = 1 := by rw [map_mul, map_inv, hzx, inv_mul_cancel]
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff (h := h) hN hq3 _).1 hz1
    have hxz : (x : GL (Fin (n + 1)) K) = z * GeneralLinearGroup.scalar (Fin (n + 1)) d := by
      have h2 : (z : GL (Fin (n + 1)) K)⁻¹ * x = GeneralLinearGroup.scalar (Fin (n + 1)) d := hd
      rw [← h2]
      group
    have hzw : (z : GL (Fin (n + 1)) K) * (w : GL (Fin (n + 1)) K) =
        (w : GL (Fin (n + 1)) K) * (z : GL (Fin (n + 1)) K) :=
      congrArg Subtype.val (hcomm z w hzσ hwσ (by rw [hzx]; exact hxE) (by rw [hwb]; exact hbB.1))
    rw [hxz, mul_assoc, (commute_scalar d (w : GL (Fin (n + 1)) K)).eq.symm, ← mul_assoc, hzw,
      mul_assoc]
  have hfixconj : ∀ x : primeFormUnitary h (idGram K (n + 1)),
      glAut σ (x : GL (Fin (n + 1)) K) = x →
      (x : GL (Fin (n + 1)) K) * (w : GL (Fin (n + 1)) K) =
        (w : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) →
      glAut σ ((M : GL (Fin (n + 1)) K)⁻¹ * (x : GL (Fin (n + 1)) K) * (M : GL (Fin (n + 1)) K)) =
        (M : GL (Fin (n + 1)) K)⁻¹ * (x : GL (Fin (n + 1)) K) * (M : GL (Fin (n + 1)) K) := by
    intro x hxσ hxw
    rw [map_mul, map_mul, map_inv, hxσ, hglM]
    have hsc : ∀ g : GL (Fin (n + 1)) K, GeneralLinearGroup.scalar (Fin (n + 1)) c * g =
        g * GeneralLinearGroup.scalar (Fin (n + 1)) c := fun g => (commute_scalar c g).eq.symm
    calc ((w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c)⁻¹ * x *
          ((w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c)
        = (GeneralLinearGroup.scalar (Fin (n + 1)) c)⁻¹ * ((M : GL (Fin (n + 1)) K)⁻¹ *
            ((w : GL (Fin (n + 1)) K) * x * (w : GL (Fin (n + 1)) K)⁻¹) * M) *
            GeneralLinearGroup.scalar (Fin (n + 1)) c := by group
      _ = (GeneralLinearGroup.scalar (Fin (n + 1)) c)⁻¹ * ((M : GL (Fin (n + 1)) K)⁻¹ * x * M) *
            GeneralLinearGroup.scalar (Fin (n + 1)) c := by
          rw [← hxw, mul_inv_cancel_right]
      _ = (M : GL (Fin (n + 1)) K)⁻¹ * x * M := by
          rw [mul_assoc, ← hsc, ← mul_assoc, inv_mul_cancel, one_mul]
  set E'' := E.map (MulAut.congr (κ M)⁻¹).toMonoidHom with hE''def
  have hcongr : ∀ φ : MulAut (primeFormP h (idGram K (n + 1))),
      MulAut.congr (κ M)⁻¹ φ = (κ M)⁻¹ * φ * κ M := fun φ => by
    ext y
    rfl
  have hσE'' : fσ ∈ E'' := by
    refine ⟨b * fσ, hbσE, ?_⟩
    change MulAut.congr (κ M)⁻¹ (b * fσ) = fσ
    rw [hcongr]
    exact hM
  have hE''a : IsElemAbelian p E'' := isElemAbelian_map_congr _ hE
  have hE''c : Nat.card E'' = p ^ 3 := (card_map_congr _ E).trans hcard
  have hmemE'' : ∀ x : primeFormUnitary h (idGram K (n + 1)), κ x ∈ E'' →
      κ (M * x * M⁻¹) ∈ E := by
    intro x hx
    obtain ⟨y, hyE, hyx⟩ := hx
    have h2 : (κ M)⁻¹ * y * κ M = κ x := by rw [← hcongr]; exact hyx
    have h3 : y = κ (M * x * M⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← h2]
      group
    rw [← h3]
    exact hyE
  have hDconj : ∀ x : primeFormUnitary h (idGram K (n + 1)),
      κ (M * x * M⁻¹) ∈ primeFormD h (idGram K (n + 1)) := fun x => ⟨_, rfl⟩
  have hlift'' : ∀ y ∈ E'', y ∈ primeFormD h (idGram K (n + 1)) →
      ∃ x : primeFormUnitary h (idGram K (n + 1)), κ x = y ∧
        glAut σ (x : GL (Fin (n + 1)) K) = x := by
    intro y hyE'' hyD
    obtain ⟨x', rfl⟩ := hyD
    have hx'E := hmemE'' x' hyE''
    obtain ⟨z, hzx, hzσ⟩ := hlift _ hx'E (hDconj x')
    refine ⟨M⁻¹ * z * M, ?_, ?_⟩
    · change κ (M⁻¹ * z * M) = κ x'
      rw [map_mul, map_mul, map_inv, hzx, map_mul, map_mul, map_inv]
      group
    · have := hfixconj z hzσ (hwcomm z (by rw [hzx]; exact hx'E) (by rw [hzx]; exact hDconj x'))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hσconj : ∀ x : primeFormUnitary h (idGram K (n + 1)), glAut σ (x : GL (Fin (n + 1)) K) = x →
      κ x ∈ E'' → glAut σ ((M * x * M⁻¹ : primeFormUnitary h (idGram K (n + 1))) :
        GL (Fin (n + 1)) K) = (M * x * M⁻¹ : primeFormUnitary h (idGram K (n + 1))) := by
    intro x hxσ hx
    have hxw := hwcomm (M * x * M⁻¹) (hmemE'' x hx) (hDconj x)
    change (M : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) * (M : GL (Fin (n + 1)) K)⁻¹ *
        (w : GL (Fin (n + 1)) K) =
      (w : GL (Fin (n + 1)) K) * ((M : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) *
        (M : GL (Fin (n + 1)) K)⁻¹) at hxw
    change glAut σ ((M : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) *
        (M : GL (Fin (n + 1)) K)⁻¹) =
      (M : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) * (M : GL (Fin (n + 1)) K)⁻¹
    rw [map_mul, map_mul, map_inv, hxσ, hglM]
    have hsc : GeneralLinearGroup.scalar (Fin (n + 1)) c * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * GeneralLinearGroup.scalar (Fin (n + 1)) c :=
      (commute_scalar c _).eq.symm
    calc (w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c * x *
          ((w : GL (Fin (n + 1)) K)⁻¹ * M * GeneralLinearGroup.scalar (Fin (n + 1)) c)⁻¹
        = (w : GL (Fin (n + 1)) K)⁻¹ * ((M : GL (Fin (n + 1)) K) *
            (GeneralLinearGroup.scalar (Fin (n + 1)) c * x) *
            (GeneralLinearGroup.scalar (Fin (n + 1)) c)⁻¹ * (M : GL (Fin (n + 1)) K)⁻¹) *
            w := by group
      _ = (w : GL (Fin (n + 1)) K)⁻¹ * ((M : GL (Fin (n + 1)) K) * x *
            (M : GL (Fin (n + 1)) K)⁻¹ * w) := by
          rw [hsc]
          group
      _ = (M : GL (Fin (n + 1)) K) * x * (M : GL (Fin (n + 1)) K)⁻¹ := by
          rw [hxw]
          group
  have hcomm'' : ∀ x y : primeFormUnitary h (idGram K (n + 1)),
      glAut σ (x : GL (Fin (n + 1)) K) = x → glAut σ (y : GL (Fin (n + 1)) K) = y →
      κ x ∈ E'' → κ y ∈ E'' → x * y = y * x := by
    intro x y hxσ hyσ hx hy
    have h2 := hcomm (M * x * M⁻¹) (M * y * M⁻¹) (hσconj x hxσ hx) (hσconj y hyσ hy)
      (hmemE'' x hx) (hmemE'' y hy)
    have h3 : M * (x * y) * M⁻¹ = M * (y * x) * M⁻¹ := by
      calc M * (x * y) * M⁻¹ = (M * x * M⁻¹) * (M * y * M⁻¹) := by group
        _ = (M * y * M⁻¹) * (M * x * M⁻¹) := h2
        _ = M * (y * x) * M⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  have hpow'' : ∀ x : primeFormUnitary h (idGram K (n + 1)), glAut σ (x : GL (Fin (n + 1)) K) = x →
      κ x ∈ E'' → x ^ (ℓ ^ (f / p) + 1) = 1 := by
    intro x hxσ hx
    have h2 := hpow (M * x * M⁻¹) (hσconj x hxσ hx) (hmemE'' x hx)
    rw [conj_pow] at h2
    have h3 : x ^ (ℓ ^ (f / p) + 1) = M⁻¹ * (M * x ^ (ℓ ^ (f / p) + 1) * M⁻¹) * M := by group
    rw [h3, h2]
    group
  have h2 := map_suSub_le_closure_hyperLiftSet h hn hp hp2 hpq hσ hq₀ hE''a hE''c hσE'' hlift''
    hcomm'' hpow''
  set Q := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K)) (n + 1)) with hQ
  have hFmk : (subfieldPSU h h₀ hbar (n + 1)).range = (suSub h h₀ hbar (n + 1)).map Q :=
    range_subfieldPSU_eq_map h h₀ hbar (n + 1)
  have hfixF : ∀ x ∈ (subfieldPSU h h₀ hbar (n + 1)).range, fσ x = x := fun x hx =>
    range_subfieldPSU_le h (n + 1) h₀ hbar hx
  have hne' : (suSub h h₀ hbar (n + 1)).map (primeFormConjSU h _ M).toMonoidHom ≠
      suSub h h₀ hbar (n + 1) := by
    intro heq
    have hFmap : ((subfieldPSU h h₀ hbar (n + 1)).range).map (κ M).toMonoidHom =
        (subfieldPSU h h₀ hbar (n + 1)).range := by
      rw [hFmk, map_primeFormConjHom_map_mk h h₀ hbar (n + 1) M, heq]
    have hfix' : ∀ x ∈ (subfieldPSU h h₀ hbar (n + 1)).range, (b * fσ) x = x := by
      intro x hx
      have hx' : x ∈ ((subfieldPSU h h₀ hbar (n + 1)).range).map (κ M).toMonoidHom := by
        rw [hFmap]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      change (b * fσ) (κ M y) = κ M y
      rw [show (b * fσ) (κ M y) = (b * fσ * κ M) y from rfl, hconj, MulAut.mul_apply,
        hfixF y hy]
    have hβ : ∀ x ∈ (subfieldPSU h h₀ hbar (n + 1)).range, b x = x := by
      intro x hx
      have h3 : (b * fσ) x = b (fσ x) := rfl
      rw [hfixF x hx] at h3
      rw [← h3]
      exact hfix' x hx
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h (n + 1) h₀ hbar hN hne hq₀' b hβ
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hN hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply hb1
    rw [hτ, hτ1, map_one]
  have hgen := subfieldPairSUOdd_of_ne_two ℓ f (f / p) K h (fixSubfield σ) h₀ hbar p hp hp2 hfeq
    hq₀ (n + 1) hN M hne'
  have htrans : (Subgroup.closure (hyperLiftSet p E'')).map (κ M).toMonoidHom ≤
      Subgroup.closure (hyperLiftSet p E) := by
    have h3 := map_closure_hyperLiftSet_le (κ M) p E''
    rwa [hE''def, map_congr_map_congr_inv] at h3
  have hcomap : (Subgroup.closure (hyperLiftSet p E)).comap Q = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (hg | ⟨g, hg, rfl⟩)
    · exact h1 ⟨g, hg, rfl⟩
    · have h3 : κ M (Q g) ∈ Subgroup.closure (hyperLiftSet p E) :=
        htrans ⟨Q g, h2 ⟨g, hg, rfl⟩, rfl⟩
      have hQg : Q ((primeFormConjSU h _ M).toMonoidHom g) = κ M (Q g) :=
        (primeFormConjHom_mk h _ M g).symm
      show Q ((primeFormConjSU h _ M).toMonoidHom g) ∈ Subgroup.closure (hyperLiftSet p E)
      rw [hQg]
      exact h3
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hg : g ∈ (Subgroup.closure (hyperLiftSet p E)).comap Q := by
    rw [hcomap]
    exact Subgroup.mem_top g
  exact hg

end Split

section ArithU

theorem mul_add_one_lt_pow_add_one {p q : ℕ} (hq : 3 ≤ q) (hp : 3 ≤ p) :
    p * (q + 1) < q ^ p + 1 := by
  induction p, hp using Nat.le_induction with
  | base => nlinarith [pow_succ q 2]
  | succ p hp ih =>
    have h1 : q + 1 ≤ q ^ p := by
      calc q + 1 ≤ q ^ 2 := by nlinarith
        _ ≤ q ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ]
    nlinarith

theorem exists_prime_dvd_pow_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 3 ≤ q)
    (hpq : p ∣ q + 1) :
    p * (q + 1) ∣ q ^ p + 1 ∧ ∃ r : ℕ, r.Prime ∧ r ∣ q ^ p + 1 ∧ ¬ r ∣ q + 1 ∧ r ≠ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ : q + 1 ∣ q ^ p + 1 := by simpa using hodd.nat_add_dvd_pow_add_pow q 1
  have hmZ : (m : ℤ) = ∑ i ∈ Finset.range p, (-(q : ℤ)) ^ i := by
    have h1 : (∑ i ∈ Finset.range p, (-(q : ℤ)) ^ i) * (-(q : ℤ) - 1) = (-(q : ℤ)) ^ p - 1 :=
      geom_sum_mul _ _
    have h2 : (-(q : ℤ)) ^ p = -(q : ℤ) ^ p := Odd.neg_pow hodd _
    have h3 : ((q : ℤ) ^ p + 1) = ((q : ℤ) + 1) * m := by exact_mod_cast hm
    have hq1 : ((q : ℤ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hq1
    linear_combination -h3 + h1 + h2
  have hmod : ∀ r : ℕ, r ∣ q + 1 → (m : ZMod r) = p := by
    intro r hr
    have h1 : (q : ZMod r) = -1 := by
      have h0 : ((q + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hr
      push_cast at h0
      linear_combination h0
    have h2 := congrArg (Int.cast : ℤ → ZMod r) hmZ
    push_cast at h2
    rw [h2, h1]
    simp
  have hpm : p ∣ m := by
    have h1 := hmod p hpq
    rw [ZMod.natCast_self] at h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 h1
  refine ⟨?_, ?_⟩
  · rw [hm, mul_comm p]
    exact Nat.mul_dvd_mul_left _ hpm
  have hpq0 : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ q + 1 - q := Nat.dvd_sub hpq h
    rw [show q + 1 - q = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hval : padicValNat p (q ^ p + 1) = padicValNat p (q + 1) + 1 := by
    have h1 := padicValNat.pow_add_pow (x := q) (y := 1) (p := p) hodd (by simpa using hpq) hpq0
      hodd
    simpa [padicValNat_self] using h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hvm : padicValNat p m = 1 := by
    rw [hm, padicValNat.mul (by omega) hm0] at hval
    omega
  obtain ⟨m', hm'⟩ := hpm
  have hpm' : ¬ p ∣ m' := by
    rintro ⟨m'', rfl⟩
    have h1 : p ^ 2 ∣ m := ⟨m'', by rw [hm']; ring⟩
    have h2 := (padicValNat_dvd_iff_le hm0).1 h1
    omega
  have hlt := mul_add_one_lt_pow_add_one hq (three_le_of_odd_prime hp hodd)
  have hm'1 : m' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm'
    rw [hm, hm', mul_comm] at hlt
    omega
  have hm'm : m' ∣ q ^ p + 1 := by
    rw [hm, hm']
    exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  refine ⟨m'.minFac, Nat.minFac_prime hm'1, (Nat.minFac_dvd m').trans hm'm, ?_, ?_⟩
  · intro hr
    have h1 := hmod _ hr
    have h2 : (m : ZMod m'.minFac) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, hm']
      exact Dvd.dvd.mul_left (Nat.minFac_dvd m') _
    rw [h2, eq_comm, ZMod.natCast_eq_zero_iff] at h1
    have h3 : m'.minFac = p := (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime hm'1) hp).1 h1
    exact hpm' (h3 ▸ Nat.minFac_dvd m')
  · intro h
    exact hpm' (h ▸ Nat.minFac_dvd m')

theorem exists_pow_eq_of_norm_one {K : Type} [Field K] [Finite K] {p q₀ : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq₀ : 3 ≤ q₀) (hpq : p ∣ q₀ + 1)
    (hK : q₀ ^ p + 1 ∣ Nat.card K - 1) {y : K} (hy : y ^ (q₀ + 1) = 1) :
    ∃ c : K, c ^ p = y ∧ c ^ (q₀ ^ p + 1) = 1 := by
  obtain ⟨hdvd, -⟩ := exists_prime_dvd_pow_add_one hp hp2 hq₀ hpq
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hK
  have hq1 : q₀ + 1 ∣ q₀ ^ p + 1 := (Dvd.intro_left _ rfl).trans hdvd
  have hy1 : y ^ (q₀ ^ p + 1) = 1 := by
    obtain ⟨a, ha⟩ := hq1
    rw [ha, pow_mul, hy, one_pow]
  obtain ⟨a, -, ha⟩ := hω.eq_pow_of_pow_eq_one hy1
  obtain ⟨N, hN⟩ := hdvd
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have hyN : y ^ ((q₀ + 1) * N) = 1 := by rw [pow_mul, hy, one_pow]
  have hdiv : q₀ ^ p + 1 ∣ a * ((q₀ + 1) * N) := by
    apply hω.dvd_of_pow_eq_one
    rw [pow_mul, ha, hyN]
  rw [hN, show p * (q₀ + 1) * N = p * ((q₀ + 1) * N) by ring] at hdiv
  have hpa : p ∣ a := by
    have hpos : 0 < (q₀ + 1) * N := by positivity
    rw [show a * ((q₀ + 1) * N) = a * ((q₀ + 1) * N) from rfl] at hdiv
    exact (Nat.mul_dvd_mul_iff_right hpos).1 hdiv
  obtain ⟨b, rfl⟩ := hpa
  refine ⟨ω ^ b, by rw [← pow_mul, mul_comm, ha], ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

end ArithU

section StdU

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2 (relIndex_closure_pair_of_indep)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem mk_eq_mk_of_eq_scalar_mul (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {g g' : gramSU h (idGram K n)} {c : Kˣ} (hcN : h.norm (c : K) = 1) (hcn : c ^ n = 1)
    (hgg : (g' : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * g) :
    (g' : primeFormP h (idGram K n)) = (g : primeFormP h (idGram K n)) := by
  rw [QuotientGroup.eq]
  refine ⟨c⁻¹, ?_, by rw [inv_pow, hcn, inv_one], ?_⟩
  · rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hcN, inv_one]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, hgg, _root_.mul_inv_rev, mul_assoc, ← map_inv,
      (commute_scalar c⁻¹ (g : GL (Fin n) K)).eq.symm, inv_mul_cancel_left]

theorem heisShiftMat_map (φ : K →+* K) (p : ℕ) : (heisShiftMat K p).map φ = heisShiftMat K p := by
  ext i j
  rw [Matrix.map_apply, heisShiftMat_entry]
  split_ifs <;> simp

@[expose] noncomputable def shiftSU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : Odd p) :
    gramSU h (idGram K p) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisShiftMat K p)
      (by rw [det_heisShiftMat K hp]; exact one_ne_zero), by
    refine mem_gramSU.2 ⟨?_, det_heisShiftMat K hp⟩
    change ((heisShiftMat K p).map h.bar)ᵀ * 1 * heisShiftMat K p = 1
    rw [Matrix.mul_one, heisShiftMat_map, heisShiftMat, Matrix.transpose_permMatrix,
      ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[expose] noncomputable def shiftU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : Odd p) :
    primeFormUnitary h (idGram K p) :=
  ⟨(shiftSU h hp : GL (Fin p) K), ((mem_gramSU_iff_unitary h).1 (shiftSU h hp).2).1⟩

@[expose] noncomputable def diagSU (h : UnitaryFieldData ℓ f K) {p : ℕ} {ζ : K} (hζ : ζ ^ p = 1)
    (hζN : h.bar ζ * ζ = 1) (hp : Odd p) : gramSU h (idGram K p) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisDiagMat (p := p) ζ)
      (by rw [det_heisDiagMat hζ hp]; exact one_ne_zero), by
    refine mem_gramSU.2 ⟨?_, det_heisDiagMat hζ hp⟩
    change ((heisDiagMat (p := p) ζ).map h.bar)ᵀ * 1 * heisDiagMat (p := p) ζ = 1
    rw [Matrix.mul_one, heisDiagMat, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Function.comp_apply, map_pow, ← mul_pow, hζN, one_pow, Pi.one_apply]⟩

@[expose] noncomputable def diagU (h : UnitaryFieldData ℓ f K) {p : ℕ} {ζ : K} (hζ : ζ ^ p = 1)
    (hζN : h.bar ζ * ζ = 1) (hp : Odd p) : primeFormUnitary h (idGram K p) :=
  ⟨(diagSU h hζ hζN hp : GL (Fin p) K), ((mem_gramSU_iff_unitary h).1 (diagSU h hζ hζN hp).2).1⟩

theorem primeFormConjHom_mk_eq_of_conj (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (A : primeFormUnitary h (idGram K n)) (g : gramSU h (idGram K n)) {c : Kˣ}
    (hcN : h.norm (c : K) = 1) (hcn : c ^ n = 1)
    (hAg : (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c * g) :
    primeFormConjHom h (idGram K n) A (g : primeFormP h (idGram K n)) =
      (g : primeFormP h (idGram K n)) := by
  rw [primeFormConjHom_mk]
  exact mk_eq_mk_of_eq_scalar_mul h hcN hcn hAg

theorem primeFormFieldHom_mk_eq (h : UnitaryFieldData ℓ f K) {n : ℕ} (σ : K ≃+* K)
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {c : Kˣ}
    (hcN : h.norm (c : K) = 1) (hcn : c ^ n = 1)
    (hσg : glAut σ (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * g) :
    primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ
        (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  change primeFormFieldAut h isPrimeFormGram_one σ
    (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = _
  rw [primeFormFieldAut_mk]
  exact mk_eq_mk_of_eq_scalar_mul h hcN hcn hσg

theorem bar_map (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (x : K) : h.bar (σ x) = σ (h.bar x) := by
  rw [h.bar_apply, h.bar_apply, map_pow]

theorem mk_diag_mem_closure_hyperLiftSet (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hq3 : 3 < ℓ ^ f) {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {σ : K ≃+* K}
    (hσD : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∉ primeFormD h (idGram K p))
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E)
    (hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 → ∃ c : K, c ^ p = y ∧ h.bar c * c = 1)
    {g : gramSU h (idGram K p)} {s : Fin p → K}
    (hg : ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = diagonal s)
    (hs : ∀ i, σ (s i) = s i) :
    (g : primeFormP h (idGram K p)) ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := h.finite
  have hp3 : 3 ≤ p := three_le_of_odd_prime hp hodd
  obtain ⟨hgU, hgdet⟩ := mem_gramSU.1 g.2
  have hdet : ∏ i, s i = 1 := by
    rw [hg, det_diagonal] at hgdet
    exact hgdet
  have hsN : ∀ i, h.bar (s i) * s i = 1 := by
    intro i
    have h1 : (((diagonal s).map h.bar)ᵀ * diagonal s : Matrix (Fin p) (Fin p) K) = 1 := by
      have h2 := hgU
      rw [hg] at h2
      simpa [idGram] using h2
    have h3 := congrFun (congrFun h1 i) i
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
    exact h3
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i h0
    have h1 := hsN i
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  set s' : ℕ → K := fun j => if hj : j < p then s ⟨j, hj⟩ else 1 with hs'def
  have hs'σ : ∀ j, σ (s' j) = s' j := by
    intro j
    simp only [hs'def]
    split_ifs with hj
    · exact hs _
    · exact map_one σ
  have hs'0 : ∀ j, s' j ≠ 0 := by
    intro j
    simp only [hs'def]
    split_ifs with hj
    · exact hs0 _
    · exact one_ne_zero
  have hs'N : ∀ j, h.bar (s' j) * s' j = 1 := by
    intro j
    simp only [hs'def]
    split_ifs with hj
    · exact hsN _
    · rw [map_one, one_mul]
  have hs'i : ∀ i : Fin p, s' i = s i := fun i => by simp [hs'def, i.isLt]
  set d : Fin p → K := fun i => ∏ j ∈ Finset.range i, (s' j)⁻¹ with hddef
  have hdσ : ∀ i, σ (d i) = d i := fun i => by
    simp only [hddef, map_prod, map_inv₀, hs'σ]
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (hs'0 j)
  have hdN : ∀ i, h.bar (d i) * d i = 1 := fun i => by
    simp only [hddef, map_prod, map_inv₀, ← Finset.prod_mul_distrib, ← mul_inv, hs'N, inv_one,
      Finset.prod_const_one]
  have hdrel : ∀ i : Fin p, d i = s i * d (finRotate p i) := by
    intro i
    by_cases hi : (i : ℕ) + 1 < p
    · have h1 : ((finRotate p i : Fin p) : ℕ) = (i : ℕ) + 1 := by
        rw [finRotate_val_mod, Nat.mod_eq_of_lt hi]
      simp only [hddef, h1, Finset.prod_range_succ, hs'i]
      field_simp [hs0 i]
    · have hip : (i : ℕ) + 1 = p := by have := i.isLt; omega
      have h1 : ((finRotate p i : Fin p) : ℕ) = 0 := by
        rw [finRotate_val_mod, hip, Nat.mod_self]
      have h2 : ∏ j ∈ Finset.range p, s' j = 1 := by
        rw [← Fin.prod_univ_eq_prod_range]
        simpa [hs'i] using hdet
      rw [← hip, Finset.prod_range_succ, hs'i] at h2
      have h3 : d (finRotate p i) = 1 := by
        show ∏ j ∈ Finset.range ((finRotate p i : Fin p) : ℕ), (s' j)⁻¹ = 1
        rw [h1, Finset.prod_range_zero]
      rw [h3, mul_one]
      show ∏ j ∈ Finset.range (i : ℕ), (s' j)⁻¹ = s i
      rw [Finset.prod_inv_distrib]
      exact inv_eq_of_mul_eq_one_right h2
  have hP0 : ∏ i, d i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd0 i
  have hPσ : σ (∏ i, d i)⁻¹ = (∏ i, d i)⁻¹ := by
    rw [map_inv₀, map_prod]
    simp only [hdσ]
  have hPN : h.bar (∏ i, d i)⁻¹ * (∏ i, d i)⁻¹ = 1 := by
    rw [map_inv₀, map_prod, ← mul_inv, ← Finset.prod_mul_distrib]
    simp only [hdN, Finset.prod_const_one, inv_one]
  obtain ⟨c, hcp, hcN⟩ := hroot _ (inv_ne_zero hP0) hPσ hPN
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact inv_ne_zero hP0 hcp.symm
  have htdet : (diagonal fun i => c * d i : Matrix (Fin p) (Fin p) K).det = 1 := by
    rw [det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hcp, inv_mul_cancel₀ hP0]
  let t : gramSU h (idGram K p) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => c * d i)
        (by rw [htdet]; exact one_ne_zero), by
      refine mem_gramSU.2 ⟨?_, htdet⟩
      change ((diagonal fun i => c * d i : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * 1 *
        (diagonal fun i => c * d i) = 1
      rw [Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [map_mul,
        show h.bar c * h.bar (d i) * (c * d i) = (h.bar c * c) * (h.bar (d i) * d i) by ring,
        hcN, hdN, one_mul]⟩
  have htcoe : (((t : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      diagonal fun i => c * d i := rfl
  set S := shiftSU h hodd with hSdef
  have hScoe : (((S : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      heisShiftMat K p := rfl
  have hcomm : t * S = g * (S * t) := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      Units.val_mul, htcoe, hg, hScoe]
    ext i j
    rw [diagonal_mul, diagonal_mul, mul_diagonal, heisShiftMat_entry]
    split_ifs with hij
    · subst hij
      rw [hdrel i]
      ring
    · simp
  have hgcomm : ⁅t, S⁆ = g := by
    rw [commutatorElement_def, hcomm]
    group
  set Du := diagU h hζ.pow_eq_one hζN hodd with hDudef
  have hDucoe : (((Du : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = heisDiagMat ζ := rfl
  have hD1 : primeFormConjHom h _ Du ≠ 1 := by
    intro h1
    obtain ⟨u, -, hu⟩ := (primeFormConjHom_eq_one_iff (h := h) (by omega) hq3 Du).1 h1
    have h0 := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K)
      ⟨0, hp.pos⟩ ⟨0, hp.pos⟩) hu
    have h1' := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K)
      ⟨1, hp.one_lt⟩ ⟨1, hp.one_lt⟩) hu
    simp only [hDucoe, heisDiagMat, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at h0 h1'
    simp only [pow_zero] at h0
    simp only [pow_one] at h1'
    exact hζ.ne_one hp.one_lt (h1'.trans h0.symm)
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ with hfσ
  have hσDu : fσ ∉ Subgroup.zpowers (primeFormConjHom h _ Du) := fun h' =>
    hσD ((Subgroup.zpowers_le.2 (⟨Du, rfl⟩ : primeFormConjHom h _ Du ∈ primeFormD h _)) h')
  have hrel := (relIndex_closure_pair_of_indep hp hE hc hD hσE hD1 hσDu).2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζpow : (Units.mk0 ζ⁻¹ (inv_ne_zero hζ0)) ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow, hζ.pow_eq_one, inv_one, Units.val_one])
  have hζnorm : h.norm ((Units.mk0 ζ⁻¹ (inv_ne_zero hζ0) : Kˣ) : K) = 1 := by
    rw [Units.val_mk0, UnitaryFieldData.norm, map_inv₀, ← mul_inv, mul_comm, hζN, inv_one]
  have htfix : (t : primeFormP h (idGram K p)) ∈ fixedPoints (Subgroup.closure
      ({primeFormConjHom h _ Du, fσ} : Set (MulAut (primeFormP h (idGram K p))))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · refine primeFormConjHom_mk_eq_of_conj h Du t (c := 1) (by simp [UnitaryFieldData.norm])
        (one_pow _) ?_
      rw [map_one, one_mul]
      have hDt : (Du : GL (Fin p) K) * (t : GL (Fin p) K) = (t : GL (Fin p) K) * Du := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hDucoe, htcoe, heisDiagMat, diagonal_mul_diagonal,
          diagonal_mul_diagonal]
        congr 1
        funext i
        ring
      rw [hDt, mul_inv_cancel_right]
    · have hσc0 : σ c / c ≠ 0 := div_ne_zero ((map_ne_zero σ).2 hc0) hc0
      refine primeFormFieldHom_mk_eq h σ t (c := Units.mk0 (σ c / c) hσc0) ?_ ?_ ?_
      · rw [Units.val_mk0, UnitaryFieldData.norm, map_div₀, bar_map h σ c,
          show σ c / c * (σ (h.bar c) / h.bar c) = σ (h.bar c * c) / (h.bar c * c) by
            rw [map_mul]; field_simp [hc0, (map_ne_zero h.bar).2 hc0],
          hcN, map_one, div_one]
      · apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow, ← map_pow, hcp, hPσ, div_self
          (inv_ne_zero hP0), Units.val_one]
      · apply Units.ext
        rw [Units.val_mul, coe_glAut, htcoe, GeneralLinearGroup.coe_scalar, Units.val_mk0,
          Matrix.diagonal_map (map_zero _)]
        rw [Matrix.scalar_apply, diagonal_mul_diagonal]
        congr 1
        funext i
        rw [map_mul, hdσ]
        field_simp
  have hSfix : (S : primeFormP h (idGram K p)) ∈ fixedPoints (Subgroup.closure
      ({primeFormConjHom h _ Du, fσ} : Set (MulAut (primeFormP h (idGram K p))))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · refine primeFormConjHom_mk_eq_of_conj h Du S hζnorm hζpow ?_
      have h1 : heisDiagMat ζ * heisShiftMat K p = ζ⁻¹ • (heisShiftMat K p * heisDiagMat ζ) :=
        heisDiagMat_mul_heisShiftMat ζ hζ.pow_eq_one
      apply Units.ext
      have hDD : heisDiagMat ζ * (((Du : GL (Fin p) K)⁻¹ : GL (Fin p) K) :
          Matrix (Fin p) (Fin p) K) = 1 := by
        rw [← hDucoe, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hDucoe, hScoe, h1,
        GeneralLinearGroup.coe_scalar,
        Units.val_mk0, Matrix.smul_mul, Matrix.mul_assoc, hDD, Matrix.mul_one, Matrix.scalar_apply,
        Matrix.smul_eq_diagonal_mul]
    · refine primeFormFieldHom_mk_eq h σ S (c := 1) (by simp [UnitaryFieldData.norm])
        (one_pow _) ?_
      rw [map_one, one_mul]
      apply Units.ext
      rw [coe_glAut, hScoe]
      exact heisShiftMat_map (σ : K →+* K) p
  have hmem : (g : primeFormP h (idGram K p)) ∈ hyperLiftSet p E := by
    rw [← hgcomm]
    change QuotientGroup.mk' _ ⁅t, S⁆ ∈ hyperLiftSet p E
    rw [map_commutatorElement]
    exact commutator_mem_hyperLiftSet (closure_pair_le hD hσE) hrel htfix hSfix
  exact Subgroup.subset_closure hmem

theorem mk_fourier_mem_closure_hyperLiftSet (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hq3 : 3 < ℓ ^ f) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {σ : K ≃+* K}
    (hσD : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∉ primeFormD h (idGram K p))
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 → ∃ c : K, c ^ p = y ∧ h.bar c * c = 1)
    {lam : K} (hlam0 : lam ≠ 0) (hlamσ : σ lam = lam) (hlamN : h.bar lam * lam * p = 1)
    {g : gramSU h (idGram K p)} {s : Fin p → K}
    (hgΦ : ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * heisFourierMat ζ =
      heisFourierMat ζ * diagonal s)
    (hgσ : glAut σ (g : GL (Fin p) K) = g) :
    (g : primeFormP h (idGram K p)) ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := h.finite
  set Φ : Matrix (Fin p) (Fin p) K := heisFourierMat ζ with hΦdef
  have hΦdet : Φ.det ≠ 0 := det_heisFourierMat_ne_zero hζ
  have hΦ'det : (lam • Φ).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hlam0) hΦdet
  have hΦunit : ((lam • Φ).map h.bar)ᵀ * (lam • Φ) = 1 := by
    have h1 := CFSG.LieType.SeitzGeneration.ug81_fourier_unitary h hpq hζ
    have h2 : ((lam • Φ).map h.bar)ᵀ * (lam • Φ) = (h.bar lam * lam * p) • 1 := by
      rw [Matrix.map_smul' _ _ _ (fun a b => map_mul h.bar a b), Matrix.transpose_smul,
        Matrix.smul_mul, Matrix.mul_smul, h1, smul_smul, smul_smul]
    rw [h2, hlamN, one_smul]
  let ΦG : GL (Fin p) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (lam • Φ) hΦ'det
  have hΦGc : (ΦG : Matrix (Fin p) (Fin p) K) = lam • Φ := rfl
  have hΦU : ΦG ∈ primeFormUnitary h (idGram K p) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact hΦunit
  set ΦU : primeFormUnitary h (idGram K p) := ⟨ΦG, hΦU⟩ with hΦUdef
  have hΦσ : glAut σ ΦG = ΦG := by
    apply Units.ext
    rw [coe_glAut, hΦGc]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hΦdef, heisFourierMat,
      Matrix.of_apply]
    rw [map_mul, map_pow, hζσ, hlamσ]
  set κ := primeFormConjHom h (idGram K p) with hκ
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ with hfσ
  have hfU : primeFormFieldU h isPrimeFormGram_one σ ΦU = ΦU := Subtype.ext hΦσ
  have hfh : fσ * κ ΦU = κ ΦU * fσ := by
    have h1 : fσ * κ ΦU * fσ⁻¹ = κ ΦU := by
      have := primeFormField_conj_eq h isPrimeFormGram_one σ ΦU
      rw [hfU] at this
      exact this
    calc fσ * κ ΦU = fσ * κ ΦU * fσ⁻¹ * fσ := by group
      _ = κ ΦU * fσ := by rw [h1]
  set τ : MulAut (primeFormP h (idGram K p)) := κ ΦU with hτ
  set E' := E.map (MulAut.congr τ.symm).toMonoidHom with hE'
  have hcongr : ∀ φ : MulAut (primeFormP h (idGram K p)), MulAut.congr τ.symm φ = τ⁻¹ * φ * τ :=
    fun φ => rfl
  have hΦinv : ((ΦG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (lam • Φ)⁻¹ := by
    rw [← hΦGc, Matrix.coe_units_inv]
  have hΦinvmul : (lam • Φ)⁻¹ * (lam • Φ) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hΦ'det)
  have hSΦ : ΦU⁻¹ * shiftU h hodd * ΦU = diagU h hζ.pow_eq_one hζN hodd := by
    apply Subtype.ext
    apply Units.ext
    change ((ΦG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * heisShiftMat K p * (lam • Φ) =
      heisDiagMat ζ
    rw [hΦinv, Matrix.mul_assoc, Matrix.mul_smul, heisShiftMat_mul_heisFourierMat hζ.pow_eq_one,
      ← Matrix.smul_mul, ← Matrix.mul_assoc, hΦinvmul, Matrix.one_mul]
    rfl
  have hE'a : IsElemAbelian p E' := isElemAbelian_map_congr _ hE
  have hE'c : Nat.card E' = p ^ 3 := (card_map_congr _ E).trans hc
  have hσE' : fσ ∈ E' := ⟨fσ, hσE, by
    show MulAut.congr τ.symm fσ = fσ
    rw [hcongr, mul_assoc, hfh, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  have hDE' : κ (diagU h hζ.pow_eq_one hζN hodd) ∈ E' := ⟨κ (shiftU h hodd), hS, by
    show MulAut.congr τ.symm _ = _
    rw [hcongr, hτ, ← map_inv, ← map_mul, ← map_mul, hSΦ]⟩
  have hg₀mem : ΦG⁻¹ * (g : GL (Fin p) K) * ΦG ∈ gramSU h (idGram K p) := by
    have := conj_mem_gramSU h _ (inv_mem hΦU) g.2
    rwa [inv_inv] at this
  set g₀ : gramSU h (idGram K p) := ⟨ΦG⁻¹ * (g : GL (Fin p) K) * ΦG, hg₀mem⟩ with hg₀def
  have hg₀c : (((g₀ : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      diagonal s := by
    change ((ΦG⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * (lam • Φ) = diagonal s
    rw [hΦinv, Matrix.mul_assoc, Matrix.mul_smul, hgΦ, ← Matrix.smul_mul, ← Matrix.mul_assoc,
      hΦinvmul, Matrix.one_mul]
  have hg₀σ : glAut σ ((g₀ : gramSU h (idGram K p)) : GL (Fin p) K) = g₀ := by
    change glAut σ (ΦG⁻¹ * (g : GL (Fin p) K) * ΦG) = ΦG⁻¹ * (g : GL (Fin p) K) * ΦG
    rw [map_mul, map_mul, map_inv, hΦσ, hgσ]
  have hsσ : ∀ i, σ (s i) = s i := by
    intro i
    have h1 := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K) i i) hg₀σ
    simp only [coe_glAut, Matrix.map_apply, hg₀c, diagonal_apply_eq] at h1
    exact h1
  have h0 := mk_diag_mem_closure_hyperLiftSet h hp hodd hq3 hE'a hE'c hσD hσE' hζ hζN hDE' hroot
    hg₀c hsσ
  have h1 := map_closure_hyperLiftSet_le τ.symm.symm p E'
  rw [hE', map_congr_symm_map_congr τ.symm E] at h1
  have h2 : τ (g₀ : primeFormP h (idGram K p)) = (g : primeFormP h (idGram K p)) := by
    rw [hτ, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change ΦG * (ΦG⁻¹ * (g : GL (Fin p) K) * ΦG) * ΦG⁻¹ = g
    group
  rw [← h2]
  exact h1 ⟨_, h0, rfl⟩

theorem heisShiftMat_map_subtype {k : Subfield K} (p : ℕ) :
    (heisShiftMat k p).map k.subtype = heisShiftMat K p := by
  ext i j
  rw [Matrix.map_apply, heisShiftMat_entry, heisShiftMat_entry]
  split_ifs <;> simp

theorem closure_hyperLiftSet_eq_top_of_std_of_sub
    (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hodd : Odd p)
    (hpq : p ∣ ℓ ^ f + 1)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hq₀ : ℓ ^ (f / p) ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hζN : h.bar ζ * ζ = 1) {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E)
    (hsub : (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) p).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) K) :
          Matrix (Fin p) (Fin p) K)) p)) ≤ Subgroup.closure (hyperLiftSet p E)) :
    Subgroup.closure (hyperLiftSet p E) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfin : Finite K := h.finite
  have hp3 : 3 ≤ p := three_le_of_odd_prime hp hodd
  have : Finite (MulAut (primeFormP h (idGram K p))) := MulEquiv.finite_left
  set k : Subfield K := fixSubfield σ with hkdef
  set h₀ : UnitaryFieldData ℓ (f / p) k := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  set e := f / p with he
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfe : f = p * e := (Nat.mul_div_cancel' hpf).symm
  have hℓ := h.prime
  have hq₀1 : 1 < ℓ ^ e := h₀.one_lt_pow
  have hqq : ℓ ^ f = (ℓ ^ e) ^ p := by rw [hfe, pow_mul']
  have hpq₀ : p ∣ ℓ ^ e + 1 := by
    have h1 : (((ℓ ^ e) ^ p + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).2 (by rw [← hqq]; exact hpq)
    push_cast at h1
    rw [ZMod.pow_card] at h1
    exact (ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h1)
  have hq₀3 : ℓ ^ e ≠ 3 := by
    intro h3
    rw [h3] at hpq₀
    have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpq₀
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hq₀4 : 4 ≤ ℓ ^ e := by omega
  have hq3 : 3 < ℓ ^ f := by
    rw [hqq]
    calc 3 < ℓ ^ e := by omega
      _ = (ℓ ^ e) ^ 1 := (pow_one _).symm
      _ ≤ (ℓ ^ e) ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hne : ¬(p = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hC : IsPrimeFormGram (1 : GL (Fin p) K) := isPrimeFormGram_one
  set κ := primeFormConjHom h (idGram K p) with hκ
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ with hfσ
  have hισ : primeFormFieldFactor h hC hp3 hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hp3 hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : fσ ∉ primeFormD h (idGram K p) := by
    rw [← ker_primeFormFieldFactor h hC hp3 hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨-, r, hr, hrq, hrq₀, hrp⟩ := exists_prime_dvd_pow_add_one hp hp2 (by omega) hpq₀
  rw [← hqq] at hrq
  haveI : Fact r.Prime := ⟨hr⟩
  have hfink : Finite k := h₀.finite
  haveI : Fintype k := Fintype.ofFinite k
  have hcardk : Fintype.card k = (ℓ ^ e) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h₀.card_eq_sq]
  have hrk : Nat.Coprime r (Fintype.card k - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hr, hcardk]
    intro hdvd
    have h1 : (ℓ ^ e) ^ 2 - 1 = (ℓ ^ e - 1) * (ℓ ^ e + 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ e) 1
      rw [sq]
      simpa [mul_comm] using this
    rw [h1] at hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h2 | h2
    ·
      have h3 : ((ℓ ^ e : ℕ) : ZMod r) = 1 := by
        have h4 : ((ℓ ^ e - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
        rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h4
        exact h4
      have h5 : (((ℓ ^ e) ^ p + 1 : ℕ) : ZMod r) = 0 := by
        rw [← hqq]
        exact (ZMod.natCast_eq_zero_iff _ _).2 hrq
      push_cast at h5 h3
      rw [h3, one_pow] at h5
      have h6 : ((2 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h5
      have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
        ((ZMod.natCast_eq_zero_iff _ _).1 h6)
      subst hr2
      apply hrq₀
      have h7 : 2 ∣ (ℓ ^ e) ^ p + 1 := by rw [← hqq]; exact hrq
      have h8 : Odd ((ℓ ^ e) ^ p) := by
        rcases Nat.even_or_odd ((ℓ ^ e) ^ p) with hev | hod
        · exfalso
          obtain ⟨a, ha⟩ := hev
          rw [ha] at h7
          omega
        · exact hod
      obtain ⟨b, hb⟩ := (Nat.odd_pow_iff hp.ne_zero).1 h8
      exact ⟨b + 1, by omega⟩
    · exact hrq₀ h2
  obtain ⟨uu, huu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by
    rw [Nat.card_units, h.card_eq_sq]
    have : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      rw [sq]
      simpa [mul_comm] using this
    rw [this]
    exact Dvd.dvd.mul_left hrq _)
  set u : K := (uu : K) with hu
  have hu0 : u ≠ 0 := uu.ne_zero
  have hur : u ^ r = 1 := by
    rw [hu, ← Units.val_pow_eq_pow_val, ← huu, pow_orderOf_eq_one, Units.val_one]
  have huq : u ^ (ℓ ^ f + 1) = 1 := by
    obtain ⟨a, ha⟩ := hrq
    rw [ha, pow_mul, hur, one_pow]
  have huN : h.bar u * u = 1 := by rw [h.bar_apply, ← pow_succ, huq]
  have hkone : ∀ x : K, σ x = x → x ≠ 0 → x ^ r = 1 → x = 1 := by
    intro x hx hx0 hxr
    have h1 : (⟨x, hx⟩ : k) ^ (Fintype.card k - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (fun h0 => hx0 (congrArg Subtype.val h0))
    have h2 : x ^ (Fintype.card k - 1) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : x ^ (Nat.gcd r (Fintype.card k - 1)) = 1 := pow_gcd_eq_one.2 ⟨hxr, h2⟩
    rwa [hrk.gcd_eq_one, pow_one] at h3
  have hσu : σ u ≠ u := by
    intro h1
    have := hkone u h1 hu0 hur
    rw [hu] at this
    have hone : uu = 1 := Units.ext this
    rw [hone, orderOf_one] at huu
    exact hr.one_lt.ne huu
  set tv : Fin p → K := fun i => (σ ^ (i : ℕ)) u with htv
  have hNr : ∏ i, tv i = ∏ i ∈ Finset.range p, (σ ^ i) u :=
    Fin.prod_univ_eq_prod_range (fun i => (σ ^ i) u) p
  have hσN : σ (∏ i ∈ Finset.range p, (σ ^ i) u) = ∏ i ∈ Finset.range p, (σ ^ i) u := by
    rw [map_prod]
    have h1 := Finset.prod_range_succ (fun i => (σ ^ i) u) p
    have h2 := Finset.prod_range_succ' (fun i => (σ ^ i) u) p
    rw [hσp] at h1
    rw [pow_zero] at h2
    simp only [ringEquiv_pow_succ_apply] at h2
    exact mul_right_cancel₀ hu0 (h2.symm.trans h1)
  have hN0 : ∏ i ∈ Finset.range p, (σ ^ i) u ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 hu0
  have hN1 : ∏ i ∈ Finset.range p, (σ ^ i) u = 1 := by
    refine hkone _ hσN hN0 ?_
    rw [← Finset.prod_pow]
    simp only [← map_pow, hur, map_one, Finset.prod_const_one]
  have htvN : ∀ i, h.bar (tv i) * tv i = 1 := by
    intro i
    simp only [htv]
    rw [h.bar_apply, ← map_pow, ← map_mul, ← h.bar_apply, huN, map_one]
  have htdet : (diagonal tv : Matrix (Fin p) (Fin p) K).det = 1 := by
    rw [det_diagonal, hNr, hN1]
  let t : gramSU h (idGram K p) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal tv) (by rw [htdet]; exact one_ne_zero), by
      refine mem_gramSU.2 ⟨?_, htdet⟩
      change ((diagonal tv : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * 1 * diagonal tv = 1
      rw [Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact htvN i⟩
  have htcoe : (((t : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      diagonal tv := rfl
  set S := shiftSU h hodd with hSdef
  have hScoe : (((S : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      heisShiftMat K p := rfl
  have htS : glAut σ ((t : gramSU h (idGram K p)) : GL (Fin p) K) * (S : GL (Fin p) K) =
      (S : GL (Fin p) K) * (t : GL (Fin p) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, htcoe, hScoe, diagonal_map (map_zero _)]
    ext i j
    rw [diagonal_mul, mul_diagonal, heisShiftMat_entry]
    split_ifs with hij
    · subst hij
      rw [one_mul, mul_one]
      show σ ((σ ^ (i : ℕ)) u) = (σ ^ ((finRotate p i : Fin p) : ℕ)) u
      rw [← ringEquiv_pow_succ_apply, finRotate_val_mod, ← pow_eq_pow_mod _ hσp]
    · simp
  set Du := diagU h hζ.pow_eq_one hζN hodd with hDudef
  set Su := shiftU h hodd with hSudef
  have hDucoe : (((Du : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = heisDiagMat ζ := rfl
  have hD1 : κ Du ≠ 1 := by
    intro h1
    obtain ⟨u', -, hu'⟩ := (primeFormConjHom_eq_one_iff (h := h) (by omega) hq3 Du).1 h1
    have h0 := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K)
      ⟨0, hp.pos⟩ ⟨0, hp.pos⟩) hu'
    have h1' := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K)
      ⟨1, hp.one_lt⟩ ⟨1, hp.one_lt⟩) hu'
    simp only [hDucoe, heisDiagMat, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at h0 h1'
    simp only [pow_zero] at h0
    simp only [pow_one] at h1'
    exact hζ.ne_one hp.one_lt (h1'.trans h0.symm)
  have hb : (κ Su)⁻¹ * fσ ∈ E := E.mul_mem (E.inv_mem hS) hσE
  have hbD : (κ Su)⁻¹ * fσ ∉ Subgroup.zpowers (κ Du) := by
    intro h'
    apply hσD
    have e1 : fσ = κ Su * ((κ Su)⁻¹ * fσ) := by group
    rw [e1]
    exact (primeFormD h _).mul_mem ⟨Su, rfl⟩
      ((Subgroup.zpowers_le.2 (⟨Du, rfl⟩ : κ Du ∈ primeFormD h _)) h')
  have hrel := (relIndex_closure_pair_of_indep hp hE hc hD hb hD1 hbD).2
  have htfix : (t : primeFormP h (idGram K p)) ∈ fixedPoints (Subgroup.closure
      ({κ Du, (κ Su)⁻¹ * fσ} : Set (MulAut (primeFormP h (idGram K p))))) := by
    refine CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_
    rintro φ (rfl | rfl)
    · refine primeFormConjHom_mk_eq_of_conj h Du t (c := 1) (by simp [UnitaryFieldData.norm])
        (one_pow _) ?_
      rw [map_one, one_mul]
      have hDt : (Du : GL (Fin p) K) * (t : GL (Fin p) K) = (t : GL (Fin p) K) * Du := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hDucoe, htcoe, heisDiagMat, diagonal_mul_diagonal,
          diagonal_mul_diagonal]
        congr 1
        funext i
        ring
      rw [hDt, mul_inv_cancel_right]
    · change (κ Su)⁻¹ (fσ (t : primeFormP h (idGram K p))) = t
      have h1 : fσ (t : primeFormP h (idGram K p)) =
          ((primeFormFieldSU h isPrimeFormGram_one σ t : gramSU h _) : primeFormP h _) :=
        primeFormFieldAut_mk h isPrimeFormGram_one σ t
      rw [h1, ← map_inv, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      change ((Su⁻¹ : primeFormUnitary h (idGram K p)) : GL (Fin p) K) *
          glAut σ (t : GL (Fin p) K) *
          ((Su⁻¹ : primeFormUnitary h (idGram K p)) : GL (Fin p) K)⁻¹ = t
      rw [Subgroup.coe_inv, inv_inv, mul_assoc]
      change (S : GL (Fin p) K)⁻¹ * (glAut σ (t : GL (Fin p) K) * (S : GL (Fin p) K)) = t
      rw [htS, inv_mul_cancel_left]
  have htr : t ^ r = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, htcoe, diagonal_pow, Subgroup.coe_one,
      Units.val_one, ← diagonal_one]
    congr 1
    ext i
    simp only [Pi.pow_apply, htv, ← map_pow, hur, map_one, Pi.one_apply]
  have hpr : ¬ p ∣ r := fun h' => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h').symm
  have htmem : (t : primeFormP h (idGram K p)) ∈ hyperLiftSet p E :=
    mem_hyperLiftSet_of_pow (closure_pair_le hD hb) hrel hpr
      (by rw [← QuotientGroup.mk_pow, htr, QuotientGroup.mk_one]) htfix
  set tU : primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) :=
    ⟨(t : GL (Fin p) K), ((mem_gramSU_iff_unitary h).1 t.2).1⟩ with htUdef
  have htinv : (((t⁻¹ : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      diagonal fun i => (tv i)⁻¹ := by
    have htv0 : ∀ i, tv i ≠ 0 := fun i => (map_ne_zero _).2 hu0
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, htcoe]
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (htv0 i)
  set Sk := shiftSU h₀ hodd with hSkdef
  have hne : (suSub h h₀ hbar p).map (primeFormConjSU h _ tU).toMonoidHom ≠
      suSub h h₀ hbar p := by
    intro heq
    have hmem : primeFormConjSU h _ tU (subfieldSU h h₀ hbar p Sk) ∈ suSub h h₀ hbar p := by
      rw [← heq]
      exact ⟨_, ⟨Sk, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    have hfixσ : glAut σ (((primeFormConjSU h _ tU (subfieldSU h h₀ hbar p Sk) :
        gramSU h _) : GL (Fin p) K)) =
        ((primeFormConjSU h _ tU (subfieldSU h h₀ hbar p Sk) : gramSU h _) : GL (Fin p) K) := by
      rw [← hy]
      exact glAut_subfieldGL σ p y
    have hmat : (((primeFormConjSU h _ tU (subfieldSU h h₀ hbar p Sk) : gramSU h _) :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        diagonal tv * heisShiftMat K p * diagonal (fun i => (tv i)⁻¹) := by
      change ((t : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
        (((subfieldSU h h₀ hbar p Sk : gramSU h _) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
        (((t : GL (Fin p) K)⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
      rw [htcoe, coe_subfieldSU, coe_subfieldGL]
      have h2 : (((t : GL (Fin p) K)⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
          diagonal fun i => (tv i)⁻¹ := htinv
      rw [h2]
      congr 2
      exact heisShiftMat_map_subtype p
    have h01 := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K)
      ⟨0, hp.pos⟩ ⟨1, hp.one_lt⟩) hfixσ
    simp only [coe_glAut, Matrix.map_apply, hmat] at h01
    have hrot : finRotate p ⟨0, hp.pos⟩ = ⟨1, hp.one_lt⟩ := by
      apply Fin.ext
      rw [finRotate_val_mod]
      exact Nat.mod_eq_of_lt hp.one_lt
    have hent : (diagonal tv * heisShiftMat K p * diagonal (fun i => (tv i)⁻¹))
        ⟨0, hp.pos⟩ ⟨1, hp.one_lt⟩ = tv ⟨0, hp.pos⟩ * (tv ⟨1, hp.one_lt⟩)⁻¹ := by
      rw [mul_diagonal, diagonal_mul, heisShiftMat_entry, if_pos hrot, mul_one]
    rw [hent] at h01
    have ht0 : tv ⟨0, hp.pos⟩ = u := by
      show (σ ^ 0) u = u
      rw [pow_zero]
      rfl
    have ht1 : tv ⟨1, hp.one_lt⟩ = σ u := by
      show (σ ^ 1) u = σ u
      rw [pow_one]
    rw [ht0, ht1] at h01
    have hw0 : u * (σ u)⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero ((map_ne_zero σ).2 hu0))
    have hwr : (u * (σ u)⁻¹) ^ r = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, hur, map_one, inv_one, mul_one]
    have hw1 := hkone _ h01 hw0 hwr
    apply hσu
    have := mul_eq_one_iff_eq_inv₀ (inv_ne_zero ((map_ne_zero σ).2 hu0)) |>.1 hw1
    rw [inv_inv] at this
    exact this.symm
  have hgen := subfieldPairSUOdd_of_ne_two ℓ f e K h k h₀ hbar p hp hp2 hfe hq₀ p hp3 tU hne
  set Q := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) K) :
    Matrix (Fin p) (Fin p) K)) p) with hQ
  have htQ : Q t ∈ Subgroup.closure (hyperLiftSet p E) := Subgroup.subset_closure htmem
  have hcomap : (Subgroup.closure (hyperLiftSet p E)).comap Q = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (hg | ⟨g, hg, rfl⟩)
    · exact hsub ⟨g, hg, rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      have h1 : (primeFormConjSU h _ tU).toMonoidHom g = t * g * t⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htQ (hsub ⟨g, hg, rfl⟩))
        (Subgroup.inv_mem _ htQ)
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hg : g ∈ (Subgroup.closure (hyperLiftSet p E)).comap Q := by
    rw [hcomap]
    exact Subgroup.mem_top g
  exact hg

theorem exists_pow_eq_of_fixed_norm (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {σ : K ≃+* K} (hσ : orderOf σ = p) (hq₀ : ℓ ^ (f / p) ≠ 2)
    {y : K} (hyσ : σ y = y) (hyN : h.bar y * y = 1) : ∃ c : K, c ^ p = y ∧ h.bar c * c = 1 := by
  have hfin : Finite K := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfe : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hqq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [hfe, pow_mul', Nat.mul_div_cancel_left _ hp.pos]
  have hq₀1 : 1 < ℓ ^ (f / p) := h₀.one_lt_pow
  have hpq₀ : p ∣ ℓ ^ (f / p) + 1 := by
    have h1 : (((ℓ ^ (f / p)) ^ p + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).2 (by rw [← hqq]; exact hpq)
    push_cast at h1
    haveI : Fact p.Prime := ⟨hp⟩
    rw [ZMod.pow_card] at h1
    exact (ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h1)
  have hq₀3 : ℓ ^ (f / p) ≠ 3 := by
    intro h3
    rw [h3] at hpq₀
    have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpq₀
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hK : (ℓ ^ (f / p)) ^ p + 1 ∣ Nat.card K - 1 := by
    rw [← hqq, h.card_eq_sq]
    have : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      rw [sq]
      simpa [mul_comm] using this
    rw [this]
    exact Dvd.intro_left _ rfl
  have hy1 : y ^ (ℓ ^ (f / p) + 1) = 1 := by
    have h1 : h.bar y = y ^ ℓ ^ (f / p) := by
      have := hbar ⟨y, hyσ⟩
      rw [UnitaryFieldData.bar_apply] at this
      rw [← this]
      rfl
    rw [pow_succ, ← h1, hyN]
  obtain ⟨c, hcp, hcq⟩ := exists_pow_eq_of_norm_one hp hp2 (by omega) hpq₀ hK hy1
  refine ⟨c, hcp, ?_⟩
  rw [h.bar_apply, ← pow_succ, hqq, hcq]

theorem map_suSub_le_closure_of_torusGen (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hodd : Odd p) (hpq : p ∣ ℓ ^ f + 1) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hq₀ : ℓ ^ (f / p) ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hζσ : σ ζ = ζ) {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E)
    (hgen : TorusFourierGenU (fixSubfield_unitaryFieldData h hp hp2 hσ) p) :
    (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) p).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)) p)) ≤ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfin : Finite K := h.finite
  have hp3 : 3 ≤ p := three_le_of_odd_prime hp hodd
  set k : Subfield K := fixSubfield σ with hkdef
  set h₀ : UnitaryFieldData ℓ (f / p) k := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  set e := f / p with he
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfe : f = p * e := (Nat.mul_div_cancel' hpf).symm
  have hℓ := h.prime
  have hq₀1 : 1 < ℓ ^ e := h₀.one_lt_pow
  have hqq : ℓ ^ f = (ℓ ^ e) ^ p := by rw [hfe, pow_mul']
  have hq3 : 3 < ℓ ^ f := by
    rw [hqq]
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ (ℓ ^ e) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (ℓ ^ e) ^ p := Nat.pow_le_pow_right (by omega) hp.two_le
  have hne : ¬(p = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hC : IsPrimeFormGram (1 : GL (Fin p) K) := isPrimeFormGram_one
  have hισ : primeFormFieldFactor h hC hp3 hne (primeFormFieldHom h hC σ) = σ := by
    have := primeFormFieldFactor_apply h hC hp3 hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∉ primeFormD h (idGram K p) := by
    rw [← ker_primeFormFieldFactor h hC hp3 hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 →
      ∃ c : K, c ^ p = y ∧ h.bar c * c = 1 := fun y _ hyσ hyN =>
    exists_pow_eq_of_fixed_norm h hp hp2 hpq hσ hq₀ hyσ hyN
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hfink : Finite k := h₀.finite
  haveI : CharP k ℓ := h₀.charP
  have hpk : (p : k) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff k ℓ p).1 h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 this).symm
  have hpinv : ((p : k)⁻¹) ∈ h₀.fixedField := by
    rw [h₀.mem_fixedField, map_inv₀, map_natCast]
  obtain ⟨lam₀, hlam₀⟩ := h₀.normHom_surjective ⟨(p : k)⁻¹, hpinv⟩
  have hlamN₀ : h₀.norm lam₀ = (p : k)⁻¹ := congrArg Subtype.val hlam₀
  have hlam₀0 : lam₀ ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hlamN₀
    exact inv_ne_zero hpk hlamN₀.symm
  have hlamN : h.bar (lam₀ : K) * (lam₀ : K) * p = 1 := by
    have hpK : ((p : k) : K) = (p : K) := map_natCast k.subtype p
    rw [← hbar, ← Subfield.coe_mul, mul_comm (h₀.bar lam₀), ← UnitaryFieldData.norm, hlamN₀,
      Subfield.coe_inv, hpK]
    exact inv_mul_cancel₀ (by rw [← hpK]; exact_mod_cast hpk)
  set ζk : k := ⟨ζ, hζσ⟩ with hζk
  have hζk' : IsPrimitiveRoot ζk p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := k.subtype) Subtype.val_injective).1 hζ
  have hΦk : (heisFourierMat ζk : Matrix (Fin p) (Fin p) k).map k.subtype = heisFourierMat ζ := by
    ext i j
    simp [heisFourierMat, hζk]
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let incl : unitarySU ℓ e k p →*
      gramSU h₀ ((1 : GL (Fin p) k) : Matrix (Fin p) (Fin p) k) :=
    Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h₀ p))
  set Q := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) K) :
    Matrix (Fin p) (Fin p) K)) p) with hQ
  let Γ : unitarySU ℓ e k p →* primeFormP h (idGram K p) :=
    Q.comp ((subfieldSU h h₀ hbar p).comp incl)
  set H : Subgroup (GL (Fin p) k) :=
    ((Subgroup.closure (hyperLiftSet p E)).comap Γ).map (unitarySU ℓ e k p).subtype with hHdef
  have hHU : H ≤ unitarySU ℓ e k p := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmemH : ∀ (g : GL (Fin p) k) (hg : g ∈ unitarySU ℓ e k p),
      Γ ⟨g, hg⟩ ∈ Subgroup.closure (hyperLiftSet p E) → g ∈ H :=
    fun g hg hΓ => ⟨⟨g, hg⟩, hΓ, rfl⟩
  have hT : ∀ g ∈ unitarySU ℓ e k p, (∃ t, (g : Matrix (Fin p) (Fin p) k) = diagonal t) →
      g ∈ H := by
    rintro g hg ⟨t, ht⟩
    refine hmemH g hg ?_
    have hmat : (((subfieldSU h h₀ hbar p (incl ⟨g, hg⟩) : gramSU h _) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) = diagonal fun i => ((t i : k) : K) := by
      rw [coe_subfieldSU, coe_subfieldGL]
      change (g : Matrix (Fin p) (Fin p) k).map k.subtype = _
      rw [ht, diagonal_map (map_zero _)]
      rfl
    exact mk_diag_mem_closure_hyperLiftSet h hp hodd hq3 hE hc hσD hσE hζ hζN hD hroot hmat
      (fun i => (t i).2)
  have hTw : ∀ g ∈ unitarySU ℓ e k p, (∃ t, (g : Matrix (Fin p) (Fin p) k) *
      heisFourierMat ζk = heisFourierMat ζk * diagonal t) → g ∈ H := by
    rintro g hg ⟨t, ht⟩
    refine hmemH g hg ?_
    have hmat : (((subfieldSU h h₀ hbar p (incl ⟨g, hg⟩) : gramSU h _) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal fun i => ((t i : k) : K) := by
      rw [coe_subfieldSU, coe_subfieldGL]
      change (g : Matrix (Fin p) (Fin p) k).map k.subtype * heisFourierMat ζ = _
      have h1 := congrArg (fun M : Matrix (Fin p) (Fin p) k => M.map k.subtype) ht
      rw [Matrix.map_mul, Matrix.map_mul, hΦk, diagonal_map (map_zero _)] at h1
      exact h1
    have hσG : glAut σ (((subfieldSU h h₀ hbar p (incl ⟨g, hg⟩) : gramSU h _) :
        GL (Fin p) K)) = ((subfieldSU h h₀ hbar p (incl ⟨g, hg⟩) : gramSU h _) : GL (Fin p) K) :=
      glAut_subfieldGL σ p _
    exact mk_fourier_mem_closure_hyperLiftSet h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hS hroot
      (lam := (lam₀ : K)) (by exact_mod_cast hlam₀0) lam₀.2 hlamN hmat hσG
  have htop := hgen ζk hζk' H hHU hT hTw
  rintro _ ⟨y, ⟨y', rfl⟩, rfl⟩
  have hy'U : (y' : GL (Fin p) k) ∈ unitarySU ℓ e k p := by
    rw [unitarySU_eq_gramSU h₀ p]
    exact y'.2
  have hyH : (y' : GL (Fin p) k) ∈ H := htop ▸ hy'U
  obtain ⟨z, hz, hzy⟩ := hyH
  have hz' : z = ⟨(y' : GL (Fin p) k), hy'U⟩ := Subtype.ext hzy
  rw [hz'] at hz
  exact hz

theorem shift_inv_pow_conj_diag {p : ℕ} [NeZero p] {ζ : K} (hζ : ζ ^ p = 1) (hζ0 : ζ ≠ 0)
    (S D : GL (Fin p) K) (hSc : (S : Matrix (Fin p) (Fin p) K) = heisShiftMat K p)
    (hDc : (D : Matrix (Fin p) (Fin p) K) = heisDiagMat ζ) (m : ℕ) :
    ((S ^ m)⁻¹ * D * S ^ m : GL (Fin p) K) =
      GeneralLinearGroup.scalar (Fin p) ((Units.mk0 ζ hζ0)⁻¹ ^ m) * D := by
  set c : Kˣ := (Units.mk0 ζ hζ0)⁻¹ with hcdef
  have hcomm : ∀ (u : Kˣ) (g : GL (Fin p) K),
      g * GeneralLinearGroup.scalar (Fin p) u = GeneralLinearGroup.scalar (Fin p) u * g :=
    fun u g => (commute_scalar u g).eq
  have h2 : D * S = GeneralLinearGroup.scalar (Fin p) c * (S * D) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hSc, hDc,
      heisDiagMat_mul_heisShiftMat ζ hζ, GeneralLinearGroup.coe_scalar, hcdef,
      Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h1 : S⁻¹ * D * S = GeneralLinearGroup.scalar (Fin p) c * D := by
    calc S⁻¹ * D * S = S⁻¹ * (GeneralLinearGroup.scalar (Fin p) c * (S * D)) := by
          rw [mul_assoc, h2]
      _ = (S⁻¹ * GeneralLinearGroup.scalar (Fin p) c) * (S * D) := (mul_assoc _ _ _).symm
      _ = GeneralLinearGroup.scalar (Fin p) c * (S⁻¹ * (S * D)) := by
          rw [hcomm, mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin p) c * D := by rw [inv_mul_cancel_left]
  induction m with
  | zero => simp
  | succ m ih =>
    calc (S ^ (m + 1))⁻¹ * D * S ^ (m + 1) = S⁻¹ * ((S ^ m)⁻¹ * D * S ^ m) * S := by
          rw [pow_succ, _root_.mul_inv_rev]
          group
      _ = S⁻¹ * (GeneralLinearGroup.scalar (Fin p) (c ^ m) * D) * S := by rw [ih]
      _ = GeneralLinearGroup.scalar (Fin p) (c ^ m) * (S⁻¹ * D * S) := by
          rw [← mul_assoc S⁻¹, hcomm, mul_assoc, mul_assoc, mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin p) (c ^ (m + 1)) * D := by
          rw [h1, ← mul_assoc, ← map_mul, ← pow_succ]

theorem mk_projCentD_mem_closure (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hq3 : 3 < ℓ ^ f) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {σ : K ≃+* K}
    (hσD : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∉ primeFormD h (idGram K p))
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E)
    (hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 → ∃ c : K, c ^ p = y ∧ h.bar c * c = 1)
    {lam : K} (hlam0 : lam ≠ 0) (hlamσ : σ lam = lam) (hlamN : h.bar lam * lam * p = 1)
    {g : gramSU h (idGram K p)} (hgσ : glAut σ (g : GL (Fin p) K) = g) {c : K}
    (hgD : ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * heisDiagMat ζ =
      c • (heisDiagMat ζ * ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))) :
    (g : primeFormP h (idGram K p)) ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set S := shiftSU h hodd with hSdef
  have hScoe : (((S : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      heisShiftMat K p := rfl
  have hSσ : glAut σ ((S : gramSU h (idGram K p)) : GL (Fin p) K) = S := by
    apply Units.ext
    rw [coe_glAut, hScoe]
    exact heisShiftMat_map (σ : K →+* K) p
  have hSΦ : (((S : gramSU h (idGram K p)) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      heisFourierMat ζ = heisFourierMat ζ * diagonal fun j : Fin p => ζ ^ (j : ℕ) := by
    rw [hScoe]
    exact heisShiftMat_mul_heisFourierMat hζ.pow_eq_one
  have hSmem : (S : primeFormP h (idGram K p)) ∈ Subgroup.closure (hyperLiftSet p E) :=
    mk_fourier_mem_closure_hyperLiftSet h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hS hroot hlam0
      hlamσ hlamN hSΦ hSσ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set G : Matrix (Fin p) (Fin p) K := ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hG
  have hGdet : G.det = 1 := (mem_gramSU.1 g.2).2
  obtain ⟨l, hl⟩ : ∃ l, G ⟨0, hp.pos⟩ l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : G.det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hp.pos⟩ hcon
    rw [hGdet] at h0
    exact one_ne_zero h0
  have hcl : c = ζ ^ (l : ℕ) := by
    have h1 := congrFun (congrFun hgD ⟨0, hp.pos⟩) l
    rw [heisDiagMat, mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h1
    simp only [pow_zero, one_mul] at h1
    exact mul_right_cancel₀ hl (h1.symm.trans (mul_comm _ _))
  set m : ℕ := (l : ℕ) with hm
  set Du := diagU h hζ.pow_eq_one hζN hodd with hDudef
  have hDucoe : (((Du : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = heisDiagMat ζ := rfl
  have hc0 : c ≠ 0 := by rw [hcl]; exact pow_ne_zero _ hζ0
  set cu : Kˣ := Units.mk0 c hc0 with hcu
  have hcomm : ∀ (u : Kˣ) (x : GL (Fin p) K),
      x * GeneralLinearGroup.scalar (Fin p) u = GeneralLinearGroup.scalar (Fin p) u * x :=
    fun u x => (commute_scalar u x).eq
  have hgDG : (g : GL (Fin p) K) * (Du : GL (Fin p) K) * (g : GL (Fin p) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin p) cu * (Du : GL (Fin p) K) := by
    have h1 : (g : GL (Fin p) K) * (Du : GL (Fin p) K) =
        GeneralLinearGroup.scalar (Fin p) cu * ((Du : GL (Fin p) K) * (g : GL (Fin p) K)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hDucoe, ← hG, hgD,
        GeneralLinearGroup.coe_scalar, hcu, Units.val_mk0, Matrix.scalar_apply,
        Matrix.smul_eq_diagonal_mul]
    rw [h1, mul_assoc, mul_inv_cancel_right]
  have hSm := shift_inv_pow_conj_diag hζ.pow_eq_one hζ0 (S : GL (Fin p) K) (Du : GL (Fin p) K)
    hScoe hDucoe m
  set g' : gramSU h (idGram K p) := g * (S ^ m)⁻¹ with hg'def
  have hg'c : ((g' : gramSU h (idGram K p)) : GL (Fin p) K) =
      (g : GL (Fin p) K) * ((S : GL (Fin p) K) ^ m)⁻¹ := rfl
  have hg'D : (g' : GL (Fin p) K) * (Du : GL (Fin p) K) = (Du : GL (Fin p) K) * g' := by
    have hscal : GeneralLinearGroup.scalar (Fin p) ((Units.mk0 ζ hζ0)⁻¹ ^ m) *
        GeneralLinearGroup.scalar (Fin p) cu = 1 := by
      rw [← map_mul]
      have : (Units.mk0 ζ hζ0)⁻¹ ^ m * cu = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
          hcu, Units.val_mk0, hcl, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hζ0), Units.val_one]
      rw [this, map_one]
    have h1 : (g' : GL (Fin p) K) * (Du : GL (Fin p) K) * (g' : GL (Fin p) K)⁻¹ =
        (Du : GL (Fin p) K) := by
      rw [hg'c, _root_.mul_inv_rev, inv_inv]
      calc (g : GL (Fin p) K) * ((S : GL (Fin p) K) ^ m)⁻¹ * (Du : GL (Fin p) K) *
            ((S : GL (Fin p) K) ^ m * (g : GL (Fin p) K)⁻¹)
          = (g : GL (Fin p) K) * (((S : GL (Fin p) K) ^ m)⁻¹ * (Du : GL (Fin p) K) *
              (S : GL (Fin p) K) ^ m) * (g : GL (Fin p) K)⁻¹ := by group
        _ = (g : GL (Fin p) K) * (GeneralLinearGroup.scalar (Fin p) ((Units.mk0 ζ hζ0)⁻¹ ^ m) *
              (Du : GL (Fin p) K)) * (g : GL (Fin p) K)⁻¹ := by rw [hSm]
        _ = GeneralLinearGroup.scalar (Fin p) ((Units.mk0 ζ hζ0)⁻¹ ^ m) *
              ((g : GL (Fin p) K) * (Du : GL (Fin p) K) * (g : GL (Fin p) K)⁻¹) := by
            rw [← mul_assoc (g : GL (Fin p) K), hcomm, mul_assoc, mul_assoc, mul_assoc]
        _ = (Du : GL (Fin p) K) := by
            rw [hgDG, ← mul_assoc, hscal, one_mul]
    calc (g' : GL (Fin p) K) * (Du : GL (Fin p) K)
        = (g' : GL (Fin p) K) * (Du : GL (Fin p) K) * (g' : GL (Fin p) K)⁻¹ * g' := by group
      _ = (Du : GL (Fin p) K) * g' := by rw [h1]
  set G' : Matrix (Fin p) (Fin p) K := ((g' : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hG'
  have hG'D : G' * heisDiagMat ζ = heisDiagMat ζ * G' := by
    have := congrArg Units.val hg'D
    rw [Units.val_mul, Units.val_mul, hDucoe] at this
    exact this
  have hG'diag : G' = diagonal fun i => G' i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      have h1 := congrFun (congrFun hG'D i) j
      rw [heisDiagMat, mul_diagonal, diagonal_mul] at h1
      have h2 : ζ ^ (j : ℕ) ≠ ζ ^ (i : ℕ) := fun h' =>
        hij (Fin.ext (hζ.pow_inj j.isLt i.isLt h')).symm
      have h3 : G' i j * (ζ ^ (j : ℕ) - ζ ^ (i : ℕ)) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)
  have hg'σ : glAut σ ((g' : gramSU h (idGram K p)) : GL (Fin p) K) = g' := by
    rw [hg'c, map_mul, map_inv, map_pow, hgσ, hSσ]
  have hG'σ : ∀ i, σ (G' i i) = G' i i := by
    intro i
    have h1 := congrArg (fun A : GL (Fin p) K => (A : Matrix (Fin p) (Fin p) K) i i) hg'σ
    simpa only [coe_glAut, Matrix.map_apply] using h1
  have hg'mem := mk_diag_mem_closure_hyperLiftSet h hp hodd hq3 hE hc hσD hσE hζ hζN hD hroot
    hG'diag hG'σ
  have hgg : g = g' * S ^ m := by rw [hg'def, inv_mul_cancel_right]
  rw [hgg, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  exact Subgroup.mul_mem _ hg'mem (Subgroup.pow_mem _ hSmem m)

theorem mk_mem_closure_of_conj_projCentD (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hq3 : 3 < ℓ ^ f) (hpq : p ∣ ℓ ^ f + 1)
    {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {σ : K ≃+* K}
    (hσD : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∉ primeFormD h (idGram K p))
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ)
    (hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 → ∃ c : K, c ^ p = y ∧ h.bar c * c = 1)
    {lam : K} (hlam0 : lam ≠ 0) (hlamσ : σ lam = lam) (hlamN : h.bar lam * lam * p = 1)
    (N : primeFormUnitary h (idGram K p)) (hNσ : glAut σ (N : GL (Fin p) K) = N)
    (hSN : primeFormConjHom h _ (N * shiftU h hodd * N⁻¹) ∈ E)
    (hDN : primeFormConjHom h _ (N * diagU h hζ.pow_eq_one hζN hodd * N⁻¹) ∈ E)
    {g : gramSU h (idGram K p)} (hgσ : glAut σ (g : GL (Fin p) K) = g) {c : K}
    (hgD : (((N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) * (N : GL (Fin p) K) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * heisDiagMat ζ =
      c • (heisDiagMat ζ * (((N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) *
        (N : GL (Fin p) K) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))) :
    (g : primeFormP h (idGram K p)) ∈ Subgroup.closure (hyperLiftSet p E) := by
  classical
  set κ := primeFormConjHom h (idGram K p) with hκ
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ with hfσ
  set τ : MulAut (primeFormP h (idGram K p)) := κ N with hτ
  set E' := E.map (MulAut.congr τ.symm).toMonoidHom with hE'
  have hcongr : ∀ φ : MulAut (primeFormP h (idGram K p)), MulAut.congr τ.symm φ = τ⁻¹ * φ * τ :=
    fun φ => rfl
  have hfU : primeFormFieldU h isPrimeFormGram_one σ N = N := Subtype.ext hNσ
  have hfh : fσ * τ = τ * fσ := by
    have h1 : fσ * τ * fσ⁻¹ = τ := by
      have := primeFormField_conj_eq h isPrimeFormGram_one σ N
      rw [hfU] at this
      exact this
    calc fσ * τ = fσ * τ * fσ⁻¹ * fσ := by group
      _ = τ * fσ := by rw [h1]
  have hE'a : IsElemAbelian p E' := isElemAbelian_map_congr _ hE
  have hE'c : Nat.card E' = p ^ 3 := (card_map_congr _ E).trans hc
  have hσE' : fσ ∈ E' := ⟨fσ, hσE, by
    show MulAut.congr τ.symm fσ = fσ
    rw [hcongr, mul_assoc, hfh, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  have hSE' : κ (shiftU h hodd) ∈ E' := ⟨_, hSN, by
    show MulAut.congr τ.symm _ = _
    rw [hcongr, hτ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group⟩
  have hDE' : κ (diagU h hζ.pow_eq_one hζN hodd) ∈ E' := ⟨_, hDN, by
    show MulAut.congr τ.symm _ = _
    rw [hcongr, hτ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group⟩
  have hg₀mem : (N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) * (N : GL (Fin p) K) ∈
      gramSU h (idGram K p) := by
    have := conj_mem_gramSU h _ (inv_mem N.2) g.2
    rwa [inv_inv] at this
  set g₀ : gramSU h (idGram K p) :=
    ⟨(N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) * (N : GL (Fin p) K), hg₀mem⟩ with hg₀def
  have hg₀σ : glAut σ ((g₀ : gramSU h (idGram K p)) : GL (Fin p) K) = g₀ := by
    change glAut σ ((N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) * (N : GL (Fin p) K)) =
      (N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) * (N : GL (Fin p) K)
    rw [map_mul, map_mul, map_inv, hNσ, hgσ]
  have h0 := mk_projCentD_mem_closure h hp hodd hq3 hpq hE'a hE'c hσD hσE' hζ hζN hζσ hSE' hDE'
    hroot hlam0 hlamσ hlamN hg₀σ hgD
  have h1 := map_closure_hyperLiftSet_le τ.symm.symm p E'
  rw [hE', map_congr_symm_map_congr τ.symm E] at h1
  have h2 : τ (g₀ : primeFormP h (idGram K p)) = (g : primeFormP h (idGram K p)) := by
    rw [hτ, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (N : GL (Fin p) K) * ((N : GL (Fin p) K)⁻¹ * (g : GL (Fin p) K) *
      (N : GL (Fin p) K)) * (N : GL (Fin p) K)⁻¹ = g
    group
  rw [← h2]
  exact h1 ⟨_, h0, rfl⟩

theorem heisDiagMat_mul_heisFourierMat_mul_heisShiftMat {p : ℕ} [NeZero p] {ζ : K}
    (hζ : ζ ^ p = 1) :
    heisDiagMat ζ * heisFourierMat ζ * heisShiftMat K p = heisFourierMat (p := p) ζ := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single ((finRotate p).symm j)]
  · rw [heisShiftMat_entry, if_pos (Equiv.apply_symm_apply _ _), mul_one, heisDiagMat,
      diagonal_mul]
    simp only [heisFourierMat, Matrix.of_apply]
    have hk : (((finRotate p).symm j : Fin p) : ℕ) + 1 ≡ (j : ℕ) [MOD p] := by
      have h1 := finRotate_val_mod ((finRotate p).symm j)
      rw [Equiv.apply_symm_apply] at h1
      unfold Nat.ModEq
      rw [← h1, Nat.mod_eq_of_lt j.isLt]
    have hmod : ((i : ℕ) + (i : ℕ) * (((finRotate p).symm j : Fin p) : ℕ)) % p =
        ((i : ℕ) * (j : ℕ)) % p := by
      have := Nat.ModEq.mul_left (i : ℕ) hk
      unfold Nat.ModEq at this
      rw [show (i : ℕ) + (i : ℕ) * (((finRotate p).symm j : Fin p) : ℕ) =
        (i : ℕ) * ((((finRotate p).symm j : Fin p) : ℕ) + 1) by ring, this]
    rw [← pow_add, pow_eq_pow_mod _ hζ, hmod, ← pow_eq_pow_mod _ hζ]
  · intro b _ hb
    rw [heisShiftMat_entry, if_neg (fun h' => hb (by rw [← h', Equiv.symm_apply_apply])),
      mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem heisShiftMat_three : heisShiftMat K 3 = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  rw [heisShiftMat_entry]
  fin_cases i <;> fin_cases j <;> simp [Fin.ext_iff, finRotate_val_mod]

theorem hS_eq_sq : (hS : Matrix (Fin 3) (Fin 3) K) = heisShiftMat K 3 * heisShiftMat K 3 := by
  rw [heisShiftMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, Matrix.mul_apply, Fin.sum_univ_three]

theorem heisShiftMat_three_cube :
    heisShiftMat K 3 * heisShiftMat K 3 * heisShiftMat K 3 = 1 := by
  rw [heisShiftMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem hD_eq (ω : K) : hD ω = heisDiagMat (p := 3) ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hD, heisDiagMat, Matrix.diagonal_apply]

theorem hD_mul_hS_mul_hS (ω : K) : hD ω * hS * hS = heisDiagMat (p := 3) ω * heisShiftMat K 3 := by
  rw [hD_eq, hS_eq_sq]
  calc heisDiagMat ω * (heisShiftMat K 3 * heisShiftMat K 3) *
        (heisShiftMat K 3 * heisShiftMat K 3) =
      heisDiagMat ω * ((heisShiftMat K 3 * heisShiftMat K 3 * heisShiftMat K 3) *
        heisShiftMat K 3) := by simp only [Matrix.mul_assoc]
    _ = heisDiagMat ω * heisShiftMat K 3 := by rw [heisShiftMat_three_cube, Matrix.one_mul]

theorem heisDiagMat_mul_heisFourierMat_three {ζ : K} (hζ : ζ ^ 3 = 1) :
    heisDiagMat ζ * heisFourierMat ζ =
      heisFourierMat (p := 3) ζ * (heisShiftMat K 3 * heisShiftMat K 3) := by
  have h1 := heisDiagMat_mul_heisFourierMat_mul_heisShiftMat (p := 3) hζ
  calc heisDiagMat ζ * heisFourierMat ζ
      = heisDiagMat ζ * heisFourierMat ζ *
          (heisShiftMat K 3 * heisShiftMat K 3 * heisShiftMat K 3) := by
        rw [heisShiftMat_three_cube, Matrix.mul_one]
    _ = heisDiagMat ζ * heisFourierMat ζ * heisShiftMat K 3 *
          (heisShiftMat K 3 * heisShiftMat K 3) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]

theorem diag_mul_shift_sq_three {ζ : K} (hζ : ζ ^ 3 = 1) :
    diagonal ![1, ζ, 1] * (heisShiftMat K 3 * heisShiftMat K 3) =
      heisDiagMat ζ * (heisShiftMat K 3 * heisShiftMat K 3) * diagonal ![1, ζ, 1] := by
  rw [heisShiftMat_three, ← hD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
    first | rfl | linear_combination hζ | linear_combination -hζ

theorem diag_mul_shift_three {ζ : K} (hζ : ζ ^ 3 = 1) :
    diagonal ![1, 1, ζ ^ 2] * heisShiftMat K 3 =
      heisDiagMat ζ * heisShiftMat K 3 * diagonal ![1, 1, ζ ^ 2] := by
  rw [heisShiftMat_three, ← hD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
    first | rfl | linear_combination hζ | linear_combination -hζ

theorem conj_comm_smul_of_conj {n : ℕ} (N A B g : GL (Fin n) K) (hNA : N * A * N⁻¹ = B) {c : K}
    (hG : (g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      c • ((B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K))) :
    ((N⁻¹ * g * N : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      c • ((A : Matrix (Fin n) (Fin n) K) *
        ((N⁻¹ * g * N : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hA : A = N⁻¹ * B * N := by rw [← hNA]; group
  have h1 : (N : Matrix (Fin n) (Fin n) K) * ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA]
  simp only [Units.val_mul]
  calc ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
        (N : Matrix (Fin n) (Fin n) K) * (((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K))
      = ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *
          (N : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (N : Matrix (Fin n) (Fin n) K), h1, Matrix.one_mul]
    _ = ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (c • ((B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K))) *
          (N : Matrix (Fin n) (Fin n) K) := by rw [hG]
    _ = _ := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (N : Matrix (Fin n) (Fin n) K), h1, Matrix.one_mul]

theorem map_mem_heisLines {k : Subfield K} {ω : k} {M : Matrix (Fin 3) (Fin 3) k}
    (hM : M ∈ heisLines ω) : M.map k.subtype ∈ heisLines (ω : K) := by
  have hDm : (hD ω).map k.subtype = hD (ω : K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD]
  have hSm : (hS : Matrix (Fin 3) (Fin 3) k).map k.subtype = hS := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS]
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM ⊢
  rcases hM with rfl | rfl | rfl | rfl
  · exact Or.inl hDm
  · exact Or.inr (Or.inl hSm)
  · exact Or.inr (Or.inr (Or.inl (by rw [Matrix.map_mul, hDm, hSm])))
  · exact Or.inr (Or.inr (Or.inr (by rw [Matrix.map_mul, Matrix.map_mul, hDm, hSm])))

theorem mk_heisLine_mem_closure (h : UnitaryFieldData ℓ f K) (hodd : Odd 3) (hq3 : 3 < ℓ ^ f)
    (hpq : 3 ∣ ℓ ^ f + 1) {E : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3) {σ : K ≃+* K}
    (hσD : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ ∉ primeFormD h (idGram K 3))
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ ∈ E)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (hζN : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E)
    (hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 → ∃ c : K, c ^ 3 = y ∧ h.bar c * c = 1)
    {lam : K} (hlam0 : lam ≠ 0) (hlamσ : σ lam = lam)
    (hlamN : h.bar lam * lam * ((3 : ℕ) : K) = 1)
    {g : gramSU h (idGram K 3)} (hgσ : glAut σ (g : GL (Fin 3) K) = g)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : M ∈ heisLines ζ) {c : K}
    (hgM : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :
    (g : primeFormP h (idGram K 3)) ∈ Subgroup.closure (hyperLiftSet 3 E) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  set Su := shiftU h hodd with hSu
  set Du := diagU h hζ3 hζN hodd with hDu
  set κ := primeFormConjHom h (idGram K 3) with hκ
  have hΦ'det : (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hlam0) (det_heisFourierMat_ne_zero hζ)
  have hΦunit : ((lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
      (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) = 1 := by
    have h1 := CFSG.LieType.SeitzGeneration.ug81_fourier_unitary h hpq hζ
    have h2 : ((lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
        (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) =
        (h.bar lam * lam * ((3 : ℕ) : K)) • 1 := by
      rw [Matrix.map_smul' _ _ _ (fun a b => map_mul h.bar a b), Matrix.transpose_smul,
        Matrix.smul_mul, Matrix.mul_smul, h1, smul_smul, smul_smul]
    rw [h2, hlamN, one_smul]
  let ΦG : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hΦ'det
  have hΦU : ΦG ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact hΦunit
  set ΦU : primeFormUnitary h (idGram K 3) := ⟨ΦG, hΦU⟩ with hΦUdef
  have hΦσ : glAut σ ΦG = ΦG := by
    apply Units.ext
    rw [coe_glAut]
    change (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)).map σ =
      lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, heisFourierMat, Matrix.of_apply]
    rw [map_mul, map_pow, hζσ, hlamσ]
  have hb2 : h.bar (ζ ^ 2) * ζ ^ 2 = 1 := by rw [map_pow, ← mul_pow, hζN, one_pow]
  have hN₂det : (diagonal ![1, ζ, 1] : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [hζ0]
  have hN₃det : (diagonal ![1, 1, ζ ^ 2] : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [hζ0]
  let N₂G : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hN₂det
  let N₃G : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hN₃det
  have hN₂U : N₂G ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    change ((diagonal ![1, ζ, 1] : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      diagonal ![1, ζ, 1] = 1
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hζN]
  have hN₃U : N₃G ∈ primeFormUnitary h (idGram K 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    change ((diagonal ![1, 1, ζ ^ 2] : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      diagonal ![1, 1, ζ ^ 2] = 1
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp
    · simp
    · exact hb2
  set N₂U : primeFormUnitary h (idGram K 3) := ⟨N₂G, hN₂U⟩ with hN₂Udef
  set N₃U : primeFormUnitary h (idGram K 3) := ⟨N₃G, hN₃U⟩ with hN₃Udef
  have hN₂σ : glAut σ N₂G = N₂G := by
    apply Units.ext
    rw [coe_glAut]
    change (diagonal ![1, ζ, 1] : Matrix (Fin 3) (Fin 3) K).map σ = diagonal ![1, ζ, 1]
    rw [diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp [hζσ]
  have hN₃σ : glAut σ N₃G = N₃G := by
    apply Units.ext
    rw [coe_glAut]
    change (diagonal ![1, 1, ζ ^ 2] : Matrix (Fin 3) (Fin 3) K).map σ = diagonal ![1, 1, ζ ^ 2]
    rw [diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> simp [hζσ]
  have hG1 : Su * ΦU = ΦU * Du := by
    apply Subtype.ext
    apply Units.ext
    change heisShiftMat K 3 * (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) =
      (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) * heisDiagMat ζ
    rw [Matrix.mul_smul, heisShiftMat_mul_heisFourierMat hζ3, Matrix.smul_mul]
    rfl
  have hG2 : Du * ΦU = ΦU * (Su * Su) := by
    apply Subtype.ext
    apply Units.ext
    change heisDiagMat ζ * (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) =
      (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) *
        (heisShiftMat K 3 * heisShiftMat K 3)
    rw [Matrix.mul_smul, heisDiagMat_mul_heisFourierMat_three hζ3, Matrix.smul_mul]
  have hG3 : Du * ΦU * Su = ΦU := by
    apply Subtype.ext
    apply Units.ext
    change heisDiagMat ζ * (lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)) *
      heisShiftMat K 3 = lam • (heisFourierMat ζ : Matrix (Fin 3) (Fin 3) K)
    rw [Matrix.mul_smul, Matrix.smul_mul, heisDiagMat_mul_heisFourierMat_mul_heisShiftMat hζ3]
  have hG4 : N₂U * (Su * Su) = Du * (Su * Su) * N₂U := by
    apply Subtype.ext
    apply Units.ext
    exact diag_mul_shift_sq_three hζ3
  have hG5 : N₃U * Su = Du * Su * N₃U := by
    apply Subtype.ext
    apply Units.ext
    exact diag_mul_shift_three hζ3
  have hG6 : N₂U * Du = Du * N₂U := by
    apply Subtype.ext
    apply Units.ext
    change diagonal ![1, ζ, 1] * heisDiagMat ζ = heisDiagMat ζ * diagonal ![1, ζ, 1]
    rw [heisDiagMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hG7 : N₃U * Du = Du * N₃U := by
    apply Subtype.ext
    apply Units.ext
    change diagonal ![1, 1, ζ ^ 2] * heisDiagMat ζ = heisDiagMat ζ * diagonal ![1, 1, ζ ^ 2]
    rw [heisDiagMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  ·
    rw [hD_eq] at hgM
    exact mk_projCentD_mem_closure h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hS hD hroot hlam0
      hlamσ hlamN hgσ hgM
  ·
    have hU1 : ΦU⁻¹ * Su * ΦU⁻¹⁻¹ = Du := by
      rw [inv_inv, mul_assoc, hG1, ← mul_assoc, inv_mul_cancel, one_mul]
    have hU2 : ΦU⁻¹ * Du * ΦU⁻¹⁻¹ = Su * Su := by
      rw [inv_inv, mul_assoc, hG2, ← mul_assoc, inv_mul_cancel, one_mul]
    have hNA : ((ΦU⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) * (Du : GL (Fin 3) K) *
        ((ΦU⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K)⁻¹ =
        ((Su * Su : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) := congrArg Subtype.val hU2
    rw [hS_eq_sq] at hgM
    refine mk_mem_closure_of_conj_projCentD h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hroot hlam0
      hlamσ hlamN ΦU⁻¹ ?_ (by rw [hU1]; exact hD) (by rw [hU2, map_mul]; exact mul_mem hS hS) hgσ
      (conj_comm_smul_of_conj _ (Du : GL (Fin 3) K) _ _ hNA hgM)
    change glAut σ ΦG⁻¹ = ΦG⁻¹
    rw [map_inv, hΦσ]
  ·
    have hV1 : N₂U * ΦU⁻¹ * Su * (N₂U * ΦU⁻¹)⁻¹ = Du := by
      calc N₂U * ΦU⁻¹ * Su * (N₂U * ΦU⁻¹)⁻¹ = N₂U * (ΦU⁻¹ * (Su * ΦU)) * N₂U⁻¹ := by group
        _ = Du := by
          rw [hG1, ← mul_assoc ΦU⁻¹, inv_mul_cancel, one_mul, hG6, mul_inv_cancel_right]
    have hV2 : N₂U * ΦU⁻¹ * Du * (N₂U * ΦU⁻¹)⁻¹ = Du * (Su * Su) := by
      calc N₂U * ΦU⁻¹ * Du * (N₂U * ΦU⁻¹)⁻¹ = N₂U * (ΦU⁻¹ * (Du * ΦU)) * N₂U⁻¹ := by group
        _ = N₂U * (Su * Su) * N₂U⁻¹ := by rw [hG2, ← mul_assoc ΦU⁻¹, inv_mul_cancel, one_mul]
        _ = Du * (Su * Su) := by rw [hG4, mul_inv_cancel_right]
    have hNA : ((N₂U * ΦU⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) *
        (Du : GL (Fin 3) K) *
        ((N₂U * ΦU⁻¹ : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K)⁻¹ =
        ((Du * (Su * Su) : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) :=
      congrArg Subtype.val hV2
    rw [hD_eq, hS_eq_sq] at hgM
    refine mk_mem_closure_of_conj_projCentD h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hroot hlam0
      hlamσ hlamN (N₂U * ΦU⁻¹) ?_ (by rw [hV1]; exact hD)
      (by rw [hV2, map_mul, map_mul]; exact mul_mem hD (mul_mem hS hS)) hgσ
      (conj_comm_smul_of_conj _ (Du : GL (Fin 3) K) _ _ hNA hgM)
    change glAut σ (N₂G * ΦG⁻¹) = N₂G * ΦG⁻¹
    rw [map_mul, map_inv, hN₂σ, hΦσ]
  ·
    have hW0 : ΦU * Su * ΦU⁻¹ = Du⁻¹ := by
      calc ΦU * Su * ΦU⁻¹ = Du⁻¹ * (Du * ΦU * Su) * ΦU⁻¹ := by group
        _ = Du⁻¹ := by rw [hG3, mul_inv_cancel_right]
    have hW0' : ΦU * Du * ΦU⁻¹ = Su := by rw [← hG1, mul_inv_cancel_right]
    have h7 : N₃U * Du * N₃U⁻¹ = Du := by rw [hG7, mul_inv_cancel_right]
    have hW1 : N₃U * ΦU * Su * (N₃U * ΦU)⁻¹ = Du⁻¹ := by
      calc N₃U * ΦU * Su * (N₃U * ΦU)⁻¹ = N₃U * (ΦU * Su * ΦU⁻¹) * N₃U⁻¹ := by group
        _ = (N₃U * Du * N₃U⁻¹)⁻¹ := by rw [hW0]; group
        _ = Du⁻¹ := by rw [h7]
    have hW2 : N₃U * ΦU * Du * (N₃U * ΦU)⁻¹ = Du * Su := by
      calc N₃U * ΦU * Du * (N₃U * ΦU)⁻¹ = N₃U * (ΦU * Du * ΦU⁻¹) * N₃U⁻¹ := by group
        _ = N₃U * Su * N₃U⁻¹ := by rw [hW0']
        _ = Du * Su := by rw [hG5, mul_inv_cancel_right]
    have hNA : ((N₃U * ΦU : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) *
        (Du : GL (Fin 3) K) *
        ((N₃U * ΦU : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K)⁻¹ =
        ((Du * Su : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) :=
      congrArg Subtype.val hW2
    rw [hD_mul_hS_mul_hS] at hgM
    refine mk_mem_closure_of_conj_projCentD h hp hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hroot hlam0
      hlamσ hlamN (N₃U * ΦU) ?_ (by rw [hW1, map_inv]; exact inv_mem hD)
      (by rw [hW2, map_mul]; exact mul_mem hD hS) hgσ
      (conj_comm_smul_of_conj _ (Du : GL (Fin 3) K) _ _ hNA hgM)
    change glAut σ (N₃G * ΦG) = N₃G * ΦG
    rw [map_mul, hN₃σ, hΦσ]

theorem map_suSub_le_closure_three (hcore : UnitaryHeisCore) (h : UnitaryFieldData ℓ f K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p = 3) (hodd : Odd p) (hpq : p ∣ ℓ ^ f + 1)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hq₀ : ℓ ^ (f / p) ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hζN : h.bar ζ * ζ = 1) (hζσ : σ ζ = ζ) {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E)
    (hS : primeFormConjHom h _ (shiftU h hodd) ∈ E)
    (hD : primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E) :
    (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) p).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)) p)) ≤ Subgroup.closure (hyperLiftSet p E) := by
  classical
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hfin : Finite K := h.finite
  set k : Subfield K := fixSubfield σ with hkdef
  set h₀ : UnitaryFieldData ℓ (f / 3) k := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  set e := f / 3 with he
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hfe : f = 3 * e := (Nat.mul_div_cancel' hpf).symm
  have hℓ := h.prime
  have hq₀1 : 1 < ℓ ^ e := h₀.one_lt_pow
  have hqq : ℓ ^ f = (ℓ ^ e) ^ 3 := by rw [hfe, pow_mul']
  have hq3 : 3 < ℓ ^ f := by
    rw [hqq]
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ (ℓ ^ e) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (ℓ ^ e) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpq₀ : 3 ∣ ℓ ^ e + 1 := by
    have h1 : (((ℓ ^ e) ^ 3 + 1 : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ 3).2 (by rw [← hqq]; exact hpq)
    push_cast at h1
    rw [ZMod.pow_card] at h1
    exact (ZMod.natCast_eq_zero_iff _ 3).1 (by push_cast; exact h1)
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hισ : primeFormFieldFactor h hC le_rfl hne (primeFormFieldHom h hC σ) = σ := by
    have := primeFormFieldFactor_apply h hC le_rfl hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ ∉ primeFormD h (idGram K 3) := by
    rw [← ker_primeFormFieldFactor h hC le_rfl hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  have hroot : ∀ y : K, y ≠ 0 → σ y = y → h.bar y * y = 1 →
      ∃ c : K, c ^ 3 = y ∧ h.bar c * c = 1 := fun y _ hyσ hyN =>
    exists_pow_eq_of_fixed_norm h hp hp2 hpq hσ hq₀ hyσ hyN
  have hpℓ : 3 ≠ ℓ := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    have h2 : 3 ∣ 1 := (Nat.dvd_add_right h1).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hfink : Finite k := h₀.finite
  haveI : CharP k ℓ := h₀.charP
  have hpk : ((3 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff k ℓ 3).1 h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 this).symm
  have hpinv : (((3 : ℕ) : k)⁻¹) ∈ h₀.fixedField := by
    rw [h₀.mem_fixedField, map_inv₀, map_natCast]
  obtain ⟨lam₀, hlam₀⟩ := h₀.normHom_surjective ⟨((3 : ℕ) : k)⁻¹, hpinv⟩
  have hlamN₀ : h₀.norm lam₀ = ((3 : ℕ) : k)⁻¹ := congrArg Subtype.val hlam₀
  have hlam₀0 : lam₀ ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hlamN₀
    exact inv_ne_zero hpk hlamN₀.symm
  have hlamN : h.bar (lam₀ : K) * (lam₀ : K) * ((3 : ℕ) : K) = 1 := by
    have hpK : (((3 : ℕ) : k) : K) = ((3 : ℕ) : K) := map_natCast k.subtype 3
    rw [← hbar, ← Subfield.coe_mul, mul_comm (h₀.bar lam₀), ← UnitaryFieldData.norm, hlamN₀,
      Subfield.coe_inv, hpK]
    exact inv_mul_cancel₀ (by rw [← hpK]; exact_mod_cast hpk)
  set ζk : k := ⟨ζ, hζσ⟩ with hζk
  have hζk' : IsPrimitiveRoot ζk 3 :=
    (IsPrimitiveRoot.map_iff_of_injective (f := k.subtype) Subtype.val_injective).1 hζ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let incl : unitarySU ℓ e k 3 →*
      gramSU h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h₀ 3))
  set Q := QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)) 3) with hQ
  let Γ : unitarySU ℓ e k 3 →* primeFormP h (idGram K 3) :=
    Q.comp ((subfieldSU h h₀ hbar 3).comp incl)
  have hcl := hcore ℓ e k h₀ hpq₀ hq₀ ζk hζk'
  have htop : (Subgroup.closure (hyperLiftSet 3 E)).comap Γ = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨M, hM, c, hgM⟩
    have hGσ : glAut σ (((subfieldSU h h₀ hbar 3 (incl g) : gramSU h _) : GL (Fin 3) K)) =
        ((subfieldSU h h₀ hbar 3 (incl g) : gramSU h _) : GL (Fin 3) K) :=
      glAut_subfieldGL σ 3 _
    have hGc : (((subfieldSU h h₀ hbar 3 (incl g) : gramSU h _) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map k.subtype :=
      rfl
    have hGM : (((subfieldSU h h₀ hbar 3 (incl g) : gramSU h _) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * M.map k.subtype = (c : K) • (M.map k.subtype *
          (((subfieldSU h h₀ hbar 3 (incl g) : gramSU h _) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) := by
      rw [hGc, ← Matrix.map_mul, hgM, ← Matrix.map_mul]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
    exact mk_heisLine_mem_closure h hodd hq3 hpq hE hc hσD hσE hζ hζN hζσ hS hD hroot
      (by exact_mod_cast hlam₀0) lam₀.2 hlamN hGσ (map_mem_heisLines hM) hGM
  rintro _ ⟨y, ⟨y', rfl⟩, rfl⟩
  have hy'U : (y' : GL (Fin 3) k) ∈ unitarySU ℓ e k 3 := by
    rw [unitarySU_eq_gramSU h₀ 3]
    exact y'.2
  have hmem : (⟨y', hy'U⟩ : unitarySU ℓ e k 3) ∈ (Subgroup.closure (hyperLiftSet 3 E)).comap Γ := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

end StdU

@[expose] def UFieldSplit {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ (ℓ f n : ℕ) (Kf : Type) (_ : Field Kf) (h : UnitaryFieldData ℓ f Kf)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf (n + 1))) (σ : Kf ≃+* Kf),
    2 ≤ n ∧ p ∣ ℓ ^ f + 1 ∧ ℓ ^ (f / p) ≠ 2 ∧ orderOf σ = p ∧
    primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ ∈ E.map (modelAut θ) ∧
    (∀ y ∈ E.map (modelAut θ), y ∈ primeFormD h (idGram Kf (n + 1)) →
      ∃ x : primeFormUnitary h (idGram Kf (n + 1)), primeFormConjHom h _ x = y ∧
        glAut σ (x : GL (Fin (n + 1)) Kf) = x) ∧
    (∀ x y : primeFormUnitary h (idGram Kf (n + 1)),
      glAut σ (x : GL (Fin (n + 1)) Kf) = x → glAut σ (y : GL (Fin (n + 1)) Kf) = y →
      primeFormConjHom h _ x ∈ E.map (modelAut θ) →
      primeFormConjHom h _ y ∈ E.map (modelAut θ) → x * y = y * x) ∧
    ∀ x : primeFormUnitary h (idGram Kf (n + 1)), glAut σ (x : GL (Fin (n + 1)) Kf) = x →
      primeFormConjHom h _ x ∈ E.map (modelAut θ) → x ^ (ℓ ^ (f / p) + 1) = 1

theorem seitzHyperGamma_eq_top_of_uFieldSplit {K : Type} [Group K]
    [Finite K] (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hU : UFieldSplit p E) : seitzHyperGamma p E = ⊤ := by
  obtain ⟨ℓ, f, n, Kf, _, h, θ, σ, hn, hpq, hq₀, hσ, hσE, hlift, hcomm, hpow⟩ := hU
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := modelAut_injective hperf θ
  have hE' : IsElemAbelian p (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hc' : Nat.card (E.map (modelAut θ)) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  exact seitzHyperGamma_eq_top_of_closure_hyperLiftSet_model hperf (isPGroup_of_isElemAbelian hE)
    θ (closure_hyperLiftSet_eq_top_of_split h hn hp hp2 hpq hσ hq₀ hE' hc' hσE hlift hcomm hpow)

@[expose] def UFieldStd {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ (ℓ f : ℕ) (Kf : Type) (_ : Field Kf) (h : UnitaryFieldData ℓ f Kf)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf p)) (σ : Kf ≃+* Kf) (ζ : Kf)
    (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (hodd : Odd p),
    p ∣ ℓ ^ f + 1 ∧ ℓ ^ (f / p) ≠ 2 ∧ orderOf σ = p ∧ σ ζ = ζ ∧
    primeFormFieldHom h (isPrimeFormGram_one (n := p)) σ ∈ E.map (modelAut θ) ∧
    primeFormConjHom h _ (shiftU h hodd) ∈ E.map (modelAut θ) ∧
    primeFormConjHom h _ (diagU h hζ.pow_eq_one hζN hodd) ∈ E.map (modelAut θ)

theorem seitzHyperGamma_eq_top_of_uFieldStd
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hU : UFieldStd p E) : seitzHyperGamma p E = ⊤ := by
  obtain ⟨ℓ, f, Kf, _, h, θ, σ, ζ, hζ, hζN, hodd, hpq, hq₀, hσ, hζσ, hσE, hSE, hDE⟩ := hU
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := modelAut_injective hperf θ
  have hE' : IsElemAbelian p (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hc' : Nat.card (E.map (modelAut θ)) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hsub : (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ)
      (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) p).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin p) Kf) :
        Matrix (Fin p) (Fin p) Kf)) p)) ≤
        Subgroup.closure (hyperLiftSet p (E.map (modelAut θ))) := by
    by_cases hp3 : p = 3
    · exact map_suSub_le_closure_three unitaryHeisCore h hp hp2 hp3 hodd hpq hσ hq₀ hζ hζN hζσ hE'
        hc' hσE hSE hDE
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h1 := Nat.odd_iff.1 hodd
        have h4 : p ≠ 4 := by
          rintro rfl
          norm_num at h1
        omega
      have hpq₀ : p ∣ ℓ ^ (f / p) + 1 := by
        obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
        have hqq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by
          rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hpf]
        have h1 : (((ℓ ^ (f / p)) ^ p + 1 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ p).2 (by rw [← hqq]; exact hpq)
        push_cast at h1
        rw [ZMod.pow_card] at h1
        exact (ZMod.natCast_eq_zero_iff _ p).1 (by push_cast; exact h1)
      have hgen := torusFourierGenU_of_prime (fixSubfield_unitaryFieldData h hp hp2 hσ) hp5 hpq₀
      exact map_suSub_le_closure_of_torusGen h hp hp2 hodd hpq hσ hq₀ hζ hζN hζσ hE' hc' hσE
        hSE hDE hgen
  exact seitzHyperGamma_eq_top_of_closure_hyperLiftSet_model hperf (isPGroup_of_isElemAbelian hE)
    θ (closure_hyperLiftSet_eq_top_of_std_of_sub h hp hp2 hodd hpq hσ hq₀ hζ hζN hE' hc' hσE hSE
      hDE hsub)

end CFSG.LieType.SeitzGeneration.QuasiHigh4
