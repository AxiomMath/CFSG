module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8Cent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8Abs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem apply_mem_range_subfieldPSU (h : UnitaryFieldData ℓ f K) (hq : ¬(3 = 3 ∧ ℓ ^ f = 2))
    {σ : K ≃+* K} {e : ℕ} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (Y : primeFormUnitary h (idGram K 3))
    (hcomm : primeFormConjHom h (idGram K 3) Y * primeFormFieldHom h isPrimeFormGram_one σ =
      primeFormFieldHom h isPrimeFormGram_one σ * primeFormConjHom h (idGram K 3) Y)
    {t : primeFormP h (idGram K 3)} (ht : t ∈ (subfieldPSU h h₀ hbar 3).range) :
    primeFormConjHom h (idGram K 3) Y t ∈ (subfieldPSU h h₀ hbar 3).range := by
  have hn : 3 ≤ 3 := le_rfl
  have h1 : primeFormConjHom h (idGram K 3) (primeFormFieldU h isPrimeFormGram_one σ Y) =
      primeFormConjHom h (idGram K 3) Y :=
    (primeFormField_conj_eq h isPrimeFormGram_one σ Y).symm.trans
      (mul_inv_eq_iff_eq_mul.2 hcomm.symm)
  have hz : primeFormConjHom h (idGram K 3)
      (Y⁻¹ * primeFormFieldU h isPrimeFormGram_one σ Y) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp hz
  have hσY : glAut σ (Y : GL (Fin 3) K) = (Y : GL (Fin 3) K) *
      GeneralLinearGroup.scalar (Fin 3) z := by
    have h2 : ((Y : GL (Fin 3) K))⁻¹ * glAut σ (Y : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) z := by
      simpa [coe_primeFormFieldU h isPrimeFormGram_one σ Y] using hz
    rwa [inv_mul_eq_iff_eq_mul] at h2
  obtain ⟨s, rfl⟩ := ht
  induction s using QuotientGroup.induction_on with
  | H s₀ =>
    set s : GL (Fin 3) K := subfieldGL (fixSubfield σ) 3
      (s₀ : GL (Fin 3) (fixSubfield σ)) with hs
    have hsmem : s ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      subfieldGL_mem_gramSU h h₀ hbar 3 s₀.2
    have hσs : glAut σ s = s := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [coe_glAut, Matrix.map_apply, hs, coe_subfieldGL, Matrix.map_apply]
      exact (((s₀ : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) i j).2
    set M : GL (Fin 3) K := (Y : GL (Fin 3) K) * s * (Y : GL (Fin 3) K)⁻¹ with hM
    have hmem : M ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      conj_mem_gramSU h _ Y.2 hsmem
    have hfix : glAut σ M = M := by
      rw [hM, map_mul, map_mul, map_inv, hσY, hσs]
      have hcs : GeneralLinearGroup.scalar (Fin 3) z * s * (GeneralLinearGroup.scalar (Fin 3) z)⁻¹ =
          s := by
        rw [Matrix.GeneralLinearGroup.scalar_commute z s, mul_assoc, mul_inv_cancel, mul_one]
      calc (Y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) z * s *
            ((Y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) z)⁻¹
          = (Y : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) z * s *
              (GeneralLinearGroup.scalar (Fin 3) z)⁻¹) * (Y : GL (Fin 3) K)⁻¹ := by group
        _ = (Y : GL (Fin 3) K) * s * (Y : GL (Fin 3) K)⁻¹ := by rw [hcs]
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed 3 hfix
    have hg₀SU := mem_gramSU_of_subfieldGL h 3 h₀ hbar (hg₀ ▸ hmem)
    refine ⟨((⟨g₀, hg₀SU⟩ : gramSU h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ))) : primeFormP h₀ _), ?_⟩
    rw [subfieldPSU_mk, subfieldPSU_mk, primeFormConjHom_mk]
    congr 1
    exact Subtype.ext hg₀

theorem exists_cube_root_of_card_four {L : Type} [Field L] (h₀ : UnitaryFieldData 2 1 L) :
    ∃ ω : Lˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hfin : Finite L := h₀.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Lˣ = 3 := by
    rw [Nat.card_units, h₀.card]
    norm_num
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) 3 (by rw [hcard])
  refine ⟨ω, ?_, ?_⟩
  · have := pow_orderOf_eq_one ω
    rwa [hω] at this
  · intro h1
    rw [h1, orderOf_one] at hω
    omega

theorem hO_range (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData 2 1 (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) (R : Subgroup (primeFormP h (idGram K 3)))
    (hRT : R ≤ (subfieldPSU h h₀ hbar 3).range)
    (hRn : ∀ t ∈ (subfieldPSU h h₀ hbar 3).range, ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hR3 : ∀ r ∈ R, Nat.Coprime 3 (orderOf r)) : R = ⊥ := by
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_card_four h₀
  have hinj := subfieldPSU_injective h h₀ hbar 3 (by norm_num)
  have : (R.comap (subfieldPSU h h₀ hbar 3)).Normal :=
    ⟨fun r hr s => by
      rw [Subgroup.mem_comap] at hr ⊢
      rw [map_mul, map_mul, map_inv]
      exact hRn _ ⟨s, rfl⟩ _ hr⟩
  have h1 := eq_bot_of_normal_coprime h₀ ω hω3 hω1 (R.comap (subfieldPSU h h₀ hbar 3))
    (fun r hr => by
      rw [Subgroup.mem_comap] at hr
      have := hR3 _ hr
      rwa [orderOf_injective (subfieldPSU h h₀ hbar 3) hinj r] at this)
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨r₀, rfl⟩ := hRT hr
  have : r₀ ∈ R.comap (subfieldPSU h h₀ hbar 3) := hr
  rw [h1, Subgroup.mem_bot] at this
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem eq_one_of_fixes_range (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData 2 1 (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    {g : MulAut (primeFormP h (idGram K 3))} (hg3 : Nat.Coprime 3 (orderOf g))
    (hfix : ∀ t ∈ (subfieldPSU h h₀ hbar 3).range, g t = t) : g = 1 := by
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_card_four h₀
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by decide
  have : Finite K := h.finite
  set sA := subfieldSU h h₀ hbar 3 (sX h₀ ω hω3) with hsA
  set sB := subfieldSU h h₀ hbar 3 (sP h₀) with hsB
  set A : primeFormUnitary h (idGram K 3) := ⟨sA, sA.2.1⟩ with hA
  set B : primeFormUnitary h (idGram K 3) := ⟨sB, sB.2.1⟩ with hB
  set cK : Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom ω with hcK
  have hc3 : cK ^ 3 = 1 := by rw [hcK, ← map_pow, hω3, map_one]
  have hc1 : cK ≠ 1 := by
    intro h'
    apply hω1
    apply Units.ext
    apply Subtype.val_injective
    have := congrArg Units.val h'
    simpa [hcK] using this
  have hAB : (A : GL (Fin 3) K) * B = B * A * GeneralLinearGroup.scalar (Fin 3) cK := by
    have := congrArg (subfieldGL (fixSubfield σ) 3) (Xg_mul_Pg ω hω3)
    rw [map_mul, map_mul, map_mul, subfieldGL_scalar] at this
    exact this
  have hA3 : primeFormConjHom h (idGram K 3) A ^ 3 = 1 := by
    rw [← map_pow]
    have : A ^ 3 = 1 := Subtype.ext (by
      change (subfieldGL (fixSubfield σ) 3 (Xg ω)) ^ 3 = 1
      rw [← map_pow, Xg_pow_three ω hω3, map_one])
    rw [this, map_one]
  have hB3 : primeFormConjHom h (idGram K 3) B ^ 3 = 1 := by
    rw [← map_pow]
    have : B ^ 3 = 1 := Subtype.ext (by
      change (subfieldGL (fixSubfield σ) 3 Pg) ^ 3 = 1
      rw [← map_pow, Pg_pow_three, map_one])
    rw [this, map_one]
  have hρA : primeFormConjHom h (idGram K 3) A = MulAut.conj (sA : primeFormP h (idGram K 3)) :=
    primeFormConjHom_eq_conj h (idGram K 3) sA
  have hρB : primeFormConjHom h (idGram K 3) B = MulAut.conj (sB : primeFormP h (idGram K 3)) :=
    primeFormConjHom_eq_conj h (idGram K 3) sB
  have haK : (sA : primeFormP h (idGram K 3)) = subfieldPSU h h₀ hbar 3 (aE h₀ ω hω3) := rfl
  have hbK : (sB : primeFormP h (idGram K 3)) = subfieldPSU h h₀ hbar 3 (bE h₀) := rfl
  have hρ : primeFormConjHom h (idGram K 3) A * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) A := by
    rw [hρA, hρB, ← map_mul, ← map_mul, haK, hbK, ← map_mul, ← map_mul, ab_comm h₀ ω hω3]
  have hcomm : ∀ s : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      (s : primeFormP h (idGram K 3)) ∈ (subfieldPSU h h₀ hbar 3).range →
        g * MulAut.conj (s : primeFormP h (idGram K 3)) =
          MulAut.conj (s : primeFormP h (idGram K 3)) * g := by
    intro s hs
    have h1 := mul_conj_mul_inv_apply g (s : primeFormP h (idGram K 3))
    rw [hfix _ hs] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  exact eq_one_of_commute_heisenberg h hc3 hc1 hAB hA3 hB3 hρ
    (by rw [hρA]; exact hcomm sA ⟨aE h₀ ω hω3, rfl⟩)
    (by rw [hρB]; exact hcomm sB ⟨bE h₀, rfl⟩) hg3

theorem eq_one_of_q8 (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H)
    (hy : primeFormFieldHom h isPrimeFormGram_one σ ∈ D)
    {Y : primeFormUnitary h (idGram K 3)}
    (hY : primeFormConjHom h (idGram K 3) Y ∈ localDeltaIn 3 H D) :
    primeFormConjHom h (idGram K 3) Y = 1 := by
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by decide
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite K := h.finite
  let h₀ : UnitaryFieldData 2 1 (fixSubfield σ) := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set y := primeFormFieldHom h hC σ with hydef
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  have hy1 : y ≠ 1 := by
    intro h1
    exact hσ1 (primeFormFieldHom_injective h 3 hn hq (by rw [← hydef, h1, map_one]))
  have hg := le_core_of_mem_localDeltaIn hY hy hy1
  have hcomm := commute_of_mem_localDeltaIn hY hy
  have hcop := coprime_orderOf_of_mem_localDeltaIn hp hY hy hy1
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h hC hn hq
  have hσfix : ∀ c ∈ fixSubfield σ, σ c = c := fun c hc => hc
  have hfixT := apply_eq_of_mem_gLAPPrimeCoreOf hinj hH hg (subfieldPSU h h₀ hbar 3).range
    (fun t ht => primeFormFieldHom_apply_of_mem_range h 3 h₀ hbar hσfix ht)
    (fun t ht => apply_mem_range_subfieldPSU h hq h₀ hbar Y hcomm ht)
    (hO_range h h₀ hbar)
  exact eq_one_of_fixes_range h h₀ hbar hcop hfixT

theorem eq_one_of_q8_of_mem (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) {x : MulAut (primeFormP h (idGram K 3))}
    (hx : x ∈ D) {M : primeFormUnitary h (idGram K 3)}
    (hM : (primeFormConjHom h (idGram K 3) M)⁻¹ * x * primeFormConjHom h (idGram K 3) M =
      primeFormFieldHom h isPrimeFormGram_one σ)
    {Y : primeFormUnitary h (idGram K 3)}
    (hY : primeFormConjHom h (idGram K 3) Y ∈ localDeltaIn 3 H D) :
    primeFormConjHom h (idGram K 3) Y = 1 := by
  set c : MulAut (primeFormP h (idGram K 3)) := primeFormConjHom h (idGram K 3) M with hc
  let φ : MulAut (primeFormP h (idGram K 3)) ≃* MulAut (primeFormP h (idGram K 3)) :=
    MulAut.conj c⁻¹
  have hφ : ∀ a, φ a = c⁻¹ * a * c := fun a => by
    simp [φ]
  have hy' : primeFormFieldHom h isPrimeFormGram_one σ ∈ D.map φ.toMonoidHom :=
    Subgroup.mem_map.2 ⟨x, hx, by rw [MulEquiv.toMonoidHom_eq_coe]; simpa [hφ] using hM⟩
  have hH' : innerAut (primeFormP h (idGram K 3)) ≤ H.map φ.toMonoidHom := by
    intro z hz
    obtain ⟨g, rfl⟩ := hz
    refine Subgroup.mem_map.2 ⟨c * MulAut.conj g * c⁻¹, hH ⟨c g, ?_⟩, ?_⟩
    · exact (mul_conj_mul_inv_apply c g).symm
    · rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hφ]
      group
  have hρ : primeFormConjHom h (idGram K 3) (M⁻¹ * Y * M) = φ (primeFormConjHom h (idGram K 3) Y) := by
    rw [hφ, map_mul, map_mul, map_inv]
  have hY' : primeFormConjHom h (idGram K 3) (M⁻¹ * Y * M) ∈
      localDeltaIn 3 (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) := by
    rw [localDeltaIn_map_mulEquiv, hρ]
    exact Subgroup.mem_map.2 ⟨_, hY, rfl⟩
  have h1 := eq_one_of_q8 h hσ hH' hy' hY'
  rw [hρ] at h1
  exact φ.injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Solomon.Coordinator
