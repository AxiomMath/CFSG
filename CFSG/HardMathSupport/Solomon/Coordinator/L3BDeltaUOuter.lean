module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryContain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Lang.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_order_three_primeFormP {e : ℕ} {L : Type} [Field L] (h₀ : UnitaryFieldData ℓ e L) :
    ∃ s : gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L),
      s ^ 3 = 1 ∧ (s : primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) ≠ 1 := by
  let π : Equiv.Perm (Fin 3) := finRotate 3
  have hsign : Equiv.Perm.sign π = 1 := by simp [π]
  have hpow : (unitaryPermGL π : GL (Fin 3) L) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, coe_unitaryPermGL, pow_succ, pow_succ, pow_one,
      ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
    have : π * (π * π) = 1 := by decide
    rw [this, Matrix.permMatrix_one]
  have hmem := unitaryPermGL_mem_gramSU h₀ hsign
  refine ⟨⟨unitaryPermGL π, hmem⟩, Subtype.ext hpow, ?_⟩
  intro h1
  obtain ⟨c', -, -, hc'⟩ := (QuotientGroup.eq_one_iff _).mp h1
  change (unitaryPermGL π : GL (Fin 3) L) = GeneralLinearGroup.scalar (Fin 3) c' at hc'
  have e1 := congrArg (fun z : GL (Fin 3) L => (z : Matrix (Fin 3) (Fin 3) L) 0 1) hc'
  simp [coe_unitaryPermGL, π] at e1

theorem localDeltaIn_eq_bot_of_not_le_primeFormD_three (h : UnitaryFieldData ℓ f K)
    (hq : ¬(3 = 3 ∧ ℓ ^ f = 2)) (hq₀ : ¬(3 = 3 ∧ ℓ ^ (f / 3) = 2))
    {D : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hD : IsElemAbelian 3 D)
    (hDl : ¬ D ≤ primeFormD h (idGram K 3))
    {H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have hn : 3 ≤ 3 := le_rfl
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have := h.finite
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K 3)) := by unfold primeFormP; infer_instance
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
  set F := primeFormFieldFactor h hC hn hq with hF
  have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
  have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
  have hσ1 : F x ≠ 1 := fun h1 => hxl (by
    rw [← ker_primeFormFieldFactor h hC hn hq]
    exact h1)
  have hσ : orderOf (F x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hq hp hp2 x hxp (F x) rfl hσ
  set σ := F x with hσdef
  have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M with hc
  have hxy : x = c * primeFormFieldHom h isPrimeFormGram_one σ * c⁻¹ := by
    rw [← hM]
    group
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h hC hn hq
  set T₀ := (subfieldPSU h h₀ hbar 3).range with hT₀
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH hxD hx1 c
    (primeFormFieldHom h isPrimeFormGram_one σ) hxy T₀ (fun t ht => ?_)
    (fun k hk t ht => conj_mem_range_subfieldPSU h h₀ hbar hk ht)
    (isQuasisimple_range_subfieldPSU h h₀ hbar hn hq₀) ?_ ?_
  · exact range_subfieldPSU_le h 3 h₀ hbar ht
  · obtain ⟨s₀, hs₀p, hs₀1⟩ := exists_order_three_primeFormP h₀
    set t : T₀ := ⟨subfieldPSU h h₀ hbar 3 (s₀ : primeFormP h₀ _), ⟨_, rfl⟩⟩ with ht
    have htp : orderOf t = 3 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hs₀1 ?_
      · rw [Subgroup.coe_pow, ht, ← map_pow, ← QuotientGroup.mk_pow, hs₀p]
        exact map_one _
      · apply subfieldPSU_injective h h₀ hbar 3 (by omega)
        rw [map_one]
        exact congrArg Subtype.val h1
    have := orderOf_dvd_natCard t
    rwa [htp] at this
  · intro g hg hfixg
    obtain ⟨hfs, hzp, hcard⟩ := fixingSubgroup_range_subfieldPSU h 3 h₀ hbar hn hq hq₀
    have hgfix : g ∈ fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))) ((subfieldPSU h h₀ hbar 3).range :
          Set (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :=
      (mem_fixingSubgroup_iff _).2 fun t ht => by rw [MulAut.smul_def]; exact hfixg t ht
    rw [hfs, hzp] at hgfix
    have hdvd : orderOf g ∣ 3 := by
      have h3 : orderOf g ∣ orderOf σ := by
        rw [← hcard]
        exact (Subgroup.orderOf_dvd_natCard _ hgfix)
      rwa [hσ] at h3
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hg) (by rw [Nat.coprime_self]; exact hp.one_lt.ne')


end CFSG.HardMathSupport.Solomon.Coordinator
