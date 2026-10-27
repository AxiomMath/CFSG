module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagField
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Lang.Coordinator

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Subfield

variable (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} {e : ℕ}
  (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
  (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)

theorem conj_mem_range_subfieldPSU {k t : primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)}
    (hk : primeFormFieldHom h isPrimeFormGram_one σ k = k)
    (ht : t ∈ (subfieldPSU h h₀ hbar n).range) :
    k * t * k⁻¹ ∈ (subfieldPSU h h₀ hbar n).range := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  obtain ⟨y, rfl⟩ := ht
  obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hk' : ((primeFormFieldSU h isPrimeFormGram_one σ g :
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = (g : primeFormP h _) := by
    rw [← primeFormFieldAut_mk]
    exact hk
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.mp hk'
  have hσg : glAut σ (g : GL (Fin n) K) =
      (g : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by
    have h1 : (glAut σ (g : GL (Fin n) K))⁻¹ * (g : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc
    rw [← h1, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
  set s : GL (Fin n) K := subfieldGL (fixSubfield σ) n (s₀ : GL (Fin n) (fixSubfield σ)) with hs
  have hσs : glAut σ s = s := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_glAut, Matrix.map_apply, hs, coe_subfieldGL, Matrix.map_apply]
    exact (((s₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2
  have hfix : glAut σ ((g : GL (Fin n) K) * s * (g : GL (Fin n) K)⁻¹) =
      (g : GL (Fin n) K) * s * (g : GL (Fin n) K)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hσg, hσs]
    have hcs : (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * s * GeneralLinearGroup.scalar (Fin n) c =
        s := by
      rw [mul_assoc, (commute_scalar c s).eq, inv_mul_cancel_left]
    calc (g : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * s *
          ((g : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹)⁻¹
        = (g : GL (Fin n) K) * ((GeneralLinearGroup.scalar (Fin n) c)⁻¹ * s *
            GeneralLinearGroup.scalar (Fin n) c) * (g : GL (Fin n) K)⁻¹ := by group
      _ = (g : GL (Fin n) K) * s * (g : GL (Fin n) K)⁻¹ := by rw [hcs]
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hfix
  have hmem : (g : GL (Fin n) K) * s * (g : GL (Fin n) K)⁻¹ ∈
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    mul_mem (mul_mem g.2 (subfieldGL_mem_gramSU h h₀ hbar n s₀.2)) (inv_mem g.2)
  have hg₀SU := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ hmem)
  refine ⟨((⟨g₀, hg₀SU⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
  rw [subfieldPSU_mk, subfieldPSU_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hg₀

theorem isQuasisimple_range_subfieldPSU (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2)) :
    CFSG.IsQuasisimple (subfieldPSU h h₀ hbar n).range := by
  let φ := MonoidHom.ofInjective (subfieldPSU_injective h h₀ hbar n (by omega))
  have := isSimpleGroup_primeFormP_one h₀ hn hq₀
  have hs : IsSimpleGroup (subfieldPSU h h₀ hbar n).range := φ.symm.isSimpleGroup
  have hna := not_commute_primeFormP_one h₀ hn hq₀
  have hab : ∃ a b : (subfieldPSU h h₀ hbar n).range, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact hna fun x y => φ.injective (by rw [map_mul, map_mul, hc])
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hab).1

end Subfield

theorem dvd_pow_div_add_one {p : ℕ} (hp : p.Prime) (hpf : p ∣ f) (hpq : p ∣ ℓ ^ f + 1) :
    p ∣ ℓ ^ (f / p) + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  rw [← ZMod.natCast_eq_zero_iff] at hpq ⊢
  rw [hf] at hpq
  push_cast at hpq ⊢
  rwa [ZMod.pow_card] at hpq

theorem localDeltaIn_eq_bot_of_not_le_primeFormD (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2))
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hDl : ¬ D ≤ primeFormD h (idGram K n))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : innerAut (primeFormP h (idGram K n)) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
  set F := primeFormFieldFactor h hC hn hq with hF
  have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
  have hxp : orderOf x = p := orderOf_eq_prime (hD.2 x hxD) hx1
  have hσ1 : F x ≠ 1 := fun h1 => hxl (by
    rw [← ker_primeFormFieldFactor h hC hn hq]
    exact h1)
  have hσ : orderOf (F x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hq hp hp2 x hxp (F x) rfl hσ
  set σ := F x with hσdef
  have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hc
  have hxy : x = c * primeFormFieldHom h isPrimeFormGram_one σ * c⁻¹ := by
    rw [← hM]
    group
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h hC hn hq
  set T₀ := (subfieldPSU h h₀ hbar n).range with hT₀
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH hxD hx1 c
    (primeFormFieldHom h isPrimeFormGram_one σ) hxy T₀ (fun t ht => ?_)
    (fun k hk t ht => conj_mem_range_subfieldPSU h h₀ hbar hk ht)
    (isQuasisimple_range_subfieldPSU h h₀ hbar hn hq₀) ?_ ?_
  · exact range_subfieldPSU_le h n h₀ hbar ht
  ·
    have hp1 : p ∣ ℓ ^ (f / p) + 1 := dvd_pow_div_add_one hp hpf hpq
    have : Finite (fixSubfield σ) := h₀.finite
    have hcardu : p ∣ Nat.card (fixSubfield σ)ˣ := by
      rw [Nat.card_units, h₀.card, pow_mul, show (ℓ ^ 2) ^ (f / p) = (ℓ ^ (f / p)) ^ 2 by ring]
      have e2 : (ℓ ^ (f / p)) ^ 2 - 1 = (ℓ ^ (f / p) - 1) * (ℓ ^ (f / p) + 1) := by
        have : 1 ≤ ℓ ^ (f / p) := Nat.one_le_pow _ _ h.prime.pos
        zify [this, Nat.one_le_pow 2 (ℓ ^ (f / p)) (by omega)]
        ring
      rw [e2]
      exact Dvd.dvd.mul_left hp1 _
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (fixSubfield σ)ˣ) p hcardu
    have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
    have hζN : h₀.norm ((ζ : (fixSubfield σ)ˣ) : fixSubfield σ) = 1 := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
      obtain ⟨m, hm⟩ := hp1
      rw [hm, pow_mul, ← Units.val_pow_eq_pow_val, hζp, Units.val_one, one_pow]
    set i0 : Fin n := ⟨0, by omega⟩
    set i1 : Fin n := ⟨1, by omega⟩
    set i2 : Fin n := ⟨2, by omega⟩
    set d : Fin n → (fixSubfield σ)ˣ := Pi.mulSingle i0 ζ * Pi.mulSingle i1 ζ⁻¹ with hd
    obtain ⟨hdN, hdP⟩ := pairDiag_norm_prod h₀ hζN i0 i1
    have hs₀ := unitaryDiagGL_mem_gramSU h₀ hdN hdP
    set s₀ : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) := ⟨unitaryDiagGL d, hs₀⟩ with hs₀def
    have hd0 : d i0 = ζ := by
      simp [hd, i0, i1, Fin.ext_iff]
    have hd2 : d i2 = 1 := by
      simp [hd, i0, i1, i2, Fin.ext_iff]
    have hs₀p : s₀ ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hs₀def, coe_unitaryDiagGL,
        diagonal_pow, Subgroup.coe_one, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val]
      have : d ^ p = 1 := by
        rw [hd, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hζp, inv_pow, hζp, inv_one,
          Pi.mulSingle_one, Pi.mulSingle_one, mul_one]
      rw [← Pi.pow_apply, this, Pi.one_apply, Units.val_one]
    have hs₀1 : (s₀ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) ≠ 1 := by
      intro h1
      obtain ⟨c', -, -, hc'⟩ := (QuotientGroup.eq_one_iff _).mp h1
      have e0 := congrArg (fun z : GL (Fin n) (fixSubfield σ) =>
        (z : Matrix (Fin n) (Fin n) (fixSubfield σ)) i0 i0) hc'
      have e2 := congrArg (fun z : GL (Fin n) (fixSubfield σ) =>
        (z : Matrix (Fin n) (Fin n) (fixSubfield σ)) i2 i2) hc'
      simp only [hs₀def, coe_unitaryDiagGL, diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
        scalar_apply] at e0 e2
      rw [hd0] at e0
      rw [hd2] at e2
      have : ((ζ : (fixSubfield σ)ˣ) : fixSubfield σ) = 1 := by
        rw [e0, ← e2]
        rfl
      have hz1 : ζ = 1 := Units.ext this
      rw [hz1, orderOf_one] at hζ
      exact hp.one_lt.ne hζ
    set t : T₀ := ⟨subfieldPSU h h₀ hbar n (s₀ : primeFormP h₀ _), ⟨_, rfl⟩⟩ with ht
    have htp : orderOf t = p := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => hs₀1 ?_
      · rw [Subgroup.coe_pow, ht, ← map_pow, ← QuotientGroup.mk_pow, hs₀p]
        exact map_one _
      · apply subfieldPSU_injective h h₀ hbar n (by omega)
        rw [map_one]
        exact congrArg Subtype.val h1
    rw [← htp]
    exact orderOf_dvd_natCard t
  · intro g hg hfixg
    obtain ⟨hfs, hzp, hcard⟩ := fixingSubgroup_range_subfieldPSU h n h₀ hbar hn hq hq₀
    have hgfix : g ∈ fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))) ((subfieldPSU h h₀ hbar n).range :
          Set (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
      (mem_fixingSubgroup_iff _).2 fun t ht => by rw [MulAut.smul_def]; exact hfixg t ht
    rw [hfs, hzp] at hgfix
    have hdvd : orderOf g ∣ p := by
      rw [← hσ, ← hcard]
      exact (Subgroup.orderOf_dvd_natCard _ hgfix)
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hg) (by rw [Nat.coprime_self]; exact hp.one_lt.ne')

end CFSG.HardMathSupport.Timmesfeld.CrossChar
