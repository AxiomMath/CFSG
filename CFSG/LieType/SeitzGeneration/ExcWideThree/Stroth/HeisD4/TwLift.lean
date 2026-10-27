module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Lift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis


section Frob

variable {L : Type} [Field L]

theorem units_map_mem_subsystem (σ : L →+* L) {g : ModGL Tag.E6 L}
    (hg : g ∈ subsystemGroup Tag.E6 L d4Support) :
    Units.map (entrywiseHom σ) g ∈ subsystemGroup Tag.E6 L d4Support := by
  have hle : subsystemGroup Tag.E6 L d4Support ≤
      (subsystemGroup Tag.E6 L d4Support).comap (Units.map (entrywiseHom σ)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_entrywiseHom_xUnit]
      exact xUnit_mem_subsystemGroup hj _
    · rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_entrywiseHom_yUnit]
      exact yUnit_mem_subsystemGroup hj _
  exact hle hg

theorem exists_units_map_eq_subsystem {σ : L →+* L} (hσ : Function.Surjective σ)
    (g : subsystemGroup Tag.E6 L d4Support) :
    ∃ g' : subsystemGroup Tag.E6 L d4Support,
      Units.map (entrywiseHom σ) (g' : ModGL Tag.E6 L) = (g : ModGL Tag.E6 L) := by
  have hle : subsystemGroup Tag.E6 L d4Support ≤
      (subsystemGroup Tag.E6 L d4Support).map (Units.map (entrywiseHom σ)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσ c
      exact ⟨xUnit Tag.E6 L j c', xUnit_mem_subsystemGroup hj _,
        units_map_entrywiseHom_xUnit σ j c'⟩
    · obtain ⟨c', rfl⟩ := hσ c
      exact ⟨yUnit Tag.E6 L j c', yUnit_mem_subsystemGroup hj _,
        units_map_entrywiseHom_yUnit σ j c'⟩
  obtain ⟨g', hg', hgg⟩ := hle g.2
  exact ⟨⟨g', hg'⟩, hgg⟩

theorem d4Res_units_map (σ : L →+* L) (h : subsystemGroup Tag.E6 L d4Support) :
    d4Res L ⟨Units.map (entrywiseHom σ) (h : ModGL Tag.E6 L), units_map_mem_subsystem σ h.2⟩ =
      Units.map (entrywiseHom σ) (d4Res L h) :=
  d4PreservingRes_units_map σ (subsystemGroup_le_d4Preserving h.2)

theorem units_map_mem_adjointGroup' {τ : Tag} (σ : L →+* L) {x : ModGL τ L}
    (hx : x ∈ adjointGroup τ L) : Units.map (entrywiseHom σ) x ∈ adjointGroup τ L := by
  rw [← baseChangeGL_eq_entrywise]
  exact baseChangeGL_mem_adjointGroup σ hx

end Frob

section Gamma

variable {L : Type} [Field L] [IsAlgClosed L]

theorem gamma_fixed_of_comm {Fr : L →+* L} (hFrs : Function.Surjective Fr)
    (hPF : Units.map (entrywiseHom Fr) (d4DiagramMap L) = d4DiagramMap L)
    {y m : ModGL Tag.E6 L} {ε : ℕ}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (hy : y = m * d4TrialityRep L ^ ε)
    (hcomm : ∀ x ∈ subsystemGroup Tag.E6 L d4Support,
      Units.map (entrywiseHom Fr) (y * x * y⁻¹) = y * Units.map (entrywiseHom Fr) x * y⁻¹) :
    Units.map (entrywiseHom Fr) (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩) =
      d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ := by
  set γ := d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ with hγ
  set P := d4DiagramMap L with hP
  set Fs' : ModGL Tag.D4 L →* ModGL Tag.D4 L := Units.map (entrywiseHom Fr) with hFs'
  set c₁ := γ⁻¹ * Fs' γ with hc₁
  have hγA : γ ∈ adjointGroup Tag.D4 L := d4PreservingRes_torus_sup_mem_adjoint hm
  have hFγA : Fs' γ ∈ adjointGroup Tag.D4 L := units_map_mem_adjointGroup' Fr hγA
  have hc₁A : c₁ ∈ adjointGroup Tag.D4 L := mul_mem (inv_mem hγA) hFγA
  have hFγ : Fs' γ = γ * c₁ := by rw [hc₁]; group
  have hFG : Fs' (γ * P ^ ε) = (γ * c₁) * P ^ ε := by
    rw [map_mul, map_pow, hFs', hPF, ← hFs', hFγ]
  have hstar : ∀ h : subsystemGroup Tag.E6 L d4Support,
      c₁ * (P ^ ε * Fs' (d4Res L h) * (P ^ ε)⁻¹) * c₁⁻¹ =
        P ^ ε * Fs' (d4Res L h) * (P ^ ε)⁻¹ := by
    intro h
    obtain ⟨h₁, hh₁, hr₁⟩ := d4Res_conj_y hm ε h
    set h' : subsystemGroup Tag.E6 L d4Support :=
      ⟨Units.map (entrywiseHom Fr) (h : ModGL Tag.E6 L), units_map_mem_subsystem Fr h.2⟩ with hh'
    obtain ⟨h₂, hh₂, hr₂⟩ := d4Res_conj_y hm ε h'
    have hrel : (⟨Units.map (entrywiseHom Fr) (h₁ : ModGL Tag.E6 L),
        units_map_mem_subsystem Fr h₁.2⟩ : subsystemGroup Tag.E6 L d4Support) = h₂ := by
      apply Subtype.ext
      show Units.map (entrywiseHom Fr) (h₁ : ModGL Tag.E6 L) = (h₂ : ModGL Tag.E6 L)
      rw [hh₁, hh₂, ← hy]
      exact hcomm h h.2
    have e1 := d4Res_units_map Fr h₁
    rw [hrel, hr₂, hr₁] at e1
    have e2 : d4Res L h' = Fs' (d4Res L h) := d4Res_units_map Fr h
    rw [e2, map_mul, map_mul, map_inv, hFG] at e1
    set W := Fs' (d4Res L h) with hW
    calc c₁ * (P ^ ε * W * (P ^ ε)⁻¹) * c₁⁻¹ =
        γ⁻¹ * (((γ * c₁) * P ^ ε) * W * ((γ * c₁) * P ^ ε)⁻¹) * γ := by group
      _ = γ⁻¹ * ((γ * P ^ ε) * W * (γ * P ^ ε)⁻¹) * γ := by rw [e1]
      _ = P ^ ε * W * (P ^ ε)⁻¹ := by group
  have hcommA : ∀ z : ↥(adjointGroup Tag.D4 L), c₁ * (z : ModGL Tag.D4 L) * c₁⁻¹ = z := by
    intro z
    obtain ⟨x, hx⟩ : ∃ x : subsystemGroup Tag.E6 L d4Support, d4Res L x = z := by
      have hz : (z : ModGL Tag.D4 L) ∈ (d4Res L).range := by
        rw [range_d4Res]
        exact z.2
      exact hz
    obtain ⟨h₀, hh₀⟩ := exists_units_map_eq_subsystem hFrs
      ((d4Triality L ^ ε)⁻¹ x : subsystemGroup Tag.E6 L d4Support)
    have hz : (z : ModGL Tag.D4 L) = P ^ ε * Fs' (d4Res L h₀) * (P ^ ε)⁻¹ := by
      have e1 := d4Res_d4Triality_pow ε ((d4Triality L ^ ε)⁻¹ x : subsystemGroup Tag.E6 L d4Support)
      have e2 : ((d4Triality L ^ ε : MulAut (subsystemGroup Tag.E6 L d4Support))
          ((d4Triality L ^ ε)⁻¹ x : subsystemGroup Tag.E6 L d4Support)) = x :=
        MulAut.apply_inv_self _ _ x
      have e3 : d4Res L ((d4Triality L ^ ε)⁻¹ x : subsystemGroup Tag.E6 L d4Support) =
          Fs' (d4Res L h₀) := by
        have := d4Res_units_map Fr h₀
        rw [← this]
        congr 1
        exact Subtype.ext hh₀.symm
      rw [e2, hx, e3] at e1
      exact e1
    rw [hz]
    exact hstar h₀
  have hcenter : (⟨c₁, hc₁A⟩ : ↥(adjointGroup Tag.D4 L)) ∈
      Subgroup.center ↥(adjointGroup Tag.D4 L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    show (z : ModGL Tag.D4 L) * c₁ = c₁ * (z : ModGL Tag.D4 L)
    have h := hcommA z
    calc (z : ModGL Tag.D4 L) * c₁ = (c₁ * (z : ModGL Tag.D4 L) * c₁⁻¹) * c₁ := by rw [h]
      _ = c₁ * (z : ModGL Tag.D4 L) := by group
  rw [center_adjointGroup_eq_bot_field Tag.D4 L, Subgroup.mem_bot] at hcenter
  have hc : c₁ = 1 := congrArg Subtype.val hcenter
  rw [hFγ, hc, mul_one]

end Gamma

section Descent

variable {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

theorem exists_gamma_descent_of_fixed (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (hγF : Units.map (entrywiseHom Fr)
        (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩) =
      d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩) :
    ∃ (b : Fin Tag.D4.rank → Kˣ) (j : ModGL Tag.D4 K), j ∈ adjointGroup Tag.D4 K ∧
      d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ =
        baseChangeGL (algebraMap K L) (rootDiagUnit Tag.D4 b * j) := by
  have hγ := d4PreservingRes_torus_sup_mem_adjoint hm
  obtain ⟨b, u, hu, hbu⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_mul_of_frobenius_fixed
    Tag.D4 Fr hFr hγ hγF
  obtain ⟨j, hj, rfl⟩ := hu
  exact ⟨b, j, hj, by rw [hbu, map_mul]⟩

end Descent

section Main

open CFSG.HardMathSupport.Lang.D4Three

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem exists_fixed_ell_std_tw (hK3 : ringChar K ≠ 3)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {y m : ModGL Tag.E6 L} {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (hy : y = m * d4TrialityRep L ^ ε)
    (hy3 : y ^ 3 = 1)
    (hcomm : ∀ x ∈ subsystemGroup Tag.E6 L d4Support,
      Units.map (entrywiseHom Fr) (y * x * y⁻¹) = y * Units.map (entrywiseHom Fr) x * y⁻¹) :
    ∃ x ∈ subsystemGroup Tag.E6 L d4Support, x ≠ 1 ∧
      x ^ ringChar K = 1 ∧ Units.map (entrywiseHom Fr) x = x ∧ y * x = x * y := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hLchar : ringChar L = ringChar K := ringChar.eq L (ringChar K)
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K))
    exact ⟨z, by rw [hFr, hz]⟩
  have hP : baseChangeGL (algebraMap K L) (d4P K) = d4DiagramMap L :=
    baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4
  have hPF : Units.map (entrywiseHom Fr) (d4DiagramMap L) = d4DiagramMap L := by
    rw [← hP]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed Fr hFr (d4P K)
  have hγF := gamma_fixed_of_comm hFrs hPF hm hy hcomm
  obtain ⟨b, j, hj, hγ⟩ := exists_gamma_descent_of_fixed Fr hFr hm hγF
  set X : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b * j * d4P K ^ ε with hX
  set g'' : ↥(adjointGroup Tag.D4 K) := ⟨rootDiagUnit Tag.D4 b * j * (rootDiagUnit Tag.D4 b)⁻¹,
    conj_rootDiagUnit_mem_adjointGroup b hj⟩ with hg''
  set α : MulAut ↥(adjointGroup Tag.D4 K) :=
    MulAut.conj g'' * (exactNormalAut Tag.D4 K b 1 0 * d4Graph K ε) with hα
  have hαX : Parrott.D4Graph.ClassOdd.IsConjBy α X := by
    have := Parrott.D4Graph.ClassOdd.isConjBy_normalForm g'' b ε
    refine this.congr ?_
    rw [hX]
    simp only [hg'']
    group
  have hkey : ∀ h : subsystemGroup Tag.E6 L d4Support, ∃ h' : subsystemGroup Tag.E6 L d4Support,
      (h' : ModGL Tag.E6 L) = y * (h : ModGL Tag.E6 L) * y⁻¹ ∧
      d4Res L h' = baseChangeGL (algebraMap K L) X * d4Res L h *
        (baseChangeGL (algebraMap K L) X)⁻¹ := by
    intro h
    obtain ⟨h', hh', hr⟩ := d4Res_conj_y hm ε h
    refine ⟨h', by rw [hh', hy], ?_⟩
    rw [hr, hγ]
    have e : baseChangeGL (algebraMap K L) (rootDiagUnit Tag.D4 b * j) * d4DiagramMap L ^ ε =
        baseChangeGL (algebraMap K L) X := by
      rw [hX]
      simp only [map_mul, map_pow, hP]
    rw [e]
  have hsurj : ∀ z : ↥(adjointGroup Tag.D4 K),
      ∃ q0 : subsystemGroup Tag.E6 K d4Support, d4Res K q0 = z := by
    intro z
    have hz : (z : ModGL Tag.D4 K) ∈ (d4Res K).range := by
      rw [range_d4Res]
      exact z.2
    exact hz
  have hbc : ∀ q0 : subsystemGroup Tag.E6 K d4Support,
      d4Res L (d4QBaseChange K (algebraMap K L) q0) = baseChangeGL (algebraMap K L) (d4Res K q0) :=
    fun q0 => d4Res_baseChangeGL _ q0
  have hinj := baseChangeGL_injective (τ := Tag.D4) (algebraMap K L)
  have hα3 : α ^ 3 = 1 := by
    have hIC : Parrott.D4Graph.ClassOdd.IsConjBy (α ^ 3) (X ^ 3) := by
      have := (hαX.mul hαX).mul hαX
      rwa [← pow_three', ← pow_three'] at this
    refine MulEquiv.ext fun z => Subtype.ext ?_
    rw [hIC z]
    show X ^ 3 * (z : ModGL Tag.D4 K) * (X ^ 3)⁻¹ = z
    obtain ⟨q0, hq0⟩ := hsurj z
    set h : subsystemGroup Tag.E6 L d4Support := d4QBaseChange K (algebraMap K L) q0 with hh
    obtain ⟨h₁, hh₁, hr₁⟩ := hkey h
    obtain ⟨h₂, hh₂, hr₂⟩ := hkey h₁
    obtain ⟨h₃, hh₃, hr₃⟩ := hkey h₂
    have hyyy : y * y * y = 1 := by rw [← pow_three']; exact hy3
    have h3 : h₃ = h := Subtype.ext (by
      rw [hh₃, hh₂, hh₁]
      calc y * (y * (y * (h : ModGL Tag.E6 L) * y⁻¹) * y⁻¹) * y⁻¹ =
          (y * y * y) * (h : ModGL Tag.E6 L) * (y * y * y)⁻¹ := by group
        _ = h := by rw [hyyy]; group)
    have hres : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) =
        baseChangeGL (algebraMap K L) (X ^ 3 * (z : ModGL Tag.D4 K) * (X ^ 3)⁻¹) := by
      have e0 : d4Res L h = baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) := by
        rw [hh, hbc, hq0]
      have e1 := hr₃
      rw [h3] at e1
      rw [hr₂, hr₁, e0] at e1
      rw [map_mul, map_mul, map_inv, map_pow, pow_three']
      refine e1.trans ?_
      group
    exact (hinj hres).symm
  have hαT : D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1 :=
    ⟨g'', b, 1, ε, by omega, one_pow _, ⟨by omega, rfl⟩, rfl⟩
  have hKc : ringChar K = 2 ∨ 5 ≤ ringChar K := by
    have hp := (Fact.out : (ringChar K).Prime)
    have h2 := hp.two_le
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl h
    · right
      omega
  obtain ⟨z, hz1, hzp, hzf⟩ := d4_exists_fixed_ell hKc hα3 hαT
  obtain ⟨q0, hq0⟩ := hsurj z
  set x₁ : subsystemGroup Tag.E6 L d4Support := d4QBaseChange K (algebraMap K L) q0 with hx₁
  have hrx₁ : d4Res L x₁ = baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) := by
    rw [hx₁, hbc, hq0]
  have hzne : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    have h' : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) =
        baseChangeGL (algebraMap K L) (1 : ModGL Tag.D4 K) := by rw [h, map_one]
    exact hinj h'
  have hn : ringChar L = 2 ∨ (ringChar K + 1) % 2 = 0 := by
    have hp := (Fact.out : (ringChar K).Prime)
    rcases hp.eq_two_or_odd with h | h
    · exact Or.inl (by rw [hLchar, h])
    · right
      omega
  have hzℓ : baseChangeGL (algebraMap K L) (z : ModGL Tag.D4 K) ^ ringChar K = 1 := by
    rw [← map_pow]
    have : (z : ModGL Tag.D4 K) ^ ringChar K = 1 := by
      have := congrArg Subtype.val hzp
      simpa using this
    rw [this, map_one]
  refine ⟨((x₁ ^ (ringChar K + 1) : subsystemGroup Tag.E6 L d4Support) : ModGL Tag.E6 L),
    (x₁ ^ (ringChar K + 1)).2, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h1' : x₁ ^ (ringChar K + 1) = 1 := Subtype.ext h1
    have h2 : d4Res L (x₁ ^ (ringChar K + 1)) = 1 := by rw [h1', map_one]
    rw [map_pow, hrx₁, pow_succ, hzℓ, one_mul] at h2
    exact hzne h2
  · have hκ : d4Res L (x₁ ^ ringChar K) = 1 := by rw [map_pow, hrx₁, hzℓ]
    have hxℓ : (x₁ ^ (ringChar K + 1)) ^ ringChar K = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact d4Res_ker_pow hκ hn
    rw [← Subgroup.coe_pow, hxℓ, Subgroup.coe_one]
  · have hx1F : Units.map (entrywiseHom Fr) (x₁ : ModGL Tag.E6 L) = (x₁ : ModGL Tag.E6 L) :=
      CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed Fr hFr (q0 : ModGL Tag.E6 K)
    rw [Subgroup.coe_pow, map_pow, hx1F]
  · obtain ⟨h', hh', hr⟩ := hkey x₁
    have hXz : X * (z : ModGL Tag.D4 K) * X⁻¹ = z := by
      have := hαX z
      rw [hzf] at this
      exact this.symm
    have hr' : d4Res L h' = d4Res L x₁ := by
      rw [hr, hrx₁, ← map_mul, ← map_inv, ← map_mul, hXz]
    have hκ : d4Res L (h' * x₁⁻¹) = 1 := by rw [map_mul, map_inv, hr', mul_inv_cancel]
    have hκc := mem_center_of_d4Res_eq_one hκ
    have hκn : (h' * x₁⁻¹) ^ (ringChar K + 1) = 1 := d4Res_ker_pow hκ hn
    have hcomm : Commute (h' * x₁⁻¹) x₁ := (Subgroup.mem_center_iff.1 hκc x₁).symm
    have hpow : h' ^ (ringChar K + 1) = x₁ ^ (ringChar K + 1) := by
      have e : h' = (h' * x₁⁻¹) * x₁ := by group
      conv_lhs => rw [e]
      rw [hcomm.mul_pow, hκn, one_mul]
    have h3 : (y * (x₁ : ModGL Tag.E6 L) * y⁻¹) ^ (ringChar K + 1) =
        (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) := by
      rw [← hh', ← Subgroup.coe_pow, hpow, Subgroup.coe_pow]
    have e2 : (y * (x₁ : ModGL Tag.E6 L) * y⁻¹) ^ (ringChar K + 1) =
        y * (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) * y⁻¹ := by
      have := conj_pow (a := y) (b := (x₁ : ModGL Tag.E6 L)) (i := ringChar K + 1)
      exact this
    have h4 : y * (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) * y⁻¹ =
        (x₁ : ModGL Tag.E6 L) ^ (ringChar K + 1) := e2.symm.trans h3
    rw [Subgroup.coe_pow]
    exact mul_inv_eq_iff_eq_mul.1 h4


end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
