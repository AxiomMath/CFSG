module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem ringEquiv_apply_eq_sq [Finite K] (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) : σ (ω : K) = (ω : K) ^ 2 := by
  set u : Kˣ := Units.map σ.toRingHom.toMonoidHom ω with hu
  obtain ⟨m, hm⟩ := exists_eq_pow hK hω u
  have h3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hm3 : u = ω ^ (m % 3) := by
    rw [hm]
    conv_lhs => rw [← Nat.mod_add_div m 3]
    rw [pow_add, pow_mul, h3, one_pow, mul_one]
  have hlt : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : m % 3
  · exfalso
    have h1 : σ (ω : K) = 1 := by
      have := congrArg Units.val hm3
      simpa [hu] using this
    have h2 : (ω : K) = 1 := σ.injective (h1.trans σ.map_one.symm)
    have h3' : ω = 1 := Units.ext h2
    rw [h3', orderOf_one] at hω
    norm_num at hω
  · exfalso
    apply hσ
    have hσω : σ (ω : K) = (ω : K) := by
      have := congrArg Units.val hm3
      simpa [hu] using this
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · rw [hc, map_zero]; rfl
    · obtain ⟨n, hn⟩ := exists_eq_pow hK hω (Units.mk0 c hc)
      have hc' : c = (ω : K) ^ n := by
        have := congrArg Units.val hn
        simpa using this
      rw [hc', map_pow, hσω]
      rfl
  · have := congrArg Units.val hm3
    simpa [hu] using this

section Torus

variable {τ : Tag}

theorem torV_inv_of_sq {ω : Kˣ} (hω : orderOf ω = 3) (x : Fin τ.rank → ZMod 3) :
    (fun i => (torV ω x i) ^ 2) = (torV ω x)⁻¹ := by
  have h3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  funext i
  rw [Pi.inv_apply, eq_inv_iff_mul_eq_one, ← pow_succ]
  simp only [torV]
  rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]

theorem entrywise_dV_eq_inv {ω : Kˣ} (hω : orderOf ω = 3) {σ : K →+* K}
    (hσω : σ (ω : K) = (ω : K) ^ 2) (x : Fin τ.rank → ZMod 3) :
    Units.map (entrywiseHom σ) (dV ω x) = (dV ω x)⁻¹ := by
  change baseChangeGL σ (rootDiagUnit τ (torV ω x)) = _
  rw [baseChangeGL_rootDiagUnit]
  have h : (fun i => Units.map σ.toMonoidHom (torV ω x i)) =
      fun i => (torV ω x i) ^ 2 := by
    funext i
    apply Units.ext
    change σ (((ω ^ (x i).val : Kˣ)) : K) = (((ω ^ (x i).val) ^ 2 : Kˣ) : K)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hσω,
      ← pow_mul, ← pow_mul, mul_comm]
  rw [h, torV_inv_of_sq hω, dV]
  exact map_inv (rootDiagUnitHom τ K) (torV ω x)

theorem canonicalRep_conj_rootDiagUnit_of_neg {w : WeylGroup τ}
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      (rootDiagUnit τ b)⁻¹ := by
  rw [canonicalRep_conj_rootDiagUnit]
  have hwinv : ∀ u : Fin τ.rank → ℤ, w⁻¹ • u = -u := by
    intro u
    have h := hw (w⁻¹ • u)
    rw [smul_inv_smul] at h
    rw [← neg_neg (w⁻¹ • u), ← h]
  have h : weylTuple w b = b⁻¹ := by
    funext i
    rw [weylTuple, hwinv, Pi.inv_apply, ← zero_sub, rootChar_sub, rootChar_zero, one_mul]
    have := rootChar_nsmul_single b i 1
    rw [one_nsmul, pow_one] at this
    rw [this]
  rw [h]
  exact map_inv (rootDiagUnitHom τ K) b

theorem canonicalRep_conj_pinnedX_charTwo
    [CharP K 2] (w : WeylGroup τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

end Torus

section Core

variable {τ : Tag} [Finite K]

theorem false_of_fix_entrywise [CharP K 2] {ω : Kˣ} (hω : orderOf ω = 3)
    (hG : ∀ z, dV (τ := τ) ω z ∈ adjointGroup τ K)
    (hstd : familyKernel (famV (τ := τ) ω (Native.stdBasis τ.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := τ) ω (Native.stdBasis τ.rank)), w = 1)
    (hkerOK : Native.kerNonemptyOK τ = true) {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) {σ : K →+* K} (hσω : σ (ω : K) = (ω : K) ^ 2)
    (hfix : ∀ y ∈ Subgroup.centralizer {dG hG x},
      (y : ModGL τ K) = g * Units.map (entrywiseHom σ) (y : ModGL τ K) * g⁻¹) :
    False := by
  have hinv : ∀ z : Fin τ.rank → ZMod 3, g * (dV ω z)⁻¹ * g⁻¹ = dV ω z := by
    intro z
    have hz : dG hG z ∈ Subgroup.centralizer {dG hG x} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change dV ω z * dV ω x = dV ω x * dV ω z
      rw [← dV_add (by rw [← hω]; exact pow_orderOf_eq_one ω),
        ← dV_add (by rw [← hω]; exact pow_orderOf_eq_one ω), add_comm]
    have h1 := hfix _ hz
    change dV ω z = g * Units.map (entrywiseHom σ) (dV ω z) * g⁻¹ at h1
    rw [entrywise_dV_eq_inv hω hσω] at h1
    exact h1.symm
  set n₀ := canonicalRep (coxeterSystem τ) K w₀ with hn₀
  have hgn : g * n₀ ∈ torusGroup τ K := by
    refine mem_torusGroup_of_mem_familyCentralizer_std hstd (mem_familyCentralizer_std
      (mul_mem hg (canonicalRep_mem_adjointGroup _ K _)) fun z => ?_)
    have hc := canonicalRep_conj_rootDiagUnit_of_neg (K := K) hw₀ (torV ω z)
    change n₀ * dV ω z * n₀⁻¹ = (dV ω z)⁻¹ at hc
    change dV ω z * (g * n₀) = (g * n₀) * dV ω z
    have e1 : dV ω z * (g * n₀) = (g * (dV ω z)⁻¹ * g⁻¹) * (g * n₀) := by
      rw [hinv z]
    have e2 : (g * (dV ω z)⁻¹ * g⁻¹) * (g * n₀) = g * (n₀ * dV ω z * n₀⁻¹) * n₀ := by
      rw [hc]; group
    have e3 : g * (n₀ * dV ω z * n₀⁻¹) * n₀ = (g * n₀) * dV ω z := by
      group
    exact e1.trans (e2.trans e3)
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom hgn
  have ha' : rootDiagUnit τ a = g * n₀ := ha
  obtain ⟨β₀, hβ₀, hβ₀1⟩ := exists_kernelRoot_of_kerNonemptyOK hkerOK hω hx
  obtain ⟨β, hβ, hβ1, hβpos⟩ : ∃ β, IsRoot τ β ∧ rootChar (torV ω x) β = 1 ∧
      0 < height β := by
    rcases IsRoot.height_pos_or_neg hβ₀ with h | h
    · exact ⟨β₀, hβ₀, hβ₀1, h⟩
    · refine ⟨-β₀, IsRoot.neg hβ₀, ?_, ?_⟩
      · rw [← zero_sub, rootChar_sub, rootChar_zero, hβ₀1, inv_one, one_mul]
      · rw [show height (-β₀) = -height β₀ by simp [height]]
        omega
  set X : ModGL τ K := pinnedX τ K β 1 with hX
  have hXG : X ∈ adjointGroup τ K := pinnedX_mem_adjointGroup β 1
  have hXc : (⟨X, hXG⟩ : adjointGroup τ K) ∈ Subgroup.centralizer {dG hG x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change X * dV ω x = dV ω x * X
    have h1 := rootDiagUnit_conj_pinnedX (torV ω x) hβ (1 : K)
    rw [hβ1, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have h1 := hfix _ hXc
  change X = g * Units.map (entrywiseHom σ) X * g⁻¹ at h1
  rw [hX, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX, map_one] at h1
  have hg' : g = rootDiagUnit τ a * n₀⁻¹ := by
    rw [ha']; group
  rw [hg'] at h1
  have h2 : n₀⁻¹ * X * n₀ = (rootDiagUnit τ a)⁻¹ * X * rootDiagUnit τ a := by
    calc n₀⁻¹ * X * n₀ = (rootDiagUnit τ a)⁻¹ *
          (rootDiagUnit τ a * n₀⁻¹ * X * (rootDiagUnit τ a * n₀⁻¹)⁻¹) *
            rootDiagUnit τ a := by group
      _ = (rootDiagUnit τ a)⁻¹ * X * rootDiagUnit τ a := by rw [← h1]
  have h3 : (rootDiagUnit τ a)⁻¹ * X * rootDiagUnit τ a = pinnedX τ K β (rootChar a⁻¹ β : K) := by
    have hinv' : rootDiagUnit τ a⁻¹ = (rootDiagUnit τ a)⁻¹ := map_inv (rootDiagUnitHom τ K) a
    have := rootDiagUnit_conj_pinnedX (a⁻¹) hβ (1 : K)
    rw [mul_one, hinv', inv_inv] at this
    exact this
  have h4 : X = pinnedX τ K (-β) (rootChar a⁻¹ β : K) := by
    have h5 : X = n₀ * (n₀⁻¹ * X * n₀) * n₀⁻¹ := by group
    rw [h5, h2, h3, hn₀, canonicalRep_conj_pinnedX_charTwo _ hβ, hw₀]
  have hpos : X ∈ posUnipotent τ K :=
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧
      0 < height α}) => rootSubgroup τ K γ) β ⟨hβ, hβpos⟩ le_rfl)
      (Subgroup.subset_closure ⟨1, rfl⟩)
  have hneg : X ∈ negUnipotent τ K := by
    rw [h4]
    exact (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧
      height α < 0}) => rootSubgroup τ K γ) (-β) ⟨IsRoot.neg hβ, by
        rw [show height (-β) = -height β by simp [height]]; omega⟩ le_rfl)
      (Subgroup.subset_closure ⟨_, rfl⟩)
  have hbot : X ∈ posUnipotent τ K ⊓ negUnipotent τ K := ⟨hpos, hneg⟩
  rw [CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent τ K, Subgroup.mem_bot] at hbot
  have h6 : pinnedX τ K β 1 = pinnedX τ K β 0 := by rw [← hX, hbot, pinnedX_zero]
  exact one_ne_zero (pinnedX_injective τ K β h6)

end Core

section E8

variable [Finite K]

theorem mem_innerAut_of_fix_E8 (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3)
    {x : Fin Tag.E8.rank → ZMod 3} (hx : x ≠ 0) (α : MulAut (adjointGroup Tag.E8 K))
    (hfix : ∀ y ∈ Subgroup.centralizer {dG (dV_mem_E8 ω) x}, α y = y) :
    α ∈ innerAut (adjointGroup Tag.E8 K) := by
  have : CharP K 2 := charP_two_of_card_four hK
  obtain ⟨hnf, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form (f := 2) (by norm_num) K
      (by rw [hK]; norm_num) Tag.E8 (Or.inr rfl)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
  simp only at hgσ
  by_cases hσ : σ = RingEquiv.refl K
  · have h1 : Θ α = σ := hΘ α g σ hgσ
    have h2 : α ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, h1, hσ]
      rfl
    rw [hker] at h2
    exact h2
  · refine (false_of_fix_entrywise hω (dV_mem_E8 ω)
      (famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis
        (famOK_std_of_hypOK Certificates.certificate13666.2.2.1))
      Certificates.certificate13666.2.2.2.2.2 CrossChar.e8Neg_smul hx g.2
      (σ := σ.toRingHom) (ringEquiv_apply_eq_sq hK hω hσ) fun y hy => ?_).elim
    have h1 := hgσ y
    rw [hfix y hy] at h1
    exact h1

theorem innerOneBalanceThree_E8_four
    (hK : Nat.card K = 4) : InnerOneBalanceThree (adjointGroup Tag.E8 K) := by
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [card_units_four hK])
  refine innerOneBalanceThree_of_toral (mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K))
    {t | ∃ x : Fin Tag.E8.rank → ZMod 3, x ≠ 0 ∧ t = dG (dV_mem_E8 ω) x} ?_ ?_ ?_
  · intro s hs3 hs1
    obtain ⟨c, hc, x, hcx⟩ := exists_conj_dV_E8 hK hω s.2 (by
      have := congrArg Subtype.val hs3
      simpa using this)
    refine ⟨⟨c, hc⟩, x, ?_, Subtype.ext hcx⟩
    rintro rfl
    apply hs1
    apply Subtype.ext
    have h := hcx
    rw [dV_zero] at h
    change (s : ModGL Tag.E8 K) = 1
    calc (s : ModGL Tag.E8 K) = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rintro _ ⟨x, hx, rfl⟩
    exact gLAPPrimeCoreOf_centralizer_dV_E8 hK hω hx
  · rintro _ ⟨x, hx, rfl⟩ α hα
    exact mem_innerAut_of_fix_E8 hK hω hx α hα

end E8

section F4

variable [Finite K]

open CFSG.LieType.Ree in
theorem mem_innerAut_of_fix_F4 (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) {x : Fin Tag.F4.rank → ZMod 3} (hx : x ≠ 0)
    (α : MulAut (adjointGroup Tag.F4 K))
    (hfix : ∀ y ∈ Subgroup.centralizer {dG (dV_mem_F4 ω) x}, α y = y) :
    α ∈ innerAut (adjointGroup Tag.F4 K) := by
  have : CharP K 2 := charP_two_of_card_four hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, hker⟩, -, -, heven, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 2) (by norm_num) K (by rw [hK]; norm_num)
  have hφ2 : ReeTag.F4.finiteExceptionalAut K ^ 2 = ReeTag.F4.finiteFrobeniusAut K := by
    rw [heven 1 rfl, pow_one]
  have htwo : ∀ β : MulAut (adjointGroup Tag.F4 K),
      (∀ y ∈ Subgroup.centralizer {dG (dV_mem_F4 ω) x}, β y = y) →
      Θ β ≠ Multiplicative.ofAdd (2 : ZMod (2 * 2)) := by
    intro β hβ hΘβ
    obtain ⟨⟨g, j⟩, hgj, -⟩ := hnf β
    simp only at hgj
    have hj : (j : ℕ) = 2 := by
      have h := (hΘ β g j hgj).symm.trans hΘβ
      have key : ∀ j : Fin (2 * 2), ((j : ℕ) : ZMod (2 * 2)) = 2 → (j : ℕ) = 2 := by decide
      exact key j (Multiplicative.ofAdd.injective h)
    rw [hj, hφ2] at hgj
    obtain ⟨g', hg'⟩ : ∃ g' : ModGL Tag.F4 K, g' = g.1 := ⟨_, rfl⟩
    have hg'G : g' ∈ adjointGroup Tag.F4 K := by
      rw [hg']
      exact g.2
    refine false_of_fix_entrywise hω (dV_mem_F4 ω)
      (famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis
        (famOK_std_of_hypOK Certificates.certificate13666.1))
      Certificates.certificate13666.2.2.2.1 CrossChar.f4Neg_smul hx hg'G
      (σ := frobenius K ReeTag.F4.prime) (by rw [frobenius_def]; rfl) fun y hy => ?_
    have h2 : (β y : ModGL Tag.F4 K) = g' *
        Units.map (entrywiseHom (frobenius K ReeTag.F4.prime)) (y : ModGL Tag.F4 K) * g'⁻¹ := by
      rw [hgj, hg']
      rfl
    rw [hβ y hy] at h2
    exact h2
  have hsq : ∀ y ∈ Subgroup.centralizer {dG (dV_mem_F4 ω) x}, (α ^ 2) y = y := by
    intro y hy
    rw [pow_two, MulAut.mul_apply, hfix y hy, hfix y hy]
  obtain ⟨k, hk⟩ : ∃ k : ZMod (2 * 2), Θ α = Multiplicative.ofAdd k :=
    ⟨Multiplicative.toAdd (Θ α), rfl⟩
  have hcases : ∀ k : ZMod (2 * 2), k = 0 ∨ k = 2 ∨ k + k = 2 := by decide
  rcases hcases k with h0 | h2 | h11
  · have h3 : Θ α = 1 := by
      rw [hk, h0]
      rfl
    exact (SetLike.ext_iff.1 hker α).1 (MonoidHom.mem_ker.2 h3)
  · exact absurd (hk.trans (by rw [h2])) (htwo α hfix)
  · exfalso
    apply htwo (α ^ 2) hsq
    refine (map_pow Θ α 2).trans ?_
    show Θ α ^ 2 = Multiplicative.ofAdd (2 : ZMod (2 * 2))
    rw [hk, pow_two, ← ofAdd_add, h11]

theorem innerOneBalanceThree_F4_four
    (hK : Nat.card K = 4) : InnerOneBalanceThree (adjointGroup Tag.F4 K) := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [card_units_four hK])
  refine innerOneBalanceThree_of_toral (mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K))
    {t | ∃ x : Fin Tag.F4.rank → ZMod 3, x ≠ 0 ∧ t = dG (dV_mem_F4 ω) x} ?_ ?_ ?_
  · intro s hs3 hs1
    obtain ⟨c, hc, x, hcx⟩ := exists_conj_dV_F4 hK hω s.2 (by
      have := congrArg Subtype.val hs3
      simpa using this)
    refine ⟨⟨c, hc⟩, x, ?_, Subtype.ext hcx⟩
    rintro rfl
    apply hs1
    apply Subtype.ext
    have h := hcx
    rw [dV_zero] at h
    change (s : ModGL Tag.F4 K) = 1
    calc (s : ModGL Tag.F4 K) = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rintro _ ⟨x, hx, rfl⟩
    exact gLAPPrimeCoreOf_centralizer_dV_F4 hK hω hx
  · rintro _ ⟨x, hx, rfl⟩ α hα
    exact mem_innerAut_of_fix_F4 hK hω hx α hα

end F4

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
