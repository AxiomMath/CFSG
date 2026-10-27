module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Uni
public import CFSG.HardMathSupport.Solomon.Coordinator.L5LinFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus
  CFSG.HardMathSupport.Solomon.Proving

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

local notation "ρ" => primeFormConjHom h (idGram K 5)

theorem uni_conj_fieldAut_fix {b : MulAut (primeFormP h (idGram K 5))}
    {M : primeFormUnitary h (idGram K 5)} {σ : K ≃+* K}
    (hb : (ρ M)⁻¹ * b * ρ M = primeFormFieldHom h isPrimeFormGram_one σ)
    {g : gramSU h (idGram K 5)} (hg : glAut σ (g : GL (Fin 5) K) = g) :
    b (ρ M (uniProj h 5 g)) = ρ M (uniProj h 5 g) := by
  have hb' : b = ρ M * primeFormFieldHom h isPrimeFormGram_one σ * (ρ M)⁻¹ := by
    rw [← hb]
    group
  rw [hb', MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  congr 1
  change primeFormFieldAut h isPrimeFormGram_one σ (g : primeFormP h (idGram K 5)) = _
  rw [primeFormFieldAut_mk]
  congr 1
  exact Subtype.ext hg

section Five

variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* primeFormP h (idGram K 5)}

theorem exists_descent_primeFormP_five (h5 : 5 ∣ ℓ ^ f + 1)
    {b : MulAut (primeFormP h (idGram K 5))} (hbD : b ∉ primeFormD h (idGram K 5))
    (hb5 : b ^ 5 = 1) :
    ∃ (M : primeFormUnitary h (idGram K 5)) (σ : K ≃+* K) (ζ : Kˣ),
      (ρ M)⁻¹ * b * ρ M = primeFormFieldHom h isPrimeFormGram_one σ ∧ IsPrimitiveRoot ζ 5 ∧
        h.bar (ζ : K) * (ζ : K) = 1 ∧ σ (ζ : K) = ζ ∧ σ ^ 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ ℓ ^ f = 2) := by omega
  have hb1 : b ≠ 1 := fun e => hbD (e ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn hq b with hσdef
  have hσ1 : σ ≠ 1 := by
    intro e
    apply hbD
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hq]
    exact e
  have hσ5 : σ ^ 5 = 1 := by rw [hσdef, ← map_pow, hb5, map_one]
  have hσo : orderOf σ = 5 := orderOf_eq_prime hσ5 hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq
      Nat.prime_five (by norm_num) b hbo σ rfl hσo
  obtain ⟨ζ, hζ, hζb⟩ := exists_primitiveRoot_five_norm h h5
  exact ⟨M, σ, ζ, hM, hζ, hζb,
    ringEquiv_apply_eq_of_isPrimitiveRoot_five hσ5 (IsPrimitiveRoot.coe_units_iff.2 hζ), hσ5⟩

section Data

variable (hΓ : Function.Surjective Γ) (hker : Γ.ker = Subgroup.center Lb)
  (hodd : Odd (Nat.card (Subgroup.center Lb))) {β : MulAut Lb}
  {b : MulAut (primeFormP h (idGram K 5))} (hβ : ∀ x, Γ (β x) = b (Γ x))
  {M : primeFormUnitary h (idGram K 5)} {σ : K ≃+* K}
  (hM : (primeFormConjHom h (idGram K 5) M)⁻¹ * b * primeFormConjHom h (idGram K 5) M =
    primeFormFieldHom h isPrimeFormGram_one σ)
include hΓ hker hodd hβ hM

theorem uni_conj_proj_mem_fix_of_two {g : gramSU h (idGram K 5)}
    (hg : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (g : GL (Fin 5) K))
    {e : ℕ} (he : g ^ 2 ^ e = 1) : ρ M (uniProj h 5 g) ∈ (autFix β).map Γ := by
  have hodd' : Odd (Nat.card Γ.ker) := by rw [hker]; exact hodd
  exact mem_map_autFix_of_two hΓ hker.le hβ hodd'
    (uni_conj_fieldAut_fix h hM (Units.ext (by rw [coe_glAut]; exact hg)))
    (e := e) (by rw [← map_pow, ← map_pow, he, map_one, map_one])

theorem exists_fixTorus_primeFormP_five {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5)
    (hζb : h.bar (ζ : K) * (ζ : K) = 1) (hζσ : σ (ζ : K) = ζ) :
    ∃ D : TorusData (Fin 3) 5 ↥((autFix β).map Γ),
      Nat.card (Subgroup.closure (Set.range D.X)) = 5 ^ 3 ∧
      (∀ k, ∃ x : gramSU h (idGram K 5),
        (x : GL (Fin 5) K) = starX ζ (0 : Fin 5) ![1, 2, 3] k ∧
        ((D.X k : ↥((autFix β).map Γ)) : primeFormP h (idGram K 5)) = ρ M (uniProj h 5 x)) ∧
      (∀ k, ∃ s : gramSU h (idGram K 5),
        (s : GL (Fin 5) K) = starSw (0 : Fin 5) ![1, 2, 3] k ∧
        ((D.Sw k : ↥((autFix β).map Γ)) : primeFormP h (idGram K 5)) =
          ρ M (uniProj h 5 s)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h.finite
  have hζσ' : σ ((ζ⁻¹ : Kˣ) : K) = (ζ⁻¹ : Kˣ) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hζσ]
  set c := ρ M with hc
  set Fix := (autFix β).map Γ with hFix
  have htvecσ : ∀ (i j m : Fin 5), σ ((tvec ζ i j m : Kˣ) : K) = tvec ζ i j m := by
    intro i j m
    simp only [tvec, Function.update_apply, Pi.one_apply]
    split_ifs
    · exact hζσ'
    · exact hζσ
    · simp
  have hfixSU : ∀ g : gramSU h (idGram K 5),
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (g : GL (Fin 5) K) →
        b (c (uniProj h 5 g)) = c (uniProj h 5 g) :=
    fun g hg => uni_conj_fieldAut_fix h hM (Units.ext (by rw [coe_glAut]; exact hg))
  have hmemC : ∀ g₁ g₂ : gramSU h (idGram K 5),
      ((g₁ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (g₁ : GL (Fin 5) K) →
      ((g₂ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (g₂ : GL (Fin 5) K) →
        c (uniProj h 5 (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)) ∈ Fix := by
    intro g₁ g₂ h₁ h₂
    have := mem_map_autFix_of_commutator hΓ hker.le hβ (hfixSU g₁ h₁) (hfixSU g₂ h₂)
    simpa only [map_mul, map_inv] using this
  set Mg : Subgroup (gramSU h (idGram K 5)) := Fix.comap (c.toMonoidHom.comp (uniProj h 5))
    with hMg
  have hmemM : ∀ g, g ∈ Mg ↔ c (uniProj h 5 g) ∈ Fix := fun g => Iff.rfl
  let ι : Mg →* GL (Fin 5) K := (gramSU h (idGram K 5)).subtype.comp Mg.subtype
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  let π : Mg →* Fix := (c.toMonoidHom.comp ((uniProj h 5).comp Mg.subtype)).codRestrict Fix
    (fun g => g.2)
  have hπapply : ∀ g : Mg, ((π g : Fix) : primeFormP h (idGram K 5)) = c (uniProj h 5 g) :=
    fun g => rfl
  have hπ1 : ∀ g : Mg, π g = 1 → uniProj h 5 (g : gramSU h (idGram K 5)) = 1 := by
    intro g hg
    have h1 : c (uniProj h 5 (g : gramSU h (idGram K 5))) = 1 := by
      rw [← hπapply, hg]
      rfl
    rwa [map_eq_one_iff _ c.injective] at h1
  have hπ : ∀ g : Mg, π g = 1 → ∃ a : Kˣ, ι g = GeneralLinearGroup.scalar (Fin 5) a :=
    fun g hg => uniProj_ker_scalar h _ (hπ1 g hg)
  have hdetT : ((diagHom (tvec ζ (0 : Fin 5) 4) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).det = 1 := det_starX (r := 1) ζ (d := fun _ => 4) (by decide) 0
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1
    (mem_range_gramSU h (tvec_mem_unitary h hζb (0 : Fin 5) 4) hdetT)
  have hyσ : ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (y : GL (Fin 5) K) := by
    have hy' : (y : GL (Fin 5) K) = diagHom (tvec ζ (0 : Fin 5) 4) := hy
    rw [hy']
    exact map_diagHom_eq σ.toRingHom (v := tvec ζ (0 : Fin 5) 4) (fun i => htvecσ 0 4 i)
  have hd : ∀ k : Fin 3, (0 : Fin 5) ≠ ![1, 2, 3] k := by decide
  have hsw : ∀ k : Fin 3, ∃ w : gramSU h (idGram K 5),
      (gramSU h (idGram K 5)).subtype w = starSw (0 : Fin 5) ![1, 2, 3] k ∧
        ((w : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (w : GL (Fin 5) K) ∧
          w ^ 2 ^ 2 = 1 := by
    intro k
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 (mem_range_gramSU h
      (sgnSwap_mem_unitary h (0 : Fin 5) (![1, 2, 3] k)) (det_starSw (d := ![1, 2, 3]) hd k))
    refine ⟨w, hw, ?_, ?_⟩
    · have hw' : (w : GL (Fin 5) K) = sgnSwap 0 (![1, 2, 3] k) := hw
      rw [hw']
      exact map_sgnSwap_eq σ.toRingHom (K := K) (0 : Fin 5) (![1, 2, 3] k)
    · apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      change ((gramSU h (idGram K 5)).subtype w) ^ 2 ^ 2 = 1
      rw [hw]
      exact sgnSwap_pow_four _ _
  choose w hw hwσ hw4 using hsw
  have hcommX : ∀ k : Fin 3, (gramSU h (idGram K 5)).subtype (y * w k * y⁻¹ * (w k)⁻¹) =
      starX ζ (0 : Fin 5) ![1, 2, 3] k := by
    intro k
    have hy' : (y : GL (Fin 5) K) = diagHom (tvec ζ (0 : Fin 5) 4) := hy
    have hw' : (w k : GL (Fin 5) K) = sgnSwap 0 (![1, 2, 3] k) := hw k
    show ((y * w k * y⁻¹ * (w k)⁻¹ : gramSU h (idGram K 5)) : GL (Fin 5) K) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy', hw']
    exact starX_eq_commutator ζ k
  have hmemX : ∀ k, starX ζ (0 : Fin 5) ![1, 2, 3] k ∈ ι.range := by
    intro k
    exact ⟨⟨y * w k * y⁻¹ * (w k)⁻¹, (hmemM _).2 (hmemC y (w k) hyσ (hwσ k))⟩, hcommX k⟩
  have hmemS : ∀ k, starSw (0 : Fin 5) ![1, 2, 3] k ∈ ι.range := by
    intro k
    exact ⟨⟨w k, (hmemM _).2 (uni_conj_proj_mem_fix_of_two h hΓ hker hodd hβ hM (hwσ k)
      (hw4 k))⟩, hw k⟩
  obtain ⟨D, hcard, hX, hS⟩ := exists_torusData_star hζ ι hι π hπ 0 4 ![1, 2, 3] (by decide)
    hd (by decide) (by decide) hmemX hmemS
  refine ⟨D, hcard, fun k => ?_, fun k => ?_⟩
  · obtain ⟨x, hx, hxk⟩ := hX k
    exact ⟨(x : gramSU h (idGram K 5)), hx, by rw [hxk]; exact hπapply x⟩
  · obtain ⟨s, hs, hsk⟩ := hS k
    exact ⟨(s : gramSU h (idGram K 5)), hs, by rw [hsk]; exact hπapply s⟩

end Data

theorem hasTorusFixed_three_primeFormP_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ ℓ ^ f + 1) (h2 : ringChar K ≠ 2) {β : MulAut Lb}
    {b : MulAut (primeFormP h (idGram K 5))} (hβ : ∀ x, Γ (β x) = b (Γ x))
    (hbD : b ∉ primeFormD h (idGram K 5)) (hb5 : b ^ 5 = 1) : HasTorusFixed 5 3 Lb β := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h.finite
  obtain ⟨M, σ, ζ, hM, hζ, hζb, hζσ, -⟩ := exists_descent_primeFormP_five h h5 hbD hb5
  have hneg : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
  obtain ⟨D, hcard, hX, hS⟩ := exists_fixTorus_primeFormP_five h hΓ hker hodd hβ hM hζ hζb hζσ
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (mem_range_gramSU h (negFourVec_mem_unitary h) det_negFourVec)
  have ht' : (t : GL (Fin 5) K) = diagHom (negFourVec (F := K)) := ht
  have htσ : ((t : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map σ = (t : GL (Fin 5) K) := by
    rw [ht']
    exact map_diagHom_eq σ.toRingHom (v := negFourVec (F := K)) (fun i => by
      fin_cases i <;> simp [negFourVec])
  have ht2 : t ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ht', pow_one, ← map_pow, negFourVec_sq,
      map_one]
  set T : ↥((autFix β).map Γ) :=
    ⟨ρ M (uniProj h 5 t), uni_conj_proj_mem_fix_of_two h hΓ hker hodd hβ hM htσ ht2⟩ with hT
  have hcommP : ∀ g : gramSU h (idGram K 5), Commute (t : GL (Fin 5) K) (g : GL (Fin 5) K) →
      ∀ y : ↥((autFix β).map Γ), (y : primeFormP h (idGram K 5)) = ρ M (uniProj h 5 g) →
        Commute T y := by
    intro g hg y hy
    apply Subtype.ext
    show ρ M (uniProj h 5 t) * (y : primeFormP h (idGram K 5)) =
      (y : primeFormP h (idGram K 5)) * ρ M (uniProj h 5 t)
    rw [hy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, (commute_of_gramSU h hg).eq]
  refine hasTorusFixed_of_fixData Nat.prime_five hker hodd β D hcard (T := T) ?_
    ⟨1, Subtype.ext (by
      show (ρ M (uniProj h 5 t)) ^ 2 ^ 1 = 1
      rw [← map_pow, ← map_pow, ht2, map_one, map_one])⟩ ?_ ?_
  · intro h1
    have h1' : ρ M (uniProj h 5 t) = 1 := congrArg Subtype.val h1
    rw [map_eq_one_iff _ (ρ M).injective] at h1'
    obtain ⟨a, ha⟩ := uniProj_ker_scalar h _ h1'
    change (t : GL (Fin 5) K) = _ at ha
    rw [ht'] at ha
    have h0 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) ha
    have h4 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 4 4) ha
    simp [diagHom_apply, coe_diagGL, negFourVec, GeneralLinearGroup.coe_scalar] at h0 h4
    exact hneg (h0.trans h4.symm)
  · intro k
    obtain ⟨x, hx, hxk⟩ := hX k
    refine hcommP x ?_ _ hxk
    rw [ht', hx, starX]
    exact (Commute.all _ _).map diagHom
  · intro k
    obtain ⟨s, hs, hsk⟩ := hS k
    refine hcommP s ?_ _ hsk
    rw [ht', hs, starSw]
    refine (commute_sgnSwap_diag (comp_swap_eq_of_eq ?_)).symm
    fin_cases k <;> simp [negFourVec]

end Five

end CFSG.HardMathSupport.Solomon.Coordinator
