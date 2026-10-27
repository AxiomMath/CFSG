module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLin3Data
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLinRank
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
import CFSG.RankThree.PartOne.KC.CommonEigenbasis
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {K : Type} [Field K] [Finite K]

theorem mem_range_conj_of_commute_lang {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {A B : GL (Fin 3) K}
    (h : slC A * (slC B * slF σ * (slC B)⁻¹) = (slC B * slF σ * (slC B)⁻¹) * slC A) :
    slC A ∈ (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range := by
  have h' : slF σ * slC (B⁻¹ * A * B) = slC (B⁻¹ * A * B) * slF σ := by
    rw [map_mul, map_mul, map_inv]
    calc slF σ * ((slC B)⁻¹ * slC A * slC B)
        = (slC B)⁻¹ * ((slC B * slF σ * (slC B)⁻¹) * slC A) * slC B := by group
      _ = (slC B)⁻¹ * (slC A * (slC B * slF σ * (slC B)⁻¹)) * slC B := by rw [h]
      _ = ((slC B)⁻¹ * slC A * slC B) * slF σ := by group
  obtain ⟨g, hg⟩ := slC_mem_range_conj_of_commute hℓ hf hK hσ h3 h'
  refine ⟨slC B g, ?_⟩
  rw [← mul_conj_mul_inv, hg, map_mul, map_mul, map_inv]
  group

theorem map_range_slC : (slC (K := K)).range.map (descendAut 3 K) = linearAutGroup 3 K := by
  rw [← MonoidHom.range_comp, linearAutGroup_eq_range]
  congr 1

theorem card_inf_range_slC (E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))) :
    Nat.card ↥(E ⊓ (slC (K := K)).range) =
      Nat.card ↥(E.map (descendAut 3 K) ⊓ linearAutGroup 3 K) := by
  rw [← map_range_slC, ← Subgroup.map_inf_eq _ _ _ descendAut_injective,
    Subgroup.card_map_of_injective descendAut_injective]

theorem card_eq_card_center_mul_card_map_conj {M : Type} [Group M] {AM : Subgroup M}
    (hZ : Subgroup.center M ≤ AM) :
    Nat.card AM = Nat.card (Subgroup.center M) * Nat.card (AM.map (MulAut.conj : M →* MulAut M)) := by
  have h := Subgroup.card_ker_mul_card_range ((MulAut.conj : M →* MulAut M).comp AM.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hker : ((MulAut.conj : M →* MulAut M).comp AM.subtype).ker = (Subgroup.center M).subgroupOf AM := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
    constructor
    · exact mem_center_of_conj_eq_one
    · intro hx
      ext g
      rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hx g, mul_inv_cancel_right]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv] at h
  exact h.symm

theorem exists_lang_form {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    {a : MulAut (SpecialLinearGroup (Fin 3) K)} (ha3 : a ^ 3 = 1)
    (haD : descendAut 3 K a ∉ linearAutGroup 3 K) :
    ∃ (B : GL (Fin 3) K) (σ : K ≃+* K), orderOf σ = 3 ∧ a = slC B * slF σ * (slC B)⁻¹ ∧
      3 ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hā1 : descendAut 3 K a ≠ 1 := fun h => haD (h ▸ (linearAutGroup 3 K).one_mem)
  have hā3 : descendAut 3 K a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hāp : orderOf (descendAut 3 K a) = 3 := orderOf_eq_prime hā3 hā1
  have hāS : descendAut 3 K a ∈ semilinearAutGroup 3 K :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      (le_refl 3) (by rw [hāp]; decide)
  obtain ⟨hpf, σ, hσ, ⟨h, hh, hāh⟩, hcard0⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf (le_refl 3) hK Nat.prime_three _ hāS haD hāp
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.1 hh
  refine ⟨B, σ, hσ, descendAut_injective ?_, hpf, hcard0⟩
  rw [hāh, map_mul, map_mul, map_inv, descendAut_slC, descendAut_slF]

theorem dvd_card_sub_one_of_cube {ℓ f : ℕ} (hK : Nat.card K = ℓ ^ f) (hpf : 3 ∣ f) {σ : K ≃+* K}
    (hcard0 : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / 3)) (h3K : 3 ∣ Nat.card K - 1) :
    3 ∣ Nat.card (semilinearFixedSubfield σ) - 1 ∧ 9 ∣ Nat.card K - 1 := by
  set q₀ := Nat.card (semilinearFixedSubfield σ) with hq₀
  have hKq : Nat.card K = q₀ ^ 3 := by
    rw [hK, hcard0, ← pow_mul, Nat.div_mul_cancel hpf]
  have hq₀1 : 1 ≤ q₀ := Nat.card_pos
  have hpow1 : 1 ≤ q₀ ^ 3 := Nat.one_le_pow _ _ hq₀1
  rw [hKq] at h3K ⊢
  have hmod : q₀ ^ 3 % 3 = 1 := by omega
  have hr : (q₀ % 3) ^ 3 % 3 = 1 := by rw [← Nat.pow_mod]; exact hmod
  have h1 : q₀ % 3 = 1 := by
    have : q₀ % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : q₀ % 3 <;> simp_all
  have h3 : 3 ∣ q₀ - 1 := by omega
  refine ⟨h3, ?_⟩
  obtain ⟨t, ht⟩ := h3
  have hq : q₀ = 3 * t + 1 := by omega
  rw [hq]
  exact ⟨3 * t ^ 3 + 3 * t ^ 2 + t, by
    rw [show (3 * t + 1) ^ 3 - 1 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t by
      rw [show (3 * t + 1) ^ 3 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t + 1 by ring]; omega]
    ring⟩

theorem z3Model_sl3 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) : Z3Model 3 (SpecialLinearGroup (Fin 3) K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3K0 : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h')
  have hℓ4 : 4 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have hEmap : ∀ E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K)), IsElemAbelian 3 E →
      IsElemAbelian 3 (E.map (descendAut 3 K)) ∧ Nat.card (E.map (descendAut 3 K)) = Nat.card E :=
    fun E hE => ⟨hE.map _, Subgroup.card_map_of_injective descendAut_injective⟩
  refine ⟨fun E hE => ?_, fun E hE hc AM hcomm hZ hEq => ?_⟩
  · obtain ⟨h1, h2⟩ := hEmap E hE
    rw [← h2]
    exact Lin.card_le_cube Nat.prime_three (by norm_num) h3K0 h1
  obtain ⟨h1, h2⟩ := hEmap E hE
  obtain ⟨hcardL, h3K, ᾱ, hᾱE, hᾱD⟩ :=
    Lin.cube_facts Nat.prime_three (by norm_num) h3K0 h1 (h2.trans hc)
  obtain ⟨a, haE, rfl⟩ := Subgroup.mem_map.1 hᾱE
  have haD : a ∉ (slC (K := K)).range := by
    rintro ⟨A, rfl⟩
    exact hᾱD (mem_linearAutGroup_iff.2 ⟨A, rfl⟩)
  obtain ⟨B, σ, hσ, haB, hpf, hcard0⟩ := exists_lang_form hℓ hf hK (hE.2 a haE) hᾱD
  obtain ⟨h3σ, h9K⟩ := dvd_card_sub_one_of_cube hK hpf hcard0 h3K
  have hInn : E ⊓ (slC (K := K)).range ≤
      (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range := by
    rintro γ ⟨hγE, A, rfl⟩
    refine mem_range_conj_of_commute_lang hℓ hf hK hσ h3σ (B := B) ?_
    rw [← haB]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hγE⟩ ⟨a, haE⟩)
  have hEq2 : E ⊓ (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range =
      E ⊓ (slC (K := K)).range :=
    le_antisymm (inf_le_inf_left _ (by rintro _ ⟨g, rfl⟩; exact ⟨_, slC_toGL g⟩))
      (le_inf inf_le_left hInn)
  have hcardI : Nat.card (AM.map MulAut.conj) = 9 := by
    rw [← hEq, hEq2, card_inf_range_slC, hcardL]
    norm_num
  have hZ3 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) = 3 := by
    obtain ⟨ω, hω⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd h3K
    have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := K) 0
    rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
    exact hω.card_rootsOfUnity
  have h27 : Nat.card AM = 27 := by
    rw [card_eq_card_center_mul_card_map_conj hZ, hZ3, hcardI]
  have hconjE : ∀ x ∈ AM, MulAut.conj x ∈ E := by
    intro x hx
    have h : MulAut.conj x ∈ E ⊓ (MulAut.conj : SpecialLinearGroup (Fin 3) K →*
        MulAut (SpecialLinearGroup (Fin 3) K)).range := by
      rw [hEq]
      exact Subgroup.mem_map_of_mem _ hx
    exact h.1
  have hpow : ∀ x ∈ AM, x ^ 9 = 1 := by
    intro x hx
    have hx3 : x ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
      mem_center_of_conj_eq_one (by rw [map_pow]; exact hE.2 _ (hconjE x hx))
    obtain ⟨c, hc3, hc⟩ := exists_scalar_of_mem_center hx3
    apply Subtype.ext
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, hc3,
      map_one, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨ζ, hζ⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd h9K
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ AM
    (fun x hx y hy => congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hpow
  set e : MulAut (SpecialLinearGroup (Fin 3) K) := slC P with he
  set φ := MulAut.congr e with hφ
  have hφa : ∀ α : MulAut (SpecialLinearGroup (Fin 3) K), φ α = e * α * e⁻¹ := fun α => by
    ext x
    rfl
  have hφconj : ∀ g, φ (MulAut.conj g) = MulAut.conj (e g) := fun g => by
    rw [hφa, mul_conj_mul_inv]
  have hrange : (MulAut.conj : SpecialLinearGroup (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K)).range.map
      φ.toMonoidHom = (MulAut.conj).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨e g, (hφconj g).symm⟩
    · rintro ⟨g, rfl⟩
      refine ⟨MulAut.conj (e⁻¹ g), ⟨_, rfl⟩, ?_⟩
      show φ (MulAut.conj (e⁻¹ g)) = MulAut.conj g
      rw [hφconj, MulAut.apply_inv_self]
  have hEq' : E.map φ.toMonoidHom ⊓ (MulAut.conj).range = (AM.map e.toMonoidHom).map MulAut.conj := by
    rw [← hrange, ← Subgroup.map_inf_eq _ _ _ φ.injective, hEq, Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro g
    exact hφconj g
  have hAM' : IsMulCommutative (AM.map e.toMonoidHom) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y₀, hy₀, hy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg e.toMonoidHom (congrArg Subtype.val (hcomm.is_comm.comm ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩))
  have hdiag' : ∀ d ∈ AM.map e.toMonoidHom, ∀ i j, i ≠ j → (d : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    rintro _ ⟨x, hx, rfl⟩ i j hij
    show ((slC P x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0
    rw [slC_coe]
    exact hP x hx i j hij
  have h27' : Nat.card (AM.map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, h27]
  have ha'E : φ a ∈ E.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ haE
  have ha'D : φ a ∉ (slC (K := K)).range := by
    rintro ⟨A, hA⟩
    apply haD
    refine ⟨P⁻¹ * A * P, ?_⟩
    rw [map_mul, map_mul, map_inv, hA, hφa, he]
    group
  have hdat := z3Data_of_diag hℓ hf hK hℓ4 h2K (hE.map _) hAM' hEq' hdiag' h27' ha'E ha'D
  have h2 := z3Data_congr Nat.prime_three (MulEquiv.symm e) hdat
  have hE'' : (E.map φ.toMonoidHom).map (MulAut.congr (MulEquiv.symm e)).toMonoidHom = E := by
    rw [Subgroup.map_map]
    have : (MulAut.congr (MulEquiv.symm e)).toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext β x
      simp [hφ, MulAut.congr_apply]
    rw [this, Subgroup.map_id]
  rwa [hE''] at h2

theorem mem_zpowers_of_scalar {z g : SpecialLinearGroup (Fin 3) K} {c : K}
    (hc : (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c) (hcp : IsPrimitiveRoot c 3)
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : g ∈ Subgroup.zpowers z := by
  obtain ⟨c', hc'3, hc'⟩ := exists_scalar_of_mem_center hg
  obtain ⟨m, -, hm⟩ := hcp.eq_pow_of_pow_eq_one hc'3
  have : g = z ^ m := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, hc', ← hm, ← map_pow]
  rw [this]
  exact Subgroup.npow_mem_zpowers z m

theorem exists_equiv_sl3 {F : Type} [Field F] [Finite F] (hF2 : Nat.card F ≠ 2) (hF4 : Nat.card F ≠ 4)
    {M : Type} [Group M] [Finite M] (hM : CFSG.Open.IsQuasisimple M) (hZ : Subgroup.center M ≠ ⊥)
    (e : M ⧸ Subgroup.center M ≃* projectiveSL 3 F) :
    Nonempty (M ≃* SpecialLinearGroup (Fin 3) F) ∧ IsPGroup 3 (Subgroup.center M) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρC : SpecialLinearGroup (Fin 3) F →* M ⧸ Subgroup.center M :=
    e.symm.toMonoidHom.comp (proj 3 F) with hρC
  have hC : Function.Surjective ρC := e.symm.surjective.comp (proj_surjective 3 F)
  have hKs : Function.Surjective (QuotientGroup.mk' (Subgroup.center M)) := QuotientGroup.mk'_surjective _
  have hcK : (QuotientGroup.mk' (Subgroup.center M)).ker ≤ Subgroup.center M := by
    rw [QuotientGroup.ker_mk']
  have hperf : Group.IsPerfect M := Group.isPerfect_def.2 hM.1
  obtain ⟨φ, hφ, hφs⟩ := CFSG.LieType.SemisimpleCentralizers.HeldLang.exists_surjective_lift ρC
    (QuotientGroup.mk' (Subgroup.center M)) hC hKs hcK hperf
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (m := 2) (by norm_num)
        (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num) hF2
          (fun h => hF4 h.2) (fun h => absurd h.1 (by norm_num))) hπ hcen)
  have hkerC : ∀ g, ρC g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    intro g hg
    have h1 : proj 3 F g = 1 := by
      have h2 : e.symm (proj 3 F g) = 1 := hg
      rwa [map_eq_one_iff _ e.symm.injective] at h2
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.1 h1
  have hcenM : ∀ m ∈ Subgroup.center M,
      ∃ g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F), φ g = m := by
    intro m hm
    obtain ⟨g, rfl⟩ := hφs m
    refine ⟨g, hkerC g ?_, rfl⟩
    rw [← hφ g]
    exact (QuotientGroup.eq_one_iff _).2 hm
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    by_contra hz1
    have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := hkerC z (by rw [← hφ z, hz, map_one])
    obtain ⟨c, hc3, hc⟩ := exists_scalar_of_mem_center hzc
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hz1
      apply Subtype.ext
      rw [hc, map_one, Matrix.SpecialLinearGroup.coe_one]
    have hcp : IsPrimitiveRoot c 3 := by
      have h := IsPrimitiveRoot.orderOf c
      rwa [orderOf_eq_prime hc3 hc1] at h
    apply hZ
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨g, hg, rfl⟩ := hcenM m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_scalar hc hcp hg)
    rw [Subgroup.mem_bot, map_zpow, hz, _root_.one_zpow]
  refine ⟨⟨(MulEquiv.ofBijective φ ⟨hinj, hφs⟩).symm⟩, fun x => ⟨1, ?_⟩⟩
  obtain ⟨g, hg, hgx⟩ := hcenM x x.2
  obtain ⟨c', hc'3, hc'⟩ := exists_scalar_of_mem_center hg
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc', ← map_pow, hc'3, map_one, Matrix.SpecialLinearGroup.coe_one]
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hgx, ← map_pow, hg3, map_one]

theorem z3LinBranch_holds : Z3LinBranch := by
  intro p Q hp hp2 hQ2 hQp M _ _ hM hO hZ hcat
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .A 2 Q at hi
  subst hi
  let F := GaloisField Q.p Q.exponent
  let e : M ⧸ Subgroup.center M ≃* projectiveSL 3 F := e₀.trans
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  have hcardF : Nat.card F = Q.p ^ Q.exponent := GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
  have hodd : Odd (Nat.card F) := by
    rw [hcardF]
    exact (Q.prime_p.odd_of_ne_two hQ2).pow
  have hF2 : Nat.card F ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  have hF4 : Nat.card F ≠ 4 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  obtain ⟨⟨eM⟩, hpg⟩ := exists_equiv_sl3 hF2 hF4 hM hZ e
  have hp3 : p = 3 := by
    by_contra hp3
    apply hZ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center M)) := by
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    have hle : Subgroup.center M ≤ GLAPPrimeCore p M :=
      show Subgroup.center M ≤ CFSG.pPrimeCore p M from le_sSup ⟨inferInstance, hcop⟩
    rw [hO] at hle
    exact eq_bot_iff.2 hle
  subst hp3
  exact z3Model_congr Nat.prime_three eM.symm
    (z3Model_sl3 Q.prime_p Q.exponent_pos hcardF hQ2 hQp)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3

end
