module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Sp44
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdEven
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix Assembly.LowTwoRank LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher UnbalancedCatalog UnbalancedCatalog.SpChain
open scoped commutatorElement

theorem card_of_lieModel_Sp44 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSp 2 2 2) :
    Nat.card Y = 979200 := by
  rw [Catalog7Std.card_of_lieModel_PSp (by norm_num) h]
  decide


theorem sp44 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSp 2 2 2 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  have := hN
  have hst := RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY
  obtain ⟨⟨-, he, hr, hne⟩, K, _, _, hK, ⟨φ⟩⟩ := hst
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have hs : IsSimpleGroup ↥N := (LieType.Simplicity.fam_classical_converse ↥N
    ⟨.PSp, 2, 2, 2, RestrictedStd.statedClassicalModel_of_lieModel (by decide) hY⟩).2.2
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have : IsMulCommutative ↥N := ⟨⟨hc⟩⟩
    have hpr := Group.is_simple_iff_prime_card.mp hs
    rw [card_of_lieModel_Sp44 hY] at hpr
    exact absurd hpr (by norm_num)
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  have hLCW : Assembly.IsComponentOf J (N ⊓ centralizer ({α} : Set G)) :=
    isComponentOf_of_le hJc (le_inf hJN hJc.1) inf_le_right
  obtain ⟨p', f', hp'2, hsrc⟩ : ∃ p f : ℕ, p ≠ 2 ∧
      (StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2) := by
    rcases hsmall with ⟨p', f', -, hp'2, -, -, hm'⟩ | h7
    · exact ⟨p', f', hp'2, Or.inl (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm')⟩
    · exact ⟨3, 1, by decide, Or.inr (Or.inl h7)⟩
  have hre : ¬ (2 = 2 ∧ 2 = 1) := by omega
  obtain ⟨ρ, hρinj, hρW, -, g, σ, hσ, hρa⟩ :=
    OutcomeLocal.sp_socle_extension hnab hC hα hLCW hp'2 hsrc (by norm_num : 2 ≤ 2)
      (by norm_num : 1 ≤ 2) hre hK φ
  obtain ⟨-, -, -, -, hσsq, -, -, -, -, hι₀inj, -, -, -, -, h, hρa', -, -, hLmap, -⟩ :=
    OutcomeLocal.sp_socle_field_case hα hLCW (by norm_num : 2 ≤ 2) (by norm_num : 1 ≤ 2) hK φ
      hρinj hρW hσ hρa hp'2 hsrc
  obtain ⟨ω, hω⟩ := exists_omega_four (K := K) (by rw [hK]; norm_num)
  obtain ⟨hk2, hkJ, hkσ⟩ := sp44K_facts ω hω
  obtain ⟨-, -, -, hU, hV, -, hG2, hG1⟩ := sp44_mat_facts
  set k := descentField σ with hkdef
  let ψk := ZMod.castHom (dvd_refl 2) ↥k
  let ψK := ZMod.castHom (dvd_refl 2) K
  have hu : sp44GU ∈ StatedSp 2 (ZMod 2) := SymplecticTorusWeyl.mem_statedSp_iff.mpr hU
  have hv : sp44GV ∈ StatedSp 2 (ZMod 2) := SymplecticTorusWeyl.mem_statedSp_iff.mpr hV
  let u' : StatedSp 2 ↥k := ⟨GeneralLinearGroup.map ψk sp44GU, UnitaryHigher.map_mem_statedSp ψk hu⟩
  let v' : StatedSp 2 ↥k := ⟨GeneralLinearGroup.map ψk sp44GV, UnitaryHigher.map_mem_statedSp ψk hv⟩
  set g' := ⁅u', v'⁆ with hg'def
  have hψ : k.subtype.comp ψk = ψK := RingHom.ext_zmod _ _
  have hjg : ((subfieldSpHom 2 k g' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.map ψK ⁅sp44GU, sp44GV⁆ := by
    apply Units.ext
    show ((g' : GL (Fin 2 ⊕ Fin 2) ↥k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥k).map k.subtype =
      _
    rw [hg'def, show ((⁅u', v'⁆ : StatedSp 2 ↥k) : GL (Fin 2 ⊕ Fin 2) ↥k) =
      ⁅(u' : GL (Fin 2 ⊕ Fin 2) ↥k), (v' : GL (Fin 2 ⊕ Fin 2) ↥k)⁆ from
        map_commutatorElement (StatedSp 2 ↥k).subtype u' v', ← map_commutatorElement]
    show (((⁅sp44GU, sp44GV⁆ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map ψk).map k.subtype = _
    rw [Matrix.map_map]
    show ((⁅sp44GU, sp44GV⁆ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map (k.subtype.comp ψk) = _
    rw [hψ]
    rfl
  have hjgM : (((subfieldSpHom 2 k g' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 !![1, 0; 0, 0] !![0, 0; 0, 1] 1 := by
    rw [hjg]
    show ((⁅sp44GU, sp44GV⁆ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map ψK = _
    rw [coe_sp44_comm, sp44G_map]
  let k₀GL : GL (Fin 2 ⊕ Fin 2) K := ⟨sp44K ω, sp44K ω, hk2, hk2⟩
  have hk₀ : k₀GL ∈ StatedSp 2 K := SymplecticTorusWeyl.mem_statedSp_iff.mpr hkJ
  let k₀ : StatedSp 2 K := ⟨k₀GL, hk₀⟩
  have hσfun : (σ : K → K) = (· ^ 2) := funext hσsq
  have hσk : fieldSp 2 K σ k₀ = k₀ * subfieldSpHom 2 k g' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp]
    show (sp44K ω).map σ = sp44K ω * (((subfieldSpHom 2 k g' : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)
    rw [hjgM, ← hkσ]
    congr 1
  have hσj : fieldSp 2 K σ (subfieldSpHom 2 k g') = subfieldSpHom 2 k g' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp, hjgM, fromBlocks_map]
    congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
  have hfc : ∀ x : StatedSp 2 K,
      fieldAut 2 K σ * spInner 2 K x = spInner 2 K (fieldSp 2 K σ x) * fieldAut 2 K σ := by
    intro x
    rw [← fieldAut_mul_spInner_mul_inv, inv_mul_cancel_right]
  have key : (spInner 2 K k₀)⁻¹ * fieldAut 2 K σ * spInner 2 K k₀ =
      fieldAut 2 K σ * spInner 2 K (subfieldSpHom 2 k g') := by
    rw [mul_assoc, hfc, hσk, hfc, hσj, map_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel,
      one_mul]
  set Ch := spInner 2 K h with hChdef
  have hgN' : spInner 2 K (subfieldSpHom 2 k g') ∈
      ⁅((spInner 2 K).comp (subfieldSpHom 2 k)).range,
        ((spInner 2 K).comp (subfieldSpHom 2 k)).range⁆ := by
    have : spInner 2 K (subfieldSpHom 2 k g') = ⁅((spInner 2 K).comp (subfieldSpHom 2 k)) u',
        ((spInner 2 K).comp (subfieldSpHom 2 k)) v'⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [this]
    exact commutator_mem_commutator ⟨u', rfl⟩ ⟨v', rfl⟩
  have hz : Ch * spInner 2 K (subfieldSpHom 2 k g') * Ch⁻¹ ∈ J.map ρ := by
    rw [hLmap]
    exact ⟨_, hgN', by simp [MulAut.conj_apply]⟩
  obtain ⟨z, hzJ, hρz⟩ := mem_map.mp hz
  have hg'2 : orderOf g' = 2 := by
    have hinjk : Function.Injective (GeneralLinearGroup.map (n := Fin 2 ⊕ Fin 2) ψk) := by
      intro x y hxy
      apply Units.ext
      have := congrArg
        (fun w : GL (Fin 2 ⊕ Fin 2) ↥k => (w : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥k)) hxy
      exact Matrix.map_injective ψk.injective this
    have hc : ((g' : GL (Fin 2 ⊕ Fin 2) ↥k)) = GeneralLinearGroup.map ψk ⁅sp44GU, sp44GV⁆ := by
      rw [hg'def, show ((⁅u', v'⁆ : StatedSp 2 ↥k) : GL (Fin 2 ⊕ Fin 2) ↥k) =
        ⁅(u' : GL (Fin 2 ⊕ Fin 2) ↥k), (v' : GL (Fin 2 ⊕ Fin 2) ↥k)⁆ from
          map_commutatorElement (StatedSp 2 ↥k).subtype u' v', ← map_commutatorElement]
    rw [← Subgroup.orderOf_coe, hc, orderOf_injective _ hinjk]
    refine orderOf_eq_prime (Units.ext ?_) fun h1 => hG1 ?_
    · rw [pow_two, Units.val_mul, coe_sp44_comm, hG2, Units.val_one]
    · rw [← coe_sp44_comm, h1, Units.val_one]
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective ρ hρinj, hρz, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have := orderOf_injective _ hι₀inj g'
    simp only [MonoidHom.coe_comp, Function.comp_apply] at this
    rw [this, hg'2]
  set γ₀ : G := ((φ.symm (proj 2 K (h * k₀ * h⁻¹)) : N) : G) with hγ₀def
  have hργ₀ : ρ γ₀ = Ch * spInner 2 K k₀ * Ch⁻¹ := by
    rw [hγ₀def, hρW, MulEquiv.apply_symm_apply, ← spInner_eq_conj, map_mul, map_mul, map_inv]
  refine concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hzJ hz2
    (φ.symm (proj 2 K (h * k₀ * h⁻¹))).2 (hρinj ?_)
  rw [map_mul, map_mul, map_inv, hργ₀, hρa', map_mul, hρa', hρz]
  calc (Ch * spInner 2 K k₀ * Ch⁻¹)⁻¹ * (Ch * fieldAut 2 K σ * Ch⁻¹) *
        (Ch * spInner 2 K k₀ * Ch⁻¹) =
        Ch * ((spInner 2 K k₀)⁻¹ * fieldAut 2 K σ * spInner 2 K k₀) * Ch⁻¹ := by group
    _ = Ch * (fieldAut 2 K σ * spInner 2 K (subfieldSpHom 2 k g')) * Ch⁻¹ := by rw [key]
    _ = Ch * fieldAut 2 K σ * Ch⁻¹ * (Ch * spInner 2 K (subfieldSpHom 2 k g') * Ch⁻¹) := by
      group

end CFSG.ComponentClassification.GSThmB.CF23I
