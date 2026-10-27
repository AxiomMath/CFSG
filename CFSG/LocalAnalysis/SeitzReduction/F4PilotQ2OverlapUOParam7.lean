module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamTw
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.SeitzReduction.SymplecticPilot (ctuEmbed ctuBlock ctuBlockEquiv complSpEquiv)

section Norm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_normalized_coverU7 {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (e : L ≃* adjointGroup .F4 K) (ε : h.fixedField ≃+* K) {t : G} (Φ₁ : uGroup7 h →* G)
    (hker : Φ₁.ker ≤ center (uGroup7 h))
    (hc : ∀ g, t * Φ₁ g * t⁻¹ =
      Φ₁ (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv g))
    (hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X) :
    ∃ Φ' : uGroup7 h →* G, Φ'.range = Φ₁.range ∧ Φ'.ker ≤ center (uGroup7 h) ∧
      ∀ s : StatedSp 3 h.fixedField, Φ' (uEmbed7 h s) = levi6Hom e ε s := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := finite_gramSU h ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)
  have hfix : fixedSubgroup (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv) =
      (uEmbed7 h).range := fixedSubgroup_barSU7 h
  have hιperf : ⁅(uEmbed7 h).range, (uEmbed7 h).range⁆ = (uEmbed7 h).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hcore : perfectCore (fixedSubgroup
      (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv)) = (uEmbed7 h).range := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hβ : ∀ g, Φ₁ (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv g) =
      t * Φ₁ g * t⁻¹ := fun g => (hc g).symm
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₁ hker hβ
  rw [hcore, hD] at hmap
  set κ : StatedSp 3 h.fixedField →* G := Φ₁.comp (uEmbed7 h) with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : uEmbed7 h g ∈ center (uGroup7 h) := hker hg
    have hgc' : g ∈ center (StatedSp 3 h.fixedField) := by
      rw [mem_center_iff]
      intro x
      apply uEmbed7_injective h
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hgc (uEmbed7 h x)
    rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot] at hgc'
    exact mem_bot.mp hgc'
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 h.fixedField) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  obtain ⟨ρ'', hρ''⟩ := exists_ringEquiv_extend h ρ
  set δh : MulAut (uGroup7 h) :=
    MulAut.conj (uEmbed7 h s) * primeFormFieldSU h (isPrimeFormGram_graphGram7 F) ρ'' with hδh
  set Φ' : uGroup7 h →* G := Φ₁.comp δh.toMonoidHom with hΦ'
  have hΦ'ι : ∀ g, Φ' (uEmbed7 h g) = levi6Hom e ε g := by
    intro g
    rw [← hκδ, hsρ, hκdef]
    change Φ₁ (uEmbed7 h s * primeFormFieldSU h (isPrimeFormGram_graphGram7 F) ρ''
        (uEmbed7 h g) * (uEmbed7 h s)⁻¹) =
      Φ₁ (uEmbed7 h (s * statedSpMap ((ρ : h.fixedField ≃+* h.fixedField) :
        h.fixedField →+* h.fixedField) 3 g * s⁻¹))
    rw [primeFormFieldSU_uEmbed7 h hρ'']
    simp only [map_mul, map_inv]
  refine ⟨Φ', ?_, ?_, hΦ'ι⟩
  · rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 δh.surjective,
      ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : δh g ∈ center (uGroup7 h) := hker hg
    rw [← Subgroup.map_center_eq (δh.symm : uGroup7 h ≃* uGroup7 h)]
    exact ⟨δh g, h1, δh.symm_apply_apply g⟩

end Norm

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_twoSu7Cover {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 1) ^ 2 ∧
      ∃ Φ : StatedSU 7 (2 ^ 1) F →* G, Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧
        Φ.ker ≤ center (StatedSU 7 (2 ^ 1) F) := by
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  obtain ⟨S, _, hS, ρ, hρ, hker, hodd⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .unitary7) (by decide) hk
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (2 ^ 1) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 7 (2 ^ 1) F)) := by
    rcases hS with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * 1) (by
    rw [hF, ← pow_mul, mul_comm])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := StatedSU 7 (2 ^ 1) F
  set π : M →* StatedProj M := QuotientGroup.mk' ((StatedScalars (Fin 7) F).subgroupOf M)
  set ρ' : E →* StatedProj M := ε.toMonoidHom.comp ρ
  have hρ' : Function.Surjective ρ' := ε.surjective.comp hρ
  have hkerρ : ρ'.ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ε.map_eq_one_iff]
  have hker' : ρ'.ker ≤ center E := hkerρ ▸ hker
  have hodd' : Odd (Nat.card ρ'.ker) := hkerρ ▸ hodd
  have : Group.IsPerfect E := isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central_odd π (QuotientGroup.mk'_surjective _)
    (fun E' _ _ π' hπ' hcen' hodd'' =>
      CFSG.SeitzReduction.UnitaryPilot.exists_section_statedSU_of_coprime hF (m := 7)
        (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num)) hπ' hcen'
        (fun _ => Nat.coprime_two_left.2 hodd'')) ρ' hρ' hker' hodd'
  refine ⟨F, inferInstance, inferInstance, hF, E.subtype.comp Φ₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro g hg
    have hg₀ : Φ₀ g = 1 := E.subtype_injective (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact statedScalars_subgroupOf_le_center M h1

theorem exists_twoUnitary7Cover_normalized {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (h : UnitaryFieldData 2 1 F)
      (ε : h.fixedField ≃+* K) (Φ : uGroup7 h →* G),
      Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧ Φ.ker ≤ center (uGroup7 h) ∧
      ∀ s : StatedSp 3 h.fixedField, Φ (uEmbed7 h s) = levi6Hom e ε s := by
  obtain ⟨F, _, _, hF1, Φ₀, hE₀, hker₀⟩ := exists_twoSu7Cover hw e hXJ hcyc hX₀ hk
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * 1) (by
    rw [hF1, ← pow_mul, mul_comm])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 1 F := unitaryFieldData_of_card (by omega) hF1
  have eS : StatedSU 7 (2 ^ 1) F =
      gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h 7
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 7) (by norm_num) (by omega)
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)),
      Function.Surjective π' → π'.ker ≤ center E' → Odd (Nat.card π'.ker) →
        ∃ s : gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) →* E',
          ∀ g, π' (s g) = g := by
    intro E' _ _ π' hπ' hcen hodd
    have hkerE : (eM.symm.toMonoidHom.comp π').ker = π'.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ eM.symm.injective]
    obtain ⟨s, hs⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_section_statedSU_of_coprime hF1
        (m := 7) (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num))
        (π := eM.symm.toMonoidHom.comp π') (eM.symm.surjective.comp hπ') (hkerE ▸ hcen)
        (fun _ => Nat.coprime_two_left.2 (hkerE ▸ hodd))
    refine ⟨s.comp eM.symm.toMonoidHom, fun g => eM.symm.injective ?_⟩
    exact hs (eM.symm g)
  have hoddZ : Odd (Nat.card (center (StatedSU 7 (2 ^ 1) F))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr
      (CFSG.LieType.Universal.Unitary.equivStatedSU hF1 7)).toEquiv]
    exact CFSG.SeitzReduction.SymplecticPilot.odd_card_center_SU hF1 le_rfl (by norm_num)
      (by decide)
  have hodd₁ : Odd (Nat.card Φ₁.ker) := by
    have h1 : Nat.card (center (gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F))) =
        Nat.card (center (StatedSU 7 (2 ^ 1) F)) :=
      Nat.card_congr (Subgroup.centerCongr eM.symm).toEquiv
    exact Odd.of_dvd_nat (h1 ▸ hoddZ) (Subgroup.card_dvd_of_le hker₁)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ := exists_twoGraphLift_of_oddClosed hw e hXJ hcyc hX₀
    (κ := .unitary7) (by decide) hk hsplit Φ₁ hE₁ hker₁ hodd₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary7_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ =
      Φ₂ (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hw.card_eq, pow_one]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀']
    rfl
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr', hk', hn'⟩ := exists_normalized_coverU7 h e ε Φ₂ hker₂ hc hD
  exact ⟨F, inferInstance, inferInstance, inferInstance, h, ε, Φ', hr'.trans hE₂, hk', hn'⟩

end Cover

section Gram7

open CFSG.SeitzReduction.SymplecticPilot (transportMat transportMat_mul transportMat_one
  det_transportMat transportMat_isometry transportMat_symm_transportMat
  transportMat_transportMat_symm ringEquiv_unitaryInvolution ringEquiv_symm_bar ctuCoord ctuPar
  antidiag_ctuCoord)
open CFSG.LieType.Universal.Unitary (antidiag conjTr)

@[expose] def twoU7IdxFun : (Fin 3 ⊕ Fin 3) ⊕ Fin 1 → Fin 7 :=
  Sum.elim (fun u => (sp6ToSLIdx u).castSucc) fun _ => 6

theorem twoU7IdxFun_bijective : Function.Bijective twoU7IdxFun := by
  decide

@[expose] noncomputable def twoU7Idx : (Fin 3 ⊕ Fin 3) ⊕ Fin 1 ≃ Fin 7 :=
  Equiv.ofBijective _ twoU7IdxFun_bijective

@[expose] noncomputable def twoU7Tau : Fin 7 ≃ Fin (2 * 3 + 1) :=
  twoU7Idx.symm.trans (ctuCoord 3 1)

theorem twoU7Tau_twoU7Idx (w : (Fin 3 ⊕ Fin 3) ⊕ Fin 1) :
    twoU7Tau (twoU7Idx w) = ctuCoord 3 1 w := by
  simp [twoU7Tau]

theorem ctuPar_iff_gram7 : ∀ w w' : (Fin 3 ⊕ Fin 3) ⊕ Fin 1, w' = ctuPar w ↔
    (((twoU7IdxFun w : Fin 7) : ℕ) < 3 ∧ ((twoU7IdxFun w' : Fin 7) : ℕ) =
        (twoU7IdxFun w : ℕ) + 3) ∨
      (((twoU7IdxFun w' : Fin 7) : ℕ) < 3 ∧ ((twoU7IdxFun w : Fin 7) : ℕ) =
        (twoU7IdxFun w' : ℕ) + 3) ∨
      (((twoU7IdxFun w : Fin 7) : ℕ) = 6 ∧ ((twoU7IdxFun w' : Fin 7) : ℕ) = 6) := by
  decide

theorem transportMat_antidiag_twoU7 {F : Type} [Field F] :
    transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
      (antidiag (2 * 3 + 1) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F) = gram7 F := by
  ext a b
  obtain ⟨w, rfl⟩ := twoU7Idx.surjective a
  obtain ⟨w', rfl⟩ := twoU7Idx.surjective b
  rw [transportMat, Matrix.map_apply, submatrix_apply, twoU7Tau_twoU7Idx, twoU7Tau_twoU7Idx,
    antidiag_ctuCoord (by omega), gram7, of_apply]
  have e1 : (twoU7Idx w : Fin 7) = twoU7IdxFun w := rfl
  have e2 : (twoU7Idx w' : Fin 7) = twoU7IdxFun w' := rfl
  rw [e1, e2]
  by_cases hw : w' = ctuPar w
  · rw [ite_eq_left hw, ite_eq_left ((ctuPar_iff_gram7 w w').1 hw)]
    simp
  · rw [ite_eq_right hw, ite_eq_right (mt (ctuPar_iff_gram7 w w').2 hw)]
    simp

variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)

theorem transportMat_mem_uGroup7 (y : SU (unitaryInvolution F 2 1) (2 * 3 + 1)) :
    ((transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
        ((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F)).map
          h.bar)ᵀ * ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) *
      transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
        ((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F) =
        ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) ∧
      (transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
        ((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F)).det =
          1 := by
  refine ⟨?_, by rw [det_transportMat, y.2.1, map_one]⟩
  rw [coe_graphGram7, ← transportMat_antidiag_twoU7]
  exact transportMat_isometry _ _ (ringEquiv_unitaryInvolution h (RingEquiv.refl F)) y.2.2

@[expose] noncomputable def twoU7Hom :
    SU (unitaryInvolution F 2 1) (2 * 3 + 1) →* uGroup7 h where
  toFun y := ⟨⟨transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
      ((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F),
      transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
        ((y⁻¹ : SU (unitaryInvolution F 2 1) (2 * 3 + 1)) : GL (Fin (2 * 3 + 1)) F),
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one],
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one]⟩,
    transportMat_mem_uGroup7 h y⟩
  map_one' := Subtype.ext (Units.ext (by
    change transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
      (1 : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F) = 1
    rw [transportMat_one]))
  map_mul' y z := Subtype.ext (Units.ext (by
    change transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
      (((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F) *
        ((z : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F)) = _
    rw [transportMat_mul]
    rfl))

theorem coe_twoU7Hom (y : SU (unitaryInvolution F 2 1) (2 * 3 + 1)) :
    (((twoU7Hom h y : uGroup7 h) : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) =
      transportMat (RingEquiv.refl F : F →+* F) twoU7Tau
        ((y : GL (Fin (2 * 3 + 1)) F) : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) F) := rfl

theorem twoU7Hom_bijective : Function.Bijective (twoU7Hom h) := by
  constructor
  · intro y z hyz
    have h1 := congrArg (fun g : uGroup7 h =>
      transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
        ((g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)) hyz
    simp only [coe_twoU7Hom, transportMat_symm_transportMat] at h1
    exact Subtype.ext (Units.ext h1)
  · intro g
    have hC' : transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
        ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = antidiag (2 * 3 + 1) := by
      rw [coe_graphGram7, ← transportMat_antidiag_twoU7, transportMat_symm_transportMat]
    have hiso : ∀ g' : uGroup7 h,
        conjTr (unitaryInvolution F 2 1) (transportMat ((RingEquiv.refl F).symm : F →+* F)
          twoU7Tau.symm ((g' : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)) *
          antidiag (2 * 3 + 1) * transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
            ((g' : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = antidiag (2 * 3 + 1) := by
      intro g'
      rw [← hC']
      exact transportMat_isometry _ _ (ringEquiv_symm_bar h (RingEquiv.refl F)) g'.2.1
    refine ⟨⟨⟨transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
        ((g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F),
      transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
        ((g⁻¹ : uGroup7 h) : GL (Fin 7) F),
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one],
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one]⟩,
      by
        change (transportMat ((RingEquiv.refl F).symm : F →+* F) twoU7Tau.symm
          ((g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)).det = 1
        rw [det_transportMat, g.2.2, map_one],
      hiso g⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_twoU7Hom]
    exact transportMat_transportMat_symm (RingEquiv.refl F) twoU7Tau _

@[expose] noncomputable def twoU7Equiv : SU (unitaryInvolution F 2 1) (2 * 3 + 1) ≃* uGroup7 h :=
  MulEquiv.ofBijective (twoU7Hom h) (twoU7Hom_bijective h)

end Gram7

section Block

open CFSG.SeitzReduction.SymplecticPilot (transportMat ctuEmbed_apply_ctuCoord)

theorem twoU7Hom_ctuEmbed {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 1 F) [CharP h.fixedField 2] (ε : h.fixedField ≃+* K)
    (hι : ∀ c, unitaryInvolution F 2 1 ((h.fixedField.subtype.comp
      (ε.symm : K →+* h.fixedField)) c) =
        (h.fixedField.subtype.comp (ε.symm : K →+* h.fixedField)) c) (y : StatedSp 3 K) :
    twoU7Hom h (ctuEmbed 1 le_rfl (unitaryInvolution F 2 1)
        (h.fixedField.subtype.comp (ε.symm : K →+* h.fixedField)) hι y) =
      uEmbed7 h (statedSpMap (ε.symm : K →+* h.fixedField) 3 y) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_twoU7Hom, coe_uEmbed7]
  ext a b
  obtain ⟨w, rfl⟩ := twoU7Idx.surjective a
  obtain ⟨w', rfl⟩ := twoU7Idx.surjective b
  rw [transportMat, Matrix.map_apply, submatrix_apply, twoU7Tau_twoU7Idx, twoU7Tau_twoU7Idx,
    ctuEmbed_apply_ctuCoord, Matrix.map_apply, coe_sp6ToSL7]
  have e1 : ∀ u, twoU7Idx (Sum.inl u) = (sp6ToSLIdx u).castSucc := fun u => rfl
  have e2 : ∀ i, twoU7Idx (Sum.inr i) = 6 := fun i => rfl
  rcases w with u | i <;> rcases w' with v | j
  · rw [e1, e1, sp6ToSLBlockMat_castSucc_castSucc, fromBlocks_apply₁₁, Matrix.map_apply,
      coe_sp6ToSL6, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  · rw [e1, e2, sp6ToSLBlockMat_castSucc_six, fromBlocks_apply₁₂]
    simp
  · rw [e2, e1, sp6ToSLBlockMat_six_castSucc, fromBlocks_apply₂₁]
    simp
  · rw [e2, e2, sp6ToSLBlockMat_six_six, fromBlocks_apply₂₂, Subsingleton.elim i j,
      Matrix.one_apply_eq]
    simp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_twoUnitary7BlockCover {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
      (Φ : ctuBlock (unitaryInvolution F 2 1) 1 ({3} : Finset (Fin 4)) →* G),
      Nat.card F = (2 ^ 1) ^ 2 ∧ Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧
      Φ.ker ≤ center (ctuBlock (unitaryInvolution F 2 1) 1 ({3} : Finset (Fin 4))) ∧
      ∀ g, Φ (twoUniIota le_rfl hι g) = ((e.symm (c3LeviHom K g) : L) : G) := by
  obtain ⟨F, _, _, _, h, ε, Φ, hr, hker, hn⟩ :=
    exists_twoUnitary7Cover_normalized hw e hXJ hcyc hX₀ hk
  have := fixedField_charP h
  have hF : Nat.card F = (2 ^ 1) ^ 2 := by rw [h.card]; norm_num
  set ι : K →+* F := h.fixedField.subtype.comp (ε.symm : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
    exact (h.mem_fixedField).1 (ε.symm c).2
  set β := ctuBlockEquiv (unitaryInvolution F 2 1) (le_rfl : 1 ≤ 1) (3 : Fin (3 + 1)) with hβ
  set Φ' : ctuBlock (unitaryInvolution F 2 1) 1 ({3} : Finset (Fin 4)) →* G :=
    Φ.comp ((twoU7Equiv h).toMonoidHom.comp β.toMonoidHom) with hΦ'
  have hr' : Φ'.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ((twoU7Equiv h).surjective.comp β.surjective), ← MonoidHom.range_eq_map, hr]
  have hker' : Φ'.ker ≤ center (ctuBlock (unitaryInvolution F 2 1) 1 ({3} : Finset (Fin 4))) :=
    ker_comp_mulEquiv_le_center Φ hker (β.trans (twoU7Equiv h))
  refine ⟨F, inferInstance, inferInstance, inferInstance, ι, hι, Φ', hF, hr', hker', fun g => ?_⟩
  have h1 : β (twoUniIota le_rfl hι g) = ctuEmbed 1 le_rfl (unitaryInvolution F 2 1) ι hι g :=
    CFSG.SeitzReduction.SymplecticPilot.ctuBlockEquiv_ctuEmbed le_rfl hι
      (3 : Fin (3 + 1)) g (twoUniIota le_rfl hι g).2
  have h3 : twoU7Equiv h (ctuEmbed 1 le_rfl (unitaryInvolution F 2 1) ι hι g) =
      uEmbed7 h (statedSpMap (ε.symm : K →+* h.fixedField) 3 g) :=
    twoU7Hom_ctuEmbed h ε hι g
  have h4 : statedSpCongr ε 3 (statedSpMap (ε.symm : K →+* h.fixedField) 3 g) = g :=
    (statedSpCongr ε 3).apply_symm_apply g
  change Φ (twoU7Equiv h (β (twoUniIota le_rfl hι g))) = _
  rw [h1, h3, hn, levi6Hom]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, h4, coe_subtype]
  rfl

theorem twoGraphCoverInput_unitary7_of_values
    (hV : ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
      Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
        (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
        TwoUniBlockValues .unitary7 le_rfl ι hι) :
    TwoGraphCoverInput .unitary7 := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨F, _, _, _, ι, hι, Φ, hF, hr, hker, hn⟩ :=
    exists_twoUnitary7BlockCover hw e hXJ hcyc hX₀ hk
  exact ⟨_, inferInstance, inferInstance, twoUniIota le_rfl hι, Φ, hr, hker, hn,
    twoGraphCoverModel_twoUniIota hK hF le_rfl hι (hV K F hK hF ι hι)⟩

theorem twoOverlapInvAt_unitary7_of_values
    (hV : ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
      Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
        (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
        TwoUniBlockValues .unitary7 le_rfl ι hι) :
    TwoOverlapInvAt .unitary7 :=
  twoOverlapInvAt_of_coverInput (twoGraphCoverInput_unitary7_of_values hV)

end Block

end CFSG.SeitzReduction.F4Pilot
