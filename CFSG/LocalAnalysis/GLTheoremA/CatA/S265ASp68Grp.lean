module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68Lin
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpCent
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Lay

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut proj_surjective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.CASymplecticSubfield (subfieldSpProj subfieldFixedGroup subfieldSpProj_proj)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap mat_spMap spMap_injective spMap_surjective)
open CFSG.RankThree.Classical (spEnd)

section Field

variable {K : Type} [Field K] [Finite K]

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross in
private theorem exists_sp62Embedding (hK : Nat.card K = 8) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ (ι : ZMod 2 →+* K) (j : StatedSp 3 (ZMod 2) →* StatedProj (StatedSp 3 K)),
      Function.Injective j ∧ (∀ g, j g = proj 3 K (spMap ι g)) ∧
      ∀ x, x ∈ j.range ↔ fieldAut 3 K σ x = x := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, hkcard, -, -, -, hfix, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) (r := 3)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK' σ hσ
  set k := descentField σ
  have hk2 : Nat.card k = 2 := by rw [hkcard]; norm_num
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num : 1 ≤ 3) hK'
  let τ : ZMod 2 ≃+* k := ZMod.ringEquivOfPrime k Nat.prime_two
    (by rw [← Nat.card_eq_fintype_card, hk2])
  let ι : ZMod 2 →+* K := k.subtype.comp τ.toRingHom
  let j : StatedSp 3 (ZMod 2) →* StatedProj (StatedSp 3 K) :=
    (subfieldSpProj 3 k).comp ((proj 3 k).comp (spMap τ.toRingHom))
  have hj : ∀ g, j g = proj 3 K (spMap ι g) := fun g => by
    change proj 3 K (subfieldSpHom 3 k (spMap τ.toRingHom g)) = _
    congr 1
    refine Subtype.ext (Units.ext ?_)
    change ((spMap τ.toRingHom g : GL (Fin 3 ⊕ Fin 3) k) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k).map k.subtype = _
    rw [← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, mat_spMap,
      ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, mat_spMap, Matrix.map_map]
    rfl
  have hsurj : Function.Surjective ((proj 3 k).comp (spMap τ.toRingHom)) :=
    proj_surjective.comp (spMap_surjective τ)
  refine ⟨ι, j, ?_, hj, fun x => ?_⟩
  · have hinj : Function.Injective (proj 3 K) :=
      CFSG.HardMathSupport.Dickson.Bal207.proj_injective_of_charP_two 3
    intro g h hgh
    rw [hj, hj] at hgh
    exact spMap_injective ι (hinj hgh)
  · have hrange : j.range = (subfieldSpProj 3 k).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map]
    rw [← hfix x, hrange]
    rfl

theorem exists_elemAbelian_fixSubgroup_fieldAut_eight (hK : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    ∃ E : Subgroup (StatedProj (StatedSp 3 K)), E ≤ fixSubgroup (fieldAut 3 K σ) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, j, hj, -, hfix⟩ := exists_sp62Embedding hK hσ
  obtain ⟨Q, -, hQr⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.spF2QTorus_holds 3 (ZMod 2)
    (Nat.card_zmod 2) le_rfl
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hQr
  refine ⟨E.map j, fun x hx => ?_, CFSG.SectionRank.isElemAbelian_map hE j, ?_⟩
  · obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (hfix _).mp ⟨g, rfl⟩
  · rw [Subgroup.card_map_of_injective hj, hEc]
    norm_num

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross in
theorem glaPLayer_fixSubgroup_fieldAut_eight (hK : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    GLAPLayer 3 (fixSubgroup (fieldAut 3 K σ)) = fixSubgroup (fieldAut 3 K σ) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, hfix, -, hJs, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) (r := 3)
      Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK' σ hσ
  have hH : subfieldFixedGroup K 3 σ = fixSubgroup (fieldAut 3 K σ) := Subgroup.ext hfix
  obtain ⟨hsimple, x, y, hxy⟩ := hJs fun h => absurd h.1 (by norm_num)
  obtain ⟨E, hE, -, hEc⟩ := exists_elemAbelian_fixSubgroup_fieldAut_eight hK hσ
  rw [← hH] at hE ⊢
  refine le_antisymm (sSup_le fun _ hL => hL.1)
    (CFSG.HardMathSupport.Solomon.Coordinator.le_glaPLayer_of_normal_simple Nat.prime_three le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) ⟨x, y, hxy⟩ ?_)
  exact (show 3 ∣ 27 by norm_num).trans (hEc ▸ Subgroup.card_dvd_of_le hE)

theorem eq_bot_of_normalized_two_subgroup_fieldAut_eight (hK : Nat.card K = 8) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {A U : Subgroup (StatedProj (StatedSp 3 K))}
    (hA : A ≤ fixSubgroup (fieldAut 3 K σ)) (hAe : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hL : ∀ a ∈ A, a ≠ 1 → GLAPLayer 3 (fixSubgroup (fieldAut 3 K σ) ⊓
      Subgroup.centralizer ({a} : Set (StatedProj (StatedSp 3 K)))) = ⊥)
    (hU : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set (StatedProj (StatedSp 3 K)))) :
    U = ⊥ := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num : 1 ≤ 3) hK'
  obtain ⟨ι, j, hj, hjp, hfix⟩ := exists_sp62Embedding hK hσ
  let π : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective (proj 3 K)
    ⟨CFSG.HardMathSupport.Dickson.Bal207.proj_injective_of_charP_two 3, proj_surjective⟩
  have hπ : ∀ g, π.symm (j g) = spMap ι g := fun g => by
    rw [MulEquiv.symm_apply_eq, hjp]
    rfl
  have hU' := sp_eq_bot_of_normalized_two_subgroup_of_card_nine (n := 3) (K := K)
    (fun x hx => eq_one_of_pow_three_eq_one_of_card_eight hK hx)
    (Ab := A.map π.symm.toMonoidHom) (T := U.map π.symm.toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hAe _)
    (by rw [Subgroup.card_map_of_injective π.symm.injective, h9])
    (fun s hs hs1 => ?_) (hU.map _)
    ((Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _))
  · exact (Subgroup.map_eq_bot_iff_of_injective U π.symm.injective).mp hU'
  obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨g, rfl⟩ := (hfix a).mpr (hA haA)
  have ha1 : j g ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hg1 : g ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hg3 : g ^ 3 = 1 := hj (by rw [map_pow, hAe.2 _ haA, map_one])
  have hcent : (Subgroup.centralizer ({g} : Set (StatedSp 3 (ZMod 2)))).map j =
      fixSubgroup (fieldAut 3 K σ) ⊓
        Subgroup.centralizer ({j g} : Set (StatedProj (StatedSp 3 K))) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(hfix _).mp ⟨z, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hz, map_mul]
    · rintro ⟨hy1, hy2⟩
      obtain ⟨z, rfl⟩ := (hfix y).mpr hy1
      refine ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr (hj ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hy2
  have hlay : GLAPLayer 3 (Subgroup.centralizer ({g} : Set (StatedSp 3 (ZMod 2)))) = ⊥ := by
    have h := CFSG.glaPLayer_map_eq_of_injective Nat.prime_three j hj
      (Subgroup.centralizer ({g} : Set (StatedSp 3 (ZMod 2))))
    rw [hcent, hL _ haA ha1] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ hj).mp h
  rw [MulEquiv.coe_toMonoidHom, hπ, finrank_ker_spEnd_spMap]
  exact finrank_ker_le_two_of_layer_eq_bot_sp6 hg3 hg1 hlay

end Field

section NotInner

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10


theorem not_inducesInnerMod_of_fieldOn {Ω : Type} [Group Ω] [Finite Ω] {X S : Subgroup Ω} {b : Ω}
    (hS : GLAPComponent 3 X S) (hF : FieldOn 3 b S) : ¬ InducesInnerMod 3 S b := by
  intro hin
  have h1 := MI.canon_marking_and_labelAll_simple (P' := MI.RawInnBody 3)
    (fun lab hlab => MI.canonRawInn Nat.prime_three (by norm_num) hlab) hF.2
  obtain ⟨-, lab, -, R, _, I, F, θ, -, -, ⟨⟨-, f, hf, u, hu, hord, hind⟩, hmul, hinv,
    hinn, hfI⟩⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h1
  have e1 := (MI.induces_indRel_iff hF.1 θ).1 hind
  obtain ⟨s, hs'⟩ := (MI.indAut_mem_inner_iff Nat.prime_three hS hF.1).2 hin
  have hc : MulAut.congr θ (MulAut.conj s) = MulAut.conj (θ s) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hφ : u * f * u⁻¹ ∈ I := by
    rw [e1, ← hs', hc]
    exact hinn _
  have hf' : f = u⁻¹ * (u * f * u⁻¹) * u := by group
  exact hfI f hf hord (hf' ▸ hmul _ (hmul _ (hinv u hu) _ hφ) u hu)

end NotInner

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
