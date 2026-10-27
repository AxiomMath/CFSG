module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Id2
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

open scoped commutatorElement

namespace U33

variable {F : Type} [Field F]

theorem inv_i_eq (d : Idata F) : (d.i)⁻¹ = -d.i := by
  refine inv_eq_of_mul_eq_one_right ?_
  have hi := d.sq
  linear_combination -hi

theorem S0_facts (hF : Nat.card F = 9) (i : Fˣ) (hi : orderOf i = 4) :
    Nat.card (S0 hF (Idata.ofUnit hF i hi)) = 32 ∧
      ∃ P : Sylow 2 (StatedSU 3 3 F), (P : Subgroup (StatedSU 3 3 F)) = S0 hF (Idata.ofUnit hF i hi) := by
  set d := Idata.ofUnit hF i hi with hd
  have hdi : d.i = (i : F) := rfl
  obtain ⟨-, hall⟩ := CFSG.LinearGroups.UnitaryThreeOverNine.wreath_sylow_model hF i hi
  have hs : ((sEl hF d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(i : F)⁻¹, (i : F), 1] := by
    rw [coe_sEl, sM_eq_diagonal]
    have : (i : F)⁻¹ = -(i : F) := by rw [← hdi]; exact inv_i_eq d
    rw [this, hdi]
  have ht : ((tEl hF d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(i : F)⁻¹, 1, (i : F)] := by
    rw [coe_tEl, tM_eq_diagonal]
    have : (i : F)⁻¹ = -(i : F) := by rw [← hdi]; exact inv_i_eq d
    rw [this, hdi]
  have hw : ((wEl hF : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] :=
    rfl
  obtain ⟨-, -, -, -, -, -, -, -, hcard, hP, -⟩ := hall (sEl hF d) (tEl hF d) (wEl hF) hs ht hw
  exact ⟨hcard, hP⟩

section Conj

variable {G : Type} [Group G] {L R : Subgroup G}

@[expose] noncomputable def conjL (L : Subgroup G) (r : G)
    (hr : r ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L :=
  L.normalizerMonoidHom ⟨r, hr⟩

theorem coe_conjL (r : G) (hr : r ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    ((conjL L r hr x : ↥L) : G) = r * x * r⁻¹ :=
  L.normalizerMonoidHom_apply_apply_coe ⟨r, hr⟩ x

theorem conjL_map_S (hRN : R ≤ Subgroup.normalizer (L : Set G)) {r : G} (hr : r ∈ R) :
    ((R ⊓ L).subgroupOf L).map (conjL L r (hRN hr)).toMonoidHom = (R ⊓ L).subgroupOf L := by
  have key : ∀ (r : G) (hr : r ∈ R) (x : ↥L), x ∈ (R ⊓ L).subgroupOf L →
      conjL L r (hRN hr) x ∈ (R ⊓ L).subgroupOf L := by
    intro r hr x hx
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, (conjL L r (hRN hr) x).2⟩)
    rw [coe_conjL]
    exact R.mul_mem (R.mul_mem hr (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1)
      (R.inv_mem hr)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key r hr y hy
  · intro hx
    refine ⟨conjL L r⁻¹ (hRN (R.inv_mem hr)) x, key r⁻¹ (R.inv_mem hr) x hx, ?_⟩
    apply Subtype.ext
    show ((conjL L r (hRN hr) (conjL L r⁻¹ (hRN (R.inv_mem hr)) x) : ↥L) : G) = x
    rw [coe_conjL, coe_conjL]
    group

theorem normalizes_of_stable (hRN : R ≤ Subgroup.normalizer (L : Set G)) {K0 : Subgroup ↥L}
    (h : ∀ (r : G) (hr : r ∈ R) (x : ↥L), x ∈ K0 → conjL L r (hRN hr) x ∈ K0) :
    R ≤ Subgroup.normalizer ((K0.map L.subtype : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨conjL L r (hRN hr) x, h r hr x hx, by simp [coe_conjL]⟩
  · rintro ⟨y, hy, hyk⟩
    have hkL : k ∈ L := by
      have hyL : (y : G) ∈ L := y.2
      have hyk' : (y : G) = r * k * r⁻¹ := hyk
      rw [hyk'] at hyL
      exact (Subgroup.mem_normalizer_iff.1 (hRN hr) k).2 hyL
    refine ⟨⟨k, hkL⟩, ?_, rfl⟩
    have hx : (⟨k, hkL⟩ : ↥L) = conjL L r⁻¹ (hRN (R.inv_mem hr)) y := by
      apply Subtype.ext
      rw [coe_conjL]
      have hyk' : (y : G) = r * k * r⁻¹ := hyk
      rw [hyk']
      group
    rw [hx]
    exact h r⁻¹ (R.inv_mem hr) y hy

end Conj

section Final

variable {F : Type} [Field F]

theorem K1_sup_stab0 (hF : Nat.card F = 9) (d : Idata F) : K1 hF ⊔ stab0 hF = ⊤ := by
  exact eq_top_of_mem d (H := K1 hF ⊔ stab0 hF) (fun g hg => Subgroup.mem_sup_left (mem_K1_iff.2 hg))
    (Subgroup.mem_sup_left (gEl_mem_K1 d)) (Subgroup.mem_sup_right cEl_mem_stab0)

theorem K1_ne_top (hF : Nat.card F = 9) : K1 hF ≠ ⊤ := by
  intro h
  have h1 := card_K1 (hF := hF)
  rw [h, Subgroup.card_top, card_statedSU hF] at h1
  omega

theorem stab0_ne_top (hF : Nat.card F = 9) (d : Idata F) : stab0 hF ≠ ⊤ := by
  intro h
  have h1 := card_stab0 d (hF := hF)
  rw [h, Subgroup.card_top, card_statedSU hF] at h1
  omega

end Final

end U33

theorem pairsFor_typeU33 : PairsFor TypeU33 := by
  intro G _ _ L R _hq hty hR hRN hS
  obtain ⟨-, F, hFf, hFfin, hFcard, ⟨e⟩⟩ := hty
  have hF : Nat.card F = 9 := by rw [hFcard]; norm_num
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hF
  let d : U33.Idata F := U33.Idata.ofUnit hF i hi
  have hscal := statedScalars_subgroupOf_statedSU_eq_bot hF
  let e' : ↥L ≃* (StatedSU 3 3 F ⧸ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 3 F)) := e
  let φ₀ : ↥L ≃* StatedSU 3 3 F :=
    e'.trans ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  obtain ⟨hcard0, P0, hP0⟩ := U33.S0_facts hF i hi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSLp : IsPGroup 2 SL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSLi : ¬ 2 ∣ SL.index := hS.2.2
  let PL : Sylow 2 ↥L := hSLp.toSylow hSLi
  let PK : Sylow 2 (StatedSU 3 3 F) := PL.mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (StatedSU 3 3 F) PK P0
  let φ : ↥L ≃* StatedSU 3 3 F := φ₀.trans (MulAut.conj k)
  have hSφ : SL.map φ.toMonoidHom = U33.S0 hF d := by
    have h1 : SL.map φ₀.toMonoidHom = (PK : Subgroup (StatedSU 3 3 F)) :=
      (Sylow.coe_mapSurjective (f := φ₀.toMonoidHom) φ₀.surjective PL).symm
    have h2 : ((k • PK : Sylow 2 (StatedSU 3 3 F)) : Subgroup (StatedSU 3 3 F)) =
        (PK : Subgroup (StatedSU 3 3 F)).map (MulAut.conj k).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hk] at h2
    calc SL.map φ.toMonoidHom = (SL.map φ₀.toMonoidHom).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl
      _ = (PK : Subgroup (StatedSU 3 3 F)).map (MulAut.conj k).toMonoidHom := by rw [h1]
      _ = (P0 : Subgroup (StatedSU 3 3 F)) := h2.symm
      _ = U33.S0 hF d := hP0
  have hK1 : (U33.canK1 SL).map φ.toMonoidHom = U33.K1 hF := by
    rw [← U33.canK1_map, hSφ, U33.canK1_eq_K1]
  have hK2 : (U33.canK2 SL).map φ.toMonoidHom = U33.stab0 hF := by
    rw [← U33.canK2_map, hSφ, U33.canK2_eq_stab0 hcard0]
  have hsymm : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have e1 : (U33.K1 hF).map φ.symm.toMonoidHom = U33.canK1 SL := by
    rw [← hK1, Subgroup.map_map, hsymm, Subgroup.map_id]
  have e2 : (U33.stab0 hF).map φ.symm.toMonoidHom = U33.canK2 SL := by
    rw [← hK2, Subgroup.map_map, hsymm, Subgroup.map_id]
  have hW1 : U33.Witness ((U33.canK1 SL).map L.subtype) := by
    have h2 := ((U33.witness_K1 (hF := hF) d).map φ.symm.toMonoidHom φ.symm.injective).map
      L.subtype L.subtype_injective
    rwa [e1] at h2
  have hW2 : U33.Witness ((U33.canK2 SL).map L.subtype) := by
    have h2 := ((U33.witness_stab0 (hF := hF) d).map φ.symm.toMonoidHom φ.symm.injective).map
      L.subtype L.subtype_injective
    rwa [e2] at h2
  refine ⟨(U33.canK1 SL).map L.subtype, (U33.canK2 SL).map L.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, hW1.charTwo, hW2.charTwo, hW1.not_hasChi0Block,
    hW2.not_hasChi0Block⟩
  · intro h
    have h1 : U33.canK1 SL = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
    apply U33.K1_ne_top hF
    rw [← hK1, h1, Subgroup.map_top_of_surjective _ φ.surjective]
  · intro h
    have h1 : U33.canK2 SL = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
    apply U33.stab0_ne_top hF d
    rw [← hK2, h1, Subgroup.map_top_of_surjective _ φ.surjective]
  · rw [← Subgroup.map_sup]
    have h1 : U33.canK1 SL ⊔ U33.canK2 SL = ⊤ := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [Subgroup.map_sup, hK1, hK2, U33.K1_sup_stab0 hF d,
        Subgroup.map_top_of_surjective _ φ.surjective]
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  · exact U33.normalizes_of_stable hRN fun r hr x hx =>
      U33.mem_canK1_of_map_eq (U33.conjL L r (hRN hr)) (U33.conjL_map_S hRN hr) hx
  · exact U33.normalizes_of_stable hRN fun r hr x hx =>
      U33.mem_canK2_of_map_eq (U33.conjL L r (hRN hr)) (U33.conjL_map_S hRN hr) hx

end CFSG.QuasithinUnique.Vol2Native.L239
