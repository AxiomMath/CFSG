module

public import CFSG.CGT.T75N.L29Overgroup
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCoverUncond
public import CFSG.GroupTheory.SylowTwoOfConj
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

theorem isMulCommutative_quotient_pCore_of_surjective
    {M L : Type} [Group M] [Finite M] [Group L] [Finite L]
    (f : M →* L) (hf : Function.Surjective f)
    (h : IsMulCommutative (M ⧸ CFSG.pCore 2 M)) :
    IsMulCommutative (L ⧸ CFSG.pCore 2 L) := by
  have hle : CFSG.pCore 2 M ≤ (CFSG.pCore 2 L).comap f := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨CFSG.pCore_normal.map f hf, CFSG.pCore_isPGroup.map f⟩
  let g : M ⧸ CFSG.pCore 2 M →* L ⧸ CFSG.pCore 2 L :=
    QuotientGroup.map (N := CFSG.pCore 2 M) (M := CFSG.pCore 2 L) (f := f) hle
  have hsurj : Function.Surjective (QuotientGroup.mk ∘ f : M → L ⧸ CFSG.pCore 2 L) :=
    (QuotientGroup.mk'_surjective (N := CFSG.pCore 2 L)).comp hf
  have hg : Function.Surjective g :=
    QuotientGroup.map_surjective_of_surjective (N := CFSG.pCore 2 M) (M := CFSG.pCore 2 L)
      (f := f) hsurj hle
  exact Function.Surjective.isMulCommutative hg h

theorem isMulCommutative_upperTriangular_quotient_pCore {F : Type} [Field F] [Finite F]
    [CharP F 2] (n : Nat) :
    IsMulCommutative
      (↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular n F) ⧸
        CFSG.pCore 2
          ↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular n F)) := by
  classical
  let B : Subgroup (SpecialLinearGroup (Fin n) F) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular n F
  let φ : ↥B →* (Fin n → Fˣ) := CFSG.LieType.SteinbergBR.upperDiagHom F n
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 (CFSG.pCore 2 ↥B) := CFSG.pCore_isPGroup
  have himg2 : IsPGroup 2 ((CFSG.pCore 2 ↥B).map φ) := hp2.map φ
  have hcard : Nat.card (Fin n → Fˣ) = (Nat.card F - 1) ^ n := by
    rw [Nat.card_fun, Nat.card_units, Nat.card_fin]
  have hodd : Odd (Nat.card (Fin n → Fˣ)) := by
    rw [hcard]
    exact (odd_card_sub_one_of_char_two (F := F)).pow
  have himg_bot : (CFSG.pCore 2 ↥B).map φ = ⊥ := by
    have hoddimg : Odd (Nat.card ((CFSG.pCore 2 ↥B).map φ)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card _)
    obtain ⟨k, hk⟩ := himg2.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hoddimg.not_two_dvd_nat (hk ▸ dvd_pow_self 2 (Nat.pos_of_ne_zero hk0).ne')
    rw [Subgroup.eq_bot_iff_card, hk, hk0, pow_zero]
  have hpc_le : CFSG.pCore 2 ↥B ≤ φ.ker :=
    (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥B) (f := φ)).mp himg_bot
  have hker_eq : φ.ker =
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular n F).subgroupOf B := by
    rw [CFSG.LieType.SteinbergBR.ker_upperDiagHom]
  have hkerle : φ.ker ≤ CFSG.pCore 2 ↥B := by
    rw [hker_eq]
    refine le_sSup ⟨?_, ?_⟩
    · rw [← hker_eq]
      infer_instance
    · exact (CFSG.CGT.T75N.unitriangular_isPGroup_two (F := F) n).comap_subtype
  have hpc_eq : CFSG.pCore 2 ↥B = φ.ker := le_antisymm hpc_le hkerle
  have hrange_comm : IsMulCommutative φ.range :=
    isMulCommutative_iff.mpr fun a b =>
      Subtype.ext (mul_comm (a : Fin n → Fˣ) (b : Fin n → Fˣ))
  have hker_comm : IsMulCommutative (↥B ⧸ φ.ker) :=
    Function.Surjective.isMulCommutative
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective hrange_comm
  exact Function.Surjective.isMulCommutative
    (QuotientGroup.quotientMulEquivOfEq hpc_eq).symm.surjective hker_comm

theorem isMulCommutative_normalizer_quotient_pCore_of_linear_component
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : Nat) (hm : 1 <= m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : ¬ (m = 2 ∧ Q.card = 4))
    {U : Subgroup L} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
  classical
  obtain ⟨F, hFld, hFfin, hFchar, π, hFcard, hπsurj, hker⟩ :=
    exists_central_cover_specialLinear_of_ne_two_four hL m hm Q hQ hv e hne
  letI : Field F := hFld
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SL := Matrix.SpecialLinearGroup (Fin (m + 1)) F
  let Z : Subgroup SL := π.ker
  let W : Subgroup SL := U.comap π
  let U0 : Subgroup SL :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular (m + 1) F
  have hU2 : IsPGroup 2 U := hU.2.1
  have hZcenter : Z ≤ Subgroup.center SL := hker
  have hoddF : Odd (Nat.card F - 1) := odd_card_sub_one_of_char_two
  have hcenter_dvd : Nat.card (Subgroup.center SL) ∣ Nat.card F - 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd
      (n := m + 1) (K := F) (by omega)
  have hZodd : Odd (Nat.card Z) :=
    Odd.of_dvd_nat hoddF ((Subgroup.card_dvd_of_le hZcenter).trans hcenter_dvd)
  have hC : ¬ 2 ∣ Nat.card Z := hZodd.not_two_dvd_nat
  let Uhat : Subgroup SL := CFSG.LieType.CentralExt.liftSubgroup 2 π U
  have hUhat2 : IsPGroup 2 Uhat :=
    CFSG.LieType.CentralExt.liftSubgroup_isPGroup hZcenter hU2
  have hUhatleW : Uhat ≤ W :=
    CFSG.LieType.CentralExt.liftSubgroup_le_comap hZcenter hU2
  have hZleW : Z ≤ W := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : π z = 1 := (MonoidHom.mem_ker).1 hz
    rw [hz1]
    exact U.one_mem
  have hWindexOdd : ¬ 2 ∣ W.index := by
    rw [Subgroup.index_comap_of_surjective (H := U) hπsurj]
    have h := hU.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hWcard : Nat.card W = Nat.card Z * Nat.card Uhat := by
    rw [← Nat.card_congr
      (CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv hπsurj hZcenter hC hU2).toEquiv,
      Nat.card_prod]
  have hWdecomp : W = Z ⊔ Uhat := by
    refine le_antisymm ?_ (sup_le hZleW hUhatleW)
    intro w hw
    obtain ⟨⟨z, u⟩, hzu⟩ :=
      (CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv hπsurj hZcenter hC hU2).surjective
        ⟨w, hw⟩
    have hwval : (z : SL) * (u : SL) = w := by
      have h := congrArg Subtype.val hzu
      simpa [CFSG.LieType.CentralExt.kerProdLiftSubgroupEquiv_apply] using h
    rw [← hwval]
    exact mul_mem (Subgroup.mem_sup_left z.2) (Subgroup.mem_sup_right u.2)
  have hUhatnormW : W ≤ Subgroup.normalizer (Uhat : Set SL) := by
    rw [hWdecomp]
    exact sup_le (hZcenter.trans (Subgroup.center_le_normalizer (Uhat : Set SL)))
      Subgroup.le_normalizer
  have hUhatsubcard : Nat.card (Uhat.subgroupOf W) = Nat.card Uhat :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUhatleW).toEquiv
  have hUhatIndexW : ¬ 2 ∣ (Uhat.subgroupOf W).index := by
    have h := Subgroup.card_mul_index (H := Uhat.subgroupOf W)
    have hmul : Nat.card Uhat * (Uhat.subgroupOf W).index = Nat.card Uhat * Nat.card Z := by
      calc Nat.card Uhat * (Uhat.subgroupOf W).index
          = Nat.card (Uhat.subgroupOf W) * (Uhat.subgroupOf W).index := by rw [hUhatsubcard]
        _ = Nat.card W := h
        _ = Nat.card Z * Nat.card Uhat := hWcard
        _ = Nat.card Uhat * Nat.card Z := by ring
    have hidx : (Uhat.subgroupOf W).index = Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    rw [hidx]
    exact hZodd.not_two_dvd_nat
  have hUhatSylW : CFSG.QuasithinUnique.IsSylowTwoOf Uhat W :=
    ⟨hUhatleW, hUhat2, hUhatIndexW⟩
  have hUhatIndexSL : ¬ 2 ∣ Uhat.index := by
    rw [← Subgroup.relIndex_mul_index hUhatleW]
    exact Nat.Prime.not_dvd_mul Nat.prime_two hUhatIndexW hWindexOdd
  have hUhatSylSL : CFSG.QuasithinUnique.IsSylowTwoOf Uhat ⊤ := by
    refine ⟨le_top, hUhat2, ?_⟩
    have h := hUhatIndexSL
    rw [← Subgroup.relIndex_top_right] at h
    exact h
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf U0 ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := m + 1) (by omega)
  have hB : Subgroup.normalizer (U0 : Set SL) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m + 1) F :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular
  obtain ⟨g, -, hg⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf
    (P := Uhat) (P' := U0) hUhatSylSL hU0
  have hNWle : Subgroup.normalizer (W : Set SL) ≤ Subgroup.normalizer (Uhat : Set SL) := by
    intro n hn
    have hnW : CFSG.Quasithin.conjSub n W = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
    have hQleW : CFSG.Quasithin.conjSub n Uhat ≤ W := by
      calc CFSG.Quasithin.conjSub n Uhat ≤ CFSG.Quasithin.conjSub n W :=
            CFSG.Quasithin.conjSub_mono n hUhatleW
        _ = W := hnW
    have hQp : IsPGroup 2 (CFSG.Quasithin.conjSub n Uhat) :=
      hUhat2.map (MulAut.conj n).toMonoidHom
    have hQnorm : CFSG.Quasithin.conjSub n Uhat ≤
        Subgroup.normalizer (Uhat : Set SL) := hQleW.trans hUhatnormW
    have hsup2 : IsPGroup 2 (Uhat ⊔ CFSG.Quasithin.conjSub n Uhat : Subgroup SL) :=
      hUhat2.to_sup_of_normal_left' hQp hQnorm
    have hsupW : Uhat ⊔ CFSG.Quasithin.conjSub n Uhat ≤ W :=
      sup_le hUhatleW hQleW
    have hsupEq : Uhat ⊔ CFSG.Quasithin.conjSub n Uhat = Uhat :=
      CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hUhatSylW hsup2 hsupW le_sup_left
    have hQleU : CFSG.Quasithin.conjSub n Uhat ≤ Uhat :=
      (le_sup_right : CFSG.Quasithin.conjSub n Uhat ≤
        Uhat ⊔ CFSG.Quasithin.conjSub n Uhat).trans (le_of_eq hsupEq)
    have hcard : Nat.card (CFSG.Quasithin.conjSub n Uhat) = Nat.card Uhat :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hconjEq : CFSG.Quasithin.conjSub n Uhat = Uhat :=
      Subgroup.eq_of_le_of_card_ge hQleU (le_of_eq hcard.symm)
    have hconjEqInv : CFSG.Quasithin.conjSub n⁻¹ Uhat = Uhat := by
      have h : Uhat = CFSG.Quasithin.conjSub n⁻¹ Uhat := by
        have h' := congrArg (CFSG.Quasithin.conjSub n⁻¹) hconjEq
        simpa [CFSG.Quasithin.conjSub_conjSub_inv] using h'
      exact h.symm
    exact CFSG.Quasithin.F7.mem_normalizer_of_conj_le
      (le_of_eq hconjEq) (le_of_eq hconjEqInv)
  have hZnormal : Z.Normal := Subgroup.normal_of_le_center hZcenter
  have hZmap : ∀ n : SL, Z.map (MulAut.conj n) = Z := by
    intro n
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      exact hZnormal.conj_mem y hy n
    · intro z hz
      refine ⟨z, hz, ?_⟩
      simp [MulAut.conj_apply, Subgroup.mem_center_iff.mp (hZcenter hz) n, mul_assoc]
  have hNhatleNW : Subgroup.normalizer (Uhat : Set SL) ≤
      Subgroup.normalizer (W : Set SL) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
    calc W.map (MulAut.conj n)
        = (Z ⊔ Uhat).map (MulAut.conj n) := by rw [hWdecomp]
      _ = Z.map (MulAut.conj n) ⊔ Uhat.map (MulAut.conj n) :=
          Subgroup.map_sup Z Uhat (MulAut.conj n).toMonoidHom
      _ = Z ⊔ Uhat := by rw [hZmap n, hn]
      _ = W := hWdecomp.symm
  have hNW_eq : Subgroup.normalizer (W : Set SL) =
      Subgroup.normalizer (Uhat : Set SL) := le_antisymm hNWle hNhatleNW
  let Nhat : Subgroup SL := Subgroup.normalizer (Uhat : Set SL)
  let N0 : Subgroup SL := Subgroup.normalizer (U0 : Set SL)
  let B0 : Subgroup SL :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular (m + 1) F
  have hNU0eq : N0 = CFSG.Quasithin.conjSub g Nhat := by
    change Subgroup.normalizer (U0 : Set SL) =
      CFSG.Quasithin.conjSub g (Subgroup.normalizer (Uhat : Set SL))
    rw [hg, CFSG.Quasithin.conjSub_normalizer]
  let en : ↥Nhat ≃* ↥N0 :=
    (Subgroup.equivMapOfInjective Nhat (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hNU0eq.symm)
  have hN0B0 : N0 = B0 := hB
  let e2 : ↥Nhat ≃* ↥B0 := en.trans (MulEquiv.subgroupCongr hN0B0)
  have hcommB0 : IsMulCommutative (↥B0 ⧸ CFSG.pCore 2 ↥B0) :=
    isMulCommutative_upperTriangular_quotient_pCore (F := F) (n := m + 1)
  have hpc : (CFSG.pCore 2 ↥Nhat).map e2.toMonoidHom = CFSG.pCore 2 ↥B0 :=
    CFSG.pCore_map_iso 2 e2
  let eQ : ↥Nhat ⧸ CFSG.pCore 2 ↥Nhat ≃* ↥B0 ⧸ CFSG.pCore 2 ↥B0 :=
    QuotientGroup.congr _ _ e2 hpc
  have hcommNhat : IsMulCommutative (↥Nhat ⧸ CFSG.pCore 2 ↥Nhat) :=
    Function.Surjective.isMulCommutative eQ.symm.surjective hcommB0
  have hcommNSL : IsMulCommutative
      (↥(Subgroup.normalizer (W : Set SL)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (W : Set SL))) := by
    let eNW : ↥(Subgroup.normalizer (W : Set SL)) ≃* ↥Nhat :=
      MulEquiv.subgroupCongr hNW_eq
    have hpcNW : (CFSG.pCore 2 ↥(Subgroup.normalizer (W : Set SL))).map eNW.toMonoidHom =
        CFSG.pCore 2 ↥Nhat := CFSG.pCore_map_iso 2 eNW
    let eQNW : ↥(Subgroup.normalizer (W : Set SL)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (W : Set SL)) ≃*
        ↥Nhat ⧸ CFSG.pCore 2 ↥Nhat :=
      QuotientGroup.congr _ _ eNW hpcNW
    exact Function.Surjective.isMulCommutative eQNW.symm.surjective hcommNhat
  have hNmap : Subgroup.normalizer (U : Set L) =
      (Subgroup.normalizer (W : Set SL)).map π := by
    have h1 : (Subgroup.normalizer (U : Set L)).comap π =
        Subgroup.normalizer (W : Set SL) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective (H := U) hπsurj]
    rw [← h1]
    exact (Subgroup.map_comap_eq_self_of_surjective hπsurj
      (Subgroup.normalizer (U : Set L))).symm
  let f : ↥(Subgroup.normalizer (W : Set SL)) →*
      ↥(Subgroup.normalizer (U : Set L)) :=
    (MulEquiv.subgroupCongr hNmap.symm).toMonoidHom.comp
      (π.subgroupMap (Subgroup.normalizer (W : Set SL)))
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (MulEquiv.subgroupCongr hNmap.symm).surjective y
    obtain ⟨z, hz⟩ := MonoidHom.subgroupMap_surjective π (Subgroup.normalizer (W : Set SL)) x
    refine ⟨z, ?_⟩
    change (MulEquiv.subgroupCongr hNmap.symm) (π.subgroupMap _ z) = y
    rw [hz, hx]
  exact isMulCommutative_quotient_pCore_of_surjective f hfsurj hcommNSL

end CFSG.ClassicalGroups.SpecialLinear

end
