module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclKLeft
public import CFSG.Quasithin.H13.StatementsVocabComap
public import CFSG.Quasithin.Background.RonanE43Lift
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E16Shape
public import CFSG.Quasithin.Background.E3Transport
public import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4 CFSG.Blueprint
  CFSG.QuasithinUnique CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

private theorem map_centralizer_singleton_eq {K K' : Type} [Group K] [Group K'] [Finite K]
    (π : K →* K') (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) {z : K} (hz2 : orderOf z = 2) :
    (Subgroup.centralizer ({z} : Set K)).map π =
      Subgroup.centralizer ({π z} : Set K') := by
  have hodd' : Nat.Coprime (Nat.card π.ker) 2 := (Nat.coprime_two_left.mpr hodd).symm
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzsq : z ^ 2 = 1 := by rw [pow_two, hz2']
  have hQ : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz2, pow_one]
  refine le_antisymm ?_ ?_
  · rintro y ⟨c, hc, rfl⟩
    change c ∈ Subgroup.centralizer ({z} : Set K) at hc
    change π c ∈ Subgroup.centralizer ({π z} : Set K')
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hsz : s = π z := by simpa using hs
    subst hsz
    simpa only [map_mul] using congrArg π (hc z (by simp))
  · intro y hy
    obtain ⟨c, rfl⟩ := hπ y
    have hcy : c * z * c⁻¹ = z := by
      have hmem : c * z * c⁻¹ ∈ Subgroup.zpowers z := by
        refine CFSG.Quasithin.RonanE43.mem_of_map_mem_map π hker hodd' hQ ?_ (n := 1) ?_
        · rw [Subgroup.mem_map]
          refine ⟨z, Subgroup.mem_zpowers z, ?_⟩
          rw [map_mul, map_mul, map_inv]
          have hcomm : π z * π c = π c * π z :=
            (Subgroup.mem_centralizer_iff.mp hy) (π z) (by simp)
          rw [← hcomm]
          group
        · rw [conj_pow]
          simp only [pow_one, pow_two, hz2', mul_one]
          group
      have hcases : c * z * c⁻¹ = 1 ∨ c * z * c⁻¹ = z := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
        rw [← hn]
        rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
        · left
          rw [zpow_mul, zpow_two, ← pow_two, hzsq, one_zpow]
        · right
          rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hzsq, one_zpow, one_mul, zpow_one]
      rcases hcases with h1 | h1
      · exfalso
        have hord : orderOf (c * z * c⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz2]
        rw [h1, orderOf_one] at hord
        omega
      · exact h1
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhc : h = z := by simpa using hh
    rw [hhc]
    calc z * c = (c * z * c⁻¹) * c := by rw [hcy]
      _ = c * z := by group

theorem conclKLeft_of_map {K K' : Type} [Group K] [Group K'] [Finite K] (π : K →* K')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) {L V MK : Subgroup K} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set K)) (hLZ : L ⊓ π.ker = ⊥)
    (hc : ConclKLeft K' (L.map π) (V.map π) (MK.map π)) : ConclKLeft K L V MK := by
  classical
  have hodd' : Nat.Coprime (Nat.card π.ker) 2 := (Nat.coprime_two_left.mpr hodd).symm
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    have hx := hV.2 x x.2
    simpa using hx)⟩
  have hVbot : V ⊓ π.ker = ⊥ := CFSG.QuasiDihedralFusion.inf_ker_eq_bot π hodd V hV2
  let eV : ↥V ≃* ↥(V.map π) :=
    CFSG.QuasiDihedralFusion.equivMapOfIsPGroup π hodd V hV2
  have heV : ∀ v : ↥V, ((eV v : ↥(V.map π)) : K') = π v :=
    fun v => CFSG.QuasiDihedralFusion.equivMapOfIsPGroup_coe π hodd V hV2 v
  let eL : ↥L ≃* ↥(L.map π) := equivMapOfInjectiveOn π le_rfl hLZ
  have heL : ∀ l : ↥L, ((eL l : ↥(L.map π)) : K') = π l :=
    fun l => equivMapOfInjectiveOn_apply π le_rfl hLZ l
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
  unfold ConclKLeft at hc ⊢
  obtain ⟨hq, hshape, hcase⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hq
  · exact E443.shape443_of_mulEquiv ψ.symm hshape
  · rcases hcase with ⟨hFF, hnat3, hnat4, h3A6, hPSU⟩ | ⟨m, hm, hLie2, hBO⟩ |
      ⟨hLie3, hFano⟩
    · refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
      ·
        obtain ⟨hcommV', hFF'⟩ := hFF
        haveI : IsMulCommutative ↥V := hV.1
        haveI : IsMulCommutative ↥(V.map π) := hcommV'
        letI : CommGroup ↥V := IsMulCommutative.instCommGroup
        letI : CommGroup ↥(V.map π) := IsMulCommutative.instCommGroup
        have hN : Subgroup.normalizer ((V.map π : Subgroup K') : Set K') =
            (Subgroup.normalizer (V : Set K)).map π := by
          refine le_antisymm ?_ (Subgroup.le_normalizer_map π)
          intro x hx
          obtain ⟨g, rfl⟩ := hπ x
          exact Subgroup.mem_map_of_mem π
            (CFSG.Quasithin.RonanE43.mem_normalizer_of_map_mem π hker hodd' hV2 hx)
        have haut : autOn (Subgroup.normalizer ((V.map π : Subgroup K') : Set K')) (V.map π) =
            (autOn (Subgroup.normalizer (V : Set K)) V).map
              (MulAut.congr eV).toMonoidHom := by
          rw [hN]
          exact autOn_map_of_equiv π eV heV le_rfl
        have hFF0 : IsFFModule (V := ↥(V.map π))
            ((autOn (Subgroup.normalizer (V : Set K)) V).map
              (MulAut.congr eV).toMonoidHom) := by
          rwa [← haut]
        refine ⟨hV.1, ?_⟩
        exact (CFSG.Quasithin.E3.isFFModule_map_congr_iff eV).mp hFF0
      ·
        intro hLie
        have hLiec : LieModel (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) .PSL 3 2 1 :=
          E443.lieModel_of_mulEquiv' ψ.symm hLie
        exact IsNaturalSumUnder.of_map π hVbot hLV (hnat3 hLiec)
      ·
        intro hLie
        have hLiec : LieModel (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) .PSL 4 2 1 :=
          E443.lieModel_of_mulEquiv' ψ.symm hLie
        rcases hnat4 hLiec with hnat | hSL
        · left
          exact IsNaturalSumUnder.of_map π hVbot hLV hnat
        · right
          obtain ⟨hcommV', hSL'⟩ := hSL
          haveI : IsMulCommutative ↥V := hV.1
          haveI : IsMulCommutative ↥(V.map π) := hcommV'
          letI : CommGroup ↥V := IsMulCommutative.instCommGroup
          letI : CommGroup ↥(V.map π) := IsMulCommutative.instCommGroup
          refine ⟨hV.1, ?_⟩
          unfold SLExteriorTwo at hSL' ⊢
          have haut := autOn_map_of_equiv π eV heV hLV
          have h' : (FFModel.extSq (ZMod 2) 4).Realizes
              ((autOn L V).map (MulAut.congr eV).toMonoidHom) ⊤ ⊥ := by
            rwa [← haut]
          have h'' := CFSG.Quasithin.H.LU.realizes_map
            (FFModel.extSq (ZMod 2) 4) eV.symm h'
          rw [Subgroup.map_map, CFSG.Quasithin.SimsD1.TransMod.congr_symm_comp_congr,
            Subgroup.map_id] at h''
          exact h''
      ·
        intro hprem
        have hprem' := E443.threeA6_of_mulEquiv ψ hprem
        intro S hS z hz hz2
        obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
        have hS' : IsSylowTwoOf (S.map π) (L.map π) :=
          CFSG.GH74.QTGen4.DSGen4.isSylowTwoOf_map (φ := π) hS
        have hzV' : π z ∈ V.map π := Subgroup.mem_map_of_mem π hzV
        have hzC' : π z ∈ Subgroup.centralizer ((S.map π : Subgroup K') : Set K') := by
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
          rw [← map_mul, ← map_mul]
          exact congrArg π ((Subgroup.mem_centralizer_iff.mp hzC) s0 hs0)
        have hz1 : π z ≠ 1 := by
          intro h
          have hzmem : z ∈ V ⊓ π.ker := ⟨hzV, h⟩
          rw [hVbot, Subgroup.mem_bot] at hzmem
          rw [hzmem, orderOf_one] at hz2
          omega
        have hz2' : orderOf (π z) = 2 := by
          have hdvd : orderOf (π z) ∣ 2 := by
            have h := orderOf_map_dvd π z
            rwa [hz2] at h
          have hle : orderOf (π z) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
          have h0 : orderOf (π z) ≠ 0 := by
            intro hzero
            obtain ⟨k, hk⟩ := hdvd
            rw [hzero] at hk
            omega
          have hne : orderOf (π z) ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
          omega
        have hnot' := h3A6 hprem' (S.map π) hS' (π z) ⟨hzV', hzC'⟩ hz2'
        intro hVle
        apply hnot'
        have hCeq := map_centralizer_singleton_eq π hπ hker hodd hz2
        have hle : V.map π ≤
            (pCoreOf 2 (Subgroup.centralizer ({z} : Set K))).map π :=
          Subgroup.map_mono hVle
        have hle' : (pCoreOf 2 (Subgroup.centralizer ({z} : Set K))).map π ≤
            pCoreOf 2 (Subgroup.centralizer ({π z} : Set K')) := by
          rw [← hCeq]
          exact CFSG.LieType.BorelTits.map_pCoreOf_le π _
        exact hle.trans hle'
      ·
        intro hLie hcard
        have hLiec : LieModel (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) .PSU 3 3 1 :=
          E443.lieModel_of_mulEquiv' ψ.symm hLie
        have hcard' : Nat.card (V.map π) = 2 ^ 6 := by
          rw [← Nat.card_congr eV.toEquiv, hcard]
        intro S hS
        have hS' : IsSylowTwoOf (S.map π) (L.map π) :=
          CFSG.GH74.QTGen4.DSGen4.isSylowTwoOf_map (φ := π) hS
        obtain ⟨V₃', hV₃'V, hV₃'card, hV₃'norm, hV₃'not⟩ :=
          hPSU hLiec hcard' (S.map π) hS'
        let V₃ : Subgroup K := V ⊓ V₃'.comap π
        have hV₃map : V₃.map π = V₃' := by
          refine le_antisymm ?_ ?_
          · rintro y ⟨x, hx, rfl⟩
            exact hx.2
          · intro y hy
            obtain ⟨v, hvV, hvy⟩ := Subgroup.mem_map.mp (hV₃'V hy)
            refine Subgroup.mem_map.mpr ⟨v, ⟨hvV, ?_⟩, hvy⟩
            exact Subgroup.mem_comap.mpr (by rwa [hvy])
        have hV₃card : Nat.card V₃ = 2 ^ 3 := by
          have e : ↥V₃ ≃* ↥V₃' :=
            (equivMapOfInjectiveOn (V := V) (W := V₃) π inf_le_left hVbot).trans
              (MulEquiv.subgroupCongr hV₃map)
          rw [Nat.card_congr e.toEquiv, hV₃'card]
        have hSV₃ : S ≤ Subgroup.normalizer (V₃ : Set K) := by
          intro s hs
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · rintro ⟨hxV, hxV₃'⟩
            refine ⟨(Subgroup.mem_normalizer_iff.mp (hLV (hS.1 hs)) x).mp hxV, ?_⟩
            have hs' := (Subgroup.mem_normalizer_iff.mp
              (hV₃'norm (Subgroup.mem_map_of_mem π hs)) (π x)).mp hxV₃'
            exact Subgroup.mem_comap.mpr (by simpa only [map_mul, map_inv] using hs')
          · rintro ⟨hxV, hxV₃'⟩
            refine ⟨(Subgroup.mem_normalizer_iff.mp (hLV (hS.1 hs)) x).mpr hxV, ?_⟩
            refine Subgroup.mem_comap.mpr ?_
            exact (Subgroup.mem_normalizer_iff.mp
              (hV₃'norm (Subgroup.mem_map_of_mem π hs)) (π x)).mpr
              (by simpa only [map_mul, map_inv] using Subgroup.mem_comap.mp hxV₃')
        refine ⟨V₃, inf_le_left, hV₃card, hSV₃, ?_⟩
        intro hCMK
        apply hV₃'not
        intro c' hc'
        obtain ⟨c, rfl⟩ := hπ c'
        have hcC : c ∈ Subgroup.centralizer (V₃ : Set K) := by
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          have hxV : x ∈ V := hx.1
          have hxV' : π x ∈ V₃' := hx.2
          have hcx : π (c * x * c⁻¹) = π x := by
            rw [map_mul, map_mul, map_inv]
            have hcomm : π x * π c = π c * π x :=
              (Subgroup.mem_centralizer_iff.mp hc') (π x) hxV'
            rw [← hcomm]
            group
          have hyV : c * x * c⁻¹ ∈ V := by
            refine CFSG.Quasithin.RonanE43.mem_of_map_mem_map π hker hodd' hV2 ?_ (n := 1) ?_
            · rw [hcx]
              exact Subgroup.mem_map_of_mem π hxV
            · rw [conj_pow]
              simp only [pow_one]
              have hx2V : x ^ 2 = 1 := hV.2 x hxV
              rw [hx2V, mul_one, mul_inv_cancel]
          have hconj := CFSG.QuasiDihedralFusion.eq_of_mem_of_map_eq π hodd hV2
            (x := c * x * c⁻¹) (y := x) hyV hxV hcx
          calc x * c = (c * x * c⁻¹) * c := by rw [hconj]
            _ = c * x := by group
        exact Subgroup.mem_map_of_mem π (hCMK hcC)
    ·
      refine Or.inr (Or.inl ⟨m, hm, ?_, ?_⟩)
      · exact E443.lieModel_of_mulEquiv' ψ hLie2
      · obtain ⟨hcommV', hBO⟩ := hBO
        haveI : IsMulCommutative ↥V := hV.1
        haveI : IsMulCommutative ↥(V.map π) := hcommV'
        letI : CommGroup ↥V := IsMulCommutative.instCommGroup
        letI : CommGroup ↥(V.map π) := IsMulCommutative.instCommGroup
        refine ⟨hV.1, ?_⟩
        unfold BinaryOrthogonalFour TwistedTensorSL at hBO ⊢
        obtain ⟨K₀, hK₀field, hK₀finite, hK₀char, hK₀card, hReal⟩ := hBO
        refine ⟨K₀, hK₀field, hK₀finite, hK₀char, hK₀card, ?_⟩
        have haut := autOn_map_of_equiv π eV heV hLV
        have h' : (FFModel.twistTensor m (CFSG.Assembly.LowTwoRank.StatedSL 2 K₀)).Realizes
            ((autOn L V).map (MulAut.congr eV).toMonoidHom) ⊤ ⊥ := by
          rwa [← haut]
        have h'' := CFSG.Quasithin.H.LU.realizes_map
          (FFModel.twistTensor m (CFSG.Assembly.LowTwoRank.StatedSL 2 K₀)) eV.symm h'
        rw [Subgroup.map_map, CFSG.Quasithin.SimsD1.TransMod.congr_symm_comp_congr,
          Subgroup.map_id] at h''
        exact h''
    ·
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · exact E443.lieModel_of_mulEquiv' ψ hLie3
      · obtain ⟨hcommV', hFano⟩ := hFano
        haveI : IsMulCommutative ↥V := hV.1
        haveI : IsMulCommutative ↥(V.map π) := hcommV'
        letI : CommGroup ↥V := IsMulCommutative.instCommGroup
        letI : CommGroup ↥(V.map π) := IsMulCommutative.instCommGroup
        refine ⟨hV.1, ?_⟩
        unfold FanoCoreModule at hFano ⊢
        have haut := autOn_map_of_equiv π eV heV hLV
        have h' : fanoCoreModel.Realizes
            ((autOn L V).map (MulAut.congr eV).toMonoidHom) ⊤ ⊥ := by
          rwa [← haut]
        have h'' := CFSG.Quasithin.H.LU.realizes_map fanoCoreModel eV.symm h'
        rw [Subgroup.map_map, CFSG.Quasithin.SimsD1.TransMod.congr_symm_comp_congr,
          Subgroup.map_id] at h''
        exact h''

theorem conclK_of_map {K K' : Type} [Group K] [Group K'] [Finite K] (π : K →* K')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) {L V MK : Subgroup K} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set K)) (hLZ : L ⊓ π.ker = ⊥)
    (hJ4 : IsSporadic .J4 K' → π.ker = ⊥)
    (hc : ConclK K' (L.map π) (V.map π) (MK.map π)) : ConclK K L V MK := by
  rcases hc with hc | hJ
  · exact (conclKLeft_of_map π hπ hker hodd hV hLV hLZ hc).conclK
  let eL : ↥L ≃* ↥(L.map π) := equivMapOfInjectiveOn π le_rfl hLZ
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
  refine Or.inr ⟨?_, ?_⟩
  · have hkerbot : π.ker = ⊥ := hJ4 hJ.1
    have hinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hkerbot
    exact CFSG.Quasithin.IsSporadic.of_mulEquiv
      (MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm hJ.1
  · rcases hJ.2 with hM24 | hPSL5
    · left
      exact CFSG.Quasithin.IsSporadic.of_mulEquiv ψ.symm hM24
    · right
      exact E443.lieModel_of_mulEquiv' ψ hPSL5

end CFSG.SectionRank.QTK.Insp443
