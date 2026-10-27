module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M22Cases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M22Concl
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.J4

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4
  CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.M22 CFSG.Blueprint CFSG.LieType.BorelTits
open scoped IsMulCommutative

theorem isFFModule_of_map {K K' : Type} [Group K] [Group K'] [Finite K] (π : K →* K')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) {V : Subgroup K} (hV : IsElemAbelian 2 V)
    (hFF : ∃ _ : IsMulCommutative ↥(V.map π),
      IsFFModule (V := ↥(V.map π))
        (autOn (Subgroup.normalizer ((V.map π : Subgroup K') : Set K')) (V.map π))) :
    ∃ _ : IsMulCommutative ↥V,
      IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set K)) V) := by
  classical
  have hodd' : Nat.Coprime (Nat.card π.ker) 2 := (Nat.coprime_two_left.mpr hodd).symm
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    have hx := hV.2 x x.2
    simpa using hx)⟩
  let eV : ↥V ≃* ↥(V.map π) :=
    CFSG.QuasiDihedralFusion.equivMapOfIsPGroup π hodd V hV2
  have heV : ∀ v : ↥V, ((eV v : ↥(V.map π)) : K') = π v :=
    fun v => CFSG.QuasiDihedralFusion.equivMapOfIsPGroup_coe π hodd V hV2 v
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

private theorem card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card (H.map f) * Nat.card ↥(f.ker ⊓ H) = Nat.card H := by
  have h1 := Subgroup.relIndex_ker (K := H) f
  have h2 := Subgroup.relIndex_mul_card (H := f.ker) (K := H)
  rw [← h1]
  exact h2

private theorem dvd_card_of_threeA6 {Γ : Type*} [Group Γ]
    (h : Nat.card ↥(Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ)) = 3 ∧
      Nonempty ((Γ ⧸ CFSG.pCore 2 Γ) ⧸ Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ) ≃*
        alternatingGroup (Fin 6))) :
    1080 ∣ Nat.card Γ := by
  obtain ⟨hc, ⟨φ⟩⟩ := h
  have hmul := Subgroup.card_mul_index (Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ))
  have hidx : (Subgroup.center (Γ ⧸ CFSG.pCore 2 Γ)).index = 360 := by
    rw [Subgroup.index, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [hc, hidx] at hmul
  have hQ : Nat.card (Γ ⧸ CFSG.pCore 2 Γ) = 1080 := hmul.symm.trans (by norm_num)
  rw [← hQ]
  exact Subgroup.card_quotient_dvd_card (CFSG.pCore 2 Γ)

private theorem card_dvd_three_mul_of_eq_map {K X : Type*} [Group K] [Group X] (π : K →* X)
    (hker : Nat.card π.ker = 3) {L : Subgroup K} {M' : Subgroup X} (g : X)
    (hL : L.map π = M'.map (MulAut.conj g).toMonoidHom) {N : ℕ} (hcard : Nat.card ↥M' = N) :
    Nat.card ↥L ∣ 3 * N := by
  have h := card_map_mul_card_inf_ker π L
  have hd : Nat.card ↥(π.ker ⊓ L) ∣ 3 := by
    rw [← hker]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hc : Nat.card ↥(L.map π) = N := by
    rw [hL, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  rw [← h, hc, mul_comm 3]
  exact mul_dvd_mul_left _ hd

private theorem two_pow_mul_ne_360 (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 360 := by
  intro h
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num at h
  · have h3 : 3 ≤ n := by omega
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have hmul : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h8 (by omega)
    omega

private theorem not_isSporadic_J4_of_M22 :
    ¬ IsSporadic .J4 (NativeSporadic.Carrier .M22) := by
  intro hJ
  obtain ⟨e⟩ := hJ
  have h1 : Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.J4 :=
    Nat.card_congr e.toEquiv
  rw [CFSG.Sporadic.J4.card_J4] at h1
  have h2 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := by
    change Nat.card ↥NativeSporadic.M22 = 443520
    exact CFSG.Sporadic.Mathieu.card_M22
  rw [h2] at h1
  norm_num at h1

private theorem nonempty_quot_mulEquiv_of_eq_map_Mhex
    {L' : Subgroup (NativeSporadic.Carrier .M22)}
    {g : NativeSporadic.Carrier .M22} (hL : L' = Mhex.map (MulAut.conj g).toMonoidHom) :
    Nonempty (↥L' ⧸ CFSG.pCore 2 ↥L' ≃* alternatingGroup (Fin 6)) := by
  subst hL
  let econj : ↥Mhex ≃* ↥(Mhex.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective Mhex (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨eQ⟩ := nonempty_Mhex_quot_mulEquiv
  exact ⟨(QuotientGroup.congr _ _ econj
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 econj)).symm.trans eQ⟩

theorem KConf.isFFModule_of_threeA6
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22)
    (hZ3 : Nat.card ↥(Subgroup.center K) = 3)
    (h3A6 : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6))) :
    ∃ _ : IsMulCommutative ↥V,
      IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set K)) V) := by
  haveI : Finite (NativeSporadic.Carrier .M22) := by
    change Finite ↥NativeSporadic.M22
    infer_instance
  let Z := Subgroup.center K
  let q : K →* K ⧸ Z := QuotientGroup.mk' Z
  let π : K →* NativeSporadic.Carrier .M22 := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext l
    simp only [π, q, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    exact hK.odd_card_center
  have hker3 : Nat.card π.ker = 3 := by
    rw [hker]
    exact hZ3
  have hbar : KConfig (NativeSporadic.Carrier .M22) (L.map π) (V.map π) (MK.map π) := by
    have h1 : KConfig (NativeSporadic.Carrier .M22) ((L.map q).map e.toMonoidHom)
        ((V.map q).map e.toMonoidHom) ((MK.map q).map e.toMonoidHom) :=
      (hK.kConfig_bar).map_mulEquiv e
    simpa only [Subgroup.map_map] using h1
  have h1080 : 1080 ∣ Nat.card ↥L := dvd_card_of_threeA6 h3A6.2
  have hFFbar : ∃ _ : IsMulCommutative ↥(V.map π),
      IsFFModule (V := ↥(V.map π))
        (autOn (Subgroup.normalizer ((V.map π : Subgroup (NativeSporadic.Carrier .M22)) :
          Set (NativeSporadic.Carrier .M22))) (V.map π)) := by
    obtain ⟨g, hg | hg | hg⟩ := KConfig.m22_cases hbar
    ·
      have hc : ConclK (NativeSporadic.Carrier .M22) (L.map π) (V.map π) (MK.map π) :=
        KConfig.conclK_of_eq_map hbar (MulAut.conj g) hg.1 hg.2
          (fun MK' => conclK_m22_hex MK')
      have hQ : Nat.card (↥(L.map π) ⧸ CFSG.pCore 2 ↥(L.map π)) = 360 := by
        obtain ⟨φ⟩ := nonempty_quot_mulEquiv_of_eq_map_Mhex hg.2
        rw [Nat.card_congr φ.toEquiv]
        exact Hex.card_alt6
      unfold ConclK at hc
      rcases hc with ⟨-, -, ⟨hFF, -, -, -, -⟩ | ⟨m, -, hLie2, -⟩ | ⟨hLie3, -⟩⟩ | ⟨hJ, -⟩
      · exact hFF
      ·
        exfalso
        have h := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
          (hLie2.statedClassicalModel (by decide))
        exact two_pow_mul_ne_360 _ (h.symm.trans hQ)
      ·
        exfalso
        have h := LieModel.card_psl_three_two hLie3
        exact absurd (hQ.symm.trans h) (by norm_num)
      · exact (not_isSporadic_J4_of_M22 hJ).elim
    ·
      exfalso
      have h := card_dvd_three_mul_of_eq_map π hker3 g hg.2 card_Mduad
      exact absurd (h1080.trans h) (by norm_num)
    ·
      exfalso
      have h := card_dvd_three_mul_of_eq_map π hker3 g hg.2 card_eNorm_e8
      exact absurd (h1080.trans h) (by norm_num)
  exact isFFModule_of_map π hπ (le_of_eq hker) hodd hK.elemAbelian hFFbar

end CFSG.SectionRank.QTK.Insp443

end
