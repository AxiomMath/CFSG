module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenThreeInspection
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.Quasithin.Vol2.Ch10SecDFrattini
public import CFSG.Open.StatedZModTwo
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding Subgroup TenThreeThree

theorem allInner_of_mulEquiv_statedSp {r : ℕ} (hr : 3 ≤ r) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {X : Type} [Group X] (e : X ≃* CFSG.Open.StatedSp r F) :
    ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g := by
  have hsub : (CFSG.Open.StatedScalars (Fin r ⊕ Fin r) F).subgroupOf
      (CFSG.Open.StatedSp r F) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hF, Subgroup.bot_subgroupOf]
  let eP : CFSG.Open.StatedProj (CFSG.Open.StatedSp r F) ≃* CFSG.Open.StatedSp r F :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
  have hInner : ∀ α : MulAut (CFSG.Open.StatedSp r F), ∃ g, α = MulAut.conj g :=
    CFSG.SeitzReduction.SporadicRefine.allInner_of_mulEquiv eP.symm
      (CFSG.SeitzReduction.SporadicRefine.allInner_statedProjSp_of_card_two hr hF)
  exact CFSG.SeitzReduction.SporadicRefine.allInner_of_mulEquiv e hInner

theorem eq_one_of_odd_of_pCore_quotient_eq_one {A : Type} [Group A] {P : Subgroup A} {y : A}
    (hyP : y ∈ P) (hodd : Odd (orderOf y))
    (h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) (⟨y, hyP⟩ : ↥P) = 1) : y = 1 := by
  have hmem : (⟨y, hyP⟩ : ↥P) ∈ CFSG.pCore 2 ↥P := (QuotientGroup.eq_one_iff _).mp h1
  have hodd' : Odd (orderOf (⟨y, hyP⟩ : ↥P)) := by
    rwa [← Subgroup.orderOf_coe (⟨y, hyP⟩ : ↥P)]
  have h1' : (⟨y, hyP⟩ : ↥P) = 1 :=
    CFSG.Quasithin.eq_one_of_odd_orderOf_of_mem (CFSG.pCore_isPGroup (p := 2) (G := ↥P))
      hmem hodd'
  exact congrArg Subtype.val h1'

theorem exists_mem_of_normalizer_spTwo (hZ : OddCenterRest) {A : Type} [Group A] [Finite A]
    {Y P : Subgroup A} (hY : CFSG.Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) {b : A}
    (hb : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A)) :
    ∃ y ∈ P, Odd (orderOf y) ∧ ∀ w ∈ Y, b * w * b⁻¹ = y * w * y⁻¹ := by
  classical
  obtain ⟨hPY, T, hT, hTN⟩ := hP
  obtain ⟨r, K, hKfield, hKfin, hKchar, hr, hK, hψ⟩ :=
    exists_mulEquiv_statedSp_of_isQuasisimple hZ hY hO hB2
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ψ⟩ := hψ
  let α : MulAut ↥Y := Y.normalizerMonoidHom ⟨b, hbY⟩
  have hαcoe : ∀ y : ↥Y, (α y : A) = b * (y : A) * b⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨b, hbY⟩ y
  have hαodd : Odd (orderOf α) := by
    refine hb.of_dvd_nat ?_
    have h := orderOf_map_dvd Y.normalizerMonoidHom (⟨b, hbY⟩ : ↥(normalizer (Y : Set A)))
    rwa [Subgroup.orderOf_mk] at h
  have hcenSp : Subgroup.center (CFSG.Open.StatedSp r K) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := K) (n := r) (by omega)
  have hcen : Subgroup.center ↥Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply ψ.injective
    have hmem : ψ z ∈ Subgroup.center (CFSG.Open.StatedSp r K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro x
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [← map_mul, ← map_mul, hz u]
    rw [hcenSp, Subgroup.mem_bot] at hmem
    simpa using hmem
  obtain ⟨g, hg⟩ := allInner_of_mulEquiv_statedSp hr hK ψ α
  have hker : ∀ z : ↥Y, MulAut.conj z = 1 → z = 1 := by
    intro z hz1
    have hzc : z ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun σ : MulAut ↥Y => σ x) hz1
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 := congrArg (fun t : ↥Y => t * z) h1
      simpa [mul_assoc] using h2.symm
    rwa [hcen, Subgroup.mem_bot] at hzc
  have hgodd : Odd (orderOf g) := by
    have h1 : MulAut.conj (g ^ orderOf α) = 1 := by
      rw [map_pow, ← hg, pow_orderOf_eq_one]
    exact hαodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one (hker _ h1))
  let y : A := (g : A)
  have hyodd : Odd (orderOf y) := by
    rw [Subgroup.orderOf_coe g]
    exact hgodd
  have hconj : ∀ w ∈ Y, b * w * b⁻¹ = y * w * y⁻¹ := by
    intro w hw
    have h1 : α ⟨w, hw⟩ = MulAut.conj g ⟨w, hw⟩ := by rw [hg]
    have h2 : ((α ⟨w, hw⟩ : ↥Y) : A) = b * w * b⁻¹ := hαcoe ⟨w, hw⟩
    rw [← h2, h1, MulAut.conj_apply]
    rfl
  have hyY : y ∈ Y := g.2
  have hyN : y ∈ normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h := hconj w (hPY hw)
      rw [← h]
      exact (Subgroup.mem_normalizer_iff.mp hbP w).mp hw
    · intro hw
      have hwY : w ∈ Y := by
        have h1 : y⁻¹ * (y * w * y⁻¹) * y ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (hPY hw)) hyY
        simpa [mul_assoc] using h1
      have h := hconj w hwY
      exact (Subgroup.mem_normalizer_iff.mp hbP w).mpr (by rwa [← h] at hw)
  have hTP : T ≤ P := fun t ht => hTN ⟨hT.1 ht, le_normalizer ht⟩
  have hTP' : IsSylowTwoOf T P := by
    refine ⟨hTP, hT.2.1, ?_⟩
    intro h2
    have e : (T.subgroupOf P).index * (P.subgroupOf Y).index =
        (T.subgroupOf Y).index :=
      Subgroup.relIndex_mul_relIndex T P Y hTP hPY
    exact hT.2.2 (e ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨n, hnP, hnyN⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecD.exists_mul_mem_normalizer hTP' hyN
  have hnyY : n * y ∈ Y := Y.mul_mem (hPY hnP) hyY
  have hyP : y ∈ P := by
    have h : n * y ∈ P := hTN ⟨hnyY, hnyN⟩
    have h' : n⁻¹ * (n * y) ∈ P := P.mul_mem (P.inv_mem hnP) h
    simpa using h'
  exact ⟨y, hyP, hyodd, hconj⟩


theorem kFactParabolicSyl_of_griess (hGA : GriessAllModelsStatement) : KFactParabolicSyl := by
  intro A _ _ Y P hY hO hcl hP h2 b hbY hS
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  have hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y) := by
    by_contra hB2
    exact not_two_dvd_index_wSup_of_parabolic hGA hY hO hcl hP hB2 h2
  unfold SylAct at hS
  obtain ⟨hbodd, hbP, T, hTP, hT2, hbT, hTW, hTi⟩ := hS
  obtain ⟨y, hyP, hyodd, hconj⟩ :=
    exists_mem_of_normalizer_spTwo hZ hY hO hB2 hP hbodd hbY hbP
  have hPY : P ≤ Y := hP.1
  have hyT : y ∈ normalizer (T : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      change (MulAut.conj y) t ∈ T
      rw [MulAut.conj_apply, ← hconj t (hPY (hTP ht))]
      exact (Subgroup.mem_normalizer_iff.mp hbT t).mp ht
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
  let ŷ : ↥P ⧸ CFSG.pCore 2 ↥P := q ⟨y, hyP⟩
  have hŷN : ŷ ∈ Subgroup.normalizer ((T.subgroupOf P).map q : Set _) := by
    have hyN' : (⟨y, hyP⟩ : ↥P) ∈
        Subgroup.normalizer ((T.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTP]
      exact Subgroup.mem_subgroupOf.mpr hyT
    exact Subgroup.le_normalizer_map (H := T.subgroupOf P) q
      (Subgroup.mem_map_of_mem q hyN')
  have hT2' : IsPGroup 2 ((T.subgroupOf P).map q) :=
    (IsPGroup.of_equiv hT2 (Subgroup.subgroupOfEquivOfLe hTP).symm).map q
  have hŷodd : Odd (orderOf ŷ) := by
    refine hyodd.of_dvd_nat ?_
    have h := orderOf_map_dvd q (⟨y, hyP⟩ : ↥P)
    rwa [← Subgroup.orderOf_coe (⟨y, hyP⟩ : ↥P)] at h
  have hprod : IsSpTwoLeviProduct ↥P := isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hP
  have hŷ1 : ŷ = 1 := hprod.eq_one_of_mem_normalizer hŷodd hT2' hTW hTi hŷN
  have hy1 : y = 1 := eq_one_of_odd_of_pCore_quotient_eq_one hyP hyodd hŷ1
  unfold TrivOnW
  intro w hw _
  have h : b * w * b⁻¹ = w := by
    have h := hconj w (hPY hw)
    rw [hy1] at h
    simpa using h
  rw [h, mul_inv_cancel]
  exact (pCoreOf 2 P).one_mem

theorem kFactParabolicW_of_griess (hGA : GriessAllModelsStatement) : KFactParabolicW := by
  intro A _ _ Y P hY hO hcl hP b hb hbY hbP hc
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  by_cases hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)
  · right
    obtain ⟨y, hyP, hyodd, hconj⟩ :=
      exists_mem_of_normalizer_spTwo hZ hY hO hB2 hP hb hbY hbP
    have hPY : P ≤ Y := hP.1
    have hprod : IsSpTwoLeviProduct ↥P := isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hP
    let q := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
    let ŷ : ↥P ⧸ CFSG.pCore 2 ↥P := q ⟨y, hyP⟩
    have hcen : ŷ ∈ Subgroup.centralizer
        (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) w
      have hpP : (p : A) ∈ P := p.2
      have hz : y * (p : A) * y⁻¹ * (p : A)⁻¹ ∈ pCoreOf 2 P := by
        have h := hc (p : A) hpP (by simpa [q, QuotientGroup.mk'_apply] using hw)
        rwa [hconj (p : A) (hPY hpP)] at h
      have hzP : (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P) ∈ CFSG.pCore 2 ↥P := by
        rw [← CFSG.mem_openPCoreOf_iff (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)]
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hz
      have h1 : ŷ * q p * ŷ⁻¹ * (q p)⁻¹ = 1 := by
        have h := (QuotientGroup.eq_one_iff
          (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)).mpr hzP
        simpa [ŷ, q, map_mul, map_inv, QuotientGroup.mk'_apply] using h
      have h2 : q p * ŷ = ŷ * q p := by
        have h2' : ŷ * q p * ŷ⁻¹ = q p := by
          have := congrArg (fun t => t * q p) h1
          simpa [mul_assoc] using this
        have := congrArg (fun t => t * ŷ) h2'
        simpa [mul_assoc] using this.symm
      exact h2
    have hŷ1 : ŷ = 1 := by
      have hmem := hcen
      rw [hprod.centralizer_wSup_eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    have hy1 : y = 1 := eq_one_of_odd_of_pCore_quotient_eq_one hyP hyodd hŷ1
    intro y' hy'
    have h := hconj y' hy'
    rw [hy1] at h
    have h' : b * y' * b⁻¹ = y' := by simpa using h
    have h'' := congrArg (fun t => t * b) h'
    simpa [mul_assoc] using h''
  · left
    exact not_two_dvd_index_wSup_of_parabolic hGA hY hO hcl hP hB2

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
