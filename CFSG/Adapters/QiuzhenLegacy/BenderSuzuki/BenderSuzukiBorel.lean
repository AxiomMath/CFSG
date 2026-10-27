module

public import CFSG.StronglyEmbedded.BenderBorelRegularRoot
public import CFSG.StronglyEmbedded.BenderSuzukiCenter
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Open

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization

noncomputable section

theorem bender_suzukiMatrixGroup_borel (m : ℕ) (hm : 0 < m) :
    fusionBenderBorel (SuzukiMatrixGroup m) (2 ^ (2 * m + 1)) 2 := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m pi hpi
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let Omega := {z : ℙ K (Fin 4 → K) // z ∈ O}
  let G := SuzukiMatrixGroup m
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  rcases External.huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, hpi_formula, hFp, _hF_pow_four,
      _hF_order_four, _hF_class, hFcard, _hF_typeA, _hroot_mul,
      _hcommutator, _hcommutator_coordinates, htorus_equiv,
      _htorus_conjugation, hdisjoint, _hfixed_point_free⟩
  rcases htorus_equiv with ⟨eH, _heH⟩
  rcases External.huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨hpres, _hrecognition, _hfaithful, htwo_raw, _hthree,
      hOcard_raw, _hGcard, hstabilizer_raw⟩
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hFcard' : Nat.card F = q ^ 2 := by
    simpa [F, q] using hFcard
  have hHcard : Nat.card H = q - 1 := by
    calc
      Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hKcard]
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  let R : Subgroup G := F.subgroupOf (SuzukiMatrixGroup m)
  let T : Subgroup G := H.subgroupOf (SuzukiMatrixGroup m)
  let U : Subgroup G := (F ⊔ H).subgroupOf (SuzukiMatrixGroup m)
  have hR_le_U : R ≤ U := by
    intro r hr
    exact (le_sup_left : F ≤ F ⊔ H) hr
  have hT_le_U : T ≤ U := by
    intro t ht
    exact (le_sup_right : H ≤ F ⊔ H) ht
  have hRT_sup : R ⊔ T = U := by
    simpa only [R, T, U] using
      (Subgroup.subgroupOf_sup hF_le_G hH_le_G).symm
  have hRT_inf : R ⊓ T = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx_one : ((x : G) : GL (Fin 4) K) = 1 :=
        Subgroup.disjoint_def.mp hdisjoint hx.1 hx.2
      show x = 1
      apply Subtype.ext
      exact hx_one
    · exact bot_le
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    External.suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hFH_le_normalizerF :
      F ⊔ H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    sup_le Subgroup.le_normalizer hH_le_normalizerF
  have hU_le_normalizerR : U ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hg_normalizes :
        ((g : G) : GL (Fin 4) K) ∈
          Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
      hFH_le_normalizerF hg
    rw [Subgroup.mem_normalizer_iff] at hg_normalizes ⊢
    intro r
    exact hg_normalizes ((r : G) : GL (Fin 4) K)
  let eR : R ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_G
  let eT : T ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G
  have hRp : IsPGroup 2 R := hFp.of_equiv eR.symm
  have hTcard : Nat.card T = q - 1 := by
    calc
      Nat.card T = Nat.card H := Nat.card_congr eT.toEquiv
      _ = q - 1 := hHcard
  have hq_even : Even q := by
    dsimp only [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_pos : 0 < q := by
    dsimp only [q]
    positivity
  have hq_sub_one_odd : Odd (q - 1) :=
    Nat.Even.sub_odd hq_pos hq_even odd_one
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) linRep
  let ovoid : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact hpres g z hz }
  let : MulAction G Omega := ovoid.mulAction
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer : U = MulAction.stabilizer G pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ F ⊔ H ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (hstabilizer_raw g).symm
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab_raw : (a : ℙ K (Fin 4 → K)) ≠ b := by
      intro h
      exact hab (Subtype.ext h)
    have hcd_raw : (c : ℙ K (Fin 4 → K)) ≠ d := by
      intro h
      exact hcd (Subtype.ext h)
    rcases htwo_raw (a : ℙ K (Fin 4 → K)) b c d
        a.property b.property c.property d.property hab_raw hcd_raw with
      ⟨g, hga, hgb⟩
    exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
  have hRregular : ∀ a b : Omega, a ≠ pinfO → b ≠ pinfO →
      ∃! r : R, (r : G) • a = b := by
    intro a b ha hb
    have ha_raw : (a : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact ha (Subtype.ext h)
    have hb_raw : (b : ℙ K (Fin 4 → K)) ≠ pinf := by
      intro h
      exact hb (Subtype.ext h)
    rcases External.suzukiRootClosure_regular_on_ovoid_complement
        m pi hpi (a : ℙ K (Fin 4 → K)) b
          a.property b.property ha_raw hb_raw with
      ⟨r, hr, hr_unique⟩
    let rR : R :=
      ⟨⟨(r : GL (Fin 4) K), hF_le_G r.property⟩, r.property⟩
    refine ⟨rR, ?_, ?_⟩
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) K)).toLinearEquiv •
          (a : ℙ K (Fin 4 → K)) = b
      exact hr
    · intro s hs
      let sF : F := ⟨((s : G) : GL (Fin 4) K), s.property⟩
      have hs_raw :
          (Matrix.GeneralLinearGroup.toLin
            (sF : GL (Fin 4) K)).toLinearEquiv •
              (a : ℙ K (Fin 4 → K)) = b := by
        exact congrArg Subtype.val hs
      have hsF_eq : sF = r := hr_unique sF hs_raw
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : F => (x : GL (Fin 4) K)) hsF_eq
  have hRcard : Nat.card R = q ^ 2 := by
    calc
      Nat.card R = Nat.card F := Nat.card_congr eR.toEquiv
      _ = q ^ 2 := hFcard'
  have hTcyclic : IsCyclic T := eT.isCyclic.mpr
    (eH.isCyclic.mp (inferInstance : IsCyclic Kˣ))
  have hmove : ∃ g : G, g • pinfO ≠ pinfO := by
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hOcard : Nat.card Omega = q ^ 2 + 1 := by
      exact hOcard_raw
    let : Nontrivial Omega := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hOcard]
      exact Nat.lt_add_of_pos_left (pow_pos hq_pos 2))
    obtain ⟨b, hb⟩ := exists_ne pinfO
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G pinfO b
    exact ⟨g, hg ▸ hb⟩
  obtain ⟨hFcenterPow, hFcenterCard⟩ :=
    External.suzukiRootClosure_center_data m hm pi hpi_sq
  have hRcenterPow : ∀ z ∈ Subgroup.center R, z ^ 2 = 1 :=
    center_pow_two_of_mulEquiv eR.symm hFcenterPow
  have hRcenterCard : Nat.card (Subgroup.center R) = q :=
    (Nat.card_congr (Subgroup.centerCongr eR).toEquiv).trans hFcenterCard
  have hR_le_stabilizer : R ≤ MulAction.stabilizer G pinfO := by
    rw [← hU_eq_stabilizer]
    exact hR_le_U
  have hT_le_stabilizer : T ≤ MulAction.stabilizer G pinfO := by
    rw [← hU_eq_stabilizer]
    exact hT_le_U
  have hstabilizer_le_normalizer : MulAction.stabilizer G pinfO ≤
      Subgroup.normalizer (R : Set G) := by
    rw [← hU_eq_stabilizer]
    exact hU_le_normalizerR
  exact fusionBenderBorel_of_regular_root pinfO R T q 2
    hR_le_stabilizer hT_le_stabilizer hstabilizer_le_normalizer hRT_inf
    (hRT_sup.trans hU_eq_stabilizer) hTcyclic
    (by simpa only [hTcard] using hq_sub_one_odd) hRp
    (hRcard ▸ hq_even.pow_of_ne_zero (by norm_num)) hmove hRregular
    hRcenterPow hRcenterCard hRcard

theorem bender_suzuki_borel_full (a : ℕ) (ha : 1 ≤ a) :
    fusionBenderBorel (Sz a) (2 ^ (2 * a + 1)) 2 := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e := (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a).symm).trans
    (MulEquiv.subgroupCongr hmodel)
  let : Finite (Sz a) := Finite.of_surjective e e.surjective
  exact (bender_suzukiMatrixGroup_borel a (by omega)).map_mulEquiv e

end

end CFSG.Open
