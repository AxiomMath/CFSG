module

public import CFSG.GH74.Generic.S3.NbrR
public import CFSG.GH74.Generic.S3.NbrComp
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.Sporadic.Th.Max3.Relations
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.NoFus2
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def LxyLiftAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K →
    ∀ L : Subgroup (CentralizerBar (y * x)), IsComponent L → S45.barSub (y * x) Iv ≤ L →
      (∃ t' : StatedLieTag, (t' = .PSL ∨ t' = .PSU) ∧ LieModel ↥L t' 3 p f ∧ OnlyInvX (y * x) L) →
        LiftCentralAt (y * x) L

section Main

variable {G : Type} [Group G] [Finite G]

theorem nbhdR_at_of_nbr_at' (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S3Setup G x K) (honly : OnlyInvX x K) (hT : LiftCentralAt x K) (hN : NbrCompAt x K)
    (hV : LxyLiftAt x K) (hLy : LyAt x K) (hLxy : LxyAt x K) :
    ∀ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
      LieModel ↥K t 3 p f →
      ∃ (t' : StatedLieTag) (y : G) (Iw Iv Ivw T : Subgroup G),
        Nbhd3 G t t' p f x y Iw Iv Ivw T ∧ imgBar x Iw = K := by
  intro t p f ht hp hp2 hq5 hmodel
  classical
  have hKs : IsSimpleGroup ↥K := isSimple_of_model ht hmodel
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hset.comp.1.1
  have hKn : ∃ a b : ↥K, a * b ≠ b * a := S45.exists_noncomm_of_isQuasisimple hset.comp.1
  have hKc := centerless_of_model ht hmodel hKn
  have hK1 := rankCertified_one_of_model ht hp2 hmodel
  have hcentral : ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n := hT
  have hKnorm : K.Normal :=
    normal_of_component_gen4 (gen4_centralizerBar hset.gen4 x) (xbar_comm x) (xbar_mul_self hset.inv)
      (xbar_ne_one hset.inv) hset.comp hKc hK1
  have hIw : IsNormCompC (liftSub x K) x := liftSub_isNormCompC hcentral hset.comp hKs hKnorm
  have hodd := liftSub_center_odd hcentral hKperf hKc
  have hmodelw := liftSub_model hcentral hKperf hKc hmodel
  have himg : imgBar x (liftSub x K) = K := imgBar_liftSub hKperf
  obtain ⟨T, y, hT, hxT, hyR, hy2, hycen, hyuniq⟩ :=
    exists_T_y ht hp hp2 hq5 hset.inv hIw hodd hmodelw
  have hy2' : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    omega
  have hyI : y ∈ liftSub x K := hyR.2
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hyC : y ∈ centralizer ({x} : Set G) := hT.le hyR.1
  have hcomm : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
  have hxI : x ∉ liftSub x K := by
    intro hx
    have h1 := mem_imgBar.2 (show ∃ g : ↥(centralizer ({x} : Set G)), (g : G) ∈ liftSub x K ∧
      proj x g = xbar x from ⟨⟨x, hxC⟩, hx, rfl⟩)
    rw [himg] at h1
    exact hset.shape.2 h1
  have hne : y ≠ x := fun h => hxI (h ▸ hyI)
  have hIwq : IsQuasisimple ↥(liftSub x K) := hIw.1.isQuasisimple
  obtain ⟨Iv, hIvle, hyIv, hIviso, hIvnorm⟩ :=
    exists_Iv hGA ht hp hp2 hq5 hIwq hodd hmodelw hyI hy2' hy1
  have hnd : NbrData G t p f x y (liftSub x K) Iv :=
    ⟨ht, ⟨hp, hp2, hq5⟩, hset.inv, hy2, hcomm, hne, hIw, hodd, hmodelw, hIvle, hyIv, hIviso, hIvnorm⟩
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hIviso
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have hIvc : ∀ i ∈ Iv, i * y = y * i :=
    central_of_involution_of_equiv_sl2 hoddF e hyIv hy2' hy1
  have hIvC : Iv ≤ centralizer ({y} : Set G) := fun i hi =>
    Subgroup.mem_centralizer_singleton_iff.2 (hIvc i hi)
  have hIvq : IsQuasisimple ↥Iv :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hF]; omega))
  have hIvperf : ⁅Iv, Iv⁆ = Iv := Subgroup.isPerfect_iff.mp hIvq.1
  have hcompbar := hLy t p f y _ Iv hnd himg
  have hcompC : IsCompC Iv y := hN t p f y _ Iv hnd himg hcompbar
  have hyx2 : orderOf (y * x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (y * x) ^ 2 = (y * x) * (y * x) := by rw [pow_two]
        _ = y * (x * y) * x := by group
        _ = y * (y * x) * x := by rw [hcomm]
        _ = (y * y) * (x * x) := by group
        _ = 1 := by
          have hx2 : x * x = 1 := by
            have := pow_orderOf_eq_one x
            rwa [hset.inv, pow_two] at this
          rw [hy2', hx2, one_mul]
    · intro h
      apply hne
      have hx2 : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hset.inv, pow_two] at this
      calc y = y * (x * x) := by rw [hx2, mul_one]
        _ = (y * x) * x := by rw [mul_assoc]
        _ = x := by rw [h, one_mul]
  have hIvV : Iv ≤ centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G) := by
    intro i hi
    refine ⟨hIw.1.1 (hIvle hi), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hix : i * x = x * i :=
      Subgroup.mem_centralizer_singleton_iff.1 (hIw.1.1 (hIvle hi))
    calc i * (y * x) = (i * y) * x := by rw [mul_assoc]
      _ = (y * i) * x := by rw [hIvc i hi]
      _ = y * (i * x) := by rw [mul_assoc]
      _ = y * (x * i) := by rw [hix]
      _ = (y * x) * i := by rw [mul_assoc]
  have hnormalizer : centralizer ({x} : Set G) ≤ normalizer ((liftSub x K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIw.1.1).1 hIw.2
  have hsubV : (Iv.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G))).IsSubnormal := by
    refine isSubnormal_of_normal_chain (B := liftSub x K ⊓ centralizer ({y} : Set G)) ?_ ?_ ?_
    · exact le_inf hIvle hIvC
    · intro b hb a ha
      exact hIvnorm b hb.1 (Subgroup.mem_centralizer_singleton_iff.1 hb.2) a ha
    · intro v hv b hb
      have hvx : v ∈ centralizer ({x} : Set G) := hv.1
      have hvyx : v ∈ centralizer ({y * x} : Set G) := hv.2
      have hvx' : v * x = x * v := Subgroup.mem_centralizer_singleton_iff.1 hvx
      have hvyx' : v * (y * x) = (y * x) * v := Subgroup.mem_centralizer_singleton_iff.1 hvyx
      have hvy : v * y = y * v := by
        have h1 : v * y * x = y * v * x := by
          calc v * y * x = v * (y * x) := by rw [mul_assoc]
            _ = (y * x) * v := hvyx'
            _ = y * (x * v) := by rw [mul_assoc]
            _ = y * (v * x) := by rw [hvx']
            _ = y * v * x := by rw [mul_assoc]
        exact mul_right_cancel h1
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · exact ((Subgroup.mem_normalizer_iff.1 (hnormalizer hvx) b).1 hb.1)
      · have hby : b * y = y * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
        calc v * b * v⁻¹ * y = v * b * (v⁻¹ * y) := by rw [mul_assoc]
          _ = v * b * (y * v⁻¹) := by
              congr 1
              calc v⁻¹ * y = v⁻¹ * y * (v * v⁻¹) := by group
                _ = v⁻¹ * (y * v) * v⁻¹ := by group
                _ = v⁻¹ * (v * y) * v⁻¹ := by rw [hvy]
                _ = y * v⁻¹ := by group
          _ = v * (b * y) * v⁻¹ := by group
          _ = v * (y * b) * v⁻¹ := by rw [hby]
          _ = y * (v * b * v⁻¹) := by
              calc v * (y * b) * v⁻¹ = (v * y) * b * v⁻¹ := by group
                _ = (y * v) * b * v⁻¹ := by rw [hvy]
                _ = y * (v * b * v⁻¹) := by group
  have hPC : GLS.IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G)) Iv :=
    isPCompIn_of_subnormal_block hIvV hsubV hIvq
  have hsc : x ∈ centralizer ({y * x} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * (y * x) = (x * y) * x := by rw [mul_assoc]
      _ = (y * x) * x := by rw [hcomm]
  have hsy : x = y * (y * x) := by
    calc x = (y * y) * x := by rw [hy2', one_mul]
      _ = y * (y * x) := by rw [mul_assoc]
  obtain ⟨L, hLc, hbarle⟩ := S1.exists_component_of_pumpup hset.inv hsc hPC hyIv hsy
  obtain ⟨t', ht', hmodelL, honlyL⟩ := hLxy t p f y _ Iv hnd himg L hLc hbarle
  have hLs : IsSimpleGroup ↥L := isSimple_of_model ht' hmodelL
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLc.1.1
  have hLn : ∃ a b : ↥L, a * b ≠ b * a := S45.exists_noncomm_of_isQuasisimple hLc.1
  have hLcen := centerless_of_model ht' hmodelL hLn
  have hL1 := rankCertified_one_of_model ht' hp2 hmodelL
  have hcentral' : ∀ n ∈ S1.liftL (y * x) L, proj (y * x) n = 1 → ∀ l ∈ S1.liftL (y * x) L, n * l = l * n :=
    hV t p f y _ Iv hnd himg L hLc hbarle ⟨t', ht', hmodelL, honlyL⟩
  have hLnorm : L.Normal :=
    normal_of_component_gen4 (gen4_centralizerBar hset.gen4 (y * x)) (xbar_comm (y * x))
      (xbar_mul_self hyx2) (xbar_ne_one hyx2) hLc hLcen hL1
  have hIvw : IsNormCompC (liftSub (y * x) L) (y * x) := liftSub_isNormCompC hcentral' hLc hLs hLnorm
  have hoddvw := liftSub_center_odd hcentral' hLperf hLcen
  have hmodelvw := liftSub_model hcentral' hLperf hLcen hmodelL
  have hrankvw : NoCommInv (centralizer ({y * x} : Set G) ⊓
      centralizer ((liftSub (y * x) L : Subgroup G) : Set G)) :=
    noCommInv_of_onlyInv hLperf honlyL hyx2 inf_le_left inf_le_right
  have hIvvw : Iv ≤ liftSub (y * x) L := by
    have hIvC' : Iv ≤ centralizer ({y * x} : Set G) := fun i hi => (hIvV hi).2
    set Q : Subgroup ↥(centralizer ({y * x} : Set G)) := Iv.subgroupOf (centralizer ({y * x} : Set G))
      with hQ
    have hQK : Q ≤ L.comap (proj (y * x)) := by
      intro q hq
      exact hbarle (S45.proj_mem_barSub q.2 hq)
    have hQperf : ⁅Q, Q⁆ = Q := by
      apply Subgroup.map_injective (centralizer ({y * x} : Set G)).subtype_injective
      rw [Subgroup.map_commutator]
      have h2 : Q.map (centralizer ({y * x} : Set G)).subtype = Iv := by
        rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hIvC']
      rw [h2, hIvperf]
    have hQL := S1.perfect_le_liftL hQK hQperf
    intro i hi
    exact mem_liftSub.2 ⟨⟨i, hIvC' hi⟩, hQL (show (⟨i, hIvC' hi⟩ : ↥(centralizer ({y * x} : Set G))) ∈ Q from hi), rfl⟩
  have hQrank : NoCommInv (T ⊓ centralizer ((liftSub x K : Subgroup G) : Set G)) :=
    noCommInv_of_onlyInv hKperf honly hset.inv ((inf_le_left).trans hT.le) inf_le_right
  refine ⟨t', y, liftSub x K, Iv, liftSub (y * x) L, T, ?_, himg⟩
  exact
    { tag := ht
      tag' := ht'
      prime := ⟨hp, hp2, hq5⟩
      x_inv := hset.inv
      y_inv := hy2
      comm := hcomm
      ne := hne
      comp_w := hIw
      odd_w := hodd
      model_w := hmodelw
      T_sylow := hT
      x_T := hxT
      Q_rank := hQrank
      y_R := hyR
      y_central := hycen
      y_unique := hyuniq
      Iv_le := hIvle
      y_Iv := hyIv
      Iv_iso := ⟨F, hFf, hFfin, hF, ⟨e⟩⟩
      comp_v := hcompC
      Iv_le_vw := hIvvw
      comp_vw := hIvw
      odd_vw := hoddvw
      model_vw := hmodelvw
      rank_vw := hrankvw }

end Main

end CFSG.GH74.Generic.S3
