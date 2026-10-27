module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolCI
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolTop
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups

theorem knownRowThree_solvable
    (hCI : GSLit.ClassicalInvolutionInput)
    (h51 : Harris82Lemma51Quat) {G : Type} [Group G] [Finite G]
    (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) {z : G} (hz : orderOf z = 2)
    {L : Subgroup G} (hL : IsSolvableTwoComponentIn L (centralizer {z})) (hzL : z ∈ L)
    (eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) :
    IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
        pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
      Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  by_cases hnc : ρ z ∈ barZ G
  · exact (false_of_mk_mem_barZ hY hz hL eL hnc).elim
  have hLH : L.map ρ ≤ barH G := barL_le_centralizer hz hL hzL eL hnc
  have hzY : ρ z ∈ barY G := mk_mem_barY hz
  have hzH : ρ z ∈ barH G := barY_le_barH hzY
  set σ := QuotientGroup.mk' (center ↥(barH G)) with hσ
  set t : ↥(barH G) := ⟨ρ z, hzH⟩ with ht
  set J := (L.map ρ).subgroupOf (barH G) with hJ
  set Jt := J.map σ with hJt
  have htc : t ∉ center ↥(barH G) := by
    rw [center_barH, mem_subgroupOf]
    exact hnc
  have htt : t * t = 1 := Subtype.ext (mul_self_eq_one_of_orderOf (orderOf_mk_z hz))
  have ht2 : orderOf (σ t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, sq, htt, map_one]
    · rw [hσ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htc
  have hztY : σ t ∈ tY G := ⟨t, hzY, rfl⟩
  have htJ : t ∈ J := mem_map_of_mem ρ hzL
  have hztJ : σ t ∈ Jt := mem_map_of_mem σ htJ
  obtain ⟨hLC, hLs⟩ := barL_subnormal hz hL
  have hJC : J ≤ centralizer {t} := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLC hx))
  have hJs : (J.subgroupOf (centralizer {t})).IsSubnormal := by
    let ι : ↥(centralizer ({t} : Set ↥(barH G))) →*
        ↥(centralizer ({ρ z} : Set (G ⧸ pPrimeCore 2 G))) :=
      { toFun := fun x => ⟨((x : ↥(barH G)) : G ⧸ pPrimeCore 2 G), by
          rw [mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have h := Subgroup.IsSubnormal.comap ι hLs
    convert h using 1
    ext x
    exact Iff.rfl
  obtain ⟨hJtC, hJts⟩ := isSubnormal_map_center hJC hJs
  obtain ⟨eLb⟩ := nonempty_barL_equiv eL
  have hinf := barL_inf_barZ hz hzL eL hnc
  have hσinj : Function.Injective (σ.subgroupMap J) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ h1
    rw [MonoidHom.mem_ker] at h1
    have h2 : σ x = 1 := congrArg Subtype.val h1
    rw [hσ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, center_barH, mem_subgroupOf] at h2
    have h3 : (x : G ⧸ pPrimeCore 2 G) ∈ L.map ρ ⊓ barZ G := ⟨hx, h2⟩
    rw [hinf, mem_bot] at h3
    exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext h3))
  let eJJt : ↥J ≃* ↥Jt :=
    MulEquiv.ofBijective (σ.subgroupMap J) ⟨hσinj, MonoidHom.subgroupMap_surjective _ _⟩
  let eLJ : ↥J ≃* ↥(L.map ρ) := subgroupOfEquivOfLe hLH
  let eJt : ↥Jt ⧸ pPrimeCore 2 ↥Jt ≃* SL(2, ZMod 3) :=
    (QuotientGroup.congr _ _ (eJJt.symm.trans eLJ) (pPrimeCore_map_iso 2 _)).trans eLb
  have hF := genFittingFStar_eq_tY hY
  have := isSimpleGroup_tY hY
  have : IsSimpleGroup ↥(Open.genFittingFStar (↥(barH G) ⧸ center ↥(barH G))) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hFnonab : ∃ a b : ↥(Open.genFittingFStar (↥(barH G) ⧸ center ↥(barH G))),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := tY_nonab hY
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b,
      fun h => hab ?_⟩
    have h1 := congrArg (MulEquiv.subgroupCongr hF) h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  obtain ⟨e₀⟩ := nonempty_fusionZStar_equiv_tY (G := G)
  rcases oddLieType_or_m11_of_slTwoThree_fstar hCI hFnonab ht2 hJtC hJts hztJ eJt with
    hodd | hm11
  ·
    obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
    have hmY : Blueprint.LieModel ↥(tY G) τ n p f :=
      GSThmB.OddQuot.lieModel_of_equiv (MulEquiv.subgroupCongr hF) hm
    have := tY_normal (G := G)
    have := barY_normal (G := G)
    have hYodd : Odd (tY G).index := by
      have h1 := Subgroup.index_map_dvd ((barY G).subgroupOf (barH G))
        (QuotientGroup.mk'_surjective (center ↥(barH G)))
      have h2 : ((barY G).subgroupOf (barH G)).index ∣ (barY G).index :=
        Subgroup.relIndex_dvd_index_of_normal (barY G) (barH G)
      exact Odd.of_dvd_nat odd_index_barY (h1.trans h2)
    have hRodd : Odd ((tY G).subgroupOf Jt).index :=
      Odd.of_dvd_nat hYodd (Subgroup.relIndex_dvd_index_of_normal (tY G) Jt)
    have hRn : ((tY G).subgroupOf Jt).Normal := Subgroup.Normal.subgroupOf inferInstance Jt
    have hRq' := nonempty_quot_of_odd_index eJt ((tY G).subgroupOf Jt) hRodd
    let eR : ↥((tY G).subgroupOf Jt) ≃* ↥(Jt.subgroupOf (tY G)) :=
      { toFun := fun x => ⟨⟨((x : ↥Jt) : ↥(barH G) ⧸ center ↥(barH G)), x.2⟩, (x : ↥Jt).2⟩
        invFun := fun x => ⟨⟨((x : ↥(tY G)) : ↥(barH G) ⧸ center ↥(barH G)), x.2⟩,
          (x : ↥(tY G)).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    let eRq := QuotientGroup.congr _ _ eR (pPrimeCore_map_iso 2 eR)
    have hRq : Nonempty (↥(Jt.subgroupOf (tY G)) ⧸ pPrimeCore 2 ↥(Jt.subgroupOf (tY G)) ≃*
          QuaternionGroup 2) ∨
        Nonempty (↥(Jt.subgroupOf (tY G)) ⧸ pPrimeCore 2 ↥(Jt.subgroupOf (tY G)) ≃*
          SL(2, ZMod 3)) :=
      hRq'.imp (fun ⟨e⟩ => ⟨eRq.symm.trans e⟩) (fun ⟨e⟩ => ⟨eRq.symm.trans e⟩)
    have hRC : Jt.subgroupOf (tY G) ≤ centralizer {(⟨σ t, hztY⟩ : ↥(tY G))} := fun x hx => by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJtC hx))
    have hRs : ((Jt.subgroupOf (tY G)).subgroupOf
        (centralizer {(⟨σ t, hztY⟩ : ↥(tY G))})).IsSubnormal := by
      let ι : ↥(centralizer ({(⟨σ t, hztY⟩ : ↥(tY G))} : Set ↥(tY G))) →*
          ↥(centralizer ({σ t} : Set (↥(barH G) ⧸ center ↥(barH G)))) :=
        { toFun := fun x => ⟨((x : ↥(tY G)) : ↥(barH G) ⧸ center ↥(barH G)), by
            rw [mem_centralizer_singleton_iff]
            exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2)⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have h := Subgroup.IsSubnormal.comap ι hJts
      convert h using 1
      ext x
      exact Iff.rfl
    have hpf := h51 ↥(tY G) τ n p f hp hp2 hmY ⟨σ t, hztY⟩
      (by rw [Subgroup.orderOf_mk]; exact ht2) (Jt.subgroupOf (tY G)) hRC hRs hztJ hRq
    have hf : 1 ≤ f := hadm.2.1
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hpf ▸ dvd_pow_self p (by omega))
    subst hp3
    have hf1 : f = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hpf.trans (pow_one 3).symm)
    subst hf1
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥(GH74.GLS.oPrimeResidual 2 G)
    exact .inl (.inl ⟨hY.2, τ, n, 1, GSThmB.OddQuot.lieModel_of_equiv (e₀.symm.trans eZ) hmY⟩)
  ·
    obtain ⟨eM⟩ := hm11
    exact .inr (nonempty_quotient_equiv_m11 hY
      ((e₀.trans (MulEquiv.subgroupCongr hF.symm)).trans eM))

theorem false_of_isQuasisimple_of_sl2Three {Q : Type} [Group Q] (hQ : IsQuasisimple Q)
    (h : Nonempty (Q ≃* PSL(2, ZMod 3)) ∨ Nonempty (Q ≃* SL(2, ZMod 3))) : False := by
  have : Group.IsSolvable SL(2, ZMod 3) := ClassicalInvolution.Q3.isSolvable_sl2Three
  have : Group.IsSolvable Q := by
    rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsPerfect Q := hQ.1
  have := LocalCores.isQuasisimple_nontrivial hQ
  have := subsingleton_of_isPerfect_of_isSolvable (X := Q)
  exact false_of_nontrivial_of_subsingleton Q

theorem card_fusionZStar_dvd {L : Type} [Group L]
    (h : Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL(2, ZMod 3)) ∨
      Nonempty (L ⧸ pPrimeCore 2 L ≃* SL(2, ZMod 3))) :
    Nat.card (L ⧸ Open.fusionZStar L) ∣ 24 := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv L
  rw [Nat.card_congr eZ.toEquiv]
  refine (Subgroup.card_quotient_dvd_card _).trans ?_
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    have h1 := Subgroup.card_quotient_dvd_card (center SL(2, ZMod 3))
    rwa [card_specialLinearGroup_two_zmod_three] at h1
  · rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two_zmod_three]

theorem false_of_lieModel_three_of_card_dvd
    {X : Type} [Group X] {τ : Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hm : Blueprint.LieModel X τ n 3 1)
    (hX : Nat.card X ∣ 24) : False := by
  have hadm := N36.admissible_of_lieModel' hm
  obtain ⟨-, -, hfac⟩ := CatLeafProof.lieOrderFormulasInput X τ n 3 1 hadm hm
  have h2 := SporRow.two_le_lieSylowExponent_three hadm
  have hX0 : Nat.card X ≠ 0 := fun h0 => by
    rw [h0] at hX
    exact absurd (Nat.eq_zero_of_zero_dvd hX) (by norm_num)
  have h9 : 3 ^ 2 ∣ Nat.card X :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hX0).mpr (by rw [hfac]; omega)
  have h924 := h9.trans hX
  norm_num at h924

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
