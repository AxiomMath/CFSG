module

public import CFSG.CharacterTheory.Semidihedral.Local.CentralizingPerfectLift
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.CharacterTheory.Semidihedral.LocalCoverFactorization

public noncomputable section

namespace CFSG.Semidihedral.PerfectLayerNormalization

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Wreathed.PrimewisePerfectLift
open scoped Pointwise

universe u v w z

theorem perfect_subgroup_absorbs_central_kernel {G : Type u} {Q : Type v}
    [Group G] [Group Q] (f : G →* Q) (J P : Subgroup G) (hJ : Group.IsPerfect J)
    (hPJ : P ≤ J) (hcentral : (f.comp J.subtype).ker ≤ Subgroup.center J)
    (himage : P.map f = J.map f) : P = J := by
  let g := f.comp J.subtype
  let U := P.subgroupOf J
  have hU : U.map g = g.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change U.map (f.comp J.subtype) = J.map f
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hPJ, himage]
  have hgen : U ⊔ g.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hU]
    ext x
    exact iff_of_true (show g x ∈ g.range from ⟨x, rfl⟩) (Subgroup.mem_top x)
  have hUtop : U = ⊤ := by
    apply top_le_iff.mp
    let := hJ
    calc
      (⊤ : Subgroup J) = ⁅⊤, ⊤⁆ := Subgroup.commutator_eq_self.symm
      _ = ⁅U, U⁆ := by
        rw [← hgen, commutator_central_join_eq U g.ker hcentral]
      _ ≤ U := Subgroup.commutator_le_self U
  have h := congrArg (Subgroup.map J.subtype) hUtop
  simpa only [U, Subgroup.map_subgroupOf_eq_of_le hPJ, Subgroup.map_top,
    Subgroup.range_subtype] using h

theorem perfect_residual_of_perfect_solvable_product {G : Type u} [Group G] [Finite G]
    (Y J N : Subgroup G) [J.Normal] (hJ : Group.IsPerfect J)
    (hN : Group.IsSolvable N) (hY : Y = J ⊔ N) :
    (CFSG.perfectResidual Y).map Y.subtype = J := by
  have hJY : J ≤ Y := hY ▸ le_sup_left
  have hNY : N ≤ Y := hY ▸ le_sup_right
  let K := J.subgroupOf Y
  let π := QuotientGroup.mk' K
  let i := Subgroup.inclusion hNY
  have hsurj : Function.Surjective (π.comp i) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hy : (y : G) ∈ J ⊔ N := hY ▸ y.property
    obtain ⟨j, hj, a, ha, hja⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    refine ⟨⟨a, ha⟩, ?_⟩
    let jy : Y := ⟨j, hJY hj⟩
    have hjone : π jy = 1 := (QuotientGroup.eq_one_iff jy).mpr hj
    have heq : y = jy * i ⟨a, ha⟩ := Subtype.ext hja.symm
    change π (i ⟨a, ha⟩) = π y
    rw [heq, map_mul, hjone, one_mul]
  let := hN
  have hquot : Group.IsSolvable (Y ⧸ K) := Group.isSolvable_of_surjective hsurj
  have hres : CFSG.perfectResidual Y ≤ K :=
    ((CFSG.perfect_residual_characterization (G := Y)).2.2.2.2.1 K).mp hquot
  apply le_antisymm
  · exact (Subgroup.map_mono hres).trans
      (Subgroup.map_subgroupOf_eq_of_le hJY).le
  · exact perfect_subgroup_le_perfectResidualOf J Y hJ hJY

theorem every_cover_contains_same_perfect_layer {G : Type u} {Q : Type v}
    [Group G] [Finite G] [Group Q] (f : G →* Q) (Y J N : Subgroup G) [J.Normal]
    (hJ : Group.IsPerfect J) (hN : Group.IsSolvable N) (hY : Y = J ⊔ N)
    (hker : f.ker = N) (hJN : ⁅J, N⁆ = ⊥) (X : Subgroup G) (hXY : X ≤ Y)
    (himage : X.map f = J.map f) :
    J ≤ X ∧ (CFSG.perfectResidual X).map X.subtype = J := by
  let P := (CFSG.perfectResidual X).map X.subtype
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  have hPperfect : Group.IsPerfect P := by
    let : Group.IsPerfect (CFSG.perfectResidual X) := perfectResidual_isPerfect
    exact Group.IsPerfect.map X.subtype
  have hPJ : P ≤ J := by
    rw [← perfect_residual_of_perfect_solvable_product Y J N hJ hN hY]
    exact perfect_subgroup_le_perfectResidualOf P Y hPperfect (hPX.trans hXY)
  have hPimage : P.map f = J.map f := by
    let := hJ
    let : Group.IsPerfect (J.map f) := Group.IsPerfect.map f
    exact actualResidual_image f X (J.map f) himage
  have hcentral : (f.comp J.subtype).ker ≤ Subgroup.center J := by
    intro j hj
    have hjN : (j : G) ∈ N := by
      rw [← hker, MonoidHom.mem_ker]
      exact hj
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN) a.property j hjN).symm
  have hP : P = J := perfect_subgroup_absorbs_central_kernel f J P hJ hPJ hcentral hPimage
  exact ⟨hP ▸ hPX, hP⟩

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Semidihedral.Local

theorem all_local_prime_covers_give_residual_and_containment {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      ∀ X : Subgroup (C t), X ≤ Y → X.map (nu t) = T₀ →
        J ≤ X ∧ (CFSG.perfectResidual X).map X.subtype = J := by
  intro T₀ Y H₀ J
  obtain ⟨hJperfect, hJnormal, -, hJimage, hJN, hY, -⟩ :=
    (all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1 hcov
  let := hJnormal
  have hN : Group.IsSolvable (N t) := CFSG.FeitThompson.isSolvable_of_odd_natCard _
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t)))
  refine ⟨(perfect_residual_of_perfect_solvable_product Y J (N t) hJperfect hN hY).symm, ?_⟩
  intro X hXY hXimage
  apply every_cover_contains_same_perfect_layer (nu t) Y J (N t) hJperfect hN hY
    (QuotientGroup.ker_mk' _) hJN X hXY
  exact hXimage.trans hJimage.symm

theorem centralizer_zpowers_eq_singleton {G : Type u} [Group G] (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
  ext g
  constructor
  · intro hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hg t (Subgroup.mem_zpowers t)).symm
  · intro hg x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hg).symm m

theorem quotient_image_central_of_centralizer_factorization {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (t : G)
    (hfactor : R ⊔ Subgroup.centralizer ({t} : Set G) = ⊤) :
    QuotientGroup.mk' R t ∈ Subgroup.center (G ⧸ R) := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
  have hx : x ∈ R ⊔ Subgroup.centralizer ({t} : Set G) := hfactor ▸ Subgroup.mem_top x
  obtain ⟨r, hr, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hrone : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  simp only [map_mul, hrone, one_mul]
  exact congrArg (QuotientGroup.mk' R) (Subgroup.mem_centralizer_singleton_iff.mp hc)

theorem central_quotient_image_restricts_to_subgroup {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (A : Subgroup G) (t : A)
    (hcentral : QuotientGroup.mk' R (t : G) ∈ Subgroup.center (G ⧸ R)) :
    QuotientGroup.mk' (R.subgroupOf A) t ∈ Subgroup.center (A ⧸ R.subgroupOf A) := by
  let K := R.subgroupOf A
  let f := (QuotientGroup.mk' R).comp A.subtype
  have hker : f.ker = K := by
    ext a
    exact QuotientGroup.eq_one_iff (a : G)
  let g := QuotientGroup.lift K f hker.ge
  have hinj : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  apply Subgroup.mem_center_iff.mpr
  intro q
  apply hinj
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hcentral (g q)

theorem central_involution_odd_kernel_factorization {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R)) (t : G) (ht : orderOf t = 2)
    (hcentral : QuotientGroup.mk' R t ∈ Subgroup.center (G ⧸ R)) :
    R ⊔ Subgroup.centralizer ({t} : Set G) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hmap := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime
    2 R hR.not_two_dvd_nat (Subgroup.zpowers t) hT
  rw [centralizer_zpowers_eq_singleton, MonoidHom.map_zpowers] at hmap
  have hcent : Subgroup.centralizer
      (Subgroup.zpowers (QuotientGroup.mk' R t) : Set (G ⧸ R)) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (Subgroup.zpowers_le.mpr hcentral)
  rw [hcent] at hmap
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' R)) hmap
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top, sup_comm] at h
  exact h

theorem subgroup_centralizer_map {G : Type u} [Group G] (A : Subgroup G) (t : A) :
    (Subgroup.centralizer ({t} : Set A)).map A.subtype =
      A ⊓ Subgroup.centralizer ({(t : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
  · rintro ⟨hgA, hgC⟩
    refine ⟨⟨g, hgA⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)

theorem intersect_normal_product {G : Type u} [Group G] (R B C : Subgroup G) [R.Normal]
    (hBC : B ≤ C) : (R ⊔ B) ⊓ C = (R ⊓ C) ⊔ B := by
  apply le_antisymm
  · rintro x ⟨hx, hxC⟩
    obtain ⟨r, hr, b, hb, hrb⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hrC : r ∈ C := by
      have heq : r = x * b⁻¹ := by rw [← hrb, mul_inv_cancel_right]
      rw [heq]
      exact C.mul_mem hxC (C.inv_mem (hBC hb))
    rw [← hrb]
    exact Subgroup.mul_mem_sup ⟨hr, hrC⟩ hb
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hBC)

theorem invariant_sylow_normalizer_centralizer_factorization {G : Type u}
    [Group G] [Finite G] (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R))
    (t : G) (ht : orderOf t = 2)
    (hcentral : QuotientGroup.mk' R t ∈ Subgroup.center (G ⧸ R))
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ R)
    (htW : t ∈ Subgroup.normalizer (((W : Subgroup R).map R.subtype) : Set G)) :
    let A := Subgroup.normalizer (((W : Subgroup R).map R.subtype) : Set G)
    let C := Subgroup.centralizer ({t} : Set G)
    let B := A ⊓ C
    A = (R ⊓ A) ⊔ B ∧ R ⊔ B = ⊤ ∧ C = (R ⊓ C) ⊔ B := by
  intro A C B
  let ta : A := ⟨t, htW⟩
  have hRodd : Odd (Nat.card (R.subgroupOf A)) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact hR.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hta : orderOf ta = 2 := (Subgroup.orderOf_coe ta).symm.trans ht
  have hAfactor := central_involution_odd_kernel_factorization (R.subgroupOf A) hRodd ta hta
    (central_quotient_image_restricts_to_subgroup R A ta hcentral)
  have hA : A = (R ⊓ A) ⊔ B := by
    have h := congrArg (Subgroup.map A.subtype) hAfactor
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, subgroup_centralizer_map,
      Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hRA : R ⊔ A = ⊤ := (sup_comm R A).trans W.normalizer_sup_eq_top
  have hRB : R ⊔ B = ⊤ := by
    rw [hA, ← sup_assoc] at hRA
    have hRR : R ⊔ R ⊓ A = R := sup_eq_left.mpr inf_le_left
    rw [hRR] at hRA
    exact hRA
  refine ⟨hA, hRB, ?_⟩
  have h := intersect_normal_product R B C inf_le_right
  rw [hRB, top_inf_eq] at h
  exact h

theorem subgroup_normalizer_map {G : Type u} [Group G] (H : Subgroup G)
    (W : Subgroup H) :
    (Subgroup.normalizer (W : Set H)).map H.subtype =
      H ⊓ Subgroup.normalizer (W.map H.subtype : Set G) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (f := H.subtype)
    (H := W.map H.subtype) (by rw [Subgroup.range_subtype]; exact Subgroup.map_subtype_le _)
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h
  have hm := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype, inf_comm] at hm
  exact hm.symm

theorem ambient_invariant_sylow_normalizer_centralizer_factorization {G : Type u}
    [Group G] [Finite G] (H : Subgroup G) (R : Subgroup H) [R.Normal]
    (hR : Odd (Nat.card R)) (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (hfactor : R ⊔ Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ R)
    (htW : t ∈ Subgroup.normalizer
      (((W : Subgroup R).map (H.subtype.comp R.subtype)) : Set G)) :
    let C := Subgroup.centralizer ({t} : Set G)
    let Ra := R.map H.subtype
    let Wa := (W : Subgroup R).map (H.subtype.comp R.subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C
    H = Ra ⊔ B ∧ H ⊓ C = (Ra ⊓ C) ⊔ B := by
  intro C Ra Wa A B
  let th : H := ⟨t, htH⟩
  let Wh := (W : Subgroup R).map R.subtype
  let Ah := Subgroup.normalizer (Wh : Set H)
  let Ch := Subgroup.centralizer ({th} : Set H)
  have hWa : Wh.map H.subtype = Wa := Subgroup.map_map _ _ _
  have hAh : Ah.map H.subtype = A := by
    rw [subgroup_normalizer_map, hWa]
  have htAh : th ∈ Ah := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (f := H.subtype)
      (H := Wa) (by rw [Subgroup.range_subtype, ← hWa]; exact Subgroup.map_subtype_le _)
    rw [← hWa, Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h
    change th ∈ Subgroup.normalizer (Wh : Set H)
    rw [← h]
    change t ∈ Subgroup.normalizer (Wh.map H.subtype : Set G)
    rwa [hWa]
  have hth : orderOf th = 2 := (Subgroup.orderOf_coe th).symm.trans ht
  obtain ⟨-, hRB, hCB⟩ := invariant_sylow_normalizer_centralizer_factorization
    R hR th hth (quotient_image_central_of_centralizer_factorization R th hfactor) ℓ W htAh
  have hB : (Ah ⊓ Ch).map H.subtype = B := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, hAh, subgroup_centralizer_map]
    change A ⊓ (H ⊓ C) = A ⊓ C
    rw [← inf_assoc, inf_eq_left.mpr (show A ≤ H from inf_le_left)]
  constructor
  · have h := congrArg (Subgroup.map H.subtype) hRB
    rw [Subgroup.map_sup, hB, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  · have h := congrArg (Subgroup.map H.subtype) hCB
    rw [subgroup_centralizer_map, Subgroup.map_sup,
      Subgroup.map_inf _ _ _ H.subtype_injective, subgroup_centralizer_map, hB] at h
    change H ⊓ C = (Ra ⊓ (H ⊓ C)) ⊔ B at h
    have hRaH : Ra ≤ H := Subgroup.map_subtype_le _
    have hRa : Ra ⊓ (H ⊓ C) = Ra ⊓ C := by
      rw [← inf_assoc, inf_eq_left.mpr hRaH]
    rwa [hRa] at h

theorem centralizer_factor_covers_same_target {G : Type u} {Q : Type v}
    [Group G] [Group Q] (C H R B : Subgroup G) (f : C →* Q) (T : Subgroup Q)
    (hBC : B ≤ C) (hfactor : H ⊓ C = (R ⊓ C) ⊔ B)
    (hkernel : R ⊓ C ≤ f.ker.map C.subtype)
    (hcover : T ≤ ((H ⊓ C).subgroupOf C).map f) :
    ((B.subgroupOf C) ⊓ T.comap f).map f = T := by
  let Bc := B.subgroupOf C
  have hcoverB : T ≤ Bc.map f := by
    have hsub : (H ⊓ C).subgroupOf C = (R ⊓ C).subgroupOf C ⊔ Bc := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_subgroupOf_eq_of_le hBC]
      exact hfactor
    have hzero : ((R ⊓ C).subgroupOf C).map f = ⊥ := by
      apply (Subgroup.map_eq_bot_iff ((R ⊓ C).subgroupOf C)).mpr
      intro r hr
      have h := hkernel hr
      obtain ⟨r', hr', heq⟩ := Subgroup.mem_map.mp h
      have heq' : r' = r := Subtype.ext heq
      exact heq' ▸ hr'
    rw [hsub, Subgroup.map_sup, hzero, bot_sup_eq] at hcover
    exact hcover
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · intro q hq
    obtain ⟨b, hb, hbq⟩ := Subgroup.mem_map.mp (hcoverB hq)
    have hbT : b ∈ T.comap f := by
      change f b ∈ T
      rw [hbq]
      exact hq
    exact Subgroup.mem_map.mpr ⟨b, ⟨hb, hbT⟩, hbq⟩

theorem layer_normalizes_from_actual_factorization {G : Type u} {Q : Type v}
    [Group G] [Finite G] [Group Q] (C H : Subgroup G) (f : C →* Q) (T : Subgroup Q)
    (J : Subgroup C) (hJH : J.map C.subtype ≤ H)
    (hJimage : J.map f = T)
    (hcontain : ∀ X : Subgroup C, X ≤ T.comap f → X.map f = T → J ≤ X)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (hC : C = Subgroup.centralizer ({t} : Set G))
    (hfactor : R ⊔ Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤)
    (hkernel : (R.map H.subtype) ⊓ C ≤ f.ker.map C.subtype)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ R)
    (htW : t ∈ Subgroup.normalizer
      (((W : Subgroup R).map (H.subtype.comp R.subtype)) : Set G)) :
    let Ra := R.map H.subtype
    let Wa := (W : Subgroup R).map (H.subtype.comp R.subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C
    let X := B.subgroupOf C ⊓ T.comap f
    H = Ra ⊔ B ∧ H ⊓ C = (Ra ⊓ C) ⊔ B ∧ X.map f = T ∧ J ≤ X ∧
      J.map C.subtype ≤ B ∧ J.map C.subtype ≤ A := by
  intro Ra Wa A B X
  obtain ⟨hHB, hCB⟩ := ambient_invariant_sylow_normalizer_centralizer_factorization
    H R hR t htH ht hfactor ℓ W htW
  rw [← hC] at hHB hCB
  have hJHC : J.map C.subtype ≤ H ⊓ C :=
    le_inf hJH (Subgroup.map_subtype_le _)
  have hcover : T ≤ ((H ⊓ C).subgroupOf C).map f := by
    rw [← hJimage]
    apply Subgroup.map_mono
    intro j hj
    exact hJHC (Subgroup.mem_map_of_mem C.subtype hj)
  have hX : X.map f = T :=
    centralizer_factor_covers_same_target C H Ra B f T inf_le_right hCB hkernel hcover
  have hJX : J ≤ X := hcontain X inf_le_right hX
  have hJB : J.map C.subtype ≤ B := by
    rintro _ ⟨j, hj, rfl⟩
    exact (hJX hj).1
  exact ⟨hHB, hCB, hX, hJX, hJB, hJB.trans inf_le_left⟩

theorem actual_local_layer_normalization_of_cover_factorization {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (H : Subgroup G) (htH : t ∈ H)
    (hJH :
      let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      let Y := T₀.comap (nu t)
      let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
      ((CFSG.perfectResidual H₀).map H₀.subtype).map (C t).subtype ≤ H)
    (hfactor : (CFSG.pPrimeCore 2 H) ⊔
      Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤)
    (hinter : ((CFSG.pPrimeCore 2 H).map H.subtype) ⊓ C t = ((N t).map (C t).subtype) ⊓ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ (CFSG.pPrimeCore 2 H))
    (htW : t ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) : Set G)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
    let Wa := (W : Subgroup (CFSG.pPrimeCore 2 H)).map
      (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C t
    let X := B.subgroupOf (C t) ⊓ Y
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      (∀ U : Subgroup (C t), U ≤ Y → U.map (nu t) = T₀ → J ≤ U) ∧
      H = Ra ⊔ B ∧ H ⊓ C t = (Ra ⊓ C t) ⊔ B ∧
      Ra ⊓ C t = (N t).map (C t).subtype ⊓ H ∧
      X.map (nu t) = T₀ ∧ J ≤ X ∧ J.map (C t).subtype ≤ B ∧
      J.map (C t).subtype ≤ A := by
  intro T₀ Y H₀ J Ra Wa A B X
  obtain ⟨hres, hcontain⟩ := all_local_prime_covers_give_residual_and_containment
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨-, -, -, hJimage, -⟩ :=
    (all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel).1 hcov
  have hkernel : Ra ⊓ C t ≤ (nu t).ker.map (C t).subtype := by
    rw [QuotientGroup.ker_mk', hinter]
    exact inf_le_left
  have hRodd : Odd (Nat.card (CFSG.pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  obtain ⟨hHB, hCB, hX, hJX, hJB, hJA⟩ := layer_normalizes_from_actual_factorization
    (C t) H (nu t) T₀ J hJH hJimage (fun U hUY hU => (hcontain U hUY hU).1)
    (CFSG.pPrimeCore 2 H) hRodd t htH ht rfl hfactor hkernel ℓ W htW
  exact ⟨hres, fun U hUY hU => (hcontain U hUY hU).1, hHB, hCB, hinter, hX, hJX, hJB, hJA⟩

theorem containing_layer_covers_original_preimage {G : Type u} {Q : Type v}
    [Group G] [Group Q] (C H : Subgroup G) (f : C →* Q) (T : Subgroup Q)
    (J : Subgroup C) (hJH : J.map C.subtype ≤ H) (hJimage : J.map f = T) :
    (H.subgroupOf C ⊓ T.comap f).map f = T := by
  have hJHc : J ≤ H.subgroupOf C := by
    intro j hj
    exact hJH (Subgroup.mem_map_of_mem C.subtype hj)
  have hJY : J ≤ T.comap f := by
    intro j hj
    change f j ∈ T
    rw [← hJimage]
    exact Subgroup.mem_map_of_mem f hj
  apply le_antisymm
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
  · calc
      T = J.map f := hJimage.symm
      _ ≤ (H.subgroupOf C ⊓ T.comap f).map f := Subgroup.map_mono (le_inf hJHc hJY)

theorem normal_layer_products_retain_original_elements {G : Type u} [Group G]
    (H C B : Subgroup G) (R : Subgroup H) [R.Normal] (hBH : B ≤ H ⊓ C)
    (hHB : H = R.map H.subtype ⊔ B)
    (hCB : H ⊓ C = (R.map H.subtype ⊓ C) ⊔ B) :
    (H : Set G) = (R.map H.subtype : Set G) * (B : Set G) ∧
      ((H ⊓ C : Subgroup G) : Set G) =
        ((R.map H.subtype ⊓ C : Subgroup G) : Set G) * (B : Set G) ∧
      (∀ x ∈ H, ∃ r ∈ R.map H.subtype, ∃ b ∈ B, r * b = x) ∧
      (∀ x ∈ H ⊓ C, ∃ r ∈ R.map H.subtype ⊓ C, ∃ b ∈ B, r * b = x) := by
  let Ra := R.map H.subtype
  have hRaH : Ra ≤ H := Subgroup.map_subtype_le _
  have hRaof : Ra.subgroupOf H = R :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective R
  have hRanormal : (Ra.subgroupOf H).Normal := hRaof.symm ▸ inferInstance
  let := hRanormal
  have hBnorm : B ≤ Subgroup.normalizer (Ra : Set G) :=
    (hBH.trans inf_le_left).trans (Subgroup.le_normalizer_of_normal_subgroupOf hRaH)
  have hBnormC : B ≤ Subgroup.normalizer ((Ra ⊓ C : Subgroup G) : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro b hb r hr
    exact ⟨Subgroup.le_normalizer_iff.mp hBnorm b hb r hr.1,
      C.mul_mem (C.mul_mem (hBH hb).2 hr.2) (C.inv_mem (hBH hb).2)⟩
  have hHprod : (H : Set G) = (Ra : Set G) * (B : Set G) := by
    rw [hHB]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Ra B hBnorm
  have hCprod : ((H ⊓ C : Subgroup G) : Set G) =
      ((Ra ⊓ C : Subgroup G) : Set G) * (B : Set G) := by
    rw [hCB]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (Ra ⊓ C) B hBnormC
  refine ⟨hHprod, hCprod, ?_, ?_⟩
  · intro x hx
    exact Set.mem_mul.mp (hHprod ▸ hx)
  · intro x hx
    exact Set.mem_mul.mp (hCprod ▸ hx)

theorem nonabelian_simple_has_no_subgroup_index_two {G : Type u} [Group G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∀ U : Subgroup G, U.index ≠ 2 := by
  intro U hU
  have htopSimple : IsSimpleGroup (⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  let := htopSimple
  have htop : (⊤ : Subgroup G) ≤ U := simple_le_index_two ⊤ U hU (by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩,
      fun h => hab (congrArg Subtype.val h)⟩)
  have hUtop : U = ⊤ := top_le_iff.mp htop
  rw [hUtop, Subgroup.index_top] at hU
  omega

theorem first_generator_mem_original_fourgroup {G : Type u} [Group G] (t s : G) :
    t ∈ Subgroup.closure ({t, s} : Set G) :=
  Subgroup.mem_closure_of_mem (Set.mem_insert t {s})

theorem original_fourgroup_invariance_gives_involution_normalization {G : Type u} [Group G]
    (t s : G) (H W : Subgroup G)
    (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hVW : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    t ∈ H ∧ t ∈ Subgroup.normalizer (W : Set G) := by
  have htV := first_generator_mem_original_fourgroup t s
  exact ⟨hVH htV, hVW htV⟩

theorem centralizing_layer_kernel_is_original_odd_overlap {G : Type u} {Q : Type v}
    [Group G] [Group Q] (f : G →* Q) (J N : Subgroup G) (hker : f.ker = N)
    (hJN : ⁅J, N⁆ = ⊥) (hNodd : Odd (Nat.card N)) :
    let E := J ⊓ N
    (f.comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) := by
  intro E
  have hEker : (f.comp J.subtype).ker = E.subgroupOf J := by
    ext j
    change f j = 1 ↔ (j : G) ∈ J ⊓ N
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => ⟨j.property, h⟩, fun h => h.2⟩
  refine ⟨hEker, ?_, hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)⟩
  intro e he
  apply Subgroup.mem_center_iff.mpr
  intro j
  apply Subtype.ext
  exact ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN) j.property e he.2).symm

theorem isomorphism_maps_actual_centralizer {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (D : Subgroup G) :
    (Subgroup.centralizer (D : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (D.map e.toMonoidHom : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hx y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    change e d * x = x * e d
    have h := congrArg e (hx d hd)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · intro hx d hd
    apply e.injective
    have h := hx (e d) (Subgroup.mem_map_of_mem e.toMonoidHom hd)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

@[expose] def originalCentralizerEquiv {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) : C t ≃* C (e t) where
  toFun x := ⟨e x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm
      (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

theorem originalCentralizerEquiv_tInC {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) :
    originalCentralizerEquiv e t (tInC t) = tInC (e t) := rfl

theorem originalCentralizerEquiv_maps_oddCore {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) :
    (N t).map (originalCentralizerEquiv e t).toMonoidHom = N (e t) :=
  CFSG.pPrimeCore_map_iso 2 (originalCentralizerEquiv e t)

theorem originalCentralizerEquiv_maps_fullKernel {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) :
    (NZ t).map (originalCentralizerEquiv e t).toMonoidHom = NZ (e t) := by
  change (N t ⊔ Subgroup.zpowers (tInC t)).map _ =
    N (e t) ⊔ Subgroup.zpowers (tInC (e t))
  rw [Subgroup.map_sup, originalCentralizerEquiv_maps_oddCore, MonoidHom.map_zpowers]
  change N (e t) ⊔ Subgroup.zpowers (originalCentralizerEquiv e t (tInC t)) = _
  rw [originalCentralizerEquiv_tInC]

@[expose] def originalOddQuotientEquiv {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) :
    CFSG.Semidihedral.ActualSimpleLayerLocalPackage.H t ≃*
      CFSG.Semidihedral.ActualSimpleLayerLocalPackage.H (e t) :=
  QuotientGroup.congr (N t) (N (e t)) (originalCentralizerEquiv e t)
    (originalCentralizerEquiv_maps_oddCore e t)

@[expose] def originalReducedQuotientEquiv {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) : Gamma t ≃* Gamma (e t) :=
  QuotientGroup.congr (NZ t) (NZ (e t)) (originalCentralizerEquiv e t)
    (originalCentralizerEquiv_maps_fullKernel e t)

theorem originalOddQuotientEquiv_nu {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) (x : C t) :
    originalOddQuotientEquiv e t (nu t x) =
      nu (e t) (originalCentralizerEquiv e t x) := rfl

theorem originalReducedQuotientEquiv_kappa {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) (x : C t) :
    originalReducedQuotientEquiv e t (kappa t x) =
      kappa (e t) (originalCentralizerEquiv e t x) := rfl

theorem original_quotient_maps_commute {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G)
    (x : CFSG.Semidihedral.ActualSimpleLayerLocalPackage.H t) :
    originalReducedQuotientEquiv e t (barKappa t x) =
      barKappa (e t) (originalOddQuotientEquiv e t x) := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N t) x
  rfl

theorem isomorphism_maps_actual_perfectResidual {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') :
    (CFSG.perfectResidual G).map e.toMonoidHom = CFSG.perfectResidual G' := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  exact finite_perfectResidual_map_eq e.toMonoidHom e.surjective

theorem isomorphism_maps_actual_fittingSubgroup {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') :
    (CFSG.fittingSubgroup G).map e.toMonoidHom = CFSG.fittingSubgroup G' := by
  let : Finite G' := Finite.of_equiv G e.toEquiv
  have hforward : (CFSG.fittingSubgroup G).map e.toMonoidHom ≤ CFSG.fittingSubgroup G' :=
    CFSG.LocalCores.fitting_characteristic.2.2 _
      (CFSG.fittingSubgroup_normal.map e.toMonoidHom e.surjective)
      (Group.nilpotent_of_mulEquiv
        ((CFSG.fittingSubgroup G).equivMapOfInjective e.toMonoidHom e.injective))
  have hback : (CFSG.fittingSubgroup G').map e.symm.toMonoidHom ≤ CFSG.fittingSubgroup G :=
    CFSG.LocalCores.fitting_characteristic.2.2 _
      (CFSG.fittingSubgroup_normal.map e.symm.toMonoidHom e.symm.surjective)
      (Group.nilpotent_of_mulEquiv
        ((CFSG.fittingSubgroup G').equivMapOfInjective e.symm.toMonoidHom e.symm.injective))
  apply le_antisymm hforward
  have h := Subgroup.map_mono (f := e.toMonoidHom) hback
  have hundo :
      ((CFSG.fittingSubgroup G').map e.symm.toMonoidHom).map e.toMonoidHom =
        CFSG.fittingSubgroup G' := by
    have hu := CFSG.LocalCores.map_map_symm e.symm (CFSG.fittingSubgroup G')
    simpa only [MulEquiv.symm_symm] using hu
  rw [hundo] at h
  exact h

theorem isomorphism_maps_actual_layer {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') :
    (CFSG.layer G).map e.toMonoidHom = CFSG.layer G' := by
  have hbij := (CFSG.LocalCores.component_isomorphism e).2
  change e.mapSubgroup (sSup {D : Subgroup G | CFSG.IsComponent D}) = CFSG.layer G'
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

theorem isomorphism_maps_actual_generalizedFitting {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') :
    (CFSG.generalizedFitting G).map e.toMonoidHom = CFSG.generalizedFitting G' := by
  change (CFSG.fittingSubgroup G ⊔ CFSG.layer G).map e.toMonoidHom =
    CFSG.fittingSubgroup G' ⊔ CFSG.layer G'
  rw [Subgroup.map_sup, isomorphism_maps_actual_fittingSubgroup, isomorphism_maps_actual_layer]

theorem isomorphism_maps_actual_preimage {G : Type u} {G' : Type v} {Q : Type w} {Q' : Type z}
    [Group G] [Group G'] [Group Q] [Group Q'] (e : G ≃* G') (a : Q ≃* Q')
    (f : G →* Q) (f' : G' →* Q') (hcomm : ∀ x, a (f x) = f' (e x))
    (T : Subgroup Q) :
    (T.comap f).map e.toMonoidHom = (T.map a.toMonoidHom).comap f' := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change f (e.symm x) ∈ T ↔ f' x ∈ T.map a.toMonoidHom
  rw [Subgroup.mem_map_equiv]
  have h := hcomm (e.symm x)
  rw [e.apply_symm_apply] at h
  rw [← h, a.symm_apply_apply]

theorem isomorphism_maps_actual_subgroupResidual {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (D : Subgroup G) :
    ((CFSG.perfectResidual D).map D.subtype).map e.toMonoidHom =
      (CFSG.perfectResidual (D.map e.toMonoidHom)).map (D.map e.toMonoidHom).subtype := by
  let a := D.equivMapOfInjective e.toMonoidHom e.injective
  have h := congrArg (Subgroup.map (D.map e.toMonoidHom).subtype)
    (isomorphism_maps_actual_perfectResidual a)
  rw [Subgroup.map_map] at h ⊢
  exact h

theorem original_local_layer_preimages_transport {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (t : G) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let T₀' := (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))
    let Y' := T₀'.comap (nu (e t))
    T₀.map (originalOddQuotientEquiv e t).toMonoidHom = T₀' ∧
      Y.map (originalCentralizerEquiv e t).toMonoidHom = Y' := by
  intro T₀ Y T₀' Y'
  have hL := isomorphism_maps_actual_generalizedFitting (originalReducedQuotientEquiv e t)
  have hT : T₀.map (originalOddQuotientEquiv e t).toMonoidHom = T₀' := by
    dsimp only [T₀, T₀']
    rw [isomorphism_maps_actual_preimage (originalOddQuotientEquiv e t)
      (originalReducedQuotientEquiv e t) (barKappa t) (barKappa (e t))
      (original_quotient_maps_commute e t), hL]
  refine ⟨hT, ?_⟩
  dsimp only [Y, Y']
  rw [isomorphism_maps_actual_preimage (originalCentralizerEquiv e t)
    (originalOddQuotientEquiv e t) (nu t) (nu (e t)) (originalOddQuotientEquiv_nu e t), hT]

theorem original_centralizing_layer_and_overlap_transport {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (t : G) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let T₀' := (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))
    let Y' := T₀'.comap (nu (e t))
    let H₀' := Y' ⊓ Subgroup.centralizer (N (e t) : Set (C (e t)))
    let J' := (CFSG.perfectResidual H₀').map H₀'.subtype
    let E' := J' ⊓ N (e t)
    H₀.map (originalCentralizerEquiv e t).toMonoidHom = H₀' ∧
      J.map (originalCentralizerEquiv e t).toMonoidHom = J' ∧
      E.map (originalCentralizerEquiv e t).toMonoidHom = E' := by
  intro T₀ Y H₀ J E T₀' Y' H₀' J' E'
  have hY := (original_local_layer_preimages_transport e t).2
  have hH₀ : H₀.map (originalCentralizerEquiv e t).toMonoidHom = H₀' := by
    dsimp only [H₀, H₀']
    rw [Subgroup.map_inf _ _ _ (originalCentralizerEquiv e t).injective, hY,
      isomorphism_maps_actual_centralizer, originalCentralizerEquiv_maps_oddCore]
  have hJ : J.map (originalCentralizerEquiv e t).toMonoidHom = J' := by
    dsimp only [J, J']
    rw [isomorphism_maps_actual_subgroupResidual, hH₀]
  refine ⟨hH₀, hJ, ?_⟩
  dsimp only [E, E']
  rw [Subgroup.map_inf _ _ _ (originalCentralizerEquiv e t).injective, hJ,
    originalCentralizerEquiv_maps_oddCore]

@[expose] def originalOddCoreEquiv {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) : N t ≃* N (e t) :=
  ((N t).equivMapOfInjective (originalCentralizerEquiv e t).toMonoidHom
    (originalCentralizerEquiv e t).injective).trans
      (MulEquiv.subgroupCongr (originalCentralizerEquiv_maps_oddCore e t))

theorem originalOddCoreEquiv_coe {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) (x : N t) :
    (originalOddCoreEquiv e t x : C (e t)) = originalCentralizerEquiv e t (x : C t) := by
  exact MulEquiv.subgroupCongr_apply (originalCentralizerEquiv_maps_oddCore e t)
    (((N t).equivMapOfInjective (originalCentralizerEquiv e t).toMonoidHom
      (originalCentralizerEquiv e t).injective) x)

@[expose] def originalGeneralizedFittingEquiv {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (t : G) :
    CFSG.generalizedFitting (Gamma t) ≃* CFSG.generalizedFitting (Gamma (e t)) :=
  ((CFSG.generalizedFitting (Gamma t)).equivMapOfInjective
    (originalReducedQuotientEquiv e t).toMonoidHom
    (originalReducedQuotientEquiv e t).injective).trans
      (MulEquiv.subgroupCongr
        (isomorphism_maps_actual_generalizedFitting (originalReducedQuotientEquiv e t)))

theorem isomorphism_transports_nonabelian {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (h : ∃ a b : G, a * b ≠ b * a) :
    ∃ a b : G', a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun heq => hab (e.injective ?_)⟩
  simpa only [map_mul] using heq

theorem isomorphism_transports_no_index_two {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (h : ∀ U : Subgroup G, U.index ≠ 2) :
    ∀ U : Subgroup G', U.index ≠ 2 := by
  intro U
  have hind := h (U.map e.symm.toMonoidHom)
  have hindex := Subgroup.index_map_equiv U e.symm
  change (U.map e.symm.toMonoidHom).index = U.index at hindex
  rwa [hindex] at hind

theorem isomorphism_transports_noncyclic_sylows {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ∀ P : Sylow ℓ G, ¬ IsCyclic P) : ∀ P : Sylow ℓ G', ¬ IsCyclic P := by
  intro P' hcyc
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective ℓ P'
  have hsub : (P : Subgroup G).map e.toMonoidHom = (P' : Subgroup G') := by
    have hcoe := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
    change ((P.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow ℓ G') :
      Subgroup G') = (P : Subgroup G).map e.toMonoidHom at hcoe
    exact hcoe.symm.trans (congrArg (fun Q : Sylow ℓ G' => (Q : Subgroup G')) hP)
  let a := ((P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hsub)
  let := hcyc
  exact h P (isCyclic_of_injective a.toMonoidHom a.injective)

theorem original_psl_two_model_transport {L : Type u} {L' : Type}
    [Group L] [Group L'] (e : L ≃* L') (p f : ℕ)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (L ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L' .PSL 2 p f := by
  obtain ⟨hadm, F, hF, hfin, hcard, ⟨a⟩⟩ := hmodel
  exact ⟨hadm, F, hF, hfin, hcard, ⟨e.symm.trans a⟩⟩

theorem original_all_local_prime_cover_transport {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (t : G)
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N (e t)) → ∃ P : Sylow ℓ (N (e t)),
      (Subgroup.centralizer
        (((P : Subgroup (N (e t))).map (N (e t)).subtype : Subgroup (C (e t))) :
          Set (C (e t))) ⊓
        ((CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))).comap (nu (e t))).map
          (nu (e t)) = (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) := by
  let a := originalOddCoreEquiv e t
  let c := originalCentralizerEquiv e t
  let b := originalOddQuotientEquiv e t
  have hcomm : b.toMonoidHom.comp (nu t) = (nu (e t)).comp c.toMonoidHom := by
    ext x
    exact originalOddQuotientEquiv_nu e t x
  obtain ⟨hT, hY⟩ := original_local_layer_preimages_transport e t
  intro ℓ _ hdiv
  have hdiv' : ℓ ∣ Nat.card (N t) := by
    rw [Nat.card_congr a.toEquiv]
    exact hdiv
  obtain ⟨P, hP⟩ := hcov ℓ hdiv'
  let P' : Sylow ℓ (N (e t)) := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hambient : ((P' : Subgroup (N (e t))).map (N (e t)).subtype) =
      ((P : Subgroup (N t)).map (N t).subtype).map c.toMonoidHom := by
    have hcoe := Sylow.coe_mapSurjective (f := a.toMonoidHom) a.surjective P
    change (P' : Subgroup (N (e t))) = (P : Subgroup (N t)).map a.toMonoidHom at hcoe
    rw [hcoe, Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨P', ?_⟩
  have h := congrArg (Subgroup.map b.toMonoidHom) hP
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map,
    Subgroup.map_inf _ _ _ c.injective, isomorphism_maps_actual_centralizer,
    ← hambient, hY, hT] at h
  exact h

theorem original_all_local_prime_covers_give_actual_perfect_layer {G : Type u}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    Group.IsPerfect J ∧ J.Normal ∧ tInC t ∈ J ∧ J.map (nu t) = T₀ ∧
      ⁅J, N t⁆ = ⊥ ∧ Y = J ⊔ N t ∧
      ((nu t).comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) := by
  intro T₀ Y H₀ J E
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let c := originalCentralizerEquiv e t
  let b := originalOddQuotientEquiv e t
  let d := originalGeneralizedFittingEquiv e t
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e t))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e t)) : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map (originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [isomorphism_maps_actual_centralizer, isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  obtain ⟨-, hnormal', htJ', himage', hJN', hY', -⟩ :=
    (all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift
      n hn S0' f0' (isomorphism_transports_no_index_two e hG) (e t)
      ((e.orderOf_eq t).trans ht) (isomorphism_transports_nonabelian d hnonab)
      hcentral' (isomorphism_transports_noncyclic_sylows d 2 hnc)
      p f hp hpodd hf hq (original_psl_two_model_transport d p f hmodel)).1
        (original_all_local_prime_cover_transport e t hcov)
  obtain ⟨hT, hY⟩ := original_local_layer_preimages_transport e t
  obtain ⟨-, hJ, -⟩ := original_centralizing_layer_and_overlap_transport e t
  change T₀.map b.toMonoidHom = _ at hT
  change Y.map c.toMonoidHom = _ at hY
  change J.map c.toMonoidHom = _ at hJ
  have hnormal : J.Normal := by
    apply Subgroup.Normal.of_map_injective (φ := c.toMonoidHom) c.injective
    rw [hJ]
    exact hnormal'
  have hperfect : Group.IsPerfect J := by
    let : Group.IsPerfect (CFSG.perfectResidual H₀) := perfectResidual_isPerfect
    exact Group.IsPerfect.map H₀.subtype
  have htJ : tInC t ∈ J := by
    rw [← hJ] at htJ'
    have hmem : c (tInC t) ∈ J.map c.toMonoidHom := by
      have hct : c (tInC t) = tInC (e t) := originalCentralizerEquiv_tInC e t
      rw [hct]
      exact htJ'
    rw [Subgroup.mem_map_equiv, c.symm_apply_apply] at hmem
    exact hmem
  have hcomm : b.toMonoidHom.comp (nu t) = (nu (e t)).comp c.toMonoidHom := by
    ext x
    exact originalOddQuotientEquiv_nu e t x
  have himage : J.map (nu t) = T₀ := by
    apply Subgroup.map_injective (f := b.toMonoidHom) b.injective
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hJ, himage', hT]
  have hJN : ⁅J, N t⁆ = ⊥ := by
    apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    rw [Subgroup.map_commutator, hJ, originalCentralizerEquiv_maps_oddCore, hJN',
      Subgroup.map_bot]
  have hYprod : Y = J ⊔ N t := by
    apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    rw [Subgroup.map_sup, hJ, originalCentralizerEquiv_maps_oddCore, hY]
    exact hY'
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  obtain ⟨hEker, hEcentral, hEodd⟩ := centralizing_layer_kernel_is_original_odd_overlap
    (nu t) J (N t) (QuotientGroup.ker_mk' _) hJN hNodd
  exact ⟨hperfect, hnormal, htJ, himage, hJN, hYprod, hEker, hEcentral, hEodd⟩

theorem original_all_local_prime_covers_give_residual_and_containment {G : Type u}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      ∀ X : Subgroup (C t), X ≤ Y → X.map (nu t) = T₀ →
        J ≤ X ∧ (CFSG.perfectResidual X).map X.subtype = J := by
  intro T₀ Y H₀ J
  obtain ⟨hJperfect, hJnormal, -, hJimage, hJN, hY, -⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  let := hJnormal
  have hN : Group.IsSolvable (N t) := CFSG.FeitThompson.isSolvable_of_odd_natCard _
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t)))
  refine ⟨(perfect_residual_of_perfect_solvable_product Y J (N t) hJperfect hN hY).symm, ?_⟩
  intro X hXY hXimage
  apply every_cover_contains_same_perfect_layer (nu t) Y J (N t) hJperfect hN hY
    (QuotientGroup.ker_mk' _) hJN X hXY
  exact hXimage.trans hJimage.symm

theorem original_layer_normalization_of_cover_factorization {G : Type u}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (s : G) (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH :
      let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      let Y := T₀.comap (nu t)
      let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
      ((CFSG.perfectResidual H₀).map H₀.subtype).map (C t).subtype ≤ H)
    (hfactor : (CFSG.pPrimeCore 2 H) ⊔ Subgroup.centralizer
      ({(⟨t, hVH (first_generator_mem_original_fourgroup t s)⟩ : H)} : Set H) = ⊤)
    (hinter : ((CFSG.pPrimeCore 2 H).map H.subtype) ⊓ C t = ((N t).map (C t).subtype) ⊓ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((W : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) : Set G)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
    let Wa := (W : Subgroup (CFSG.pPrimeCore 2 H)).map
      (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C t
    let X := B.subgroupOf (C t) ⊓ Y
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      (∀ U : Subgroup (C t), U ≤ Y → U.map (nu t) = T₀ →
        J ≤ U ∧ (CFSG.perfectResidual U).map U.subtype = J) ∧
      H = Ra ⊔ B ∧ H ⊓ C t = (Ra ⊓ C t) ⊔ B ∧
      Ra ⊓ C t = (N t).map (C t).subtype ⊓ H ∧
      X.map (nu t) = T₀ ∧ J ≤ X ∧ J.map (C t).subtype ≤ B ∧
      J.map (C t).subtype ≤ A ∧
      ((nu t).comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) ∧
      (H : Set G) = (Ra : Set G) * (B : Set G) ∧
      ((H ⊓ C t : Subgroup G) : Set G) = ((Ra ⊓ C t : Subgroup G) : Set G) * (B : Set G) ∧
      (∀ x ∈ H, ∃ r ∈ Ra, ∃ b ∈ B, r * b = x) ∧
      (∀ x ∈ H ⊓ C t, ∃ r ∈ Ra ⊓ C t, ∃ b ∈ B, r * b = x) := by
  intro T₀ Y H₀ J E Ra Wa A B X
  obtain ⟨hres, hcontain⟩ := original_all_local_prime_covers_give_residual_and_containment
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨-, -, -, hJimage, -, -, hEker, hEcentral, hEodd⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨htH, htW⟩ := original_fourgroup_invariance_gives_involution_normalization
    t s H Wa hVH hVW
  have hkernel : Ra ⊓ C t ≤ (nu t).ker.map (C t).subtype := by
    rw [QuotientGroup.ker_mk', hinter]
    exact inf_le_left
  have hRodd : Odd (Nat.card (CFSG.pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  obtain ⟨hHB, hCB, hX, hJX, hJB, hJA⟩ := layer_normalizes_from_actual_factorization
    (C t) H (nu t) T₀ J hJH hJimage (fun U hUY hU => (hcontain U hUY hU).1)
    (CFSG.pPrimeCore 2 H) hRodd t htH ht rfl hfactor hkernel ℓ W htW
  obtain ⟨hprod, hcprod, helements, hcelements⟩ := normal_layer_products_retain_original_elements
    H (C t) B (CFSG.pPrimeCore 2 H)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hHB hCB
  exact ⟨hres, hcontain, hHB, hCB, hinter, hX, hJX, hJB, hJA, hEker, hEcentral, hEodd,
    hprod, hcprod, helements, hcelements⟩

theorem isomorphism_maps_original_subgroup_odd_core {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) :
    ((CFSG.pPrimeCore 2 H).map H.subtype).map e.toMonoidHom =
      (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype := by
  let a := H.equivMapOfInjective e.toMonoidHom e.injective
  have h := congrArg (Subgroup.map (H.map e.toMonoidHom).subtype) (CFSG.pPrimeCore_map_iso 2 a)
  rw [Subgroup.map_map] at h ⊢
  exact h

theorem isomorphism_maps_original_element_centralizer {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) :
    (Subgroup.centralizer ({t} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set G') := by
  rw [← centralizer_zpowers_eq_singleton, isomorphism_maps_actual_centralizer,
    MonoidHom.map_zpowers]
  exact centralizer_zpowers_eq_singleton (e t)

theorem isomorphism_maps_original_subgroup_in_centralizer {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) (H : Subgroup G) :
    (H.subgroupOf (C t)).map (originalCentralizerEquiv e t).toMonoidHom =
      (H.map e.toMonoidHom).subgroupOf (C (e t)) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change (e.symm (x : G')) ∈ H ↔ (x : G') ∈ H.map e.toMonoidHom
  rw [Subgroup.mem_map_equiv]

theorem isomorphism_transports_original_subgroup_local_cover {G : Type u} {G' : Type v}
    [Group G] [Finite G] [Group G'] (e : G ≃* G') (t : G) (H : Subgroup G)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    ((H.map e.toMonoidHom).subgroupOf (C (e t)) ⊓
      ((CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))).comap (nu (e t))).map
        (nu (e t)) = (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) := by
  let c := originalCentralizerEquiv e t
  let b := originalOddQuotientEquiv e t
  have hcomm : b.toMonoidHom.comp (nu t) = (nu (e t)).comp c.toMonoidHom := by
    ext x
    exact originalOddQuotientEquiv_nu e t x
  obtain ⟨hT, hY⟩ := original_local_layer_preimages_transport e t
  have h := congrArg (Subgroup.map b.toMonoidHom) hcover
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, Subgroup.map_inf _ _ _ c.injective,
    isomorphism_maps_original_subgroup_in_centralizer, hY, hT] at h
  exact h

theorem isomorphism_transports_original_core_intersection {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G) (H : Subgroup G) :
    ((CFSG.pPrimeCore 2 H).map H.subtype) ⊓ C t = ((N t).map (C t).subtype) ⊓ H ↔
      ((CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype) ⊓ C (e t) =
        ((N (e t)).map (C (e t)).subtype) ⊓ H.map e.toMonoidHom := by
  have hN : ((N t).map (C t).subtype).map e.toMonoidHom =
      (N (e t)).map (C (e t)).subtype := by
    exact isomorphism_maps_original_subgroup_odd_core e (C t) |>.trans (by
      rw [isomorphism_maps_original_element_centralizer])
  have hC : (C t).map e.toMonoidHom = C (e t) :=
    isomorphism_maps_original_element_centralizer e t
  rw [← isomorphism_maps_original_subgroup_odd_core e H, ← hN,
    ← hC,
    ← Subgroup.map_inf _ _ _ e.injective, ← Subgroup.map_inf _ _ _ e.injective]
  exact ⟨congrArg (Subgroup.map e.toMonoidHom),
    fun h => Subgroup.map_injective (f := e.toMonoidHom) e.injective h⟩

theorem original_core_centralizer_factorization_iff {G : Type u} [Group G]
    (H : Subgroup G) (t : G) (htH : t ∈ H) :
    CFSG.pPrimeCore 2 H ⊔
      Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤ ↔
      (CFSG.pPrimeCore 2 H).map H.subtype ⊔ (H ⊓ C t) = H := by
  have hC : (Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H)).map H.subtype =
      H ⊓ C t := subgroup_centralizer_map H ⟨t, htH⟩
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmap : (CFSG.pPrimeCore 2 H ⊔
      Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H)).map H.subtype =
      (CFSG.pPrimeCore 2 H).map H.subtype ⊔ (H ⊓ C t) := by
    rw [Subgroup.map_sup, hC]
  constructor
  · intro h
    exact hmap.symm.trans ((congrArg (Subgroup.map H.subtype) h).trans htop)
  · intro h
    exact Subgroup.map_injective H.subtype_injective (hmap.trans (h.trans htop.symm))

theorem isomorphism_transports_original_core_centralizer_factorization
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (e : G ≃* G') (t : G) (H : Subgroup G) :
    (CFSG.pPrimeCore 2 H).map H.subtype ⊔ (H ⊓ C t) = H ↔
      (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype ⊔
        (H.map e.toMonoidHom ⊓ C (e t)) = H.map e.toMonoidHom := by
  have hC : (C t).map e.toMonoidHom = C (e t) :=
    isomorphism_maps_original_element_centralizer e t
  rw [← isomorphism_maps_original_subgroup_odd_core e H, ← hC,
    ← Subgroup.map_inf _ _ _ e.injective, ← Subgroup.map_sup]
  exact ⟨congrArg (Subgroup.map e.toMonoidHom),
    fun h => Subgroup.map_injective (f := e.toMonoidHom) e.injective h⟩

theorem isomorphism_transports_original_intrinsic_core_centralizer_factorization
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (e : G ≃* G') (t : G) (H : Subgroup G) (htH : t ∈ H) :
    CFSG.pPrimeCore 2 H ⊔
      Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤ ↔
      CFSG.pPrimeCore 2 (H.map e.toMonoidHom) ⊔ Subgroup.centralizer
        ({(⟨e t, Subgroup.mem_map_of_mem e.toMonoidHom htH⟩ :
          H.map e.toMonoidHom)} : Set (H.map e.toMonoidHom)) = ⊤ := by
  exact (original_core_centralizer_factorization_iff H t htH).trans
    ((isomorphism_transports_original_core_centralizer_factorization e t H).trans
      (original_core_centralizer_factorization_iff (H.map e.toMonoidHom) (e t)
        (Subgroup.mem_map_of_mem e.toMonoidHom htH)).symm)

theorem original_simple_involution_odd_core_eq_bot {G : Type u} [Group G] [Finite G]
    [IsSimpleGroup G] (t : G) (ht : orderOf t = 2) : CFSG.pPrimeCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 2 G) with h | h
  · exact h
  · have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    have htcore : t ∈ CFSG.pPrimeCore 2 G := h ▸ Subgroup.mem_top t
    have hdiv := (CFSG.pPrimeCore 2 G).orderOf_dvd_natCard htcore
    rw [ht] at hdiv
    exact False.elim (Nat.prime_two.coprime_iff_not_dvd.mp hcop hdiv)

theorem original_nontrivial_odd_core_subgroup_is_proper {G : Type u}
    [Group G] [Finite G] [IsSimpleGroup G] (t : G) (ht : orderOf t = 2)
    (H : Subgroup G) (hR : CFSG.pPrimeCore 2 H ≠ ⊥) : H < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro hH
  rw [hH] at hR
  have hmap : (CFSG.pPrimeCore 2 (⊤ : Subgroup G)).map
      Subgroup.topEquiv.toMonoidHom = ⊥ :=
    (CFSG.pPrimeCore_map_iso 2 Subgroup.topEquiv).trans
      (original_simple_involution_odd_core_eq_bot t ht)
  have hbot : CFSG.pPrimeCore 2 (⊤ : Subgroup G) = ⊥ :=
    Subgroup.map_injective Subgroup.topEquiv.injective
      (hmap.trans (Subgroup.map_bot Subgroup.topEquiv.toMonoidHom).symm)
  exact hR hbot

theorem original_layer_containing_subgroup_cover_inputs {G : Type u}
    [Group G] [Finite G] [IsSimpleGroup G] (t s : G) (ht : orderOf t = 2)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) (J : Subgroup (C t))
    (hJH : J.map (C t).subtype ≤ H)
    (hJimage : J.map (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    t ∈ H ∧ s ∈ H ∧ H < ⊤ ∧ Odd (Nat.card (CFSG.pPrimeCore 2 H)) ∧
      J ≤ H.subgroupOf (C t) ⊓ Y ∧ (H.subgroupOf (C t) ⊓ Y).map (nu t) = T₀ := by
  intro T₀ Y
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsV : s ∈ Subgroup.closure ({t, s} : Set G) :=
    Subgroup.mem_closure_of_mem (Set.mem_insert_of_mem t (Set.mem_singleton s))
  have hJY : J ≤ Y := by
    intro j hj
    change nu t j ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    rw [← hJimage]
    exact Subgroup.mem_map_of_mem (nu t) hj
  have hJHC : J ≤ H.subgroupOf (C t) := by
    intro j hj
    exact hJH (Subgroup.mem_map_of_mem (C t).subtype hj)
  exact ⟨hVH (first_generator_mem_original_fourgroup t s), hVH hsV,
    original_nontrivial_odd_core_subgroup_is_proper t ht H hR,
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H)),
    le_inf hJHC hJY,
    containing_layer_covers_original_preimage (C t) H (nu t) T₀ J hJH hJimage⟩

theorem isomorphism_maps_original_fourgroup {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t s : G) :
    (Subgroup.closure ({t, s} : Set G)).map e.toMonoidHom =
      Subgroup.closure ({e t, e s} : Set G') := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem isomorphism_maps_original_normalizer_and_centralizer
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (e : G ≃* G') (t : G) (H W : Subgroup G) :
    let A := H ⊓ Subgroup.normalizer (W : Set G)
    let A' := H.map e.toMonoidHom ⊓
      Subgroup.normalizer (W.map e.toMonoidHom : Set G')
    A.map e.toMonoidHom = A' ∧ (A ⊓ C t).map e.toMonoidHom = A' ⊓ C (e t) := by
  intro A A'
  have hA : A.map e.toMonoidHom = A' := by
    rw [Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq]
  exact ⟨hA, by rw [Subgroup.map_inf _ _ _ e.injective, hA,
    isomorphism_maps_original_element_centralizer]⟩

theorem isomorphism_transports_original_fourgroup_invariance
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (e : G ≃* G') (t s : G) (W : Subgroup G) :
    Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (W : Set G) ↔
      Subgroup.closure ({e t, e s} : Set G') ≤
        Subgroup.normalizer (W.map e.toMonoidHom : Set G') := by
  rw [← isomorphism_maps_original_fourgroup e t s,
    ← Subgroup.map_equiv_normalizer_eq W e]
  constructor
  · exact Subgroup.map_mono
  · intro h x hx
    have hmem := h (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    rw [Subgroup.mem_map_equiv] at hmem
    change e.symm (e x) ∈ Subgroup.normalizer (W : Set G) at hmem
    simpa only [MulEquiv.symm_apply_apply] using hmem

theorem isomorphism_transports_original_odd_core_sylow
    {G : Type u} {G' : Type v} [Group G] [Finite G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Sylow ℓ (CFSG.pPrimeCore 2 H)) :
    ∃ W' : Sylow ℓ (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)),
      (W' : Subgroup (CFSG.pPrimeCore 2 (H.map e.toMonoidHom))).map
        ((H.map e.toMonoidHom).subtype.comp
          (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).subtype) =
        ((W : Subgroup (CFSG.pPrimeCore 2 H)).map
          (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)).map e.toMonoidHom := by
  let a := H.equivMapOfInjective e.toMonoidHom e.injective
  let b : CFSG.pPrimeCore 2 H ≃* CFSG.pPrimeCore 2 (H.map e.toMonoidHom) :=
    ((CFSG.pPrimeCore 2 H).equivMapOfInjective a.toMonoidHom a.injective).trans
      (MulEquiv.subgroupCongr (CFSG.pPrimeCore_map_iso 2 a))
  let W' : Sylow ℓ (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)) :=
    W.mapSurjective (f := b.toMonoidHom) b.surjective
  refine ⟨W', ?_⟩
  have hW : (W' : Subgroup (CFSG.pPrimeCore 2 (H.map e.toMonoidHom))) =
      (W : Subgroup (CFSG.pPrimeCore 2 H)).map b.toMonoidHom :=
    Sylow.coe_mapSurjective (f := b.toMonoidHom) b.surjective W
  rw [hW, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem odd_subgroup_normalized_by_simple_layer_eq_bot {Q : Type u}
    [Group Q] (L U : Subgroup Q) [L.Normal] [IsSimpleGroup L]
    (heven : Even (Nat.card L))
    (hcentral : Subgroup.centralizer (L : Set Q) = ⊥)
    (hUodd : Odd (Nat.card U)) (hLU : L ≤ Subgroup.normalizer (U : Set Q)) : U = ⊥ := by
  have hUL : ∀ l ∈ L, ∀ x ∈ U, l * x * l⁻¹ ∈ U :=
    Subgroup.le_normalizer_iff.mp hLU
  have hinf : U ⊓ L = ⊥ := by
    have hnormal : ((U ⊓ L).subgroupOf L).Normal := by
      constructor
      intro x hx l
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hUL l l.property x hx.1,
        L.mul_mem (L.mul_mem l.property hx.2) (L.inv_mem l.property)⟩
    let := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((U ⊓ L).subgroupOf L) with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    · have hle : L ≤ U := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
      exact False.elim ((Nat.not_even_iff_odd.mpr
        (hUodd.of_dvd_nat (Subgroup.card_dvd_of_le hle))) heven)
  have hUC : U ≤ Subgroup.centralizer (L : Set Q) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    have hU : l * x * l⁻¹ * x⁻¹ ∈ U := U.mul_mem (hUL l hl x hx) (U.inv_mem hx)
    have hL : l * x * l⁻¹ * x⁻¹ ∈ L := by
      have h := L.mul_mem hl ((inferInstance : L.Normal).conj_mem _ (L.inv_mem hl) x)
      simpa only [mul_assoc] using h
    have hone : l * x * l⁻¹ * x⁻¹ = 1 := by
      have hmem : l * x * l⁻¹ * x⁻¹ ∈ U ⊓ L := ⟨hU, hL⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    calc
      l * x = (l * x * l⁻¹ * x⁻¹) * (x * l) := by group
      _ = x * l := by rw [hone, one_mul]
  rw [hcentral] at hUC
  exact le_bot_iff.mp hUC

theorem odd_normal_subgroup_of_layer_cover_maps_to_bot {A : Type u} {Q : Type v}
    [Group A] [Group Q] (f : A →* Q) (B : Subgroup A)
    (U : Subgroup B) [U.Normal] (hUodd : Odd (Nat.card U))
    (L : Subgroup Q) [L.Normal] [IsSimpleGroup L] (heven : Even (Nat.card L))
    (hcentral : Subgroup.centralizer (L : Set Q) = ⊥) (hLB : L ≤ B.map f) :
    U.map (f.comp B.subtype) = ⊥ := by
  apply odd_subgroup_normalized_by_simple_layer_eq_bot L _ heven hcentral
    (hUodd.of_dvd_nat (Subgroup.card_map_dvd _ _))
  apply Subgroup.le_normalizer_iff.mpr
  intro l hl x hx
  obtain ⟨b, hb, rfl⟩ := hLB hl
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨(⟨b, hb⟩ : B) * a * (⟨b, hb⟩ : B)⁻¹,
    (inferInstance : U.Normal).conj_mem a ha ⟨b, hb⟩, ?_⟩
  simp only [MonoidHom.comp_apply, map_mul, map_inv]
  rfl

theorem odd_element_in_kernel_join_involution {A : Type u} [Group A]
    (N : Subgroup A) [N.Normal] (t x : A) (ht : orderOf t = 2)
    (hxodd : Odd (orderOf x)) (hx : x ∈ N ⊔ Subgroup.zpowers t) : x ∈ N := by
  let pi := QuotientGroup.mk' N
  obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht,
      pow_orderOf_eq_one, one_zpow]
  have hpi2 : pi x ^ 2 = 1 := by
    have haone : pi a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [← haz, map_mul, haone, one_mul, ← map_pow, hz2, map_one]
  have hpix : pi x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hord : orderOf (pi x) = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpi2)
      (orderOf_dvd_of_pow_eq_one hpix)
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hxodd), Nat.dvd_one] at h
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hord)

theorem original_layer_cover_odd_core_eq_intersection {A : Type u} [Group A] [Finite A]
    (t : A) (ht : orderOf t = 2) [(Subgroup.zpowers t).Normal]
    [IsSimpleGroup (CFSG.generalizedFitting (A ⧸
      (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t)))]
    (heven : Even (Nat.card (CFSG.generalizedFitting (A ⧸
      (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t)))))
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (A ⧸ (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t)) :
        Set (A ⧸ (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t))) = ⊥)
    (B : Subgroup A)
    (hLB : CFSG.generalizedFitting (A ⧸ (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t)) ≤
      B.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 A ⊔ Subgroup.zpowers t))) :
    (CFSG.pPrimeCore 2 B).map B.subtype = B ⊓ CFSG.pPrimeCore 2 A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := CFSG.pPrimeCore 2 A
  let pi := QuotientGroup.mk' (N ⊔ Subgroup.zpowers t)
  let L := CFSG.generalizedFitting (A ⧸ (N ⊔ Subgroup.zpowers t))
  let R := CFSG.pPrimeCore 2 B
  have hRodd : Odd (Nat.card R) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := B))
  have hLn : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic
    (G := A ⧸ (N ⊔ Subgroup.zpowers t))).2
  let := hLn
  have hRimage : R.map (pi.comp B.subtype) = ⊥ :=
    odd_normal_subgroup_of_layer_cover_maps_to_bot pi B R hRodd L heven hcentral hLB
  have hNB : N.subgroupOf B ≤ R := by
    have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf B)) := by
      rw [← Subgroup.card_subtype B, Subgroup.subgroupOf_map_subtype]
      exact (CFSG.pPrimeCore_coprime_card (p := 2) (G := A)).coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
    exact le_sSup ⟨inferInstance, hcop⟩
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    have hpi : pi (r : A) = 1 := by
      have hmem := Subgroup.mem_map_of_mem (pi.comp B.subtype) hr
      rw [hRimage, Subgroup.mem_bot] at hmem
      exact hmem
    have hrNZ : (r : A) ∈ N ⊔ Subgroup.zpowers t :=
      (QuotientGroup.eq_one_iff (r : A)).mp hpi
    have hrodd : Odd (orderOf (r : A)) := by
      rw [Subgroup.orderOf_coe]
      exact hRodd.of_dvd_nat (R.orderOf_dvd_natCard hr)
    exact ⟨r.property, odd_element_in_kernel_join_involution N t r ht hrodd hrNZ⟩
  · rintro x ⟨hxB, hxN⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hxB⟩, hNB hxN, rfl⟩

theorem odd_core_of_supplement_to_whole_odd_core {A : Type u} [Group A] [Finite A]
    (B : Subgroup A) (hfactor : CFSG.pPrimeCore 2 A ⊔ B = ⊤) :
    (CFSG.pPrimeCore 2 B).map B.subtype = B ⊓ CFSG.pPrimeCore 2 A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := CFSG.pPrimeCore 2 A
  let pi := QuotientGroup.mk' R
  let f := pi.comp B.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hx : x ∈ R ⊔ B := hfactor ▸ Subgroup.mem_top x
    obtain ⟨r, hr, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    have hrone : pi r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    change pi b = pi (r * b)
    rw [map_mul, hrone, one_mul]
  have hker : f.ker = R.subgroupOf B := by
    ext b
    change pi (b : A) = 1 ↔ (b : A) ∈ R
    exact QuotientGroup.eq_one_iff _
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hker, ← Subgroup.card_subtype B, Subgroup.subgroupOf_map_subtype]
    exact (CFSG.pPrimeCore_coprime_card (p := 2) (G := A)).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hmap : (CFSG.pPrimeCore 2 B).map f = ⊥ :=
    (pPrimeCore_map_eq_of_coprime_ker 2 f hf hcop).trans
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hle : CFSG.pPrimeCore 2 B ≤ f.ker := by
    intro b hb
    have h := Subgroup.mem_map_of_mem f hb
    rw [hmap, Subgroup.mem_bot] at h
    exact h
  have hge : f.ker ≤ CFSG.pPrimeCore 2 B := le_sSup ⟨inferInstance, hcop⟩
  have hcore : CFSG.pPrimeCore 2 B = R.subgroupOf B := (le_antisymm hle hge).trans hker
  rw [hcore, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem subtype_maps_original_subgroup_odd_core {G : Type u} [Group G]
    (A : Subgroup G) (B : Subgroup A) :
    ((CFSG.pPrimeCore 2 B).map B.subtype).map A.subtype =
      (CFSG.pPrimeCore 2 (B.map A.subtype)).map (B.map A.subtype).subtype := by
  let e := B.equivMapOfInjective A.subtype Subtype.coe_injective
  have h := congrArg (Subgroup.map (B.map A.subtype).subtype) (CFSG.pPrimeCore_map_iso 2 e)
  rw [Subgroup.map_map] at h ⊢
  exact h

theorem original_layer_cover_factorization_gives_exact_core_intersection {G : Type u}
    [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (H : Subgroup G) (htH : t ∈ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hfactor : CFSG.pPrimeCore 2 H ⊔
      Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) = ⊤) :
    ((CFSG.pPrimeCore 2 H).map H.subtype) ⊓ C t = ((N t).map (C t).subtype) ⊓ H := by
  let L := CFSG.generalizedFitting (Gamma t)
  let B := H.subgroupOf (C t)
  let D := Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H)
  have hLeven : Even (Nat.card L) := by
    obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 L))
    have hU1 : Nat.card (U : Subgroup L) ≠ 1 := by
      intro h1
      apply hnc U
      rw [Subgroup.card_eq_one] at h1
      rw [h1]
      exact isCyclic_of_subsingleton
    obtain ⟨k, hk⟩ := U.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU1 (by rw [hk, pow_zero])
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans
      (hk ▸ Subgroup.card_subgroup_dvd_card (U : Subgroup L)))
  have hLB : L ≤ B.map (kappa t) := by
    intro l hl
    obtain ⟨q, hq⟩ := barKappa_surjective t l
    have hqT : q ∈ L.comap (barKappa t) := by
      change barKappa t q ∈ L
      rw [hq]
      exact hl
    rw [← hcover] at hqT
    obtain ⟨c, hc, hcq⟩ := hqT
    refine ⟨c, hc.1, ?_⟩
    change barKappa t (nu t c) = l
    rw [hcq, hq]
  have htC : orderOf (tInC t) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hBcore := original_layer_cover_odd_core_eq_intersection
    (tInC t) htC hLeven hcentral B hLB
  have hBambient : (CFSG.pPrimeCore 2 (H ⊓ C t : Subgroup G)).map (H ⊓ C t).subtype =
      H ⊓ (N t).map (C t).subtype := by
    have h := congrArg (Subgroup.map (C t).subtype) hBcore
    rw [subtype_maps_original_subgroup_odd_core, Subgroup.map_inf _ _ _ Subtype.coe_injective,
      Subgroup.subgroupOf_map_subtype] at h
    have hNC : (N t).map (C t).subtype ≤ C t := Subgroup.map_subtype_le _
    simpa only [inf_assoc, inf_eq_right.mpr hNC] using h
  have hDcore := odd_core_of_supplement_to_whole_odd_core D hfactor
  have hDambient : (CFSG.pPrimeCore 2 (H ⊓ C t : Subgroup G)).map (H ⊓ C t).subtype =
      (H ⊓ C t) ⊓ (CFSG.pPrimeCore 2 H).map H.subtype := by
    have h := congrArg (Subgroup.map H.subtype) hDcore
    rw [subtype_maps_original_subgroup_odd_core, Subgroup.map_inf _ _ _ Subtype.coe_injective,
      subgroup_centralizer_map] at h
    exact h
  have hRH : (CFSG.pPrimeCore 2 H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  calc
    (CFSG.pPrimeCore 2 H).map H.subtype ⊓ C t =
        (H ⊓ (CFSG.pPrimeCore 2 H).map H.subtype) ⊓ C t := by
      rw [inf_eq_right.mpr hRH]
    _ = (H ⊓ C t) ⊓ (CFSG.pPrimeCore 2 H).map H.subtype := by
      rw [inf_assoc, inf_comm ((CFSG.pPrimeCore 2 H).map H.subtype), ← inf_assoc]
    _ = (CFSG.pPrimeCore 2 (H ⊓ C t : Subgroup G)).map (H ⊓ C t).subtype := hDambient.symm
    _ = H ⊓ (N t).map (C t).subtype := hBambient
    _ = (N t).map (C t).subtype ⊓ H := inf_comm _ _



theorem original_layer_normalization_from_core_centralizer_factorization {G : Type u}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (s : G) (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH :
      let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      let Y := T₀.comap (nu t)
      let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
      ((CFSG.perfectResidual H₀).map H₀.subtype).map (C t).subtype ≤ H)
    (hfactor : (CFSG.pPrimeCore 2 H) ⊔ Subgroup.centralizer
      ({(⟨t, hVH (first_generator_mem_original_fourgroup t s)⟩ : H)} : Set H) = ⊤)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Sylow ℓ (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((W : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) : Set G)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
    let Wa := (W : Subgroup (CFSG.pPrimeCore 2 H)).map
      (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C t
    let X := B.subgroupOf (C t) ⊓ Y
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      (∀ U : Subgroup (C t), U ≤ Y → U.map (nu t) = T₀ →
        J ≤ U ∧ (CFSG.perfectResidual U).map U.subtype = J) ∧
      H = Ra ⊔ B ∧ H ⊓ C t = (Ra ⊓ C t) ⊔ B ∧
      Ra ⊓ C t = (N t).map (C t).subtype ⊓ H ∧
      X.map (nu t) = T₀ ∧ J ≤ X ∧ J.map (C t).subtype ≤ B ∧
      J.map (C t).subtype ≤ A ∧
      ((nu t).comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) ∧
      (H : Set G) = (Ra : Set G) * (B : Set G) ∧
      ((H ⊓ C t : Subgroup G) : Set G) = ((Ra ⊓ C t : Subgroup G) : Set G) * (B : Set G) ∧
      (∀ x ∈ H, ∃ r ∈ Ra, ∃ b ∈ B, r * b = x) ∧
      (∀ x ∈ H ⊓ C t, ∃ r ∈ Ra ⊓ C t, ∃ b ∈ B, r * b = x) := by
  let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  let Y := T₀.comap (nu t)
  let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
  let J := (CFSG.perfectResidual H₀).map H₀.subtype
  obtain ⟨-, -, -, hJimage, -, -, -, -, -⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  have hHcover : (H.subgroupOf (C t) ⊓ Y).map (nu t) = T₀ :=
    containing_layer_covers_original_preimage (C t) H (nu t) T₀ J hJH hJimage
  have hinter := original_layer_cover_factorization_gives_exact_core_intersection
    t ht hnc hcentral H (hVH (first_generator_mem_original_fourgroup t s)) hHcover hfactor
  exact original_layer_normalization_of_cover_factorization
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
    s H hVH hJH hfactor hinter ℓ W hVW


theorem covering_subgroup_central_product_of_same_layer {G : Type u} {Q : Type v}
    [Group G] [Finite G] [Group Q] (f : G →* Q) (Y J N : Subgroup G) [J.Normal]
    (hJ : Group.IsPerfect J) (hN : Group.IsSolvable N) (hY : Y = J ⊔ N)
    (hker : f.ker = N) (hJN : ⁅J, N⁆ = ⊥) (X : Subgroup G) (hXY : X ≤ Y)
    (himage : X.map f = J.map f) :
    let K := X ⊓ N
    J ≤ X ∧ (CFSG.perfectResidual X).map X.subtype = J ∧
      X = J ⊔ K ∧ ⁅J, K⁆ = ⊥ ∧
      (X : Set G) = (J : Set G) * (K : Set G) ∧
      (∀ x ∈ X, ∃ j ∈ J, ∃ k ∈ K, j * k = x) ∧
      (f.comp X.subtype).ker = N.subgroupOf X ∧ J ⊓ K = J ⊓ N := by
  intro K
  obtain ⟨hJX, hres⟩ := every_cover_contains_same_perfect_layer f Y J N hJ hN hY
    hker hJN X hXY himage
  have hXjoin : X = J ⊔ K := by
    apply le_antisymm
    · intro x hx
      have hy : x ∈ J ⊔ N := hY ▸ hXY hx
      obtain ⟨j, hj, k, hk, hjk⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      have hkX : k ∈ X := by
        have hmem := X.mul_mem (X.inv_mem (hJX hj)) hx
        rwa [← hjk, inv_mul_cancel_left] at hmem
      exact Subgroup.mem_sup_of_normal_left.mpr ⟨j, hj, k, ⟨hkX, hk⟩, hjk⟩
    · exact sup_le hJX inf_le_left
  have hcomm : ⁅J, K⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono_right (show K ≤ N from inf_le_right)).trans hJN.le
    · exact bot_le
  have hprod : (X : Set G) = (J : Set G) * (K : Set G) := by
    ext x
    change x ∈ X ↔ ∃ j ∈ J, ∃ k ∈ K, j * k = x
    rw [hXjoin]
    exact Subgroup.mem_sup_of_normal_left
  have hkernel : (f.comp X.subtype).ker = N.subgroupOf X := by
    ext x
    change f (x : G) = 1 ↔ (x : G) ∈ N
    rw [← hker, MonoidHom.mem_ker]
  have hoverlap : J ⊓ K = J ⊓ N := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hJX h.1, h.2⟩⟩
  refine ⟨hJX, hres, hXjoin, hcomm, hprod, ?_, hkernel, hoverlap⟩
  intro x hx
  exact Set.mem_mul.mp (hprod ▸ hx)


theorem original_all_covers_are_same_layer_central_products {G : Type u}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      ∀ X : Subgroup (C t), X ≤ Y → X.map (nu t) = T₀ →
        let K := X ⊓ N t
        J ≤ X ∧ (CFSG.perfectResidual X).map X.subtype = J ∧
          X = J ⊔ K ∧ ⁅J, K⁆ = ⊥ ∧
          (X : Set (C t)) = (J : Set (C t)) * (K : Set (C t)) ∧
          (∀ x ∈ X, ∃ j ∈ J, ∃ k ∈ K, j * k = x) ∧
          ((nu t).comp X.subtype).ker = (N t).subgroupOf X ∧ J ⊓ K = J ⊓ N t ∧
          (CFSG.pPrimeCore 2 X).map X.subtype = K ∧ Odd (Nat.card K) := by
  intro T₀ Y H₀ J
  obtain ⟨hJperfect, hJnormal, -, hJimage, hJN, hY, -⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  let := hJnormal
  have hN : Group.IsSolvable (N t) := CFSG.FeitThompson.isSolvable_of_odd_natCard _
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t)))
  refine ⟨(perfect_residual_of_perfect_solvable_product Y J (N t) hJperfect hN hY).symm, ?_⟩
  intro X hXY hXimage
  obtain ⟨hJX, hres, hgen, hcomm, hprod, hwitness, hker, hoverlap⟩ :=
    covering_subgroup_central_product_of_same_layer (nu t) Y J (N t) hJperfect hN hY
      (QuotientGroup.ker_mk' _) hJN X hXY (hXimage.trans hJimage.symm)
  have hLX : CFSG.generalizedFitting (Gamma t) ≤ X.map (kappa t) := by
    intro l hl
    obtain ⟨q, hq⟩ := barKappa_surjective t l
    have hqT : q ∈ T₀ := by
      change barKappa t q ∈ CFSG.generalizedFitting (Gamma t)
      rw [hq]
      exact hl
    rw [← hXimage] at hqT
    obtain ⟨c, hc, hcq⟩ := hqT
    refine ⟨c, hc, ?_⟩
    change barKappa t (nu t c) = l
    rw [hcq, hq]
  have hLeven : Even (Nat.card (CFSG.generalizedFitting (Gamma t))) := by
    obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 (CFSG.generalizedFitting (Gamma t))))
    have hU1 : Nat.card (U : Subgroup (CFSG.generalizedFitting (Gamma t))) ≠ 1 := by
      intro h1
      apply hnc U
      rw [Subgroup.card_eq_one] at h1
      rw [h1]
      exact isCyclic_of_subsingleton
    obtain ⟨k, hk⟩ := U.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU1 (by rw [hk, pow_zero])
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans
      (hk ▸ Subgroup.card_subgroup_dvd_card (U : Subgroup (CFSG.generalizedFitting (Gamma t)))))
  have htC : orderOf (tInC t) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hcore := original_layer_cover_odd_core_eq_intersection (tInC t) htC hLeven hcentral X hLX
  have hKodd : Odd (Nat.card (X ⊓ N t : Subgroup (C t))) :=
    (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))).of_dvd_nat
      (Subgroup.card_dvd_of_le (show X ⊓ N t ≤ N t from inf_le_right))
  exact ⟨hJX, hres, hgen, hcomm, hprod, hwitness, hker, hoverlap, hcore, hKodd⟩


@[expose] def OriginalSmallerSimpleRecognition (G : Type u) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] [IsSimpleGroup A],
    (∃ a b : A, a * b ≠ b * a) → Nat.card A < Nat.card G →
    ∀ (k : ℕ), 4 ≤ k → ∀ (S : Sylow 2 A),
      Nonempty (SemidihedralGroup k ≃* S) →
        CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleModel A

theorem original_smaller_simple_recognition_transport {G : Type u} {G' : Type}
    (e : G ≃ G') (hrecognition : OriginalSmallerSimpleRecognition G) :
    CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G' := by
  intro A _ _ _ hnonab hcard k hk S hS
  apply hrecognition A hnonab _ k hk S hS
  rw [Nat.card_congr e]
  exact hcard

theorem original_smaller_simple_recognition_finite_representative {G : Type u}
    [Group G] [Finite G] (hrecognition : OriginalSmallerSimpleRecognition G) :
    ∃ (G' : Type) (_ : Group G') (_ : Fintype G'),
      Nonempty (G ≃* G') ∧
        CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G' := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  exact ⟨G', hgroup, hfinite, ⟨e⟩,
    original_smaller_simple_recognition_transport e.toEquiv hrecognition⟩


theorem original_layer_cover_full_inputs_transport {G : Type u} {G' : Type}
    [Group G] [Finite G] [IsSimpleGroup G] [Group G']
    (e : G ≃* G') (hrecognition : OriginalSmallerSimpleRecognition G)
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hts : Commute t s) (hst : s ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let L' := CFSG.generalizedFitting (Gamma (e t))
    let H' := H.map e.toMonoidHom
    IsSimpleGroup G' ∧ (∃ a b : G', a * b ≠ b * a) ∧
      CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G' ∧
      (∀ U : Subgroup G', U.index ≠ 2) ∧
      (∃ (S0' : Sylow 2 G') (f0' : SemidihedralGroup n ≃* S0'),
        ∀ x : SemidihedralGroup n, (f0' x : G') = e (f0 x : G)) ∧
      orderOf (e t) = 2 ∧ orderOf (e s) = 2 ∧ Commute (e t) (e s) ∧ e s ≠ e t ∧
      IsSimpleGroup L' ∧ (∃ a b : L', a * b ≠ b * a) ∧
      Subgroup.centralizer (L' : Set (Gamma (e t))) = ⊥ ∧
      (∀ U : Sylow 2 L', ¬ IsCyclic U) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel L' .PSL 2 p f ∧
      Subgroup.closure ({e t, e s} : Set G') ≤ H' ∧ CFSG.pPrimeCore 2 H' ≠ ⊥ ∧
      (H'.subgroupOf (C (e t)) ⊓
        ((CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t))).comap (nu (e t))).map
          (nu (e t)) = (CFSG.generalizedFitting (Gamma (e t))).comap (barKappa (e t)) := by
  intro L' H'
  let d := originalGeneralizedFittingEquiv e t
  have hsimple : IsSimpleGroup G' := e.symm.isSimpleGroup
  let := hsimple
  have hGnonab' : ∃ a b : G', a * b ≠ b * a :=
    isomorphism_transports_nonabelian e hGnonab
  have hlocal : IsSimpleGroup L' := d.symm.isSimpleGroup
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  have hcentral' : Subgroup.centralizer (L' : Set (Gamma (e t))) = ⊥ := by
    have h := congrArg (Subgroup.map (originalReducedQuotientEquiv e t).toMonoidHom) hcentral
    rw [isomorphism_maps_actual_centralizer, isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  have hVH' : Subgroup.closure ({e t, e s} : Set G') ≤ H' := by
    rw [← isomorphism_maps_original_fourgroup e t s]
    exact Subgroup.map_mono hVH
  have hR' : CFSG.pPrimeCore 2 H' ≠ ⊥ := by
    let a := H.equivMapOfInjective e.toMonoidHom e.injective
    intro hbot
    have h : (CFSG.pPrimeCore 2 H).map a.toMonoidHom = ⊥ :=
      (CFSG.pPrimeCore_map_iso 2 a).trans hbot
    exact hR (Subgroup.map_injective a.injective (h.trans (Subgroup.map_bot _).symm))
  refine ⟨hsimple, hGnonab', original_smaller_simple_recognition_transport e.toEquiv hrecognition,
    nonabelian_simple_has_no_subgroup_index_two hGnonab', ⟨S0', f0', fun _ => rfl⟩,
    (e.orderOf_eq t).trans ht, (e.orderOf_eq s).trans hs, hts.map e,
    fun h => hst (e.injective h), hlocal, isomorphism_transports_nonabelian d hnonab,
    hcentral', isomorphism_transports_noncyclic_sylows d 2 hnc,
    original_psl_two_model_transport d p f hmodel, hVH', hR', ?_⟩
  exact isomorphism_transports_original_subgroup_local_cover e t H hcover



section OriginalFullNormalization

open CFSG.Semidihedral.LocalCoverFactorization

theorem original_full_layer_cover_forces_core_centralizer_factorization
    {G : Type u}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hst : s ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    (CFSG.pPrimeCore 2 H).map H.subtype ⊔ (H ⊓ C t) = H ∧
      (CFSG.pPrimeCore 2 H).map H.subtype ⊓ C t = (N t).map (C t).subtype ⊓ H := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩, -⟩ :=
    original_smaller_simple_recognition_finite_representative hrecognition
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  have hts : Commute t s := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  obtain ⟨hGsimple', hGnonab', hIH', -, ⟨S0', f0', -⟩, ht', hs', hts', hst',
    hLsimple', hnonab', hcentral', hnc', hmodel', hVH', hR', hcover'⟩ :=
    original_layer_cover_full_inputs_transport e hrecognition hGnonab n S0 f0 t s ht hs hts hst
      hnonab hcentral hnc p f hmodel H hVH hR hcover
  let := hGsimple'
  let := hLsimple'
  have hsC' : e s ∈ C (e t) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hts'.symm
  have hparent :=
    nontrivial_odd_core_local_layer_cover_forces_quaternion_factorization
      G' hGnonab' hIH' n hn S0' f0' (e t) (e s) ht' hs' hsC' (Ne.symm hst')
        hnonab' hcentral' hnc' p f hp hpodd hf hq hmodel' (H.map e.toMonoidHom)
          hVH' hR' hcover'
  obtain ⟨-, -, -, -, -, -, -, hfactor', hinter'⟩ := hparent.1.1
  have hfactor :
      (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype ⊔
        (H.map e.toMonoidHom ⊓ C (e t)) = H.map e.toMonoidHom := by
    simpa only [CFSG.Wreathed.OriginalSylowNormalizerWitness.ambientOddCore,
      CFSG.Semidihedral.QuaternionFocalFactorization.oddCore_eq_twoPrimeCore] using hfactor'
  have hinter :
      (CFSG.pPrimeCore 2 (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype ⊓
        C (e t) = (N (e t)).map (C (e t)).subtype ⊓ H.map e.toMonoidHom := by
    simpa only [CFSG.Wreathed.OriginalSylowNormalizerWitness.ambientOddCore,
      CFSG.Semidihedral.QuaternionFocalFactorization.oddCore_eq_twoPrimeCore] using hinter'
  exact ⟨(isomorphism_transports_original_core_centralizer_factorization e t H).mpr hfactor,
    (isomorphism_transports_original_core_intersection e t H).mpr hinter⟩

theorem original_full_layer_normalization_for_local_odd_sylow
    {G : Type u}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : OriginalSmallerSimpleRecognition G) (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (s : G) (hsC : s ∈ C t) (hs : orderOf s = 2) (hst : s ≠ t)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH :
      let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
      let Y := T₀.comap (nu t)
      let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
      ((CFSG.perfectResidual H₀).map H₀.subtype).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (ℓ : ℕ) [Fact ℓ.Prime] (hdiv : ℓ ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ℓ (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
      (((W : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) : Set G)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
    let Wa := (W : Subgroup (CFSG.pPrimeCore 2 H)).map
      (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
    let A := H ⊓ Subgroup.normalizer (Wa : Set G)
    let B := A ⊓ C t
    let X := B.subgroupOf (C t) ⊓ Y
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      (∀ U : Subgroup (C t), U ≤ Y → U.map (nu t) = T₀ →
        J ≤ U ∧ (CFSG.perfectResidual U).map U.subtype = J) ∧
      H = Ra ⊔ B ∧ H ⊓ C t = (Ra ⊓ C t) ⊔ B ∧
      Ra ⊓ C t = (N t).map (C t).subtype ⊓ H ∧
      X.map (nu t) = T₀ ∧ J ≤ X ∧ J.map (C t).subtype ≤ B ∧
      J.map (C t).subtype ≤ A ∧ Wa ≠ ⊥ ∧
      ((nu t).comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) ∧
      (H : Set G) = (Ra : Set G) * (B : Set G) ∧
      ((H ⊓ C t : Subgroup G) : Set G) = ((Ra ⊓ C t : Subgroup G) : Set G) * (B : Set G) ∧
      (∀ x ∈ H, ∃ r ∈ Ra, ∃ b ∈ B, r * b = x) ∧
      (∀ x ∈ H ⊓ C t, ∃ r ∈ Ra ⊓ C t, ∃ b ∈ B, r * b = x) := by
  let hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    nonabelian_simple_has_no_subgroup_index_two hGnonab
  let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  let Y := T₀.comap (nu t)
  let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
  let J := (CFSG.perfectResidual H₀).map H₀.subtype
  obtain ⟨-, -, -, hJimage, -, -, -, -, -⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  have hHcover : (H.subgroupOf (C t) ⊓ Y).map (nu t) = T₀ :=
    containing_layer_covers_original_preimage (C t) H (nu t) T₀ J hJH hJimage
  have hfactorAmbient :=
    original_full_layer_cover_forces_core_centralizer_factorization
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hst hnonab hcentral hnc
        p f hp hpodd hf hq hmodel H hVH hR hHcover
  have hfactor : CFSG.pPrimeCore 2 H ⊔ Subgroup.centralizer
      ({(⟨t, hVH (first_generator_mem_original_fourgroup t s)⟩ : H)} : Set H) = ⊤ :=
    (original_core_centralizer_factorization_iff H t
      (hVH (first_generator_mem_original_fourgroup t s))).mpr hfactorAmbient.1
  obtain ⟨hres, hall, hH, hC, hinter, hcover, hJX, hJB, hJA,
    hEker, hEcenter, hEodd, hprod, hCprod, helem, hCelem⟩ :=
    original_layer_normalization_from_core_centralizer_factorization
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
        s H hVH hJH hfactor ℓ W hVW
  have hW : (W : Subgroup (CFSG.pPrimeCore 2 H)).map
      (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype) ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype) :=
      H.subtype_injective.comp (CFSG.pPrimeCore 2 H).subtype_injective
    exact W.ne_bot_of_dvd_card hdiv
      (Subgroup.map_injective hinj (hbot.trans (Subgroup.map_bot _).symm))
  exact ⟨hres, hall, hH, hC, hinter, hcover, hJX, hJB, hJA, hW,
    hEker, hEcenter, hEodd, hprod, hCprod, helem, hCelem⟩

theorem centralizing_perfect_layer_is_contained_in_every_cover_and_normalizes_local_odd_sylows
    {G : Type u}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : OriginalSmallerSimpleRecognition G) (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
          (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    J = (CFSG.perfectResidual Y).map Y.subtype ∧
      (∀ U : Subgroup (C t), U ≤ Y → U.map (nu t) = T₀ →
        J ≤ U ∧ (CFSG.perfectResidual U).map U.subtype = J) ∧
      ((nu t).comp J.subtype).ker = E.subgroupOf J ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ Odd (Nat.card E) ∧
      ∀ (s : G), s ∈ C t → orderOf s = 2 → s ≠ t →
      ∀ (H : Subgroup G), Subgroup.closure ({t, s} : Set G) ≤ H →
        J.map (C t).subtype ≤ H → CFSG.pPrimeCore 2 H ≠ ⊥ →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (CFSG.pPrimeCore 2 H) →
      ∀ W : Sylow ℓ (CFSG.pPrimeCore 2 H),
        Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer
          (((W : Subgroup (CFSG.pPrimeCore 2 H)).map
            (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) : Set G) →
        let Ra := (CFSG.pPrimeCore 2 H).map H.subtype
        let Wa := (W : Subgroup (CFSG.pPrimeCore 2 H)).map
          (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)
        let A := H ⊓ Subgroup.normalizer (Wa : Set G)
        let B := A ⊓ C t
        let X := B.subgroupOf (C t) ⊓ Y
        H = Ra ⊔ B ∧ H ⊓ C t = (Ra ⊓ C t) ⊔ B ∧
          Ra ⊓ C t = (N t).map (C t).subtype ⊓ H ∧
          X.map (nu t) = T₀ ∧ J ≤ X ∧ J.map (C t).subtype ≤ B ∧
          J.map (C t).subtype ≤ A ∧ Wa ≠ ⊥ ∧
          (H : Set G) = (Ra : Set G) * (B : Set G) ∧
          ((H ⊓ C t : Subgroup G) : Set G) =
            ((Ra ⊓ C t : Subgroup G) : Set G) * (B : Set G) ∧
          (∀ x ∈ H, ∃ r ∈ Ra, ∃ b ∈ B, r * b = x) ∧
          (∀ x ∈ H ⊓ C t, ∃ r ∈ Ra ⊓ C t, ∃ b ∈ B, r * b = x) := by
  intro T₀ Y H₀ J E
  let hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    nonabelian_simple_has_no_subgroup_index_two hGnonab
  obtain ⟨hres, hall⟩ := original_all_local_prime_covers_give_residual_and_containment
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨-, -, -, -, -, -, hEker, hEcenter, hEodd⟩ :=
    original_all_local_prime_covers_give_actual_perfect_layer
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  refine ⟨hres, hall, hEker, hEcenter, hEodd, ?_⟩
  intro s hsC hs hst H hVH hJH hR ℓ hℓ hdiv W hVW
  obtain ⟨-, -, hH, hC, hinter, hcover, hJX, hJB, hJA, hW,
    -, -, -, hprod, hCprod, helem, hCelem⟩ :=
    original_full_layer_normalization_for_local_odd_sylow
      hGnonab hrecognition n hn S0 f0 t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
        s hsC hs hst H hVH hJH hR ℓ hdiv W hVW
  exact ⟨hH, hC, hinter, hcover, hJX, hJB, hJA, hW, hprod, hCprod, helem, hCelem⟩

end OriginalFullNormalization

end CFSG.Semidihedral.PerfectLayerNormalization
