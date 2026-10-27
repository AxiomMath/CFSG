module

public import CFSG.LocalAnalysis.GH72.DDCorrect
public import CFSG.LocalAnalysis.GH72.G3bEight
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.LocalAnalysis.GH72.DDLocal
public import CFSG.GroupTheory.DihedralTwoClassFusionSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.GroupTheory.ClosurePairCommute
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open scoped Pointwise

private theorem zmod_two_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

private theorem even_val_iff_castHom_eq_zero {m : ℕ} (hm : 1 ≤ m) (a : ZMod (2 ^ m)) :
    Even a.val ↔ ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) a = 0 := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff_even]

private theorem even_val_of_isConj_sr {m : ℕ} (hm : 1 ≤ m) {i j : ZMod (2 ^ m)}
    (h : IsConj (sr i) (sr j)) : Even i.val ↔ Even j.val := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨k', hk', hpar⟩ :=
    CFSG.GorensteinWalter.TwoClassFusion.exists_conj_sr_eq hm g⁻¹ i
  have hk'g : g * sr i * g⁻¹ = sr k' := by simpa using hk'
  have hkj : k' = j := sr.inj (hk'g.symm.trans hg)
  subst hkj
  exact hpar.symm

private theorem isConj_sr_zero_iff_even {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    IsConj (sr i) (sr 0 : DihedralGroup (2 ^ m)) ↔ Even i.val := by
  constructor
  · intro h
    exact (even_val_of_isConj_sr hm h).mpr (CFSG.GorensteinWalter.TwoClassFusion.even_val_zero)
  · intro hi
    rcases CFSG.GorensteinWalter.TwoClassFusion.isConj_sr_zero_or_one i with h | h
    · exact h
    · exfalso
      exact CFSG.GorensteinWalter.TwoClassFusion.not_even_val_one hm
        ((even_val_of_isConj_sr hm h).mp hi)

private theorem isConj_sr_one_of_not_even {m : ℕ} (hm : 1 ≤ m) {i : ZMod (2 ^ m)}
    (hi : ¬ Even i.val) : IsConj (sr i) (sr 1 : DihedralGroup (2 ^ m)) := by
  rcases CFSG.GorensteinWalter.TwoClassFusion.isConj_sr_zero_or_one i with h | h
  · exact absurd ((isConj_sr_zero_iff_even hm i).mp h) hi
  · exact h

private theorem not_even_val_iff_of_closure_sr_eq_top {m : ℕ} (hm : 2 ≤ m)
    {i j : ZMod (2 ^ m)}
    (htop : Subgroup.closure ({sr i, sr j} : Set (DihedralGroup (2 ^ m))) = ⊤) :
    ¬ (Even i.val ↔ Even j.val) := by
  intro hpar
  have hm1 : 1 ≤ m := by omega
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega : m ≠ 0)
  have hcast_eq : ZMod.castHom h2 (ZMod 2) i = ZMod.castHom h2 (ZMod 2) j := by
    by_cases hi : ZMod.castHom h2 (ZMod 2) i = 0
    · have hei : Even i.val := (even_val_iff_castHom_eq_zero hm1 i).mpr hi
      have hej : Even j.val := hpar.mp hei
      have hj0 : ZMod.castHom h2 (ZMod 2) j = 0 :=
        (even_val_iff_castHom_eq_zero hm1 j).mp hej
      rw [hi, hj0]
    · have hci : ZMod.castHom h2 (ZMod 2) i = 1 := by
        rcases zmod_two_eq_zero_or_one _ with h0 | h1
        · exact absurd h0 hi
        · exact h1
      have hnei : ¬ Even i.val := fun he => hi ((even_val_iff_castHom_eq_zero hm1 i).mp he)
      have hnej : ¬ Even j.val := fun he => hnei (hpar.mpr he)
      have hjc : ZMod.castHom h2 (ZMod 2) j ≠ 0 := fun h0 =>
        hnej ((even_val_iff_castHom_eq_zero hm1 j).mpr h0)
      have hcj : ZMod.castHom h2 (ZMod 2) j = 1 := by
        rcases zmod_two_eq_zero_or_one _ with h0 | h1
        · exact absurd h0 hjc
        · exact h1
      rw [hci, hcj]
  have hcast_d : ZMod.castHom h2 (ZMod 2) (j - i) = 0 := by
    rw [map_sub, hcast_eq]
    exact sub_self _
  have heven : Even (j - i).val := (even_val_iff_castHom_eq_zero hm1 (j - i)).mpr hcast_d
  obtain ⟨t, ht⟩ := heven
  have hji : j - i = (2 : ZMod (2 ^ m)) * (t : ZMod (2 ^ m)) := by
    calc j - i = (((j - i).val : ℕ) : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val (j - i)).symm
      _ = ((t + t : ℕ) : ZMod (2 ^ m)) := by rw [ht]
      _ = (2 : ZMod (2 ^ m)) * (t : ZMod (2 ^ m)) := by push_cast; ring
  have hsri : sr i ∈ CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j := by
    rw [CFSG.GorensteinWalter.mem_dihedralIndexTwoSubgroup_iff hm1 j]
    right
    refine ⟨-(t : ℤ), ?_⟩
    rw [sr.injEq]
    have hsum : j + (2 : ZMod (2 ^ m)) * ((-(t : ℤ) : ℤ) : ZMod (2 ^ m)) =
        j - (2 : ZMod (2 ^ m)) * (t : ZMod (2 ^ m)) := by
      push_cast
      ring
    rw [hsum, ← hji]
    ring
  have hle : Subgroup.closure ({sr i, sr j} : Set (DihedralGroup (2 ^ m))) ≤
      CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hsri
    · change sr j ∈ CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j
      rw [CFSG.GorensteinWalter.mem_dihedralIndexTwoSubgroup_iff hm1 j]
      right
      refine ⟨0, ?_⟩
      push_cast
      ring_nf
  have htop' : CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j = ⊤ := by
    rw [htop] at hle
    exact top_unique hle
  have hidx : (CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j).index = 1 :=
    Subgroup.index_eq_one.mpr htop'
  have h2idx : (CFSG.GorensteinWalter.dihedralIndexTwoSubgroup m j).index = 2 :=
    CFSG.GorensteinWalter.dihedralIndexTwoSubgroup_index_eq_two hm1 j
  omega

private theorem commute_of_mem_closure_pair {G : Type*} [Group G] {a b x y : G}
    (hab : Commute a b) (hx : x ∈ Subgroup.closure ({a, b} : Set G))
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) : Commute x y := by
  obtain ⟨m, n, rfl⟩ := (CFSG.GroupTheory.mem_closure_pair_iff_of_commute hab).mp hx
  obtain ⟨p, q, rfl⟩ := (CFSG.GroupTheory.mem_closure_pair_iff_of_commute hab).mp hy
  have h1 : Commute (a ^ m * b ^ n) (a ^ p) :=
    ((Commute.refl a).zpow_zpow m p).mul_left ((hab.symm).zpow_zpow n p)
  have h2 : Commute (a ^ m * b ^ n) (b ^ q) :=
    (hab.zpow_zpow m q).mul_left ((Commute.refl b).zpow_zpow n q)
  exact h1.mul_right h2

private theorem closure_pair_top_of_subgroup_closure {G : Type*} [Group G] {H : Subgroup G}
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) (hgen : H = Subgroup.closure {a, b}) :
    (⊤ : Subgroup ↥H) = Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥H) := by
  apply Subgroup.map_injective (f := H.subtype) (Subgroup.subtype_injective H)
  rw [Subgroup.map_top, MonoidHom.map_closure, Subgroup.range_subtype]
  have himg : H.subtype '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥H) = ({a, b} : Set G) := by
    rw [Set.image_pair]
    rfl
  rw [himg, hgen]

section MainFusion

variable {G : Type*} [Group G] [Finite G]

@[expose] def ConjIn (C : Subgroup G) (x y : G) : Prop := ∃ c ∈ C, c * x * c⁻¹ = y

private theorem conjIn_trans {C : Subgroup G} {x y z : G}
    (hxy : ConjIn C x y) (hyz : ConjIn C y z) : ConjIn C x z := by
  obtain ⟨c, hc, hcxy⟩ := hxy
  obtain ⟨d, hd, hdyz⟩ := hyz
  refine ⟨d * c, C.mul_mem hd hc, ?_⟩
  calc (d * c) * x * (d * c)⁻¹ = d * (c * x * c⁻¹) * d⁻¹ := by group
    _ = d * y * d⁻¹ := by rw [hcxy]
    _ = z := hdyz

private theorem conjIn_of_isConj_coe {H C : Subgroup G} (hCH : H ≤ C) {x y : H}
    (h : IsConj x y) : ConjIn C (x : G) (y : G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact ⟨g, hCH g.2, congrArg Subtype.val hg⟩

theorem isConj_involutions_of_dihedral_center {H C : Subgroup G} (hH : IsDihNonab H)
    {a b z : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hgen : H = Subgroup.closure {a, b})
    (hz : z ∈ H) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hz_center : H ⊓ Subgroup.centralizer (H : Set G) = Subgroup.zpowers z)
    (hC : H ≤ C)
    (haconj : ConjIn C a z) (hbconj : ConjIn C b z) :
    ∀ x ∈ H, ∀ y ∈ H, orderOf x = 2 → orderOf y = 2 → ConjIn C x y := by
  classical
  obtain ⟨k, hk2, ⟨e⟩⟩ := hH
  have hk1 : 1 ≤ k := by omega
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    obtain ⟨g, -, hg⟩ := haconj
    exact hz1 (by rw [← hg]; group)
  have hb1 : b ≠ 1 := by
    rintro rfl
    obtain ⟨g, -, hg⟩ := hbconj
    exact hz1 (by rw [← hg]; group)
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hAc : e ⟨a, ha⟩ ≠ DihedralGroup.r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
    intro hAc
    have hcenter : ∀ g : DihedralGroup (2 ^ k), g * e ⟨a, ha⟩ = e ⟨a, ha⟩ * g := by
      intro g
      rw [hAc, ← CFSG.CGT.Foote81L6.TStruct.zc_eq_r hk1]
      exact CFSG.CGT.Foote81L6.zc_comm hk1 g
    have hab_comm : Commute a b := by
      have hsub : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        apply e.injective
        rw [map_mul, map_mul]
        exact (hcenter (e ⟨b, hb⟩)).symm
      exact congrArg Subtype.val hsub
    obtain ⟨x, hx, y, hy, hxy⟩ := CFSG.GH72.IsDihNonab.exists_mul_ne_mul ⟨k, hk2, ⟨e⟩⟩
    have hxcl : x ∈ Subgroup.closure ({a, b} : Set G) := by rw [← hgen]; exact hx
    have hycl : y ∈ Subgroup.closure ({a, b} : Set G) := by rw [← hgen]; exact hy
    exact hxy (commute_of_mem_closure_pair hab_comm hxcl hycl).eq
  have hBc : e ⟨b, hb⟩ ≠ DihedralGroup.r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
    intro hBc
    have hcenter : ∀ g : DihedralGroup (2 ^ k), g * e ⟨b, hb⟩ = e ⟨b, hb⟩ * g := by
      intro g
      rw [hBc, ← CFSG.CGT.Foote81L6.TStruct.zc_eq_r hk1]
      exact CFSG.CGT.Foote81L6.zc_comm hk1 g
    have hab_comm : Commute a b := by
      have hsub : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        apply e.injective
        rw [map_mul, map_mul]
        exact hcenter (e ⟨a, ha⟩)
      exact congrArg Subtype.val hsub
    obtain ⟨x, hx, y, hy, hxy⟩ := CFSG.GH72.IsDihNonab.exists_mul_ne_mul ⟨k, hk2, ⟨e⟩⟩
    have hxcl : x ∈ Subgroup.closure ({a, b} : Set G) := by rw [← hgen]; exact hx
    have hycl : y ∈ Subgroup.closure ({a, b} : Set G) := by rw [← hgen]; exact hy
    exact hxy (commute_of_mem_closure_pair hab_comm hxcl hycl).eq
  have hAord : orderOf (e ⟨a, ha⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hao
  have hBord : orderOf (e ⟨b, hb⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hbo
  obtain ⟨i, hAi⟩ : ∃ i : ZMod (2 ^ k), e ⟨a, ha⟩ = sr i := by
    rcases CFSG.GorensteinWalter.TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two
      hk2 hAord with h | ⟨i, hi⟩
    · exact absurd h hAc
    · exact ⟨i, hi⟩
  obtain ⟨j, hBj⟩ : ∃ j : ZMod (2 ^ k), e ⟨b, hb⟩ = sr j := by
    rcases CFSG.GorensteinWalter.TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two
      hk2 hBord with h | ⟨j, hj⟩
    · exact absurd h hBc
    · exact ⟨j, hj⟩
  have hgenH : (⊤ : Subgroup ↥H) = Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥H) :=
    closure_pair_top_of_subgroup_closure ha hb hgen
  have htopD : (⊤ : Subgroup (DihedralGroup (2 ^ k))) =
      Subgroup.closure ({sr i, sr j} : Set (DihedralGroup (2 ^ k))) := by
    have h := congrArg (Subgroup.map e.toMonoidHom) hgenH
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, MonoidHom.map_closure] at h
    rw [show e.toMonoidHom '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥H) =
        ({sr i, sr j} : Set (DihedralGroup (2 ^ k))) by
      rw [Set.image_pair]
      rw [show e.toMonoidHom ⟨a, ha⟩ = sr i from hAi,
        show e.toMonoidHom ⟨b, hb⟩ = sr j from hBj]] at h
    exact h
  have hpar : ¬ (Even i.val ↔ Even j.val) :=
    not_even_val_iff_of_closure_sr_eq_top hk2 htopD.symm
  have hclasses : (IsConj (⟨a, ha⟩ : ↥H) (e.symm.toMonoidHom (sr 0)) ∧
        IsConj (⟨b, hb⟩ : ↥H) (e.symm.toMonoidHom (sr 1))) ∨
      (IsConj (⟨a, ha⟩ : ↥H) (e.symm.toMonoidHom (sr 1)) ∧
        IsConj (⟨b, hb⟩ : ↥H) (e.symm.toMonoidHom (sr 0))) := by
    have hA_u : e.symm.toMonoidHom (sr i) = (⟨a, ha⟩ : ↥H) := by
      rw [← hAi]
      exact e.symm_apply_apply ⟨a, ha⟩
    have hB_u : e.symm.toMonoidHom (sr j) = (⟨b, hb⟩ : ↥H) := by
      rw [← hBj]
      exact e.symm_apply_apply ⟨b, hb⟩
    have hmodel : (IsConj (sr i) (sr 0) ∧ IsConj (sr j) (sr 1)) ∨
        (IsConj (sr i) (sr 1) ∧ IsConj (sr j) (sr 0)) := by
      by_cases hi : Even i.val
      · have hnj : ¬ Even j.val := fun hj => hpar (iff_of_true hi hj)
        exact Or.inl ⟨(isConj_sr_zero_iff_even hk1 i).mpr hi,
          isConj_sr_one_of_not_even hk1 hnj⟩
      · have hj : Even j.val := by
          by_contra hnj
          exact hpar (iff_of_false hi hnj)
        exact Or.inr ⟨isConj_sr_one_of_not_even hk1 hi,
          (isConj_sr_zero_iff_even hk1 j).mpr hj⟩
    rcases hmodel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · have h := e.symm.toMonoidHom.map_isConj h1
        rwa [hA_u] at h
      · have h := e.symm.toMonoidHom.map_isConj h2
        rwa [hB_u] at h
    · right
      refine ⟨?_, ?_⟩
      · have h := e.symm.toMonoidHom.map_isConj h1
        rwa [hA_u] at h
      · have h := e.symm.toMonoidHom.map_isConj h2
        rwa [hB_u] at h
  let tH : ↥H := e.symm (CFSG.CGT.Foote81L6.zc k)
  have htH_e : e tH = CFSG.CGT.Foote81L6.zc k := by simp [tH]
  have htH_ne_one : tH ≠ 1 := by
    intro h
    apply CFSG.CGT.Foote81L6.zc_ne_one hk1
    have h' : e tH = e 1 := congrArg e h
    simpa [htH_e] using h'
  have htH_cent : (tH : G) ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : tH * (⟨y, hy⟩ : ↥H) = (⟨y, hy⟩ : ↥H) * tH := by
      apply e.injective
      rw [map_mul, map_mul, htH_e]
      exact (CFSG.CGT.Foote81L6.zc_comm hk1 _).symm
    exact (congrArg Subtype.val h1).symm
  have htH_zpow : (tH : G) ∈ Subgroup.zpowers z := by
    rw [← hz_center]
    exact Subgroup.mem_inf.mpr ⟨tH.2, htH_cent⟩
  have htH_eq : (tH : G) = z := by
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hz2 htH_zpow with h | h
    · exact absurd (Subtype.ext h) htH_ne_one
    · exact h
  have hstep : ∀ {x : ↥H} {m : ZMod (2 ^ k)}, e x = sr m → ConjIn C (x : G) z := by
    intro x m hxm
    have hxu : e.symm.toMonoidHom (sr m) = x := by
      rw [← hxm]
      exact e.symm_apply_apply x
    rcases CFSG.GorensteinWalter.TwoClassFusion.isConj_sr_zero_or_one m with hclass | hclass
    · have hxu0 : IsConj x (e.symm.toMonoidHom (sr 0)) := by
        have h := e.symm.toMonoidHom.map_isConj hclass
        rw [hxu] at h
        simpa using h
      rcases hclasses with ⟨ha0, -⟩ | ⟨-, hb0⟩
      · exact conjIn_trans (conjIn_of_isConj_coe hC (hxu0.trans ha0.symm)) haconj
      · exact conjIn_trans (conjIn_of_isConj_coe hC (hxu0.trans hb0.symm)) hbconj
    · have hxu1 : IsConj x (e.symm.toMonoidHom (sr 1)) := by
        have h := e.symm.toMonoidHom.map_isConj hclass
        rw [hxu] at h
        simpa using h
      rcases hclasses with ⟨-, hb1⟩ | ⟨ha1, -⟩
      · exact conjIn_trans (conjIn_of_isConj_coe hC (hxu1.trans hb1.symm)) hbconj
      · exact conjIn_trans (conjIn_of_isConj_coe hC (hxu1.trans ha1.symm)) haconj
  have hkey : ∀ x ∈ H, orderOf x = 2 → ConjIn C x z := by
    intro x hx hxo
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxo
      omega
    have hXord : orderOf (e ⟨x, hx⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hxo
    rcases CFSG.GorensteinWalter.TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two
      hk2 hXord with hcentral | ⟨m, hm⟩
    · have hx_t : (⟨x, hx⟩ : ↥H) = tH := by
        apply e.injective
        rw [htH_e, CFSG.CGT.Foote81L6.TStruct.zc_eq_r hk1]
        exact hcentral
      have hx_z : x = z := by
        have h1 : (⟨x, hx⟩ : ↥H) = (⟨z, hz⟩ : ↥H) := by
          rw [hx_t]
          exact Subtype.ext htH_eq
        exact congrArg Subtype.val h1
      exact ⟨1, C.one_mem, by rw [hx_z]; simp⟩
    · exact hstep hm
  intro x hx y hy hxo hyo
  obtain ⟨c, hc, hcx⟩ := hkey x hx hxo
  obtain ⟨d, hd, hdy⟩ := hkey y hy hyo
  refine ⟨d⁻¹ * c, C.mul_mem (C.inv_mem hd) hc, ?_⟩
  calc (d⁻¹ * c) * x * (d⁻¹ * c)⁻¹ = d⁻¹ * (c * x * c⁻¹) * d := by group
    _ = d⁻¹ * z * d := by rw [hcx]
    _ = y := by rw [← hdy]; group

end MainFusion

section CorrectedFactor

variable {G : Type*} [Group G] [Finite G]

theorem corrected_factor_core {S X Y W : Subgroup G} (hX : IsDihNonab X)
    {a b zX zY ε₁ ε₂ : G} {k : ℕ} (hk : 2 ≤ k)
    (ha : a ∈ X) (hb : b ∈ X) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hgen : X = Subgroup.closure {a, b})
    (hzX : zX ∈ X) (hzX2 : zX * zX = 1) (hzX1 : zX ≠ 1)
    (hzX_center : X ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers zX)
    (hzX_ab : zX = (a * b) ^ (2 ^ (k - 1)))
    (hY_comm : Y ≤ Subgroup.centralizer (X : Set G))
    (hzY : zY ∈ Y)
    (hε₁ : ε₁ ∈ Y) (hε₂ : ε₂ ∈ Y)
    (hε₁c : ∀ d ∈ Y, d * ε₁ = ε₁ * d) (hε₂c : ∀ d ∈ Y, d * ε₂ = ε₂ * d)
    (hε₁2 : ε₁ * ε₁ = 1) (hε₂2 : ε₂ * ε₂ = 1)
    (hW : W = Subgroup.closure {a * ε₁, b * ε₂})
    (hWX : Nonempty (↥W ≃* ↥X))
    (hzY_centW : zY ∈ Subgroup.centralizer (W : Set G))
    (hconj₁ : ConjIn (Subgroup.centralizer ({zY} : Set G)) (a * ε₁) zX)
    (hconj₂ : ConjIn (Subgroup.centralizer ({zY} : Set G)) (b * ε₂) zX) :
    IsDihNonab W ∧ W ⊓ Subgroup.centralizer (W : Set G) = Subgroup.zpowers zX ∧
      (∀ x ∈ W, ∀ y ∈ W, orderOf x = 2 → orderOf y = 2 →
        ConjIn (Subgroup.centralizer ({zY} : Set G)) x y) := by
  classical
  obtain ⟨k₁, hk₁, ⟨e₁⟩⟩ := hX
  obtain ⟨eW⟩ := hWX
  have hdihW : IsDihNonab W := ⟨k₁, hk₁, ⟨eW.trans e₁⟩⟩
  have haε₁ : a * ε₁ = ε₁ * a :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₁) a ha
  have hbε₁ : b * ε₁ = ε₁ * b :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₁) b hb
  have haε₂ : a * ε₂ = ε₂ * a :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₂) a ha
  have hbε₂ : b * ε₂ = ε₂ * b :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₂) b hb
  have hε₂ε₁ : ε₂ * ε₁ = ε₁ * ε₂ := hε₁c ε₂ hε₂
  have haε₁2 : (a * ε₁) * (a * ε₁) = 1 := by
    calc (a * ε₁) * (a * ε₁) = a * (ε₁ * a) * ε₁ := by group
      _ = a * (a * ε₁) * ε₁ := by rw [← haε₁]
      _ = (a * a) * (ε₁ * ε₁) := by group
      _ = 1 := by rw [ha2, hε₁2, one_mul]
  have hbε₂2 : (b * ε₂) * (b * ε₂) = 1 := by
    calc (b * ε₂) * (b * ε₂) = b * (ε₂ * b) * ε₂ := by group
      _ = b * (b * ε₂) * ε₂ := by rw [← hbε₂]
      _ = (b * b) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hb2, hε₂2, one_mul]
  have hε2 : (ε₁ * ε₂) * (ε₁ * ε₂) = 1 := by
    calc (ε₁ * ε₂) * (ε₁ * ε₂) = ε₁ * (ε₂ * ε₁) * ε₂ := by group
      _ = ε₁ * (ε₁ * ε₂) * ε₂ := by rw [hε₂ε₁]
      _ = (ε₁ * ε₁) * (ε₂ * ε₂) := by group
      _ = 1 := by rw [hε₁2, hε₂2, one_mul]
  have hcomm_aε₁ : Commute a ε₁ := haε₁
  have hcomm_bε₁ : Commute b ε₁ := hbε₁
  have hcomm_aε₂ : Commute a ε₂ := haε₂
  have hcomm_bε₂ : Commute b ε₂ := hbε₂
  have hcomm_ab_ε₁ : Commute (a * b) ε₁ := hcomm_aε₁.mul_left hcomm_bε₁
  have hcomm_ab_ε₂ : Commute (a * b) ε₂ := hcomm_aε₂.mul_left hcomm_bε₂
  have hcomm_ab_ε : Commute (a * b) (ε₁ * ε₂) := hcomm_ab_ε₁.mul_right hcomm_ab_ε₂
  have huv_eq : (a * ε₁) * (b * ε₂) = (a * b) * (ε₁ * ε₂) := by
    calc (a * ε₁) * (b * ε₂) = a * (ε₁ * b) * ε₂ := by group
      _ = a * (b * ε₁) * ε₂ := by rw [← hbε₁]
      _ = (a * b) * (ε₁ * ε₂) := by group
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (k - 1) = 2 * m := by
    refine ⟨2 ^ (k - 2), ?_⟩
    rw [show k - 1 = k - 2 + 1 by omega, pow_succ']
  have hεpow : (ε₁ * ε₂) ^ (2 ^ (k - 1)) = 1 := by
    rw [hm, pow_mul, show (ε₁ * ε₂) ^ 2 = 1 by rw [pow_two]; exact hε2, one_pow]
  have hpow_eq : ((a * ε₁) * (b * ε₂)) ^ (2 ^ (k - 1)) = zX := by
    rw [huv_eq, hcomm_ab_ε.mul_pow, hzX_ab, hεpow, mul_one]
  have hzX_W : zX ∈ W := by
    rw [hW]
    rw [← hpow_eq]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) _
  have hzX_centX : zX ∈ Subgroup.centralizer (X : Set G) := by
    have hmem : zX ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
      rw [hzX_center]
      exact Subgroup.mem_zpowers zX
    exact hmem.2
  have hzX_a : Commute zX a :=
    (Subgroup.mem_centralizer_iff.mp hzX_centX a ha).symm
  have hzX_b : Commute zX b :=
    (Subgroup.mem_centralizer_iff.mp hzX_centX b hb).symm
  have hzX_ε₁ : Commute zX ε₁ :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₁) zX hzX
  have hzX_ε₂ : Commute zX ε₂ :=
    Subgroup.mem_centralizer_iff.mp (hY_comm hε₂) zX hzX
  have hzX_aε₁ : Commute zX (a * ε₁) := hzX_a.mul_right hzX_ε₁
  have hzX_bε₂ : Commute zX (b * ε₂) := hzX_b.mul_right hzX_ε₂
  have hzX_centW : zX ∈ Subgroup.centralizer (W : Set G) := by
    rw [hW, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact hzX_aε₁.eq.symm
    · exact hzX_bε₂.eq.symm
  have hzX_in_center : zX ∈ W ⊓ Subgroup.centralizer (W : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzX_W, hzX_centW⟩
  obtain ⟨w, -, hwo, hwcenter⟩ :=
    CFSG.GH72.IsDihNonab.exists_inf_centralizer_self_eq hdihW
  have hw2 : w * w = 1 := by rw [← pow_two, ← hwo]; exact pow_orderOf_eq_one w
  have hzX_in_w : zX ∈ Subgroup.zpowers w := by rw [← hwcenter]; exact hzX_in_center
  have hzX_eq_w : zX = w := by
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hw2 hzX_in_w with h | h
    · exact absurd h hzX1
    · exact h
  have hcenterW : W ⊓ Subgroup.centralizer (W : Set G) = Subgroup.zpowers zX := by
    rw [hzX_eq_w]
    exact hwcenter
  have hW_cent : W ≤ Subgroup.centralizer ({zY} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzY_centW u hu
  have haε1 : a * ε₁ ∈ W := by rw [hW]; exact Subgroup.subset_closure (by simp)
  have hbε2 : b * ε₂ ∈ W := by rw [hW]; exact Subgroup.subset_closure (by simp)
  have hfusion := isConj_involutions_of_dihedral_center (H := W)
    (C := Subgroup.centralizer ({zY} : Set G)) hdihW haε1 hbε2 haε₁2 hbε₂2 hW
    hzX_W hzX2 hzX1 hcenterW hW_cent hconj₁ hconj₂
  exact ⟨hdihW, hcenterW, hfusion⟩

theorem centralizer_center_eq_singleton {H : Subgroup G} {z : G}
    (hcenter : H ⊓ Subgroup.centralizer (H : Set G) = Subgroup.zpowers z) :
    Subgroup.centralizer ((H ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  rw [hcenter]
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem corrected_factor_left (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁)
    {a b z₁ z₂ ε₁ ε₂ : G} {U : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k)
    (ha : a ∈ 𝔖.S₁) (hb : b ∈ 𝔖.S₁) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hgen : 𝔖.S₁ = Subgroup.closure {a, b})
    (hz₁ : z₁ ∈ 𝔖.S₁) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1)
    (hz₁center : 𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) = Subgroup.zpowers z₁)
    (hz₁_ab : z₁ = (a * b) ^ (2 ^ (k - 1)))
    (hz₂ : z₂ ∈ 𝔖.S₂)
    (hε₁ : ε₁ ∈ 𝔖.S₂) (hε₂ : ε₂ ∈ 𝔖.S₂)
    (hε₁c : ∀ d ∈ 𝔖.S₂, d * ε₁ = ε₁ * d) (hε₂c : ∀ d ∈ 𝔖.S₂, d * ε₂ = ε₂ * d)
    (hε₁2 : ε₁ * ε₁ = 1) (hε₂2 : ε₂ * ε₂ = 1)
    (hU : U = Subgroup.closure {a * ε₁, b * ε₂})
    (hconj₁ : ConjIn (Subgroup.centralizer ({z₂} : Set G)) (a * ε₁) z₁)
    (hconj₂ : ConjIn (Subgroup.centralizer ({z₂} : Set G)) (b * ε₂) z₁) :
    DDDecomp (𝔖.S : Subgroup G) U 𝔖.S₂ ∧ Nonempty (↥U ≃* ↥𝔖.S₁) ∧ IsDihNonab U ∧
      U ⊓ Subgroup.centralizer (U : Set G) = Subgroup.zpowers z₁ ∧
      (∀ x ∈ U, ∀ y ∈ U, orderOf x = 2 → orderOf y = 2 →
        ConjIn (Subgroup.centralizer ({z₂} : Set G)) x y) := by
  classical
  obtain ⟨W, hdW, ⟨eW⟩, hWeq⟩ :=
    dd_corrected_complement 𝔖.decomp ha hb ha2 hb2 hgen hε₁ hε₂ hε₁c hε₂c hε₁2 hε₂2
  have hWU : W = U := hWeq.trans hU.symm
  rw [hWU] at hdW
  rw [hWU] at eW
  have hcore := corrected_factor_core (S := 𝔖.S) (X := 𝔖.S₁) (Y := 𝔖.S₂) (W := U)
    h₁ hk ha hb ha2 hb2 hgen hz₁ hz₁2 hz₁1 hz₁center hz₁_ab 𝔖.decomp.commute hz₂
    hε₁ hε₂ hε₁c hε₂c hε₁2 hε₂2 hU ⟨eW⟩ (hdW.commute hz₂) hconj₁ hconj₂
  exact ⟨hdW, ⟨eW⟩, hcore.1, hcore.2.1, hcore.2.2⟩

theorem ddSwap {S S₁ S₂ : Subgroup G} (h : DDDecomp S S₁ S₂) (h₁ : IsDihNonab S₁) :
    DDDecomp S S₂ S₁ :=
  { sup_eq := by rw [sup_comm]; exact h.sup_eq
    inf_eq := by rw [inf_comm]; exact h.inf_eq
    commute := Subgroup.le_centralizer_iff.mp h.commute
    dih₁ := isDih_of_isDihNonab h.dih₂
    dih₂ := h₁ }

theorem corrected_factor_right (𝔖 : Sec3Setting G) {U : Subgroup G}
    (hU_dih : IsDihNonab U)
    (hdU : DDDecomp (𝔖.S : Subgroup G) U 𝔖.S₂)
    {c d z₂ z₁ ε₃ ε₄ : G} {V : Subgroup G} {k₂ : ℕ}
    (hk₂ : 2 ≤ k₂)
    (hc : c ∈ 𝔖.S₂) (hd : d ∈ 𝔖.S₂) (hc2 : c * c = 1) (hd2 : d * d = 1)
    (hgen₂ : 𝔖.S₂ = Subgroup.closure {c, d})
    (hz₂ : z₂ ∈ 𝔖.S₂) (hz₂2 : z₂ * z₂ = 1) (hz₂1 : z₂ ≠ 1)
    (hz₂center : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z₂)
    (hz₂_cd : z₂ = (c * d) ^ (2 ^ (k₂ - 1)))
    (hz₁ : z₁ ∈ U)
    (hε₃ : ε₃ ∈ U) (hε₄ : ε₄ ∈ U)
    (hε₃c : ∀ e ∈ U, e * ε₃ = ε₃ * e) (hε₄c : ∀ e ∈ U, e * ε₄ = ε₄ * e)
    (hε₃2 : ε₃ * ε₃ = 1) (hε₄2 : ε₄ * ε₄ = 1)
    (hV : V = Subgroup.closure {c * ε₃, d * ε₄})
    (hconj₃ : ConjIn (Subgroup.centralizer ({z₁} : Set G)) (c * ε₃) z₂)
    (hconj₄ : ConjIn (Subgroup.centralizer ({z₁} : Set G)) (d * ε₄) z₂) :
    DDDecomp (𝔖.S : Subgroup G) U V ∧ Nonempty (↥V ≃* ↥𝔖.S₂) ∧ IsDihNonab V ∧
      V ⊓ Subgroup.centralizer (V : Set G) = Subgroup.zpowers z₂ ∧
      (∀ x ∈ V, ∀ y ∈ V, orderOf x = 2 → orderOf y = 2 →
        ConjIn (Subgroup.centralizer ({z₁} : Set G)) x y) := by
  classical
  obtain ⟨V', hdUV', ⟨eV'⟩, hV'eq⟩ :=
    dd_corrected_complement_right hdU hc hd hc2 hd2 hgen₂ hε₃ hε₄ hε₃c hε₄c hε₃2 hε₄2
  have hVV' : V' = V := hV'eq.trans hV.symm
  rw [hVV'] at hdUV'
  rw [hVV'] at eV'
  have hU_comm : U ≤ Subgroup.centralizer (𝔖.S₂ : Set G) :=
    Subgroup.le_centralizer_iff.mp hdU.commute
  have hz₁_centV : z₁ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.le_centralizer_iff.mp hdUV'.commute) hz₁
  have hcore := corrected_factor_core (S := 𝔖.S) (X := 𝔖.S₂) (Y := U) (W := V)
    𝔖.decomp.dih₂ hk₂ hc hd hc2 hd2 hgen₂ hz₂ hz₂2 hz₂1 hz₂center hz₂_cd hU_comm hz₁
    hε₃ hε₄ hε₃c hε₄c hε₃2 hε₄2 hV ⟨eV'⟩ hz₁_centV hconj₃ hconj₄
  exact ⟨hdUV', ⟨eV'⟩, hcore.1, hcore.2.1, hcore.2.2⟩

theorem lemma_3_9_of_correction_data (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁)
    {U : Subgroup G} {a b z₁ z₂ ε₁ ε₂ : G} {k : ℕ}
    (hk : 2 ≤ k)
    (ha : a ∈ 𝔖.S₁) (hb : b ∈ 𝔖.S₁) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hgen : 𝔖.S₁ = Subgroup.closure {a, b})
    (hz₁ : z₁ ∈ 𝔖.S₁) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1)
    (hz₁center : 𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) = Subgroup.zpowers z₁)
    (hz₁_ab : z₁ = (a * b) ^ (2 ^ (k - 1)))
    (hz₂ : z₂ ∈ 𝔖.S₂)
    (hε₁ : ε₁ ∈ 𝔖.S₂) (hε₂ : ε₂ ∈ 𝔖.S₂)
    (hε₁c : ∀ d ∈ 𝔖.S₂, d * ε₁ = ε₁ * d) (hε₂c : ∀ d ∈ 𝔖.S₂, d * ε₂ = ε₂ * d)
    (hε₁2 : ε₁ * ε₁ = 1) (hε₂2 : ε₂ * ε₂ = 1)
    (hU : U = Subgroup.closure {a * ε₁, b * ε₂})
    (hconj₁ : ConjIn (Subgroup.centralizer ({z₂} : Set G)) (a * ε₁) z₁)
    (hconj₂ : ConjIn (Subgroup.centralizer ({z₂} : Set G)) (b * ε₂) z₁)
    {V : Subgroup G} {c d ε₃ ε₄ : G} {k₂ : ℕ}
    (hk₂ : 2 ≤ k₂)
    (hc : c ∈ 𝔖.S₂) (hd : d ∈ 𝔖.S₂) (hc2 : c * c = 1) (hd2 : d * d = 1)
    (hgen₂ : 𝔖.S₂ = Subgroup.closure {c, d})
    (hz₂2 : z₂ * z₂ = 1) (hz₂1 : z₂ ≠ 1)
    (hz₂center : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z₂)
    (hz₂_cd : z₂ = (c * d) ^ (2 ^ (k₂ - 1)))
    (hε₃ : ε₃ ∈ U) (hε₄ : ε₄ ∈ U)
    (hε₃c : ∀ e ∈ U, e * ε₃ = ε₃ * e) (hε₄c : ∀ e ∈ U, e * ε₄ = ε₄ * e)
    (hε₃2 : ε₃ * ε₃ = 1) (hε₄2 : ε₄ * ε₄ = 1)
    (hV : V = Subgroup.closure {c * ε₃, d * ε₄})
    (hconj₃ : ConjIn (Subgroup.centralizer ({z₁} : Set G)) (c * ε₃) z₂)
    (hconj₄ : ConjIn (Subgroup.centralizer ({z₁} : Set G)) (d * ε₄) z₂) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧
      (∀ x ∈ S₁', ∀ y ∈ S₁', orderOf x = 2 → orderOf y = 2 →
        ∃ g ∈ Subgroup.centralizer
          ((S₂' ⊓ Subgroup.centralizer (S₂' : Set G) : Subgroup G) : Set G),
          g * x * g⁻¹ = y) ∧
      (∀ x ∈ S₂', ∀ y ∈ S₂', orderOf x = 2 → orderOf y = 2 →
        ∃ g ∈ Subgroup.centralizer
          ((S₁' ⊓ Subgroup.centralizer (S₁' : Set G) : Subgroup G) : Set G),
          g * x * g⁻¹ = y) := by
  classical
  obtain ⟨hdU, -, hU_dih, hcenterU, hfusionU⟩ :=
    corrected_factor_left 𝔖 h₁ hk ha hb ha2 hb2 hgen hz₁ hz₁2 hz₁1 hz₁center hz₁_ab hz₂
      hε₁ hε₂ hε₁c hε₂c hε₁2 hε₂2 hU hconj₁ hconj₂
  have hz₁U : z₁ ∈ U := by
    have hmem : z₁ ∈ U ⊓ Subgroup.centralizer (U : Set G) := by
      rw [hcenterU]
      exact Subgroup.mem_zpowers z₁
    exact hmem.1
  obtain ⟨hdUV, -, hV_dih, hcenterV, hfusionV⟩ :=
    corrected_factor_right 𝔖 hU_dih hdU hk₂ hc hd hc2 hd2 hgen₂ hz₂ hz₂2 hz₂1 hz₂center
      hz₂_cd hz₁U hε₃ hε₄ hε₃c hε₄c hε₃2 hε₄2 hV hconj₃ hconj₄
  refine ⟨U, V, hdUV, ?_, ?_⟩
  · intro x hx y hy hx2 hy2
    rw [centralizer_center_eq_singleton hcenterV]
    exact hfusionU x hx y hy hx2 hy2
  · intro x hx y hy hx2 hy2
    rw [centralizer_center_eq_singleton hcenterU]
    exact hfusionV x hx y hy hx2 hy2

end CorrectedFactor

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

private structure DihGen (D : Subgroup G) where
  k : ℕ
  hk : 2 ≤ k
  a : G
  b : G
  z : G
  ha : a ∈ D
  hb : b ∈ D
  hz : z ∈ D
  ha2 : a * a = 1
  hb2 : b * b = 1
  hz2 : z * z = 1
  hz1 : z ≠ 1
  hgen : D = Subgroup.closure {a, b}
  card_D : Nat.card D = 2 ^ (k + 1)
  hz_central : ∀ g ∈ D, g * z = z * g
  hz_center : D ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z
  hab_order : orderOf (a * b) = 2 ^ k
  hz_ab : z = (a * b) ^ (2 ^ (k - 1))

private def DihGen.swap {D : Subgroup G} (g : DihGen D) : DihGen D where
  k := g.k
  hk := g.hk
  a := g.b
  b := g.a
  z := g.z
  ha := g.hb
  hb := g.ha
  hz := g.hz
  ha2 := g.hb2
  hb2 := g.ha2
  hz2 := g.hz2
  hz1 := g.hz1
  hgen := by simpa [Set.pair_comm] using g.hgen
  card_D := g.card_D
  hz_central := g.hz_central
  hz_center := g.hz_center
  hab_order := by
    have h : g.b * g.a = (g.a * g.b)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right g.hb2, inv_eq_of_mul_eq_one_right g.ha2]
    rw [h, orderOf_inv, g.hab_order]
  hz_ab := by
    have h : g.b * g.a = (g.a * g.b)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right g.hb2, inv_eq_of_mul_eq_one_right g.ha2]
    rw [g.hz_ab, h, inv_pow, ← g.hz_ab]
    exact (inv_eq_of_mul_eq_one_right g.hz2).symm

private theorem exists_dihGen {D : Subgroup G} (hD : IsDihNonab D) : Nonempty (DihGen D) := by
  classical
  have hD' : IsDihNonab D := hD
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  have hk1 : 1 ≤ k := by omega
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  let a : G := (e.symm (DihedralGroup.sr 0) : ↥D)
  let b : G := (e.symm (DihedralGroup.sr 1) : ↥D)
  let z : G := (e.symm (CFSG.CGT.Foote81L6.zc k) : ↥D)
  have ha : a ∈ D := (e.symm (DihedralGroup.sr 0)).2
  have hb : b ∈ D := (e.symm (DihedralGroup.sr 1)).2
  have hz : z ∈ D := (e.symm (CFSG.CGT.Foote81L6.zc k)).2
  have hea : e ⟨a, ha⟩ = DihedralGroup.sr 0 := by
    rw [show (⟨a, ha⟩ : ↥D) = e.symm (DihedralGroup.sr 0) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have heb : e ⟨b, hb⟩ = DihedralGroup.sr 1 := by
    rw [show (⟨b, hb⟩ : ↥D) = e.symm (DihedralGroup.sr 1) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have hez : e ⟨z, hz⟩ = CFSG.CGT.Foote81L6.zc k := by
    rw [show (⟨z, hz⟩ : ↥D) = e.symm (CFSG.CGT.Foote81L6.zc k) from Subtype.ext rfl,
      MulEquiv.apply_symm_apply]
  have ha2 : a * a = 1 := by
    have h : e (⟨a, ha⟩ * ⟨a, ha⟩) = e 1 := by
      rw [map_mul, hea, DihedralGroup.sr_mul_self, map_one]
    rw [← show (⟨a * a, mul_mem ha ha⟩ : ↥D) = ⟨a, ha⟩ * ⟨a, ha⟩ from Subtype.ext rfl] at h
    exact congrArg Subtype.val (e.injective h)
  have hb2 : b * b = 1 := by
    have h : e (⟨b, hb⟩ * ⟨b, hb⟩) = e 1 := by
      rw [map_mul, heb, DihedralGroup.sr_mul_self, map_one]
    rw [← show (⟨b * b, mul_mem hb hb⟩ : ↥D) = ⟨b, hb⟩ * ⟨b, hb⟩ from Subtype.ext rfl] at h
    exact congrArg Subtype.val (e.injective h)
  have hz2 : z * z = 1 := by
    have h : e (⟨z, hz⟩ * ⟨z, hz⟩) = e 1 := by
      rw [map_mul, hez, CFSG.CGT.Foote81L6.zc_mul_self hk1, map_one]
    rw [← show (⟨z * z, mul_mem hz hz⟩ : ↥D) = ⟨z, hz⟩ * ⟨z, hz⟩ from Subtype.ext rfl] at h
    exact congrArg Subtype.val (e.injective h)
  have hz1 : z ≠ 1 := by
    intro h
    apply CFSG.CGT.Foote81L6.zc_ne_one hk1
    have h' : (⟨z, hz⟩ : ↥D) = 1 := Subtype.ext h
    have h'' := congrArg e h'
    rw [hez] at h''
    simpa using h''
  have htop : Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} :
      Set (DihedralGroup (2 ^ k))) = ⊤ := by
    have h0 : (DihedralGroup.sr 0 : DihedralGroup (2 ^ k)) ∈
        ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ k))) := by
      simp
    have h1 : (DihedralGroup.sr 1 : DihedralGroup (2 ^ k)) ∈
        ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ k))) := by
      simp
    have hr1 : (DihedralGroup.r 1 : DihedralGroup (2 ^ k)) ∈
        Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} :
          Set (DihedralGroup (2 ^ k))) := by
      have h := (Subgroup.closure
        ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ k)))).mul_mem
        (Subgroup.subset_closure h0) (Subgroup.subset_closure h1)
      simpa [DihedralGroup.sr_mul_sr] using h
    rw [eq_top_iff]
    intro x _
    rcases x with i | i
    · rw [← ZMod.natCast_zmod_val i, ← DihedralGroup.r_one_pow i.val]
      exact Subgroup.pow_mem _ hr1 i.val
    · have h := (Subgroup.closure
          ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ k)))).mul_mem
          (Subgroup.subset_closure h0) (Subgroup.pow_mem _ hr1 i.val)
      rw [← ZMod.natCast_zmod_val i] at h
      simpa [DihedralGroup.sr_mul_r] using h
  have himg : e.toMonoidHom '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥D) =
      ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup (2 ^ k))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inl hea
      · exact Or.inr heb
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨a, ha⟩, Or.inl rfl, hea⟩
      · exact ⟨⟨b, hb⟩, Or.inr rfl, heb⟩
  have hclosureD : Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥D) = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [MonoidHom.map_closure]
    rw [himg]
    rw [htop]
    exact (Subgroup.map_top_of_surjective e.toMonoidHom (fun x => e.surjective x)).symm
  have hgen : D = Subgroup.closure ({a, b} : Set G) := by
    have hmap := congrArg (Subgroup.map D.subtype) hclosureD
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at hmap
    have hsub : D.subtype '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥D) = ({a, b} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨⟨a, ha⟩, Or.inl rfl, rfl⟩
        · exact ⟨⟨b, hb⟩, Or.inr rfl, rfl⟩
    rw [hsub] at hmap
    exact hmap.symm
  have hz_central : ∀ g ∈ D, g * z = z * g := by
    intro g hg
    have h := congrArg e.symm (CFSG.CGT.Foote81L6.zc_comm hk1 (e ⟨g, hg⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h
  have hz_center : D ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z := by
    obtain ⟨w, hwD, hw2, hwcenter⟩ :=
      CFSG.GH72.IsDihNonab.exists_inf_centralizer_self_eq hD'
    have hw2' : w * w = 1 := by
      rw [← pow_two, ← hw2]
      exact pow_orderOf_eq_one w
    have hzmem : z ∈ Subgroup.zpowers w := by
      rw [← hwcenter]
      exact ⟨hz, Subgroup.mem_centralizer_iff.mpr hz_central⟩
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hw2' hzmem with h | h
    · exact absurd h hz1
    · rw [h, hwcenter]
  have hab' : (⟨a * b, mul_mem ha hb⟩ : ↥D) = e.symm (DihedralGroup.r 1) := by
    apply e.injective
    have h1 : e (⟨a * b, mul_mem ha hb⟩ : ↥D) = e (⟨a, ha⟩ * ⟨b, hb⟩) :=
      congrArg e (Subtype.ext rfl)
    rw [h1, map_mul, hea, heb, MulEquiv.apply_symm_apply, DihedralGroup.sr_mul_sr]
    norm_num
  have hab : a * b = (e.symm (DihedralGroup.r 1) : ↥D) := congrArg Subtype.val hab'
  have hab_order : orderOf (a * b) = 2 ^ k := by
    rw [hab, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hz_ab : z = (a * b) ^ (2 ^ (k - 1)) := by
    have h : (⟨z, hz⟩ : ↥D) = (e.symm (DihedralGroup.r 1)) ^ (2 ^ (k - 1)) := by
      apply e.injective
      rw [hez, map_pow, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow]
      exact CFSG.CGT.Foote81L6.TStruct.zc_eq_r hk1
    rw [← hab'] at h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow] at h'
    exact h'
  have card_D : Nat.card D = 2 ^ (k + 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  exact ⟨⟨k, hk, a, b, z, ha, hb, hz, ha2, hb2, hz2, hz1, hgen, card_D, hz_central,
    hz_center, hab_order, hz_ab⟩⟩

private theorem DihGen.z_mem_rotation {D : Subgroup G} (g : DihGen D) :
    g.z ∈ Subgroup.zpowers (g.a * g.b) := by
  rw [g.hz_ab]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (g.a * g.b)) _

private theorem DihGen.rotation_le {D : Subgroup G} (g : DihGen D) :
    Subgroup.zpowers (g.a * g.b) ≤ D :=
  Subgroup.zpowers_le.mpr (mul_mem g.ha g.hb)

private theorem DihGen.rotation_relIndex {D : Subgroup G} (g : DihGen D) :
    (Subgroup.zpowers (g.a * g.b)).relIndex D = 2 := by
  have hcardR : Nat.card ↥(Subgroup.zpowers (g.a * g.b)) = 2 ^ g.k := by
    rw [Nat.card_zpowers, g.hab_order]
  have h := Subgroup.relIndex_mul_card (Subgroup.zpowers (g.a * g.b)) D
  rw [inf_of_le_left g.rotation_le, hcardR, g.card_D, pow_succ] at h
  have hpos : 0 < 2 ^ g.k := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])

private theorem noncentral_of_dihGen {D : Subgroup G} (hD : IsDihNonab D) (g : DihGen D) :
    ∃ y ∈ D, y * g.a ≠ g.a * y := by
  by_contra h
  have h' : ∀ y ∈ D, y * g.a = g.a * y := by
    intro y hy
    by_contra hyc
    exact h ⟨y, hy, hyc⟩
  have hcommab : g.a * g.b = g.b * g.a := (h' g.b g.hb).symm
  have hpair : ({g.a, g.b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcommab
    · exact hcommab.symm
    · exact Commute.refl _
  have hcomm : IsMulCommutative ↥(Subgroup.closure ({g.a, g.b} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  rw [← g.hgen] at hcomm
  have hcomm' : ∀ x y : ↥D, x * y = y * x := isMulCommutative_iff.mp hcomm
  obtain ⟨x, hx, y, hy, hxy⟩ := hD.exists_mul_ne_mul
  exact hxy (congrArg Subtype.val (hcomm' ⟨x, hx⟩ ⟨y, hy⟩))

private theorem card_inf_centralizer_left_eq {S D₁ D₂ : Subgroup G}
    (hd : DDDecomp S D₁ D₂) {a : G} (ha : a ∈ D₁) (ha2 : a * a = 1)
    (hnc : ∃ y ∈ D₁, y * a ≠ a * y) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({a} : Set G)) = 4 * Nat.card D₂ := by
  classical
  have hfour := hd.dih₁.isFourIn_inf_centralizer ha ha2 hnc
  have hinf : (D₁ ⊓ Subgroup.centralizer ({a} : Set G)) ⊓ D₂ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hd.inf_eq.le
  have hcomm : ∀ x ∈ D₁ ⊓ Subgroup.centralizer ({a} : Set G), ∀ y ∈ D₂, x * y = y * x :=
    fun x hx y hy => hd.comm (mem_inf.1 hx).1 hy
  rw [hd.inf_centralizer_left ha,
    CFSG.CGT.Foote81L6.card_sup_of_le_normalizer
      (CFSG.CGT.Foote81L6.le_normalizer_of_comm hcomm) hinf, hfour.2.2]

private theorem card_inf_centralizer_right_eq {S D₁ D₂ : Subgroup G}
    (hd : DDDecomp S D₁ D₂) {a : G} (ha : a ∈ D₂) (ha2 : a * a = 1)
    (hnc : ∃ y ∈ D₂, y * a ≠ a * y) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({a} : Set G)) = 4 * Nat.card D₁ := by
  classical
  have hfour := (isDih_of_isDihNonab hd.dih₂).isFourIn_inf_centralizer ha ha2 hnc
  have hinf : D₁ ⊓ (D₂ ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hd.inf_eq.le
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂ ⊓ Subgroup.centralizer ({a} : Set G), x * y = y * x :=
    fun x hx y hy => hd.comm hx (mem_inf.1 hy).1
  rw [hd.inf_centralizer_right ha, CFSG.CGT.Foote81L6.card_sup_of_le_normalizer
      (CFSG.CGT.Foote81L6.le_normalizer_of_comm hcomm) hinf, hfour.2.2]
  omega

private theorem central_of_mem_rotation_involution {D : Subgroup G} (hD : IsDihNonab D)
    (g : DihGen D) {r : G} (hr : r ∈ Subgroup.zpowers (g.a * g.b)) (hr2 : r * r = 1) :
    ∀ y ∈ D, y * r = r * y := by
  have hRle : Subgroup.zpowers (g.a * g.b) ≤ D := g.rotation_le
  have hRne : Subgroup.zpowers (g.a * g.b) ≠ ⊥ := by
    intro hbot
    have hmem : g.a * g.b ∈ Subgroup.zpowers (g.a * g.b) := Subgroup.mem_zpowers _
    rw [hbot] at hmem
    have hab1 : g.a * g.b = 1 := Subgroup.mem_bot.mp hmem
    have h1 : orderOf (g.a * g.b) = 1 := by rw [hab1, orderOf_one]
    rw [g.hab_order] at h1
    have hk2 : 2 ≤ g.k := g.hk
    have hkpos : g.k ≠ 0 := by omega
    exact (Nat.one_lt_two_pow hkpos).ne' h1
  have hnoFour : ∀ V, CFSG.CGT.Foote81L6.TStruct.IsFourIn D V →
      ¬ V ≤ Subgroup.zpowers (g.a * g.b) := by
    intro V hV hVR
    haveI : IsCyclic ↥(Subgroup.zpowers (g.a * g.b)) := Subgroup.isCyclic_zpowers _
    have hVcyc : IsCyclic ↥V := Subgroup.isCyclic_of_le hVR
    haveI : IsKleinFour ↥V := isKleinFour_of_isFourIn hV
    exact IsKleinFour.not_isCyclic hVcyc
  obtain ⟨zR, hzR, hzR2, huniq⟩ :=
    (isDih_of_isDihNonab hD).exists_unique_involution hRle hRne hnoFour
  have hz_mem : g.z ∈ Subgroup.zpowers (g.a * g.b) := g.z_mem_rotation
  have hz_ord : orderOf g.z = 2 := orderOf_eq_prime (by rw [pow_two]; exact g.hz2) g.hz1
  have hz_eq : g.z = zR := huniq g.z hz_mem hz_ord
  by_cases hr1 : r = 1
  · intro y hy
    rw [hr1, mul_one, one_mul]
  · have hr_ord : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
    have hr_eq : r = zR := huniq r hr hr_ord
    rw [hr_eq, ← hz_eq]
    exact g.hz_central

private theorem card_inf_centralizer_of_mem_rotation {S D₁ D₂ : Subgroup G}
    (hd : DDDecomp S D₁ D₂) (h₁ : IsDihNonab D₁) (g₁ : DihGen D₁)
    {t : G} (htT : t ∈ Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂)
    (ht2 : t * t = 1) (htZ : t ∉ S ⊓ Subgroup.centralizer (S : Set G)) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) = 4 * Nat.card D₁ := by
  classical
  have hRle : Subgroup.zpowers (g₁.a * g₁.b) ≤ D₁ := g₁.rotation_le
  have hc : ∀ x ∈ Subgroup.zpowers (g₁.a * g₁.b), ∀ y ∈ D₂, x * y = y * x :=
    fun x hx y hy => hd.comm (hRle hx) hy
  obtain ⟨r, hr, s, hs, rfl⟩ :=
    (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer
      (CFSG.CGT.Foote81L6.le_normalizer_of_comm hc)).1 htT
  have hrs2 := (hd.mul_self_iff (hRle hr) hs).mp ht2
  have hrc : ∀ y ∈ D₁, y * r = r * y :=
    central_of_mem_rotation_involution h₁ g₁ hr hrs2.1
  have hnc_s : ∃ y ∈ D₂, y * s ≠ s * y := by
    by_contra h
    apply htZ
    have hs_cent : ∀ y ∈ D₂, y * s = s * y := by
      intro y hy
      by_contra hyc
      exact h ⟨y, hy, hyc⟩
    refine ⟨?_, ?_⟩
    · change r * s ∈ S
      rw [← hd.sup_eq]
      exact mul_mem (Subgroup.mem_sup_left (hRle hr)) (Subgroup.mem_sup_right hs)
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp
          (hd.le_centralizer_mul (hRle hr) hs hrc hs_cent hy)
  have hD1C : D₁ ⊓ Subgroup.centralizer ({r} : Set G) = D₁ := by
    rw [inf_eq_left]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hrc y hy)
  rw [hd.inf_centralizer_mul (hRle hr) hs, hD1C, ← hd.inf_centralizer_right hs]
  exact card_inf_centralizer_right_eq hd hs hrs2.2 hnc_s

private theorem card_inf_centralizer_le_of_extremal {S : Subgroup G} (hS : IsPGroup 2 S)
    {u x : G}
    (hx : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G))) (hux : IsConj u x) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({u} : Set G)) ≤
      Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hCu : IsPGroup 2 ↥((S : Subgroup G) ⊓ (C : Subgroup G)) :=
    IsPGroup.to_le (H := (S : Subgroup G) ⊓ (C : Subgroup G)) (K := (S : Subgroup G)) hS inf_le_left
  obtain ⟨Q, hQle⟩ := (hCu.comap_subtype (K := C)).exists_le_sylow
  let P : Subgroup G := Q.map C.subtype
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 P C := ⟨Q, rfl⟩
  have hle : S ⊓ C ≤ P := by
    intro a ha
    exact Subgroup.mem_map.mpr ⟨⟨a, ha.2⟩, hQle (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hcardC : Nat.card ↥C = Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_centralizer_of_isConj hux
  have hPcard : Nat.card ↥P = Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hPsyl.card_eq, hcardC, ← hx.card_eq]
  calc Nat.card ↥(S ⊓ C) ≤ Nat.card ↥P :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    _ = Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) := hPcard

private theorem exists_extremal_conj (𝔖 : Sec3Setting G) {a : G}
    (haS : a ∈ (𝔖.S : Subgroup G)) (ha2 : orderOf a = 2) :
    ∃ t ∈ (𝔖.S : Subgroup G), IsConj a t ∧
      CFSG.ABGLocalTools.IsSylowOf 2
        ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
        (Subgroup.centralizer ({t} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2' : a * a = 1 := by
    rw [← pow_two, ← ha2]
    exact pow_orderOf_eq_one a
  let C : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (by rw [ha2'])
  have hzaC : Subgroup.zpowers a ≤ C := Subgroup.zpowers_le.mpr haC
  have hza : IsPGroup 2 (Subgroup.zpowers a) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, ha2]
    exact ⟨1, by simp⟩
  have hza' : IsPGroup 2 ((Subgroup.zpowers a).subgroupOf C) := hza.comap_subtype (K := C)
  obtain ⟨Q, hQle⟩ := hza'.exists_le_sylow
  let P : Subgroup G := Q.map C.subtype
  have hPSylow : CFSG.ABGLocalTools.IsSylowOf 2 P C := ⟨Q, rfl⟩
  obtain ⟨R, hPR⟩ := hPSylow.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R 𝔖.S
  let t : G := g * a * g⁻¹
  have haP : a ∈ P := by
    refine Subgroup.mem_map.mpr ⟨⟨a, haC⟩, ?_, rfl⟩
    exact hQle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a))
  have haR : a ∈ R := hPR haP
  have htS : t ∈ (𝔖.S : Subgroup G) := by
    have h1 : t ∈ ((g • R : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.mem_map.mpr ⟨a, haR, by rfl⟩
    rwa [hg] at h1
  have hconj : IsConj a t := isConj_iff.mpr ⟨g, rfl⟩
  have hCmap : C.map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      show MulAut.conj g y * t = t * MulAut.conj g y
      simp only [t, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
        _ = g * (a * y) * g⁻¹ := by rw [hya]
        _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
      change g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have h := congrArg (fun z => g⁻¹ * z * g) hxt
      simp only [t, MulAut.conj_apply] at h ⊢
      calc (g⁻¹ * x * g) * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [← h]
        _ = a * (g⁻¹ * x * g) := by group
  have hPmap : CFSG.ABGLocalTools.IsSylowOf 2
      (P.map (MulAut.conj g).toMonoidHom) (C.map (MulAut.conj g).toMonoidHom) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hPSylow ⊢
    obtain ⟨hle, hPg, hdvd⟩ := hPSylow
    refine ⟨Subgroup.map_mono hle, hPg.map _, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hdvd
  have hPmap' : CFSG.ABGLocalTools.IsSylowOf 2
      (P.map (MulAut.conj g).toMonoidHom) (Subgroup.centralizer ({t} : Set G)) := by
    rwa [hCmap] at hPmap
  have hle : P.map (MulAut.conj g).toMonoidHom ≤
      (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine le_inf ?_ ?_
    · rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.map_mono hPR
    · rw [← hCmap]
      exact Subgroup.map_mono hPSylow.le
  have hQ2 := IsPGroup.to_inf_left (p := 2) (H := (𝔖.S : Subgroup G))
    (K := Subgroup.centralizer ({t} : Set G)) 𝔖.S.isPGroup' 
  have heq : (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) =
      P.map (MulAut.conj g).toMonoidHom :=
    CFSG.ABGLocalTools.IsSylowOf.eq_of_le hPmap' hle inf_le_right hQ2
  exact ⟨t, htS, hconj, by rw [heq]; exact hPmap'⟩

private theorem card_inf_centralizer_le_of_not_mem_center {S D₁ D₂ : Subgroup G}
    (hd : DDDecomp S D₁ D₂) (h₁ : IsDihNonab D₁) (h₂ : IsDihNonab D₂)
    {x : G} (hxS : x ∈ S) (hx2 : x * x = 1)
    (hxZ : x ∉ S ⊓ Subgroup.centralizer (S : Set G)) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      max (4 * Nat.card D₁) (4 * Nat.card D₂) := by
  classical
  obtain ⟨g₁⟩ := exists_dihGen h₁
  obtain ⟨g₂⟩ := exists_dihGen h₂
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl, hx₁2, hx₂2⟩ := hd.exists_of_mul_self hxS hx2
  have hnc : x₁ ∉ D₁ ⊓ Subgroup.centralizer (D₁ : Set G) ∨
      x₂ ∉ D₂ ⊓ Subgroup.centralizer (D₂ : Set G) := by
    by_contra h
    have h1c : x₁ ∈ D₁ ⊓ Subgroup.centralizer (D₁ : Set G) := by
      by_contra hc
      exact h (Or.inl hc)
    have h2c : x₂ ∈ D₂ ⊓ Subgroup.centralizer (D₂ : Set G) := by
      by_contra hc
      exact h (Or.inr hc)
    have hxcent : S ≤ Subgroup.centralizer ({x₁ * x₂} : Set G) :=
      hd.le_centralizer_mul hx₁ hx₂
        (fun y hy => Subgroup.mem_centralizer_iff.1 (mem_inf.1 h1c).2 y hy)
        (fun y hy => Subgroup.mem_centralizer_iff.1 (mem_inf.1 h2c).2 y hy)
    exact hxZ ⟨hxS, Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hxcent hy))⟩
  rcases hnc with hnc₁ | hnc₂
  · have hnc₁' : ∃ y ∈ D₁, y * x₁ ≠ x₁ * y := by
      by_contra h
      exact hnc₁ ⟨hx₁, fun y hy => by
        by_contra hyc
        exact h ⟨y, hy, hyc⟩⟩
    have hanc₁ := noncentral_of_dihGen h₁ g₁
    have hle := hd.card_inf_centralizer_le_of_noncentral (y₁ := x₁) (y₂ := x₂)
      hx₁ hx₁2 hnc₁' hx₂ g₁.ha g₁.ha2 hanc₁
    rw [card_inf_centralizer_left_eq hd g₁.ha g₁.ha2 hanc₁] at hle
    exact hle.trans (le_max_right _ _)
  · have hnc₂' : ∃ y ∈ D₂, y * x₂ ≠ x₂ * y := by
      by_contra h
      exact hnc₂ ⟨hx₂, fun y hy => by
        by_contra hyc
        exact h ⟨y, hy, hyc⟩⟩
    have hanc₂ := noncentral_of_dihGen h₂ g₂
    have hds : DDDecomp S D₂ D₁ :=
      { sup_eq := by rw [sup_comm, hd.sup_eq]
        inf_eq := by rw [inf_comm, hd.inf_eq]
        commute := by
          intro b hb
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact (hd.comm hb ha).symm
        dih₁ := isDih_of_isDihNonab hd.dih₂
        dih₂ := h₁ }
    have hle := hds.card_inf_centralizer_le_of_noncentral (y₁ := x₂) (y₂ := x₁)
      hx₂ hx₂2 hnc₂' hx₁ g₂.ha g₂.ha2 hanc₂
    have hcomm : x₂ * x₁ = x₁ * x₂ := (hd.comm hx₁ hx₂).symm
    rw [hcomm, card_inf_centralizer_right_eq hd g₂.ha g₂.ha2 hanc₂] at hle
    exact hle.trans (le_max_left _ _)

private theorem isSylowOf_of_card_eq_extremal {S : Subgroup G} (hS : IsPGroup 2 S) {x y : G}
    (hx : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G)))
    (hxy : IsConj x y)
    (hcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G))) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({y} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card (p := 2)
    (P := (S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G))
    (K := Subgroup.centralizer ({y} : Set G)) inf_le_right ?_
  have hcy : Nat.card ↥(Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.card_centralizer_of_isConj hxy).symm
  rw [hcard, hx.card_eq, hcy]

private theorem extremal_disjunction (𝔖 : Sec3Setting G) {D₁ D₂ : Subgroup G}
    (hd : DDDecomp (𝔖.S : Subgroup G) D₁ D₂) (h₁ : IsDihNonab D₁) (h₂ : IsDihNonab D₂)
    (g₁ : DihGen D₁) {z₂ : G} (hz₂D : z₂ ∈ D₂) (hz₂2 : orderOf z₂ = 2)
    (hz₂c : D₂ ⊓ Subgroup.centralizer (D₂ : Set G) = Subgroup.zpowers z₂)
    {t : G} (htT : t ∈ Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂) (htconj : IsConj g₁.a t)
    (hmax : ∀ y ∈ Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂, IsConj g₁.a y →
      Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
        Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)))
    (htZ : t ∉ (𝔖.S : Subgroup G) ⊓
      Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2
        ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({g₁.a} : Set G))
        (Subgroup.centralizer ({g₁.a} : Set G)) ∨
      CFSG.ABGLocalTools.IsSylowOf 2
        ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
        (Subgroup.centralizer ({t} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup G := (𝔖.S : Subgroup G)
  let T : Subgroup G := Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂
  have hS : IsPGroup 2 S := 𝔖.S.isPGroup'
  have haS : g₁.a ∈ S := hd.le_left g₁.ha
  have hnc₁ := noncentral_of_dihGen h₁ g₁
  have ha2pow : g₁.a ^ 2 = 1 := by rw [pow_two]; exact g₁.ha2
  have ha1 : g₁.a ≠ 1 := by
    intro h
    obtain ⟨y, -, hyc⟩ := hnc₁
    exact hyc (by rw [h, one_mul, mul_one])
  have ha_ord : orderOf g₁.a = 2 := orderOf_eq_prime ha2pow ha1
  obtain ⟨x, hxS, hax, hxExt⟩ := exists_extremal_conj 𝔖 haS ha_ord
  have hx_ord : orderOf x = 2 := hax.orderOf_eq.symm.trans ha_ord
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx_ord]; exact pow_orderOf_eq_one x
  have hcard_a : Nat.card ↥(S ⊓ Subgroup.centralizer ({g₁.a} : Set G)) =
      4 * Nat.card D₂ := card_inf_centralizer_left_eq hd g₁.ha g₁.ha2 hnc₁
  have ht_ord : orderOf t = 2 := htconj.orderOf_eq.symm.trans ha_ord
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht_ord]; exact pow_orderOf_eq_one t
  have hcard_t : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) =
      4 * Nat.card D₁ := card_inf_centralizer_of_mem_rotation hd h₁ g₁ htT ht2 htZ
  have hZT : S ⊓ Subgroup.centralizer (S : Set G) ≤ T := by
    rw [hd.inf_centralizer_self]
    refine sup_le ?_ ?_
    · rw [g₁.hz_center]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (by
        rw [g₁.hz_ab]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (g₁.a * g₁.b)) _))
    · rw [hz₂c]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hz₂D)
  let M : ℕ := max (4 * Nat.card D₁) (4 * Nat.card D₂)
  let n : ℕ := Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G))
  have hn_le_M : n ≤ M := by
    by_contra hn
    have hn' : M < n := lt_of_not_ge hn
    have hxZ : x ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
      by_contra hxZ
      exact absurd (card_inf_centralizer_le_of_not_mem_center hd h₁ h₂ hxS hx2 hxZ)
        (not_le.mpr hn')
    have hxT : x ∈ T := hZT hxZ
    have hn_le_t : n ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) :=
      hmax x hxT hax
    have ht_le_M : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) ≤ M := by
      rw [hcard_t]
      exact le_max_left _ _
    exact (not_lt_of_ge (hn_le_t.trans ht_le_M)) hn'
  have hle_a_n : Nat.card ↥(S ⊓ Subgroup.centralizer ({g₁.a} : Set G)) ≤ n :=
    card_inf_centralizer_le_of_extremal hS hxExt hax
  have hle_t_n : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) ≤ n :=
    card_inf_centralizer_le_of_extremal hS hxExt (htconj.symm.trans hax)
  rcases le_total (4 * Nat.card D₁) (4 * Nat.card D₂) with hBA | hAB
  · have hM : M = 4 * Nat.card D₂ := max_eq_right hBA
    have hnA : n = 4 * Nat.card D₂ :=
      le_antisymm (by rw [← hM]; exact hn_le_M) (by rw [← hcard_a]; exact hle_a_n)
    left
    have hc : Nat.card ↥(S ⊓ Subgroup.centralizer ({g₁.a} : Set G)) =
        Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [hcard_a, ← hnA]
    exact isSylowOf_of_card_eq_extremal hS hxExt hax.symm hc
  · have hM : M = 4 * Nat.card D₁ := max_eq_left hAB
    have hnB : n = 4 * Nat.card D₁ :=
      le_antisymm (by rw [← hM]; exact hn_le_M) (by rw [← hcard_t]; exact hle_t_n)
    right
    have hc : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set G)) =
        Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [hcard_t, ← hnB]
    exact isSylowOf_of_card_eq_extremal hS hxExt (hax.symm.trans htconj) hc

private theorem exists_max_conj_in_rotation (𝔖 : Sec3Setting G) {D₁ D₂ : Subgroup G}
    (hd : DDDecomp (𝔖.S : Subgroup G) D₁ D₂) (h₁ : IsDihNonab D₁) (g₁ : DihGen D₁) :
    ∃ t ∈ (Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂),
      IsConj g₁.a t ∧
      (∀ y ∈ (Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂), IsConj g₁.a y →
        Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
          Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))) := by
  classical
  let T : Subgroup G := Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂
  have hRle : Subgroup.zpowers (g₁.a * g₁.b) ≤ D₁ := g₁.rotation_le
  have hTle : T ≤ (𝔖.S : Subgroup G) :=
    sup_le (hRle.trans hd.le_left) hd.le_right
  have hTidx : T.relIndex (𝔖.S : Subgroup G) = 2 := by
    rw [show T = Subgroup.zpowers (g₁.a * g₁.b) ⊔ D₂ from rfl,
      hd.relIndex_sup_right hRle, g₁.rotation_relIndex]
  have haS : g₁.a ∈ (𝔖.S : Subgroup G) := hd.le_left g₁.ha
  have hnc := noncentral_of_dihGen h₁ g₁
  have ha1 : g₁.a ≠ 1 := by
    intro h
    obtain ⟨y, -, hyc⟩ := hnc
    exact hyc (by rw [h, one_mul, mul_one])
  have ha2pow : g₁.a ^ 2 = 1 := by rw [pow_two]; exact g₁.ha2
  have ha_ord : orderOf g₁.a = 2 := orderOf_eq_prime ha2pow ha1
  have hconjT : ∃ g : G, g⁻¹ * g₁.a * g ∈ T := by
    by_contra h
    obtain ⟨N, hNnorm, hNsq, haN⟩ :=
      CFSG.Quasithin.thompson_transfer_exists_normal 𝔖.S hTle hTidx ha_ord
        (fun x => by
          intro hx
          exact h ⟨x, hx⟩)
    haveI : N.Normal := hNnorm
    have hQ2 : IsPGroup 2 (G ⧸ N) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨1, ?_⟩
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff (N := N) (x ^ 2)).mpr (hNsq x)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
    have hNidx : N.index = 2 ^ m := by
      rw [Subgroup.index_eq_card, hm]
    have hNne : N ≠ ⊤ := by
      intro htop
      apply haN
      rw [htop]
      exact Subgroup.mem_top g₁.a
    have hNidx1 : N.index ≠ 1 := by
      intro h1
      apply hNne
      rw [Subgroup.index_eq_one] at h1
      exact h1
    have hmpos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        apply hNidx1
        rw [h0, pow_zero] at hNidx
        exact hNidx
      · exact hpos
    obtain ⟨M, hM⟩ :=
      CFSG.QuasiDihedralFusion.exists_index_two_of_two_pow_index N hNidx hmpos
    exact 𝔖.noIndexTwo M (Subgroup.normal_of_index_eq_two hM) hM
  letI : Fintype G := Fintype.ofFinite G
  let s : Finset G := Finset.univ.filter (fun y => y ∈ T ∧ IsConj g₁.a y)
  have hs : s.Nonempty := by
    obtain ⟨g, hg⟩ := hconjT
    refine ⟨g⁻¹ * g₁.a * g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, ?_⟩⟩
    exact isConj_iff.mpr ⟨g⁻¹, by group⟩
  obtain ⟨t, hts, hmax⟩ := Finset.exists_max_image s
    (fun y => Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G))) hs
  obtain ⟨-, htT, htconj⟩ := Finset.mem_filter.mp hts
  refine ⟨t, htT, htconj, ?_⟩
  intro y hy hyconj
  exact hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hyconj⟩)

private theorem exists_sylow_centralizer_containing {S : Subgroup G} (hS : IsPGroup 2 S)
    {a : G} :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R
        (Subgroup.centralizer ({a} : Set G)) ∧
      S ⊓ Subgroup.centralizer ({a} : Set G) ≤ R := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have hCu : IsPGroup 2 ↥(S ⊓ C) :=
    IsPGroup.to_le (H := (S : Subgroup G) ⊓ (C : Subgroup G)) (K := (S : Subgroup G))
      hS inf_le_left
  obtain ⟨Q, hQle⟩ := (hCu.comap_subtype (K := C)).exists_le_sylow
  let R : Subgroup G := Q.map C.subtype
  refine ⟨R, ⟨Q, rfl⟩, ?_⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem index_odd_of_isSylow_centralizers {R S : Subgroup G} {a t : G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer ({a} : Set G)))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({t} : Set G)))
    (hac : IsConj a t) (hSnot : ¬ 2 ∣ S.index) : ¬ 2 ∣ R.index := by
  have hcard : Nat.card ↥R = Nat.card ↥S := by
    rw [hR.card_eq, hS.card_eq, Subgroup.card_centralizer_of_isConj hac]
  rw [Subgroup.index_eq_card_div] at hSnot
  rw [Subgroup.index_eq_card_div, hcard]
  exact hSnot

private theorem isSylowOf_top_of_sylow (𝔖 : Sec3Setting G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (𝔖.S : Subgroup G) ⊤ := by
  refine ⟨(𝔖.S).subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]

private theorem isSylowOf_centralizer_of_central {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {t : G}
    (ht : S ≤ Subgroup.centralizer ({t} : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 S (Subgroup.centralizer ({t} : Set G)) :=
  hS.of_le ht le_top

private theorem eq_one_or_eq_of_mem_zpowers_sq {z w : G} (hz2 : z * z = 1)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

private theorem mem_sup_zpowers_involution {z₁ z₂ w : G}
    (hz₁2 : z₁ * z₁ = 1) (hz₂2 : z₂ * z₂ = 1)
    (hcomm : ∀ x ∈ Subgroup.zpowers z₁, ∀ y ∈ Subgroup.zpowers z₂, x * y = y * x)
    (hw : w ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) (hw2 : w * w = 1) :
    w = 1 ∨ w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂ := by
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer
      (CFSG.CGT.Foote81L6.le_normalizer_of_comm hcomm)).1 hw
  have hu' := eq_one_or_eq_of_mem_zpowers_sq hz₁2 hu
  have hv' := eq_one_or_eq_of_mem_zpowers_sq hz₂2 hv
  rcases hu' with hu1 | hu1
  · rcases hv' with hv1 | hv1
    · left
      rw [hu1, hv1, mul_one]
    · right; right; left
      rw [hu1, hv1, one_mul]
  · rcases hv' with hv1 | hv1
    · right; left
      rw [hu1, hv1, mul_one]
    · right; right; right
      rw [hu1, hv1]

private theorem eq_center_of_mem_commutator_involution {D : Subgroup G} (hD : IsDihNonab D)
    {z w : G} (hzD : z ∈ D) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : D ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z)
    (hw : w ∈ ⁅D, D⁆) (hw2 : w * w = 1) (hw1 : w ≠ 1) : w = z := by
  have hwD : w ∈ D := by
    have hle : ⁅D, D⁆ ≤ D := commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact hle hw
  have hwc : w ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hD.mem_centralizer_of_mem_commutator hw hw2
  have hwZ : w ∈ D ⊓ Subgroup.centralizer (D : Set G) := Subgroup.mem_inf.mpr ⟨hwD, hwc⟩
  rw [hzc] at hwZ
  rcases eq_one_or_eq_of_mem_zpowers_sq hz2 hwZ with h | h
  · exact absurd h hw1
  · exact h

private theorem map_commutator_le_of_map_le {H K : Subgroup G} {u : G}
    (h : H.map (MulAut.conj u).toMonoidHom ≤ K) :
    (⁅H, H⁆).map (MulAut.conj u).toMonoidHom ≤ ⁅K, K⁆ := by
  rw [map_commutator]
  exact commutator_mono h h

private theorem exists_conj_le_of_isSylowOf_poly {K P Q : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ c ∈ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R P₀
  refine ⟨c, c.2, fun q hq => ?_⟩
  have h1 : MulAut.conj c • (⟨q, hQK hq⟩ : K) ∈ MulAut.conj c • (R : Subgroup K) :=
    smul_mem_pointwise_smul _ (MulAut.conj c) (R : Subgroup K)
      (hR (Subgroup.mem_subgroupOf.mpr hq))
  rw [← Sylow.coe_subgroup_smul, hc, hP₀, Subgroup.mem_subgroupOf] at h1
  exact h1

private theorem exists_conj_extremal_poly {S : Subgroup G} (hS : IsPGroup 2 S) {u v h : G}
    (hv : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G))) (huv : h⁻¹ * v * h = u) :
    ∃ g : G, g⁻¹ * u * g = v ∧
      ∀ c ∈ S ⊓ Subgroup.centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ S ⊓ Subgroup.centralizer ({v} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := S ⊓ Subgroup.centralizer ({u} : Set G)
  set P' : Subgroup G := P.map (MulAut.conj h).toMonoidHom
  have hP'K : P' ≤ Subgroup.centralizer ({v} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcu : c * u = u * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    change h * c * h⁻¹ * v = v * (h * c * h⁻¹)
    have hv' : v = h * u * h⁻¹ := by rw [← huv]; group
    rw [hv']
    calc h * c * h⁻¹ * (h * u * h⁻¹) = h * (c * u) * h⁻¹ := by group
      _ = h * (u * c) * h⁻¹ := by rw [hcu]
      _ = h * u * h⁻¹ * (h * c * h⁻¹) := by group
  have hP' : IsPGroup 2 P' := (hS.to_le inf_le_left).map _
  obtain ⟨c, hcK, hc⟩ :=
    exists_conj_le_of_isSylowOf_poly hv hP'K hP'
  refine ⟨h⁻¹ * c⁻¹, ?_, fun x hx => ?_⟩
  · have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hcK
    rw [← huv]
    calc (h⁻¹ * c⁻¹)⁻¹ * (h⁻¹ * v * h) * (h⁻¹ * c⁻¹) = c * v * c⁻¹ := by group
      _ = v := by rw [hcv]; group
  · have := hc (h * x * h⁻¹) ⟨x, hx, rfl⟩
    rwa [show c * (h * x * h⁻¹) * c⁻¹ =
      (h⁻¹ * c⁻¹)⁻¹ * x * (h⁻¹ * c⁻¹) by group] at this

private theorem conj_mem_center_of_mem_center_map {R S : Subgroup G} {u x : G}
    (hRmap : R.map (MulAut.conj u).toMonoidHom = S)
    (hx : x ∈ R ⊓ Subgroup.centralizer (R : Set G)) :
    u * x * u⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
  have hxR : x ∈ R := hx.1
  have hxC : x ∈ Subgroup.centralizer (R : Set G) := hx.2
  have hxS : u * x * u⁻¹ ∈ S := by
    rw [← hRmap]
    exact Subgroup.mem_map.mpr ⟨x, hxR, by simp [MulAut.conj_apply]⟩
  refine Subgroup.mem_inf.mpr ⟨hxS, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyS : y ∈ R.map (MulAut.conj u).toMonoidHom := by rwa [hRmap]
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hyS
  have hcomm := Subgroup.mem_centralizer_iff.mp hxC y' hy'
  calc (u * y' * u⁻¹) * (u * x * u⁻¹) = u * (y' * x) * u⁻¹ := by group
    _ = u * (x * y') * u⁻¹ := by rw [hcomm]
    _ = (u * x * u⁻¹) * (u * y' * u⁻¹) := by group

private theorem le_centralizer_of_mem_commutator_of_map_conj {S R D₁ D₂ : Subgroup G}
    (hd : DDDecomp S D₁ D₂) (h₁ : IsDihNonab D₁) {u : G}
    (hRmap : R.map (MulAut.conj u).toMonoidHom = S)
    {w : G} (hw : w ∈ ⁅R, R⁆) (hw2 : w * w = 1) :
    R ≤ Subgroup.centralizer ({w} : Set G) := by
  have hmapComm : (⁅R, R⁆).map (MulAut.conj u).toMonoidHom = ⁅S, S⁆ := by
    rw [map_commutator, hRmap]
  have hwS' : u * w * u⁻¹ ∈ ⁅S, S⁆ := by
    have hmem : u * w * u⁻¹ ∈ (⁅R, R⁆).map (MulAut.conj u).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨w, hw, by simp [MulAut.conj_apply]⟩
    rwa [hmapComm] at hmem
  have hwS'2 : (u * w * u⁻¹) * (u * w * u⁻¹) = 1 := by
    have h := congrArg (fun x => u * x * u⁻¹) hw2
    simpa [mul_assoc] using h
  have hcentS : S ≤ Subgroup.centralizer ({u * w * u⁻¹} : Set G) :=
    hd.le_centralizer_of_mem_commutator h₁ hwS' hwS'2
  intro y hy
  have hyS : u * y * u⁻¹ ∈ S := by
    rw [← hRmap]
    exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hcentS hyS)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun z => u⁻¹ * z * u) hcomm
  simpa [mul_assoc] using h

private theorem exists_rotation_decomp {S D₁ D₂ : Subgroup G} (hd : DDDecomp S D₁ D₂)
    (h₁ : IsDihNonab D₁) (g : DihGen D₁) {t : G}
    (htT : t ∈ Subgroup.zpowers (g.a * g.b) ⊔ D₂) (ht2 : t * t = 1)
    (htZ : t ∉ S ⊓ Subgroup.centralizer (S : Set G)) :
    ∃ r ∈ Subgroup.zpowers (g.a * g.b), ∃ s ∈ D₂,
      t = r * s ∧ (∀ y ∈ D₁, y * r = r * y) ∧
        (∃ y ∈ D₂, y * s ≠ s * y) := by
  classical
  have hRle : Subgroup.zpowers (g.a * g.b) ≤ D₁ := g.rotation_le
  have hc : ∀ x ∈ Subgroup.zpowers (g.a * g.b), ∀ y ∈ D₂, x * y = y * x :=
    fun x hx y hy => hd.comm (hRle hx) hy
  obtain ⟨r, hr, s, hs, rfl⟩ :=
    (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer
      (CFSG.CGT.Foote81L6.le_normalizer_of_comm hc)).1 htT
  have hrs2 := (hd.mul_self_iff (hRle hr) hs).mp ht2
  have hrc : ∀ y ∈ D₁, y * r = r * y :=
    central_of_mem_rotation_involution h₁ g hr hrs2.1
  have hnc_s : ∃ y ∈ D₂, y * s ≠ s * y := by
    by_contra h
    apply htZ
    have hs_cent : ∀ y ∈ D₂, y * s = s * y := by
      intro y hy
      by_contra hyc
      exact h ⟨y, hy, hyc⟩
    refine ⟨?_, ?_⟩
    · change r * s ∈ S
      rw [← hd.sup_eq]
      exact mul_mem (Subgroup.mem_sup_left (hRle hr)) (Subgroup.mem_sup_right hs)
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp
          (hd.le_centralizer_mul (hRle hr) hs hrc hs_cent hy)
  exact ⟨r, hr, s, hs, rfl, hrc, hnc_s⟩

private theorem false_of_max_conj_noncentral (𝔖 : Sec3Setting G) {D₁ D₂ : Subgroup G}
    (hd : DDDecomp (𝔖.S : Subgroup G) D₁ D₂) (h₁ : IsDihNonab D₁) (h₂ : IsDihNonab D₂)
    (h38 : ∀ s ∈ (𝔖.S : Subgroup G), ∀ t ∈ (𝔖.S : Subgroup G),
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({s} : Set G) →
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) →
      orderOf s = 2 → IsConj s t → s = t)
    (g : DihGen D₁) {z₂ : G} (hz₂D : z₂ ∈ D₂) (hz₂2 : z₂ * z₂ = 1) (hz₂1 : z₂ ≠ 1)
    (hz₂c : D₂ ⊓ Subgroup.centralizer (D₂ : Set G) = Subgroup.zpowers z₂)
    {t : G} (htT : t ∈ Subgroup.zpowers (g.a * g.b) ⊔ D₂) (htconj : IsConj g.a t)
    (hmax : ∀ y ∈ Subgroup.zpowers (g.a * g.b) ⊔ D₂, IsConj g.a y →
      Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
        Nat.card ↥((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)))
    (htZ : t ∉ (𝔖.S : Subgroup G) ⊓
      Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup G := (𝔖.S : Subgroup G)
  have hS : IsPGroup 2 S := 𝔖.S.isPGroup'
  have hnc_a : ∃ y ∈ D₁, y * g.a ≠ g.a * y := noncentral_of_dihGen h₁ g
  have ha_ord : orderOf g.a = 2 := by
    have ha2pow : g.a ^ 2 = 1 := by rw [pow_two]; exact g.ha2
    exact orderOf_eq_prime ha2pow (by
      intro h
      obtain ⟨y, -, hyc⟩ := hnc_a
      exact hyc (by rw [h, mul_one, one_mul]))
  have ht_ord : orderOf t = 2 := htconj.orderOf_eq.symm.trans ha_ord
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht_ord]; exact pow_orderOf_eq_one t
  obtain ⟨r, hr, s, hs, ht_eq, hrc, hnc_s⟩ :=
    exists_rotation_decomp hd h₁ g htT ht2 htZ
  have hRle : Subgroup.zpowers (g.a * g.b) ≤ D₁ := g.rotation_le
  have hcomm_t : ⁅S ⊓ Subgroup.centralizer ({r * s} : Set G),
      S ⊓ Subgroup.centralizer ({r * s} : Set G)⁆ = ⁅D₁, D₁⁆ :=
    hd.commutator_inf_centralizer_of_central_left (hRle hr) hrc hs hnc_s
  have hcomm_a : ⁅S ⊓ Subgroup.centralizer ({g.a} : Set G),
      S ⊓ Subgroup.centralizer ({g.a} : Set G)⁆ = ⁅D₂, D₂⁆ := by
    simpa using hd.commutator_inf_centralizer_of_central_right h₁ g.ha hnc_a
      (one_mem D₂) (by intro y hy; simp)
  have hz₂_cent : ∀ y ∈ D₂, y * z₂ = z₂ * y := by
    intro y hy
    have hZ : z₂ ∈ D₂ ⊓ Subgroup.centralizer (D₂ : Set G) := by
      rw [hz₂c]; exact Subgroup.mem_zpowers z₂
    exact Subgroup.mem_centralizer_iff.mp hZ.2 y hy
  have hz₂D' : z₂ ∈ ⁅D₂, D₂⁆ := h₂.mem_commutator_of_central hz₂D hz₂1 hz₂_cent
  have hz₁D' : g.z ∈ ⁅D₁, D₁⁆ := h₁.mem_commutator_of_central g.hz g.hz1 g.hz_central
  have hz₁S : g.z ∈ S := hd.le_left g.hz
  have hz₂S : z₂ ∈ S := hd.le_right hz₂D
  have hz₁_ord : orderOf g.z = 2 := by
    have h2 : g.z ^ 2 = 1 := by rw [pow_two]; exact g.hz2
    exact orderOf_eq_prime h2 g.hz1
  have hz₂_ord : orderOf z₂ = 2 := by
    have h2 : z₂ ^ 2 = 1 := by rw [pow_two]; exact hz₂2
    exact orderOf_eq_prime h2 hz₂1
  have hz₁Z : g.z ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
    rw [hd.inf_centralizer_self, g.hz_center, hz₂c]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g.z)
  have hz₂Z : z₂ ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
    rw [hd.inf_centralizer_self, g.hz_center, hz₂c]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂)
  have hS_z₁ : S ≤ Subgroup.centralizer ({g.z} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁Z.2 y hy)
  have hS_z₂ : S ≤ Subgroup.centralizer ({z₂} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₂Z.2 y hy)
  have hz₁z₂_ne : g.z ≠ z₂ := by
    intro h
    have hmem : g.z ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.mpr ⟨g.hz, h ▸ hz₂D⟩
    rw [hd.inf_eq] at hmem
    exact g.hz1 (Subgroup.mem_bot.mp hmem)
  have hExt := extremal_disjunction 𝔖 hd h₁ h₂ g hz₂D hz₂_ord hz₂c htT htconj hmax htZ
  rcases hExt with hExtA | hExtT
  ·
    obtain ⟨c, hc⟩ := isConj_iff.mp htconj.symm
    have hca : c⁻¹ * g.a * c = t := by rw [← hc]; group
    obtain ⟨u, hu, huC⟩ := exists_conj_extremal_poly hS hExtA (h := c) hca
    have hleC : (S ⊓ Subgroup.centralizer ({t} : Set G)).map
        (MulAut.conj (u⁻¹)).toMonoidHom ≤ S ⊓ Subgroup.centralizer ({g.a} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using huC x hx
    have hleD := map_commutator_le_of_map_le hleC
    have hzder : u⁻¹ * g.z * u ∈ ⁅S ⊓ Subgroup.centralizer ({g.a} : Set G),
        S ⊓ Subgroup.centralizer ({g.a} : Set G)⁆ := by
      refine hleD ?_
      exact Subgroup.mem_map.mpr ⟨g.z, by rw [ht_eq, hcomm_t]; exact hz₁D', by simp [MulAut.conj_apply]⟩
    rw [hcomm_a] at hzder
    have hw2 : (u⁻¹ * g.z * u) * (u⁻¹ * g.z * u) = 1 := by
      have h := congrArg (fun x => u⁻¹ * x * u) g.hz2
      simpa [mul_assoc] using h
    have hw1 : u⁻¹ * g.z * u ≠ 1 := by
      intro h
      apply g.hz1
      have := congrArg (fun x => u * x * u⁻¹) h
      simpa [mul_assoc] using this
    have hwz : u⁻¹ * g.z * u = z₂ :=
      eq_center_of_mem_commutator_involution h₂ hz₂D hz₂2 hz₂1 hz₂c hzder hw2 hw1
    have hconjz : IsConj g.z z₂ := isConj_iff.mpr ⟨u⁻¹, by simpa using hwz⟩
    have hEq := h38 g.z hz₁S z₂ hz₂S hS_z₁ hS_z₂ hz₁_ord hconjz
    exact hz₁z₂_ne hEq
  ·
    obtain ⟨c, hc⟩ := isConj_iff.mp htconj
    have hca : c⁻¹ * t * c = g.a := by rw [← hc]; group
    obtain ⟨u, hu, huC⟩ := exists_conj_extremal_poly hS hExtT (h := c) hca
    have hleC : (S ⊓ Subgroup.centralizer ({g.a} : Set G)).map
        (MulAut.conj (u⁻¹)).toMonoidHom ≤ S ⊓ Subgroup.centralizer ({t} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using huC x hx
    have hleD := map_commutator_le_of_map_le hleC
    have hzder : u⁻¹ * z₂ * u ∈ ⁅S ⊓ Subgroup.centralizer ({t} : Set G),
        S ⊓ Subgroup.centralizer ({t} : Set G)⁆ := by
      refine hleD ?_
      exact Subgroup.mem_map.mpr ⟨z₂, by rw [hcomm_a]; exact hz₂D', by simp [MulAut.conj_apply]⟩
    rw [ht_eq, hcomm_t] at hzder
    have hz₂2' : z₂ * z₂ = 1 := hz₂2
    have hw2 : (u⁻¹ * z₂ * u) * (u⁻¹ * z₂ * u) = 1 := by
      have h := congrArg (fun x => u⁻¹ * x * u) hz₂2
      simpa [mul_assoc] using h
    have hw1 : u⁻¹ * z₂ * u ≠ 1 := by
      intro h
      apply hz₂1
      have := congrArg (fun x => u * x * u⁻¹) h
      simpa [mul_assoc] using this
    have hwz : u⁻¹ * z₂ * u = g.z :=
      eq_center_of_mem_commutator_involution h₁ g.hz g.hz2 g.hz1 g.hz_center hzder hw2 hw1
    have hconjz : IsConj z₂ g.z := isConj_iff.mpr ⟨u⁻¹, by simpa using hwz⟩
    have hEq := h38 z₂ hz₂S g.z hz₁S hS_z₂ hS_z₁ hz₂_ord hconjz
    exact hz₁z₂_ne hEq.symm

private theorem exists_correction_of_reflection (𝔖 : Sec3Setting G) {D₁ D₂ : Subgroup G}
    (hd : DDDecomp (𝔖.S : Subgroup G) D₁ D₂) (h₁ : IsDihNonab D₁) (h₂ : IsDihNonab D₂)
    (h38 : ∀ s ∈ (𝔖.S : Subgroup G), ∀ t ∈ (𝔖.S : Subgroup G),
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({s} : Set G) →
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) →
      orderOf s = 2 → IsConj s t → s = t)
    (g : DihGen D₁) {z₂ : G} (hz₂D : z₂ ∈ D₂) (hz₂2 : z₂ * z₂ = 1)
    (hz₂1 : z₂ ≠ 1)
    (hz₂c : D₂ ⊓ Subgroup.centralizer (D₂ : Set G) = Subgroup.zpowers z₂) :
    ∃ ε ∈ D₂, (∀ d ∈ D₂, d * ε = ε * d) ∧ ε * ε = 1 ∧
      ConjIn (Subgroup.centralizer ({z₂} : Set G)) (g.a * ε) g.z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup G := (𝔖.S : Subgroup G)
  have hS : IsPGroup 2 S := 𝔖.S.isPGroup'
  have hnc_a : ∃ y ∈ D₁, y * g.a ≠ g.a * y := noncentral_of_dihGen h₁ g
  have ha1 : g.a ≠ 1 := by
    intro h
    obtain ⟨y, -, hyc⟩ := hnc_a
    exact hyc (by rw [h, one_mul, mul_one])
  obtain ⟨t, htT, htconj, hmax⟩ := exists_max_conj_in_rotation 𝔖 hd h₁ g
  by_cases htZ : t ∈ S ⊓ Subgroup.centralizer (S : Set G)
  ·
    have hS_le_Ct : S ≤ Subgroup.centralizer ({t} : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp htZ.2 y hy)
    have hS_syl_top : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := isSylowOf_top_of_sylow 𝔖
    have hS_syl_Ct : CFSG.ABGLocalTools.IsSylowOf 2 S
        (Subgroup.centralizer ({t} : Set G)) :=
      isSylowOf_centralizer_of_central hS_syl_top hS_le_Ct
    obtain ⟨R, hR_syl_Ca, hCaR⟩ := exists_sylow_centralizer_containing hS (a := g.a)
    have hRnotdvd : ¬ 2 ∣ R.index :=
      index_odd_of_isSylow_centralizers hR_syl_Ca hS_syl_Ct htconj 𝔖.S.not_dvd_index
    let Rsyl : Sylow 2 G := IsPGroup.toSylow (p := 2) hR_syl_Ca.isPGroup
      (by simpa [Subgroup.relIndex_top_right] using hRnotdvd)
    have hRsyl_coe : (Rsyl : Subgroup G) = R :=
      IsPGroup.toSylow_coe hR_syl_Ca.isPGroup
        (by simpa [Subgroup.relIndex_top_right] using hRnotdvd)
    obtain ⟨gconj, hgconj⟩ := MulAction.exists_smul_eq G Rsyl 𝔖.S
    have hRmap : R.map (MulAut.conj gconj).toMonoidHom = S := by
      have h1 := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hgconj
      rw [Sylow.coe_subgroup_smul] at h1
      rw [hRsyl_coe] at h1
      change R.map (MulAut.conj gconj).toMonoidHom = S at h1
      simpa using h1
    have hz₂Z : z₂ ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
      rw [hd.inf_centralizer_self, g.hz_center, hz₂c]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂)
    have hz₂S : z₂ ∈ S := hd.le_right hz₂D
    have hz₂comm_a : z₂ * g.a = g.a * z₂ :=
      (Subgroup.mem_centralizer_iff.mp hz₂Z.2 g.a (hd.le_left g.ha)).symm
    have hz₂Ca : z₂ ∈ S ⊓ Subgroup.centralizer ({g.a} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hz₂S, Subgroup.mem_centralizer_singleton_iff.mpr hz₂comm_a⟩
    have hz₂R : z₂ ∈ R := hCaR hz₂Ca
    have haCa : g.a ∈ S ⊓ Subgroup.centralizer ({g.a} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hd.le_left g.ha,
        Subgroup.mem_centralizer_singleton_iff.mpr (by rfl)⟩
    have haR : g.a ∈ R := hCaR haCa
    have hcomm_a : ⁅S ⊓ Subgroup.centralizer ({g.a} : Set G),
        S ⊓ Subgroup.centralizer ({g.a} : Set G)⁆ = ⁅D₂, D₂⁆ := by
      simpa using hd.commutator_inf_centralizer_of_central_right h₁ g.ha hnc_a
        (one_mem D₂) (by intro y hy; simp)
    have hz₂_cent : ∀ y ∈ D₂, y * z₂ = z₂ * y := by
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hz₂Z.2 y (hd.le_right hy)
    have hz₂D' : z₂ ∈ ⁅D₂, D₂⁆ := h₂.mem_commutator_of_central hz₂D hz₂1 hz₂_cent
    have hz₂Ca' : z₂ ∈ ⁅S ⊓ Subgroup.centralizer ({g.a} : Set G),
        S ⊓ Subgroup.centralizer ({g.a} : Set G)⁆ := by
      rw [hcomm_a]; exact hz₂D'
    have hz₂R' : z₂ ∈ ⁅R, R⁆ := commutator_mono hCaR hCaR hz₂Ca'
    have hz₂centR : R ≤ Subgroup.centralizer ({z₂} : Set G) :=
      le_centralizer_of_mem_commutator_of_map_conj hd h₁ hRmap hz₂R' hz₂2
    have hz₂ZR : z₂ ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hz₂R, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hz₂centR hy)
    have haZR : g.a ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨haR, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hR_syl_Ca.le hy)
    have hz₂gZ : gconj * z₂ * gconj⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set G) :=
      conj_mem_center_of_mem_center_map hRmap hz₂ZR
    have hz₂g_eq : gconj * z₂ * gconj⁻¹ = z₂ := by
      have hconjz : IsConj z₂ (gconj * z₂ * gconj⁻¹) := isConj_iff.mpr ⟨gconj, rfl⟩
      exact (h38 z₂ hz₂S (gconj * z₂ * gconj⁻¹) hz₂gZ.1
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hz₂Z.2 y hy))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hz₂gZ.2 y hy))
        (orderOf_eq_prime (by rw [pow_two]; exact hz₂2) hz₂1) hconjz).symm
    have hagZ : gconj * g.a * gconj⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set G) :=
      conj_mem_center_of_mem_center_map hRmap haZR
    have hag2 : (gconj * g.a * gconj⁻¹) * (gconj * g.a * gconj⁻¹) = 1 := by
      have h := congrArg (fun x => gconj * x * gconj⁻¹) g.ha2
      simpa [mul_assoc] using h
    have hag1 : gconj * g.a * gconj⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have := congrArg (fun x => gconj⁻¹ * x * gconj) h
      simpa [mul_assoc] using this
    have hz₁S : g.z ∈ S := hd.le_left g.hz
    have hS_z₁ : S ≤ Subgroup.centralizer ({g.z} : Set G) := by
      intro y hy
      have hz₁Z : g.z ∈ S ⊓ Subgroup.centralizer (S : Set G) := by
        rw [hd.inf_centralizer_self, g.hz_center, hz₂c]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g.z)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₁Z.2 y hy)
    have hS_z₂ : S ≤ Subgroup.centralizer ({z₂} : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₂Z.2 y hy)
    have hcomm12 : Commute g.z z₂ :=
      Subgroup.mem_centralizer_iff.mp hz₂Z.2 g.z hz₁S
    have hcommZ : ∀ x ∈ Subgroup.zpowers g.z, ∀ y ∈ Subgroup.zpowers z₂, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (hcomm12.zpow_zpow m n).eq
    have hag_mem : gconj * g.a * gconj⁻¹ ∈
        Subgroup.zpowers g.z ⊔ Subgroup.zpowers z₂ := by
      rw [hd.inf_centralizer_self, g.hz_center, hz₂c] at hagZ
      exact hagZ
    have hcases := mem_sup_zpowers_involution g.hz2 hz₂2 hcommZ hag_mem hag2
    have hdisj : gconj * g.a * gconj⁻¹ = g.z ∨
        gconj * (g.a * z₂) * gconj⁻¹ = g.z := by
      rcases hcases with h | h | h | h
      · exact absurd h hag1
      · exact Or.inl h
      · exfalso
        have h1 : gconj * (g.a * z₂) * gconj⁻¹ = 1 := by
          calc gconj * (g.a * z₂) * gconj⁻¹ =
              (gconj * g.a * gconj⁻¹) * (gconj * z₂ * gconj⁻¹) := by group
            _ = z₂ * z₂ := by rw [h, hz₂g_eq]
            _ = 1 := hz₂2
        have haz : g.a = z₂ := by
          have hza : g.a * z₂ = 1 := by
            have := congrArg (fun x => gconj⁻¹ * x * gconj) h1
            simpa [mul_assoc] using this
          calc g.a = g.a * 1 := (mul_one _).symm
            _ = g.a * (z₂ * z₂) := by rw [hz₂2]
            _ = (g.a * z₂) * z₂ := by group
            _ = 1 * z₂ := by rw [hza]
            _ = z₂ := one_mul _
        have hmem : g.a ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.mpr ⟨g.ha, haz ▸ hz₂D⟩
        rw [hd.inf_eq] at hmem
        exact ha1 (Subgroup.mem_bot.mp hmem)
      · right
        calc gconj * (g.a * z₂) * gconj⁻¹ =
            (gconj * g.a * gconj⁻¹) * (gconj * z₂ * gconj⁻¹) := by group
          _ = (g.z * z₂) * z₂ := by rw [h, hz₂g_eq]
          _ = g.z := by rw [mul_assoc, hz₂2, mul_one]
    have hCg : gconj ∈ Subgroup.centralizer ({z₂} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc gconj * z₂ = (gconj * z₂ * gconj⁻¹) * gconj := by group
        _ = z₂ * gconj := by rw [hz₂g_eq]
    rcases hdisj with h | h
    · refine ⟨1, one_mem D₂, ?_, ?_, ⟨gconj, hCg, by simpa using h⟩⟩
      · intro d hd; simp
      · simp
    · exact ⟨z₂, hz₂D, hz₂_cent, hz₂2, ⟨gconj, hCg, by simpa using h⟩⟩
  · exact absurd (false_of_max_conj_noncentral 𝔖 hd h₁ h₂ h38 g hz₂D hz₂2 hz₂1 hz₂c
      htT htconj hmax htZ) (by simp)

theorem lemma_3_9 (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧
      (∀ x ∈ S₁', ∀ y ∈ S₁', orderOf x = 2 → orderOf y = 2 →
        ∃ g ∈ Subgroup.centralizer
          ((S₂' ⊓ Subgroup.centralizer (S₂' : Set G) : Subgroup G) : Set G),
          g * x * g⁻¹ = y) ∧
      (∀ x ∈ S₂', ∀ y ∈ S₂', orderOf x = 2 → orderOf y = 2 →
        ∃ g ∈ Subgroup.centralizer
          ((S₁' ⊓ Subgroup.centralizer (S₁' : Set G) : Subgroup G) : Set G),
          g * x * g⁻¹ = y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₁⟩ := exists_dihGen h₁
  obtain ⟨g₂⟩ := exists_dihGen 𝔖.decomp.dih₂
  have h38 : ∀ s ∈ (𝔖.S : Subgroup G), ∀ t ∈ (𝔖.S : Subgroup G),
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({s} : Set G) →
      (𝔖.S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) →
      orderOf s = 2 → IsConj s t → s = t :=
    lemma_3_8 𝔖 h₁
  obtain ⟨ε₁, hε₁D, hε₁c, hε₁2, hconj₁⟩ :=
    exists_correction_of_reflection 𝔖 𝔖.decomp h₁ 𝔖.decomp.dih₂ h38 g₁
      g₂.hz g₂.hz2 g₂.hz1 g₂.hz_center
  obtain ⟨ε₂, hε₂D, hε₂c, hε₂2, hconj₂⟩ :=
    exists_correction_of_reflection 𝔖 𝔖.decomp h₁ 𝔖.decomp.dih₂ h38 g₁.swap
      g₂.hz g₂.hz2 g₂.hz1 g₂.hz_center
  let U : Subgroup G := Subgroup.closure {g₁.a * ε₁, g₁.b * ε₂}
  have hU : U = Subgroup.closure {g₁.a * ε₁, g₁.b * ε₂} := rfl
  obtain ⟨hdU, -, hU_dih, hcenterU, -⟩ :=
    corrected_factor_left 𝔖 h₁ g₁.hk g₁.ha g₁.hb g₁.ha2 g₁.hb2 g₁.hgen
      g₁.hz g₁.hz2 g₁.hz1 g₁.hz_center g₁.hz_ab g₂.hz hε₁D hε₂D hε₁c hε₂c
      hε₁2 hε₂2 hU hconj₁ hconj₂
  have hz₁U : g₁.z ∈ U := by
    have hmem : g₁.z ∈ U ⊓ Subgroup.centralizer (U : Set G) := by
      rw [hcenterU]
      exact Subgroup.mem_zpowers g₁.z
    exact hmem.1
  have hdS₂U : DDDecomp (𝔖.S : Subgroup G) 𝔖.S₂ U := ddSwap hdU hU_dih
  obtain ⟨ε₃, hε₃U, hε₃c, hε₃2, hconj₃⟩ :=
    exists_correction_of_reflection 𝔖 hdS₂U 𝔖.decomp.dih₂ hU_dih h38 g₂
      hz₁U g₁.hz2 g₁.hz1 hcenterU
  obtain ⟨ε₄, hε₄U, hε₄c, hε₄2, hconj₄⟩ :=
    exists_correction_of_reflection 𝔖 hdS₂U 𝔖.decomp.dih₂ hU_dih h38 g₂.swap
      hz₁U g₁.hz2 g₁.hz1 hcenterU
  let V : Subgroup G := Subgroup.closure {g₂.a * ε₃, g₂.b * ε₄}
  have hV : V = Subgroup.closure {g₂.a * ε₃, g₂.b * ε₄} := rfl
  exact lemma_3_9_of_correction_data 𝔖 h₁ g₁.hk g₁.ha g₁.hb g₁.ha2 g₁.hb2 g₁.hgen
    g₁.hz g₁.hz2 g₁.hz1 g₁.hz_center g₁.hz_ab g₂.hz hε₁D hε₂D hε₁c hε₂c hε₁2 hε₂2
    hU hconj₁ hconj₂ g₂.hk g₂.ha g₂.hb g₂.ha2 g₂.hb2 g₂.hgen g₂.hz2 g₂.hz1
    g₂.hz_center g₂.hz_ab hε₃U hε₄U hε₃c hε₄c hε₃2 hε₄2 hV hconj₃ hconj₄

end Sec3Setting

end CFSG.GH72
