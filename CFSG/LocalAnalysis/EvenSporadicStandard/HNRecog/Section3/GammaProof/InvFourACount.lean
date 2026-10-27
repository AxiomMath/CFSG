module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Orders

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem invFourACount_card_elem2_two : Nat.card (Elem2 2) = 4 := by
  change Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem invFourACount_card_shape_s4 {X : Type*} [Group X]
    (h : IsShapeTwoTwoTimesS4 X) : Nat.card X = 96 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, invFourACount_card_elem2_two, Nat.card_perm,
    Nat.card_fin]
  norm_num

private theorem invFourACount_fourA_setup (H : GammaHyps a z) {y zz b : G}
    (hy : y ∈ orb4A a z a) (hzz : zz = (a * y) ^ 2) (hb : b = zz * y) :
    IsConj a b ∧ b * y = zz ∧ y * b = zz ∧ IsConj a (y * zz) ∧ y * zz = zz * y ∧
      y * zz = b ∧ orderOf (a * y) = 4 := by
  have hyA : IsConj a y := hy.1
  have ha2 : a ^ 2 = 1 := H.sq_a (IsConj.refl a)
  have hy2 : y ^ 2 = 1 := H.sq_a hyA
  have hy2' : y * y = 1 := H.mul_self_a hyA
  have hord : orderOf (a * y) = 4 := tableV_orderOf_orb4A H.h hy
  obtain ⟨-, hyy, -, hcc⟩ :=
    tableV_dihedral ha2 hy2 hyA (m := 2) (by rw [hord])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hord⟩
  · rw [hb, hzz, ← hyy]
    exact hcc
  · rw [hb, hzz, mul_assoc, hy2', mul_one]
  · rw [hb, hzz, ← mul_assoc, hyy, mul_assoc, hy2', mul_one]
  · rw [hzz]
    exact hcc
  · rw [hzz]
    exact hyy
  · rw [hb, hzz]
    exact hyy

private lemma invFourACount_inf_leq (a b y t : G) :
    Gxy a y ⊓ Gxyz b y t ≤ Gxyz a y t := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [mem_Gxyz] at hg ⊢
  exact ⟨(mem_Gxy.mp hg.1).1, hg.2.2⟩

theorem gamma_card_fourB_five (H : GammaHyps a z) {b x y : G} (hb : IsConj a b)
    (hx : x ∈ orb4B a b) (hy : y ∈ orb2A a x ∩ orb2B a z b) : Nat.card ↥(Gxyz b y x) = 96 := by
  have F : FourBFacts b z := H.h4B b z hb (IsConj.refl z)
  have hx' : x ∈ orb4B b b := (gamma_orb4B_eq hb b).symm ▸ hx
  have hP := F.classes x hx'
  have hy5 : y ∈ fourBSet b z x 5 := by
    show y ∈ orb2A b x ∩ orb2B b z b
    exact ⟨(gamma_orb2A_eq hb x).symm ▸ hy.1, (gamma_orb2B_eq hb z b).symm ▸ hy.2⟩
  obtain ⟨t, ht6⟩ := (hP.orbit 6).nonempty
  have ht6' : t ∈ orb2AB b z x ∩ orb2BB b z b := ht6
  obtain ⟨ht'mem, hGxyz_eq, hshape⟩ := F.case_iii x hx' t ht6'
  have ht'5 : t * (b * x) ^ 2 ∈ fourBSet b z x 5 := ht'mem
  obtain ⟨k, hk_mem, hk_eq⟩ := (hP.orbit 5).transitive (t * (b * x) ^ 2) ht'5 y hy5
  let φ : G ≃* G := MulAut.conj k
  have hφt' : φ (t * (b * x) ^ 2) = y := by
    show MulAut.conj k (t * (b * x) ^ 2) = y
    rw [MulAut.conj_apply]
    exact hk_eq
  have hφb : φ b = b := by
    have hbk : b * k = k * b := mem_Gx.mp (mem_Gxy.mp hk_mem).1
    show MulAut.conj k b = b
    rw [MulAut.conj_apply, ← hbk]
    group
  have hφx : φ x = x := by
    have hxk : x * k = k * x := mem_Gx.mp (mem_Gxy.mp hk_mem).2
    show MulAut.conj k x = x
    rw [MulAut.conj_apply, ← hxk]
    group
  have hmap : (Gxyz b (t * (b * x) ^ 2) x).map φ.toMonoidHom = Gxyz b y x := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mem_Gxyz] at hu ⊢
      obtain ⟨hu1, hu2, hu3⟩ := hu
      refine ⟨mem_Gx.mpr ?_, mem_Gx.mpr ?_, mem_Gx.mpr ?_⟩
      · have h := congrArg φ (mem_Gx.mp hu1)
        simpa [map_mul, hφb] using h
      · have h := congrArg φ (mem_Gx.mp hu2)
        simpa [map_mul, hφt'] using h
      · have h := congrArg φ (mem_Gx.mp hu3)
        simpa [map_mul, hφx] using h
    · intro hg
      have hψb : φ.symm b = b := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, hφb]
      have hψt' : φ.symm y = t * (b * x) ^ 2 := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, hφt']
      have hψx : φ.symm x = x := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, hφx]
      refine ⟨φ.symm g, ?_, φ.apply_symm_apply g⟩
      rw [mem_Gxyz] at hg ⊢
      obtain ⟨hg1, hg2, hg3⟩ := hg
      refine ⟨mem_Gx.mpr ?_, mem_Gx.mpr ?_, mem_Gx.mpr ?_⟩
      · have h := congrArg φ.symm (mem_Gx.mp hg1)
        simpa [map_mul, hψb] using h
      · have h := congrArg φ.symm (mem_Gx.mp hg2)
        simpa [map_mul, hψt'] using h
      · have h := congrArg φ.symm (mem_Gx.mp hg3)
        simpa [map_mul, hψx] using h
  have hcard_eq : Nat.card ↥(Gxyz b y x) = Nat.card ↥(Gxyz b (t * (b * x) ^ 2) x) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (K := Gxyz b (t * (b * x) ^ 2) x)
      (f := φ.toMonoidHom) φ.injective
  rw [hcard_eq, ← hGxyz_eq]
  exact invFourACount_card_shape_s4 hshape

theorem gamma_fourA_row4B (H : GammaHyps a z) {y t : G} (hy : y ∈ orb4A a z a)
    (ht : t ∈ orb2A a y) (htb : t ∈ orb4B a ((a * y) ^ 2 * y)) :
    ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  let zz : G := (a * y) ^ 2
  let b : G := zz * y
  obtain ⟨hbA, hb_mul_y, hy_mul_b, -, -, -, -⟩ :=
    invFourACount_fourA_setup (zz := zz) (b := b) H hy rfl rfl
  have hyA : IsConj a y := hy.1
  have hzzZ : IsConj z zz := hy.2
  have hy_2At : y ∈ orb2A a t := H.orb2A_symm hy.1 ht
  have hy_2Bb : y ∈ orb2B a z b := ⟨hyA, by rw [hb_mul_y]; exact hzzZ⟩
  have hcardY : Nat.card ↥(Gxyz b y t) = 96 :=
    gamma_card_fourB_five H (b := b) (x := t) (y := y) hbA htb ⟨hy_2At, hy_2Bb⟩
  have hb' : b ∈ orb2B y z y := by
    refine ⟨hyA.symm.trans hbA, ?_⟩
    rw [hy_mul_b]
    exact hzzZ
  have hXcard : Nat.card ↥(Gxy a y) = 640 := by
    have hmem : y ∈ tab5Set a z 2 := by simpa [tab5Set] using hy
    rw [Gxy_eq_inf]
    simpa using (H.hT5.self).card_stab 2 y hmem
  have hZcard : Nat.card ↥(Gxy y b) = 30720 := by
    have hmem : b ∈ tab5Set y z 1 := by simpa [tab5Set] using hb'
    rw [Gxy_eq_inf]
    simpa using (H.hT5 y z hy.1 (IsConj.refl z)).card_stab 1 b hmem
  have hXZ : Gxy a y ≤ Gxy y b := by
    intro g hg
    rw [mem_Gxy] at hg ⊢
    obtain ⟨hga, hgy⟩ := hg
    have hga' : Commute a g := mem_Gx.mp hga
    have hgy' : Commute y g := mem_Gx.mp hgy
    refine ⟨hgy, ?_⟩
    rw [mem_Gx]
    have hgzz : Commute zz g := (hga'.mul_left hgy').pow_left 2
    exact hgzz.mul_left hgy'
  have hY : Gxyz b y t ≤ Gxy y b := by
    intro g hg
    rw [mem_Gxyz] at hg
    rw [mem_Gxy]
    exact ⟨hg.2.1, hg.1⟩
  have hlt : Nat.card ↥(Gxy y b) < Nat.card ↥(Gxy a y) * Nat.card ↥(Gxyz b y t) := by
    rw [hZcard, hXcard, hcardY]
    norm_num
  have hk : Nat.gcd (Nat.card ↥(Gxy a y)) (Nat.card ↥(Gxyz b y t)) ∣ 2 ^ 5 := by
    rw [hXcard, hcardY]
    norm_num
  obtain ⟨s, hs, hso⟩ :=
    gamma_exists_inv_of_card_lt (X := Gxy a y) (Y := Gxyz b y t) (Z := Gxy y b)
      hXZ hY hlt (k := 5) hk
  exact ⟨s, hso, invFourACount_inf_leq a b y t hs⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
