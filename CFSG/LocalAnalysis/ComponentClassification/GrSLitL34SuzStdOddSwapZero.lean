module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapDefs
public import CFSG.LocalAnalysis.ComponentClassification.Walter86.Asc75.L97Prep
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

theorem le_centralizer_of_forall_map_conj_eq_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P) :
    V ≤ centralizer (P : Set G) := by
  have _ : u ∈ V ∧ u ≠ 1 := ⟨hu, hu1⟩
  intro v hv
  have hE := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD
  have hvK : v ∈ centralizer (K : Set G) := (le_inf_iff.mp hE).2 (mem_sup_left hv)
  have hperf : Group.IsPerfect ↥P := by
    exact @Group.IsPerfect.ofSurjective ↥(P.subgroupOf (centralizer ({u} : Set G))) ↥P _ _
      (Subgroup.subgroupOfEquivOfLe hPu).toMonoidHom hcomp.1.1
      (Subgroup.subgroupOfEquivOfLe hPu).surjective
  exact HarrisLit.mem_centralizer_of_map_conj_eq hc hperf (hfix v hv)
    (Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)) (hK ▸ hvK)

theorem mem_centralizer_of_forall_map_conj_eq_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P) :
    y ∈ centralizer (P : Set G) := by
  let C : Subgroup G := centralizer ({u} : Set G)
  let X : Subgroup G := centralizer (V : Set G)
  have hVle : V ≤ centralizer (P : Set G) :=
    le_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK hfix
  have hPV : P ≤ X := Subgroup.le_centralizer_iff.mp hVle
  have hCX : X ≤ C := by
    refine Subgroup.centralizer_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hu
  have hPI : CGT.PushingUpLit.CGT6.Nine7.IsCompIn P C :=
    HarrisLit.isCompIn_of_isComponent hPu hcomp
  have hPIX : CGT.PushingUpLit.CGT6.Nine7.IsCompIn P X := hPI.of_le hPV hCX
  have hyt : y * t = t * y :=
    Subgroup.mem_centralizer_iff.1 hS.t_mem y hD.y_mem
  have hyV : V.map (MulAut.conj y).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hD.y_normalizes
  have hconjV : CFSG.conjugate V y⁻¹ = V := by
    rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv V y]
    exact hyV
  have hXmap : X.map (MulAut.conj y).toMonoidHom = X := by
    rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
      CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer, hconjV]
  have htV : t ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
  have hconjVt : CFSG.conjugate V t⁻¹ = V := by
    rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv V t]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer (V : Set G)) htV)
  have hXmapt : X.map (MulAut.conj t).toMonoidHom = X := by
    rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
      CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer, hconjVt]
  have htX : t ∈ normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hXmapt
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.orderOf_t, pow_orderOf_eq_one]
  have hQIY : CGT.PushingUpLit.CGT6.Nine7.IsCompIn
      (P.map (MulAut.conj y).toMonoidHom) X := by
    have h := hPIX.cj y⁻¹
    rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv P y,
      ← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv X y, hXmap] at h
    exact h
  have hcQ := HarrisLit.map_conj_le_centralizer_map hyt hc
  have hyK : K.map (MulAut.conj y).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer (K : Set G)) hD.y_centralizes)
  have heq : (HarrisLit.swapDiag (P.map (MulAut.conj y).toMonoidHom) t hcQ).range =
      (HarrisLit.swapDiag P t hc).range := by
    rw [HarrisLit.range_swapDiag_map_conj hyt hc, ← hK, hyK]
  have hnab : ∃ a ∈ (HarrisLit.swapDiag P t hc).range,
      ∃ b ∈ (HarrisLit.swapDiag P t hc).range, a * b ≠ b * a := by
    obtain ⟨a, haK, b, hbK, hab⟩ := exists_ne_of_l34SuzOdd hD
    exact ⟨a, hK ▸ haK, b, hK ▸ hbK, hab⟩
  have hmap_comp : ∀ (a b : G) (Q : Subgroup G),
      (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        Q.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b Q
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  rcases HarrisLit.eq_or_eq_map_of_range_swapDiag_eq ht2 htX hPIX hQIY hc hcQ heq hnab with
    h | h
  · have hperf : Group.IsPerfect ↥P := by
      exact @Group.IsPerfect.ofSurjective ↥(P.subgroupOf (centralizer ({u} : Set G))) ↥P _ _
        (Subgroup.subgroupOfEquivOfLe hPu).toMonoidHom hcomp.1.1
        (Subgroup.subgroupOfEquivOfLe hPu).surjective
    exact HarrisLit.mem_centralizer_of_map_conj_eq hc hperf h hyt (hK ▸ hD.y_centralizes)
  · have htt : t * t = 1 := by rw [← pow_two, ht2]
    have h2 : P.map (MulAut.conj (t * y)).toMonoidHom = P := by
      calc P.map (MulAut.conj (t * y)).toMonoidHom
          = (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
            (hmap_comp y t P).symm
        _ = (P.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by rw [h]
        _ = P.map (MulAut.conj (t * t)).toMonoidHom := hmap_comp t t P
        _ = P.map (MulAut.conj (1 : G)).toMonoidHom := by rw [htt]
        _ = P := by
          rw [show MulAut.conj (1 : G) = 1 by ext x; simp]
          exact Subgroup.map_id P
    have hsq : P.map (MulAut.conj (y * y)).toMonoidHom = P := by
      have h1 : P.map (MulAut.conj (y * y)).toMonoidHom =
          P.map (MulAut.conj (y * t)).toMonoidHom := by
        calc P.map (MulAut.conj (y * y)).toMonoidHom
            = (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom :=
              (hmap_comp y y P).symm
          _ = (P.map (MulAut.conj t).toMonoidHom).map (MulAut.conj y).toMonoidHom := by rw [h]
          _ = P.map (MulAut.conj (y * t)).toMonoidHom := hmap_comp t y P
      rw [h1, hyt, h2]
    have hyP : P.map (MulAut.conj y).toMonoidHom = P := by
      have hy : y ∈ Subgroup.zpowers (y ^ 2) :=
        mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hD.odd_orderOf_y)
      have hy2N : y ^ 2 ∈ normalizer (P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [pow_two] using hsq)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.zpowers_le.mpr hy2N hy)
    exact (hne (h.symm.trans hyP)).elim

theorem odd_card_center_of_forall_map_conj_eq_of_l34SuzOdd
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P) :
    Odd (Nat.card (center ↥P)) := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hEven)
  let zP : ↥P := (x : ↥P)
  have hzP : (zP : G) ∈ P := zP.2
  have hz2 : orderOf zP = 2 := (Subgroup.orderOf_coe x).trans hx2
  have hzG2 : orderOf (zP : G) = 2 := (Subgroup.orderOf_coe zP).trans hz2
  have hzsq : zP * zP = 1 := by
    rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzsqG : (zP : G) * (zP : G) = 1 := congrArg Subtype.val hzsq
  have hzc : (zP : G) ∈ centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨p, hp⟩)
  have hzE := mem_sup_zpowers_of_mem_center_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK
    hzP hzc hzsqG
  have hcommE : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers t, Commute a b := by
    intro a ha b hb
    rw [Subgroup.mem_zpowers_iff] at hb
    obtain ⟨n, rfl⟩ := hb
    exact (commute_iff_eq a t).mpr
      (Subgroup.mem_centralizer_iff.1 hS.t_mem a (hD.le_A ha)) |>.zpow_right n
  obtain ⟨v, hvV, w, hw, hvw⟩ := (CFSG.mem_sup_of_commute hcommE).mp hzE
  have hzG1 : (zP : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzG2
    exact absurd hzG2 (by norm_num)
  rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t hS.orderOf_t w).1 hw
    with hw1 | hw1
  · have hzV : (zP : G) ∈ V := by
      rw [← hvw, hw1]
      simpa using hvV
    have hyP := mem_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp
      hne hK hfix
    have hcomm := Subgroup.mem_centralizer_iff.1 hyP (zP : G) hzP
    have hyz : y * (zP : G) * y⁻¹ = (zP : G) := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hD.y_moves (zP : G) hzV hzG1 hyz
  · have hzPt : (zP : G) = v * t := by
      rw [← hvw, hw1]
    have hvP : v ∈ centralizer (P : Set G) :=
      le_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK hfix hvV
    have ht_eq : v⁻¹ * (zP : G) = t := by
      rw [hzPt]
      group
    have htP : t ∈ centralizer (P : Set G) := by
      rw [← ht_eq]
      exact mul_mem (inv_mem hvP) hzc
    exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer (P : Set G)) htP))

theorem isComponent_of_forall_map_conj_eq_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P) :
    ∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G))) := by
  have hVle : V ≤ centralizer (P : Set G) :=
    le_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK hfix
  have hPV : P ≤ centralizer (V : Set G) := Subgroup.le_centralizer_iff.mp hVle
  have hPle : ∀ v ∈ V, P ≤ centralizer ({v} : Set G) := by
    intro v hv
    exact hPV.trans (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hv))
  let C : Subgroup G := centralizer ({u} : Set G)
  have hPI : CGT.PushingUpLit.CGT6.Nine7.IsCompIn P C :=
    HarrisLit.isCompIn_of_isComponent hPu hcomp
  have hyP : y ∈ centralizer (P : Set G) :=
    mem_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK hfix
  have hyPfix : P.map (MulAut.conj y).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer (P : Set G)) hyP)
  have hmap_comp : ∀ (a b : G) (Q : Subgroup G),
      (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        Q.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b Q
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  have hy2Pfix : P.map (MulAut.conj (y ^ 2)).toMonoidHom = P := by
    have h : P.map (MulAut.conj (y * y)).toMonoidHom = P := by
      calc P.map (MulAut.conj (y * y)).toMonoidHom
          = (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom :=
            (hmap_comp y y P).symm
        _ = P := by rw [hyPfix, hyPfix]
    simpa [pow_two] using h
  have hyuV : y * u * y⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hD.y_normalizes u).mp hu
  have hy2uV : y ^ 2 * u * (y ^ 2)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (pow_mem hD.y_normalizes 2) u).mp hu
  have htriple : ∀ v ∈ V, v ≠ 1 →
      v = u ∨ v = y * u * y⁻¹ ∨ v = y ^ 2 * u * (y ^ 2)⁻¹ := by
    intro v hv hv1
    classical
    let a0 : ↥V := ⟨u, hu⟩
    let a1 : ↥V := ⟨y * u * y⁻¹, hyuV⟩
    let a2 : ↥V := ⟨y ^ 2 * u * (y ^ 2)⁻¹, hy2uV⟩
    have ha0a1 : a0 ≠ a1 := by
      intro h
      exact hD.y_moves u hu hu1 (congrArg Subtype.val h).symm
    have ha0a2 : a0 ≠ a2 := by
      intro h
      have h2 : y ^ 2 * u * (y ^ 2)⁻¹ = u := (congrArg Subtype.val h).symm
      have hcomm2 : Commute (y ^ 2) u := by
        rw [commute_iff_eq]
        calc y ^ 2 * u = (y ^ 2 * u * (y ^ 2)⁻¹) * y ^ 2 := by group
          _ = u * y ^ 2 := by rw [h2]
      have hy : y ∈ Subgroup.zpowers (y ^ 2) :=
        mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hD.odd_orderOf_y)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute y u := by
        rw [← hk]
        exact hcomm2.zpow_left k
      have hyu : y * u * y⁻¹ = u := by
        rw [(commute_iff_eq y u).mp hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hD.y_moves u hu hu1 hyu
    have ha1a2 : a1 ≠ a2 := by
      intro h
      have hgroup : y * u * y⁻¹ = y ^ 2 * u * (y ^ 2)⁻¹ := congrArg Subtype.val h
      have hconj : (MulAut.conj y) u = (MulAut.conj (y ^ 2)) u := hgroup
      have hmul : MulAut.conj (y ^ 2) = MulAut.conj y * MulAut.conj y := by
        ext x
        simp [MulAut.mul_apply, MulAut.conj_apply, pow_two, mul_assoc]
      rw [hmul, MulAut.mul_apply] at hconj
      have hinj := (MulAut.conj y).injective hconj
      exact hD.y_moves u hu hu1 (by simpa [MulAut.conj_apply] using hinj.symm)
    have ha0ne : a0 ≠ 1 := by
      intro h
      exact hu1 (congrArg Subtype.val h)
    have ha1ne : a1 ≠ 1 := by
      intro h
      apply hu1
      have h1 : y * u * y⁻¹ = 1 := congrArg Subtype.val h
      calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; simp
    have ha2ne : a2 ≠ 1 := by
      intro h
      apply hu1
      have h1 : y ^ 2 * u * (y ^ 2)⁻¹ = 1 := congrArg Subtype.val h
      calc u = (y ^ 2)⁻¹ * (y ^ 2 * u * (y ^ 2)⁻¹) * y ^ 2 := by group
        _ = 1 := by rw [h1]; simp
    let A : Set ↥V := {a0, a1, a2}
    let B : Set ↥V := {x | x ≠ 1}
    have hAcard : A.ncard = 3 := by
      have h0 : a0 ∉ ({a1, a2} : Set ↥V) := by
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, ha0a1, ha0a2]
      have h1 : a1 ∉ ({a2} : Set ↥V) := by
        simp [Set.mem_singleton_iff, ha1a2]
      change ({a0, a1, a2} : Set ↥V).ncard = 3
      rw [Set.ncard_insert_of_notMem h0, Set.ncard_insert_of_notMem h1, Set.ncard_singleton]
    have hBcard : B.ncard = 3 := by
      change (({1} : Set ↥V)ᶜ).ncard = 3
      rw [Set.ncard_compl, Set.ncard_singleton, hD.card_V]
    have hAB : A ⊆ B := by
      intro a ha
      simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact ha0ne
      · exact ha1ne
      · exact ha2ne
    have hABeq : A = B :=
      Set.eq_of_subset_of_ncard_le hAB (by rw [hBcard, hAcard])
    have hav : (⟨v, hv⟩ : ↥V) ∈ B := by
      change (⟨v, hv⟩ : ↥V) ≠ 1
      intro h
      exact hv1 (congrArg Subtype.val h)
    rw [← hABeq] at hav
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at hav
    rcases hav with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  intro v hv hv1
  refine ⟨hPle v hv, ?_⟩
  rcases htriple v hv hv1 with rfl | rfl | rfl
  · exact hcomp
  · have hCuY : C.map (MulAut.conj y).toMonoidHom =
        centralizer ({y * u * y⁻¹} : Set G) := by
      rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
        CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer_singleton]
      simp
    have h := hPI.cj y⁻¹
    rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv P y,
      ← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv C y, hyPfix, hCuY] at h
    exact HarrisLit.isComponent_of_isCompIn h
  · have hCuY2 : C.map (MulAut.conj (y ^ 2)).toMonoidHom =
        centralizer ({y ^ 2 * u * (y ^ 2)⁻¹} : Set G) := by
      rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
        CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer_singleton]
      simp
    have h := hPI.cj ((y ^ 2)⁻¹)
    rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv P (y ^ 2),
      ← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv C (y ^ 2), hy2Pfix, hCuY2] at h
    exact HarrisLit.isComponent_of_isCompIn h

theorem false_of_nineSeven_of_l34SuzOdd (hS : L34SuzOddSetting A t) {u : G} (hu1 : u ≠ 1)
    {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hodd : Odd (Nat.card (center ↥P))) (h97 : CGT.PushingUpLit.CGT6.Nine7.NineSeven P) :
    False := by
  unfold CGT.PushingUpLit.CGT6.Nine7.NineSeven at h97
  rcases h97 with h1 | h2 | h3
  · have hconj : CFSG.conjugate P t = P.map (MulAut.conj t).toMonoidHom := by
      rw [show CFSG.conjugate P t = CFSG.conjugate P t⁻¹ by
            rw [inv_eq_self_of_orderOf_eq_two hS.orderOf_t],
        ← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv P t]
    refine h1.2.2 t ?_
    rw [hconj]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  · obtain ⟨x, -, -, -, -, -, z, hz2, hzP, -, hzc, -⟩ := h2
    have hzc' : (⟨z, hzP⟩ : ↥P) ∈ center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro p
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc (p : G) p.2)
    let zc : ↥(center ↥P) := ⟨⟨z, hzP⟩, hzc'⟩
    have hzc2 : orderOf zc = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2]
    exact hodd.not_two_dvd_nat (by
      simpa [hzc2] using orderOf_dvd_natCard zc)
  · rcases h3.eq_bot_or_top_of_isSimpleGroup hS.base.1 with hbot | htop
    · have hbotC : (⊥ : Subgroup G).subgroupOf (centralizer ({u} : Set G)) =
          (⊥ : Subgroup ↥(centralizer ({u} : Set G))) := Subgroup.bot_subgroupOf _
      have hsub : Subsingleton (↥((⊥ : Subgroup G).subgroupOf (centralizer ({u} : Set G))) ⧸
          center ↥((⊥ : Subgroup G).subgroupOf (centralizer ({u} : Set G)))) := by
        rw [hbotC]
        have hsub2 : Subsingleton ↥(⊥ : Subgroup ↥(centralizer ({u} : Set G))) := inferInstance
        constructor
        intro a b
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [QuotientGroup.eq, @Subsingleton.elim _ hsub2 y x]
        simp
      obtain ⟨a, b, hab⟩ := (hbot ▸ hcomp).1.2.2
      exact hab (by rw [@Subsingleton.elim _ hsub a b])
    · have hZ : Subgroup.center G = ⊥ := by
        rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hS.base.1
          (inferInstance : (Subgroup.center G).Normal).isSubnormal with h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := hS.base.2.1
          exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
      have huZ : u ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ P := htop ▸ Subgroup.mem_top g
        exact (CGT.PushingUpLit.CGT6.Nine7.mem_centralizer_single.mp (hPu hg)).symm
      rw [hZ, Subgroup.mem_bot] at huZ
      exact hu1 huZ

theorem false_of_forall_map_conj_eq_of_l34SuzOdd
    (h5 : GSThmB.AschbacherTheorem5Input)
    (hKG : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hZ : L34SuzOddZeroStar)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P) : False := by
  have hodd :=
    odd_card_center_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK hfix
  have hstar := hZ G A V K t y P hc hS hD hne hK
    (le_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK hfix)
    (mem_centralizer_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK hfix)
    hodd (isComponent_of_forall_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK hfix)
  exact false_of_nineSeven_of_l34SuzOdd hS hu1 hc hPu hcomp hodd
    (CGT.PushingUpLit.CGT6.Nine7.nine_seven_star h5 hKG
      (HarrisLit.isCompIn_of_isComponent hPu hcomp).qs hstar
      (Walter86.Asc75.glaubermanAt_holds _))

end CFSG.ComponentClassification.GrSLit.L34Sec5S
