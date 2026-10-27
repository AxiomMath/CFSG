module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.CentSeven
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.S7InA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

private theorem card_centralizer_eq_of_isConj_aux {G : Type} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have he : (MulAut.conj c) x = y := by rw [MulAut.conj_apply, hc]
  rw [← he]
  exact Nat.card_congr (TwoHSData.centralizerMulEquiv (MulAut.conj c) x).toEquiv

private theorem seven_dvd_card_centralizer {H : Type} [Group H] {S : Subgroup H} {y : H}
    (hS : IsShapeSym 7 ↥S) (hy : ∀ s ∈ S, y * s = s * y) :
    7 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set H)) := by
  have hSle : S ≤ Subgroup.centralizer ({y} : Set H) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hy s hs).symm
  have h5040 : Nat.card ↥S = 5040 := by
    obtain ⟨e⟩ := hS
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  exact dvd_trans (by rw [h5040]; norm_num) (Subgroup.card_dvd_of_le hSle)

private theorem card_of_isShapeTwoTwoTimesTwoFourA5_aux {X : Type*} [Group X]
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : Nat.card X = 3840 := by
  obtain ⟨Y, _, ⟨N, hN, ⟨e⟩, ⟨f⟩⟩, ⟨g⟩⟩ := h
  have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hN16 : Nat.card ↥N = 16 := by
    rw [Nat.card_congr e.toEquiv, card_Elem2_eq]
    norm_num
  have hY : Nat.card Y = 960 := by
    rw [← Subgroup.card_mul_index N, hN16, Subgroup.index_eq_card, Nat.card_congr f.toEquiv, hA5]
  rw [Nat.card_congr g.toEquiv, Nat.card_prod, hY, card_Elem2_eq]
  norm_num

theorem mem_zpowers_of_centralizes_sym7 {H : Type} [Group H] {a z b z₁ : H}
    (hT : TwoHSFacts H a z b z₁) {S : Subgroup H} (hS : IsShapeSym 7 ↥S) {y : H}
    (hy : ∀ s ∈ S, y * s = s * y) : y ∈ Subgroup.zpowers a := by
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_centralizes_sym7 hS hT.table_seven hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  · have h2 : orderOf y = 2 := orderOf_eq_prime (p := 2) hy2 hy1
    obtain ⟨i, hi⟩ := hT.involution_cover y h2
    have h7dvd : 7 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set H)) :=
      seven_dvd_card_centralizer hS hy
    fin_cases i
    ·
      change IsConj a y at hi
      have ha_center : a ∈ Subgroup.center H := by
        rw [hT.center_eq]
        exact Subgroup.mem_zpowers a
      have hya : y = a := by
        obtain ⟨c, hc⟩ := isConj_iff.1 hi
        rw [← hc, Subgroup.mem_center_iff.mp ha_center c, mul_assoc, mul_inv_cancel, mul_one]
      rw [hya]
      exact Subgroup.mem_zpowers a
    ·
      change IsConj z y at hi
      have h7 := h7dvd
      rw [← card_centralizer_eq_of_isConj_aux hi, card_of_isShapeTwoTwoSixS5 hT.cent_z] at h7
      exact absurd h7 (by norm_num)
    ·
      change IsConj (a * z) y at hi
      have h7 := h7dvd
      rw [← card_centralizer_eq_of_isConj_aux hi, card_of_isShapeTwoTwoSixS5 hT.cent_az] at h7
      exact absurd h7 (by norm_num)
    ·
      change IsConj b y at hi
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      have hiso : ↥(Subgroup.centralizer ({b} : Set H)) ≃*
          ↥(Subgroup.centralizer ({y} : Set H)) :=
        (TwoHSData.centralizerMulEquiv (MulAut.conj c) b).trans
          (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]))
      have hshape : IsShapeTwoTwoTimesA8 ↥(Subgroup.centralizer ({y} : Set H)) :=
        IsShapeTwoTwoTimesA8.of_mulEquiv hiso hT.cent_b
      obtain ⟨φ⟩ := hS
      have hSle : S ≤ Subgroup.centralizer ({y} : Set H) := fun s hs =>
        Subgroup.mem_centralizer_singleton_iff.2 (hy s hs).symm
      have hinj : Function.Injective
          ((Subgroup.inclusion hSle).comp φ.symm.toMonoidHom) :=
        (Subgroup.inclusion_injective hSle).comp φ.symm.injective
      exact (sym7_not_injective_of_isShapeTwoTwoTimesA8 hshape _ hinj).elim
    ·
      change IsConj z₁ y at hi
      have h7 := h7dvd
      rw [← card_centralizer_eq_of_isConj_aux hi,
        card_of_isShapeTwoTwoTimesTwoFourA5_aux hT.cent_z₁] at h7
      exact absurd h7 (by norm_num)

variable {G : Type} [Group G] {a z : G}

theorem mem_zpowers_of_centralizes_sym7_of_f5Local (hL : F5Local G a z) {S : Subgroup G}
    (hSa : S ≤ Gx a) (hS : IsShapeSym 7 ↥S) {y : G} (hya : y ∈ Gx a)
    (hy : ∀ s ∈ S, y * s = s * y) : y ∈ Subgroup.zpowers a := by
  obtain ⟨z₀, b₀, u₀, hT, -⟩ := hL.fusion1.self.rep_z
  let S' : Subgroup ↥(Gx a) := S.subgroupOf (Gx a)
  have hS' : IsShapeSym 7 ↥S' := by
    obtain ⟨f⟩ := hS
    exact ⟨(Subgroup.subgroupOfEquivOfLe hSa).trans f⟩
  let y' : ↥(Gx a) := ⟨y, hya⟩
  have hy' : ∀ s ∈ S', y' * s = s * y' := by
    intro s hs
    apply Subtype.ext
    exact hy (s : G) (Subgroup.mem_subgroupOf.mp hs)
  have hmem : y' ∈ Subgroup.zpowers (GxSelf a) :=
    mem_zpowers_of_centralizes_sym7 hT hS' hy'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simpa [GxSelf, y'] using congrArg (fun w : ↥(Gx a) => (w : G)) hk⟩

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
