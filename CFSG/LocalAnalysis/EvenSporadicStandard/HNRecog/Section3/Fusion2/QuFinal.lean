module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.QuGeneral

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma exists_mul_of_mem_sup {G : Type} [Group G] {A N : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a) {x : G} (hx : x ∈ A ⊔ N) :
    ∃ a ∈ A, ∃ n ∈ N, a * n = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ n ∈ N, a * n = x}
      one_mem' := ⟨1, A.one_mem, 1, N.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro x y ⟨a, ha, n, hn, rfl⟩ ⟨b, hb, m, hm, rfl⟩
        refine ⟨a * b, A.mul_mem ha hb, n * m, N.mul_mem hn hm, ?_⟩
        calc (a * b) * (n * m) = a * (b * n) * m := by group
          _ = a * (n * b) * m := by rw [hcomm b hb n hn]
          _ = (a * n) * (b * m) := by group
      inv_mem' := by
        rintro x ⟨a, ha, n, hn, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, n⁻¹, N.inv_mem hn, ?_⟩
        calc a⁻¹ * n⁻¹ = n⁻¹ * a⁻¹ := hcomm a⁻¹ (A.inv_mem ha) n⁻¹ (N.inv_mem hn)
          _ = (a * n)⁻¹ := (mul_inv_rev a n).symm }
  have hle : A ⊔ N ≤ S := by
    rw [Subgroup.sup_eq_closure, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact ⟨x, hx, 1, N.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  exact hle hx

private lemma eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {G : Type} [Group G] {u y : G}
    (hu : u ^ 2 = 1) (hy : y ∈ Subgroup.zpowers u) : y = 1 ∨ y = u := by
  rw [Subgroup.mem_zpowers_iff] at hy
  obtain ⟨n, rfl⟩ := hy
  have huz : u ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hu]
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · left
    rw [hk, zpow_mul, huz, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, huz, one_zpow, one_mul, zpow_one]

theorem qu_facts {G : Type} [Group G] {a u : G} (ha : a ^ 2 = 1) (hu : u ^ 2 = 1) (ha1 : a ≠ 1)
    (hu1 : u ≠ 1) (hau : a ≠ u) (hcomm : a * u = u * a)
    (hC : IsExtraspecialPlusByA5WrTwo ↥(Gx u)) (hC' : IsExtraspecialPlusByA5WrTwo ↥(Gx (a * u)))
    (hX : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a u)) (hT : TwoFourData (Gxy a u)) :
    a ∉ Qz u ∧ IsElemTwo 5 (Qz u ⊓ Gx a) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) = Qz u ⊓ Qz (a * u) ∧
      IsElemTwo 4 (Qz u ⊓ Qz (a * u)) := by
  have hu2' : u * u = 1 := by rw [← pow_two]; exact hu
  have ha2' : a * a = 1 := by rw [← pow_two]; exact ha
  have hGxy_eq : Gxy a (a * u) = Gxy a u := by
    ext t
    rw [mem_Gxy, mem_Gxy]
    constructor
    · rintro ⟨hta, htau⟩
      refine ⟨hta, ?_⟩
      rw [mem_Gx] at hta htau ⊢
      calc u * t = (a * (a * u)) * t := by
            congr 1
            rw [← mul_assoc, ha2', one_mul]
        _ = a * ((a * u) * t) := by group
        _ = a * (t * (a * u)) := by rw [htau]
        _ = (a * t) * (a * u) := by group
        _ = (t * a) * (a * u) := by rw [hta]
        _ = t * (a * (a * u)) := by group
        _ = t * u := by
            congr 1
            rw [← mul_assoc, ha2', one_mul]
    · rintro ⟨hta, htu⟩
      refine ⟨hta, ?_⟩
      rw [mem_Gx] at hta htu ⊢
      calc (a * u) * t = a * (u * t) := by group
        _ = a * (t * u) := by rw [htu]
        _ = (a * t) * u := by group
        _ = (t * a) * u := by rw [hta]
        _ = t * (a * u) := by group
  have hau2 : (a * u) ^ 2 = 1 := by
    rw [Commute.mul_pow hcomm, ha, hu, one_mul]
  have hau_ne_one : a * u ≠ 1 := by
    intro h
    have h1 : a = u := by
      calc a = a * (u * u) := by rw [hu2', mul_one]
        _ = (a * u) * u := by group
        _ = u := by rw [h, one_mul]
    exact hau h1
  have hau_ne : a ≠ a * u := by
    intro h
    have h2 : a * (1 : G) = a * u := by rw [mul_one]; exact h
    have h1 : (1 : G) = u := mul_left_cancel h2
    exact hu1 h1.symm
  have hcomm' : a * (a * u) = (a * u) * a := by
    calc a * (a * u) = (a * a) * u := by group
      _ = u := by rw [ha2', one_mul]
      _ = (a * u) * a := by
          rw [show (a * u) * a = a * (u * a) by group, ← hcomm, ← mul_assoc, ha2', one_mul]
  obtain ⟨haQ, hTsub, hcard, hNle⟩ :=
    qu_general (a := a) (u := u) ha hu ha1 hu1 hau hcomm hC hX hT
  have hX' : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a (a * u)) := by rw [hGxy_eq]; exact hX
  have hT' : TwoFourData (Gxy a (a * u)) := by rw [hGxy_eq]; exact hT
  obtain ⟨_, hTsub_au, hcard_au, hNle_au⟩ :=
    qu_general (a := a) (u := a * u) ha hau2 ha1 hau_ne_one hau_ne hcomm' hC' hX' hT'
  have hTsub' : Qz (a * u) ⊓ Gx a =
      Subgroup.zpowers (a * u) ⊔ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) := by
    rw [hTsub_au, hGxy_eq]
  have hNle' : CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) ≤ Qz (a * u) := by
    rw [← hGxy_eq]; exact hNle_au
  set N : Subgroup G := CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) with hNdef
  have Qz_le_Gx : ∀ w : G, Qz w ≤ Gx w := by
    intro w
    change (CFSG.pCore 2 ↥(Gx w)).map (Gx w).subtype ≤ Gx w
    exact Subgroup.map_subtype_le _
  have hN_le_X : N ≤ Gxy a u := by
    rw [hNdef]
    change (CFSG.pCore 2 ↥(derivedOf (Gxy a u))).map
      (derivedOf (Gxy a u)).subtype ≤ Gxy a u
    exact le_trans (Subgroup.map_subtype_le _) (derivedOf_le (Gxy a u))
  have hN_le_Ga : N ≤ Gx a := le_trans hN_le_X (by rw [Gxy_eq_inf]; exact inf_le_left)
  have hN_le_Gu : N ≤ Gx u := le_trans hN_le_X (by rw [Gxy_eq_inf]; exact inf_le_right)
  have hN_le_Gau : N ≤ Gx (a * u) := by
    intro n hn
    rw [mem_Gx]
    have hna : a * n = n * a := mem_Gx.mp (hN_le_Ga hn)
    have hnu : u * n = n * u := mem_Gx.mp (hN_le_Gu hn)
    calc (a * u) * n = a * (u * n) := by group
      _ = a * (n * u) := by rw [hnu]
      _ = (a * n) * u := by group
      _ = (n * a) * u := by rw [hna]
      _ = n * (a * u) := by group
  have huau : u * a * u = a := by
    rw [mul_assoc, hcomm, ← mul_assoc, hu2', one_mul]
  have hu_central : ∀ g ∈ Gxy a u, g * u * g⁻¹ = u := by
    intro g hg
    have hgu : u * g = g * u := mem_Gx.mp (mem_Gxy.mp hg).2
    rw [hgu.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hau_central : ∀ g ∈ Gxy a u, g * (a * u) * g⁻¹ = a * u := by
    intro g hg
    have hga : a * g = g * a := mem_Gx.mp (mem_Gxy.mp hg).1
    have hgu : u * g = g * u := mem_Gx.mp (mem_Gxy.mp hg).2
    calc g * (a * u) * g⁻¹ = (g * a * g⁻¹) * (g * u * g⁻¹) := by group
      _ = a * u := by rw [hga.symm, hgu.symm]; group
  have hu_not_mem_N : u ∉ N := by
    rw [hNdef]
    exact not_mem_pCore_derived_of_central hT hu_central hu hu1
  have hau_not_mem_N : a * u ∉ N := by
    rw [hNdef]
    exact not_mem_pCore_derived_of_central hT hau_central hau2 hau_ne_one
  haveI hNcomm : IsMulCommutative N := hT.elem_two.1.1
  have hpair : ((Subgroup.zpowers u : Set G) ∪ (N : Set G)).Pairwise Commute := by
    intro p hp q hq _
    simp only [Set.mem_union] at hp hq
    rcases hp with hp | hp
    · rcases hq with hq | hq
      · exact setLike_mul_comm (s := Subgroup.zpowers u) hp hq
      · have hp' : p ∈ Subgroup.zpowers u := hp
        rw [Subgroup.mem_zpowers_iff] at hp'
        obtain ⟨m, rfl⟩ := hp'
        have hc : Commute u q := mem_Gx.mp (hN_le_Gu hq)
        exact (hc.zpow_left m)
    · rcases hq with hq | hq
      · have hq' : q ∈ Subgroup.zpowers u := hq
        rw [Subgroup.mem_zpowers_iff] at hq'
        obtain ⟨n, rfl⟩ := hq'
        have hc : Commute u p := mem_Gx.mp (hN_le_Gu hp)
        exact (hc.symm.zpow_right n)
      · exact setLike_mul_comm (s := N) hp hq
  have hcomm_zp : ∀ y ∈ Subgroup.zpowers u, ∀ n ∈ N, y * n = n * y := by
    intro y hy n hn
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨m, rfl⟩ := hy
    have hc : Commute u n := mem_Gx.mp (hN_le_Gu hn)
    exact (hc.zpow_left m).eq
  have hcomm_zp_au : ∀ y ∈ Subgroup.zpowers (a * u), ∀ n ∈ N, y * n = n * y := by
    intro y hy n hn
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨m, rfl⟩ := hy
    have hc : Commute (a * u) n := mem_Gx.mp (hN_le_Gau hn)
    exact (hc.zpow_left m).eq
  have hE5 : IsElemTwo 5 (Qz u ⊓ Gx a) := by
    refine ⟨⟨?_, ?_⟩, hcard⟩
    · rw [hTsub, Subgroup.sup_eq_closure]
      exact Subgroup.isMulCommutative_closure hpair
    · intro x hx
      rw [hTsub] at hx
      obtain ⟨y, hy, n, hn, rfl⟩ := exists_mul_of_mem_sup hcomm_zp hx
      have hc : Commute y n := hcomm_zp y hy n hn
      have hy2 : y ^ 2 = 1 := by
        rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hu hy with h | h
        · rw [h, one_pow]
        · rw [h, hu]
      rw [hc.mul_pow, hy2, hT.elem_two.1.2 n hn, one_mul]
  have hN_eq : CFSG.Open.pCoreOf 2 (derivedOf (Gxy a u)) = Qz u ⊓ Qz (a * u) := by
    apply le_antisymm
    · intro n hn
      exact ⟨hNle hn, hNle' hn⟩
    · intro t ht
      have htGu : t ∈ Gx u := Qz_le_Gx u ht.1
      have htGau : t ∈ Gx (a * u) := Qz_le_Gx (a * u) ht.2
      have htGa : t ∈ Gx a := by
        rw [mem_Gx] at htGu htGau ⊢
        calc a * t = ((a * u) * u) * t := by
              congr 1
              rw [mul_assoc, hu2', mul_one]
          _ = (a * u) * (u * t) := by group
          _ = (a * u) * (t * u) := by rw [htGu]
          _ = ((a * u) * t) * u := by group
          _ = (t * (a * u)) * u := by rw [htGau]
          _ = t * ((a * u) * u) := by group
          _ = t * a := by
              congr 1
              rw [mul_assoc, hu2', mul_one]
      have hmem1 : t ∈ Subgroup.zpowers u ⊔ N := by
        rw [← hTsub]; exact ⟨ht.1, htGa⟩
      have hmem2 : t ∈ Subgroup.zpowers (a * u) ⊔ N := by
        rw [← hTsub']; exact ⟨ht.2, htGa⟩
      obtain ⟨y1, hy1, n1, hn1, hxy1⟩ := exists_mul_of_mem_sup hcomm_zp hmem1
      obtain ⟨y2, hy2, n2, hn2, hxy2⟩ := exists_mul_of_mem_sup hcomm_zp_au hmem2
      rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hu hy1 with hy1' | hy1'
      · rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hau2 hy2 with hy2' | hy2'
        · rw [hy1', one_mul] at hxy1
          rwa [← hxy1]
        · rw [hy1', one_mul] at hxy1
          rw [hy2'] at hxy2
          exfalso
          have h1 : n1 = (a * u) * n2 := by rw [hxy1, ← hxy2]
          have h2 : a * u = n1 * n2⁻¹ := by rw [h1]; group
          exact hau_not_mem_N (by rw [h2]; exact N.mul_mem hn1 (N.inv_mem hn2))
      · rw [hy1'] at hxy1
        rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hau2 hy2 with hy2' | hy2'
        · rw [hy2', one_mul] at hxy2
          exfalso
          have h1 : u * n1 = n2 := by rw [hxy1, ← hxy2]
          have h2 : u = n2 * n1⁻¹ := by rw [← h1]; group
          exact hu_not_mem_N (by rw [h2]; exact N.mul_mem hn2 (N.inv_mem hn1))
        · rw [hy2'] at hxy2
          exfalso
          have h1 : u * n1 = (a * u) * n2 := by rw [hxy1, ← hxy2]
          have h2 : a = n1 * n2⁻¹ := by
            have h3 : n1 = a * n2 := by
              calc n1 = (u * u) * n1 := by rw [hu2', one_mul]
                _ = u * (u * n1) := by group
                _ = u * ((a * u) * n2) := by rw [h1]
                _ = (u * a * u) * n2 := by group
                _ = a * n2 := by rw [huau]
            rw [h3]; group
          exact haQ (hNle (by rw [h2]; exact N.mul_mem hn1 (N.inv_mem hn2)))
  refine ⟨haQ, hE5, hN_eq, ?_⟩
  rw [← hN_eq]
  exact hT.elem_two

end CFSG.EvenSporadicStandard.HNRecog.Section3
