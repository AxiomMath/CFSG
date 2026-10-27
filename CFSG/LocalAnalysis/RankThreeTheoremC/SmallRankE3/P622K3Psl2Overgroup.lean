module

public import CFSG.Open.QuasithinDickson
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Psl2Torus
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3SmallOrders
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3DihCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3PglOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup
open scoped MatrixGroups

theorem finite_psl2 (F : Type) [Field F] [Finite F] : Finite PSL(2, F) :=
  Finite.of_surjective (CFSG.PSL2Table.mk : Matrix.SpecialLinearGroup (Fin 2) F →* _)
    CFSG.PSL2Table.mk_surjective

theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {z t : G} (h : z * t = t * z) :
    t ∈ normalizer (zpowers z : Set G) := by
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (SetLike.mem_coe.mp hg)
  exact (Commute.zpow_left (show Commute z t from h) k).eq

theorem exists_elt_orderOf_card_of_cyclic {G : Type} [Group G] [Finite G] (J T : Subgroup G)
    [IsCyclic T] (hTJ : T ≤ J) {z : G} (hzT : z ∈ T) (hz : orderOf z = 3) :
    ∃ g : ↥J, orderOf g = Nat.card T ∧ 3 ∣ orderOf g := by
  obtain ⟨gT, hgT⟩ := IsCyclic.exists_generator (α := T)
  have hord : orderOf gT = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hgT
  have h3 : 3 ∣ Nat.card T := by
    have h1 : orderOf (⟨z, hzT⟩ : T) ∣ Nat.card T := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hz] at h1
  have hg : orderOf (⟨gT.1, hTJ gT.2⟩ : ↥J) = Nat.card T := by
    rw [Subgroup.orderOf_mk, ← hord]
    exact (Subgroup.orderOf_coe gT)
  exact ⟨⟨gT.1, hTJ gT.2⟩, hg, hg ▸ h3⟩

theorem orderOf_psl2_le {F₀ : Type} [Field F₀] [Finite F₀] {p m : ℕ} [Fact p.Prime]
    (hm : m ≠ 0) (hcard : Nat.card F₀ = p ^ m) (h5 : 5 ≤ p) (x : PSL(2, F₀)) :
    orderOf x ≤ Nat.card F₀ + 1 := by
  have hq : p ≤ Nat.card F₀ := by
    rw [hcard]
    exact Nat.le_self_pow hm p
  have hq5 : 5 ≤ Nat.card F₀ := h5.trans hq
  have hg : 0 < Nat.gcd (Nat.card F₀ - 1) 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  rcases CFSG.Glauberman.Dickson.psl2_orderOf_dvd hcard x with h | h | h
  · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  · have hpos : 0 < (Nat.card F₀ - 1) / Nat.gcd (Nat.card F₀ - 1) 2 :=
      Nat.div_pos (Nat.gcd_le_left _ (by omega)) hg
    exact (Nat.le_of_dvd hpos h).trans ((Nat.div_le_self _ _).trans (by omega))
  · have hpos : 0 < (Nat.card F₀ + 1) / Nat.gcd (Nat.card F₀ - 1) 2 :=
      Nat.div_pos ((Nat.gcd_le_left _ (by omega)).trans (by omega)) hg
    exact (Nat.le_of_dvd hpos h).trans (Nat.div_le_self _ _)

theorem psl2_overgroup_eq_top {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 11 ≤ p ^ f)
    (z : PSL(2, GaloisField p f)) (hz : orderOf z = 3)
    (R J : Subgroup PSL(2, GaloisField p f)) (hR : IsPGroup 2 R)
    (hzR : z ∈ normalizer (R : Set PSL(2, GaloisField p f)))
    (hnc : ∃ y ∈ R, z * y ≠ y * z)
    (hRJ : R ≤ J) (hNJ : normalizer (zpowers z : Set PSL(2, GaloisField p f)) ≤ J) :
    J = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  haveI hfin : Finite PSL(2, GaloisField p f) := finite_psl2 _
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hzJ : z ∈ J := hNJ (le_normalizer (mem_zpowers z))
  obtain ⟨T, hTcyc, hzT, hTcard⟩ :=
    psl2_exists_torus_containing_order_three hp2 hp3 hcardF z hz
  haveI := hTcyc
  have hTJ : T ≤ J := by
    intro t ht
    apply hNJ
    apply mem_normalizer_zpowers_of_commute
    letI : CommGroup T := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨z, hzT⟩ : T) ⟨t, ht⟩)
  obtain ⟨gJ, hgJord, hg3⟩ := exists_elt_orderOf_card_of_cyclic J T hTJ hzT hz
  have hbig : (p ^ f - 1) / 2 ≤ orderOf gJ := by
    rw [hgJord]
    rw [hcardF] at hTcard
    exact hTcard
  have hbig5 : 5 ≤ orderOf gJ := by omega
  set zJ : ↥J := ⟨z, hzJ⟩ with hzJdef
  have hzJord : orderOf zJ = 3 := by
    rw [hzJdef, Subgroup.orderOf_mk]
    exact hz
  have hR' : IsPGroup 2 (R.subgroupOf J) := hR.comap_subtype
  have hzN' : zJ ∈ normalizer ((R.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
    rw [← subgroupOf_normalizer_eq hRJ]
    exact hzR
  have hnc' : ∃ y ∈ R.subgroupOf J, zJ * y ≠ y * zJ := by
    obtain ⟨y, hyR, hy⟩ := hnc
    exact ⟨⟨y, hRJ hyR⟩, hyR, fun h => hy (congrArg Subtype.val h)⟩
  have hcomm_false : (∀ y ∈ R.subgroupOf J, zJ * y = y * zJ) → False := by
    intro h
    obtain ⟨y, hy, hne⟩ := hnc'
    exact hne (h y hy)
  rcases CFSG.Open.Open.quasithin_dickson_psl2_subgroups p f (Nat.one_le_iff_ne_zero.mpr hf) J with
    ⟨-, m, -, hcardJ⟩ | ⟨hcyc, -⟩ | ⟨d, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, P, hPn, -, hPcard, hcycq, -, -, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    exfalso
    have h1 : orderOf zJ ∣ Nat.card ↥J := orderOf_dvd_natCard zJ
    rw [hzJord, hcardJ] at h1
    have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h1
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
  ·
    exfalso
    haveI := hcyc
    exact hcomm_false fun y _ => (IsCyclic.commGroup (α := ↥J)).mul_comm zJ y
  ·
    exfalso
    exact hcomm_false (commute_of_dihedral e zJ hzJord (R.subgroupOf J) hR' hzN')
  ·
    exfalso
    have h := orderOf_le_three_alternating_four (e gJ)
    rw [MulEquiv.orderOf_eq] at h
    omega
  ·
    exfalso
    have h := orderOf_le_four_perm_four (e gJ)
    rw [MulEquiv.orderOf_eq] at h
    omega
  ·
    exfalso
    have h := orderOf_le_five_alternating_five (e gJ)
    rw [MulEquiv.orderOf_eq] at h
    omega
  ·
    exfalso
    haveI := hPn
    have hP' : IsPGroup p P := IsPGroup.of_card hPcard
    haveI : IsCyclic (R.subgroupOf J) :=
      isCyclic_of_two_group_of_quotient_cyclic hp2 P hP' hcycq (R.subgroupOf J) hR'
    exact hcomm_false (commute_of_isCyclic_two_group (R.subgroupOf J) hR' zJ hzJord hzN')
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf (Nat.eq_zero_of_zero_dvd hm)
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases hmf : m = f
    · subst hmf
      apply Subgroup.eq_top_of_card_eq
      exact Nat.card_congr e.toEquiv
    · exfalso
      have h2m : 2 * m ≤ f := by
        obtain ⟨k, hk⟩ := hm
        have hk2 : 2 ≤ k := by
          rcases k with _ | _ | k
          · exact absurd (by simpa using hk) hf
          · exact absurd (by simpa using hk.symm) hmf
          · omega
        calc 2 * m ≤ m * k := by
              rw [mul_comm]
              exact Nat.mul_le_mul_left m hk2
          _ = f := hk.symm
      have hord := orderOf_psl2_le hm0 hcardm hp5 (e gJ)
      rw [MulEquiv.orderOf_eq, hcardm] at hord
      have hsq : p ^ m * p ^ m ≤ p ^ f := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      have hq05 : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow hm0 p)
      have h5q : 5 * p ^ m ≤ p ^ m * p ^ m := Nat.mul_le_mul_right _ hq05
      omega
  ·
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf (Nat.eq_zero_of_zero_dvd (by simpa using hm))
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h2m : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf) hm
    have hord := orderOf_pgl_two_le hcardm (e gJ)
    rw [MulEquiv.orderOf_eq, hcardm] at hord
    have hsq : p ^ m * p ^ m ≤ p ^ f := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    have hq05 : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow hm0 p)
    have h5q : 5 * p ^ m ≤ p ^ m * p ^ m := Nat.mul_le_mul_right _ hq05
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
