module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.Semidihedral.DihedralNormalIndex

open CFSG.GorensteinWalter

noncomputable section

universe u

theorem orderOf_even_rotation {m : ℕ} (hm : 1 ≤ m) :
    orderOf (DihedralGroup.r (2 : ZMod (2 ^ m))) = 2 ^ (m - 1) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  have hr : DihedralGroup.r (2 : ZMod (2 ^ m)) =
      (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ 2 := by
    simp [DihedralGroup.r_pow]
  rw [hr, orderOf_pow, DihedralGroup.orderOf_r_one]
  have hgcd : Nat.gcd (2 ^ m) 2 = 2 := by
    rw [Nat.gcd_eq_right]
    exact pow_dvd_pow 2 hm
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hgcd, hpow, Nat.mul_div_left _ (by norm_num : 0 < 2)]

theorem index_two_family_equiv {m : ℕ} (hm : 1 ≤ m)
    (j : ZMod (2 ^ m)) :
    Nonempty (dihedralIndexTwoSubgroup m j ≃* DihedralGroup (2 ^ (m - 1))) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let I : Subgroup (DihedralGroup (2 ^ m)) := dihedralIndexTwoSubgroup m j
  let ρ : I := ⟨DihedralGroup.r 2,
    (le_sup_left : Subgroup.zpowers (DihedralGroup.r 2) ≤ I)
      (Subgroup.mem_zpowers _)⟩
  let σ : I := ⟨DihedralGroup.sr j,
    (le_sup_right : Subgroup.zpowers (DihedralGroup.sr j) ≤ I)
      (Subgroup.mem_zpowers _)⟩
  have hgen : (⊤ : Subgroup I) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x _
      have hx : (x : DihedralGroup (2 ^ m)) ∈
          (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).map I.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simp [σ, pow_two]
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    simp only [σ, ρ, Subgroup.coe_mul, Subgroup.coe_inv,
      DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r, DihedralGroup.r.injEq]
    ring
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hσ
    apply sr_not_mem_zpowers_r_one j
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hσ
    have hval : (DihedralGroup.r 2 : DihedralGroup (2 ^ m)) ^ a =
        DihedralGroup.sr j := congrArg Subtype.val ha
    rw [← hval]
    exact (Subgroup.zpowers_le.mpr (r_mem_zpowers_r_one 2))
      (Subgroup.mem_zpowers_iff.mpr ⟨a, rfl⟩)
  have horder : orderOf ρ = 2 ^ (m - 1) := by
    calc
      orderOf ρ = orderOf (DihedralGroup.r (2 : ZMod (2 ^ m))) :=
        (orderOf_injective I.subtype I.subtype_injective ρ).symm
      _ = 2 ^ (m - 1) := orderOf_even_rotation hm
  have hmodel := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  rwa [horder] at hmodel

theorem proper_normal_noncyclic_equiv
    {D : Type u} [Group D]
    {m : ℕ} (hm : 1 ≤ m) (e : D ≃* DihedralGroup (2 ^ m))
    (P : Subgroup D) (hPnormal : P.Normal) (hPnc : ¬ IsCyclic P)
    (hPproper : P ≠ ⊤) :
    Nonempty (P ≃* DihedralGroup (2 ^ (m - 1))) := by
  let P' : Subgroup (DihedralGroup (2 ^ m)) := P.map e.toMonoidHom
  have hP'normal : P'.Normal := (e.normal_map_iff).2 hPnormal
  let eP : P ≃* P' := P.equivMapOfInjective e.toMonoidHom e.injective
  have hP'nc : ¬ IsCyclic P' := fun h => hPnc (eP.isCyclic.mpr h)
  have hP'proper : P' ≠ ⊤ := by
    intro h
    apply hPproper
    have hcomap := congrArg (Subgroup.comap e.toMonoidHom) h
    change (P.map e.toMonoidHom).comap e.toMonoidHom =
      (⊤ : Subgroup (DihedralGroup (2 ^ m))).comap e.toMonoidHom at hcomap
    rw [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at hcomap
    exact hcomap
  obtain htop | ⟨j, hj⟩ :=
    normal_noncyclic_subgroup_dihedral_two_pow hm P' hP'normal hP'nc
  · exact False.elim (hP'proper htop)
  · obtain ⟨eI⟩ := index_two_family_equiv hm j
    have eP' : P' ≃* DihedralGroup (2 ^ (m - 1)) := by
      rw [hj]
      exact eI
    exact ⟨eP.trans eP'⟩

theorem normal_intersection_not_isCyclic
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (L : Subgroup G) (hLnormal : L.Normal)
    (T : Sylow 2 L) (hTnc : ¬ IsCyclic T) :
    ¬ IsCyclic ↥((S : Subgroup G) ⊓ L) := by
  let : L.Normal := hLnormal
  obtain ⟨U, hU⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 L S
  have eU : U ≃* ↥((S : Subgroup G) ⊓ L) := by
    rw [hU, ← Subgroup.inf_subgroupOf_right (S : Subgroup G) L]
    exact Subgroup.subgroupOfEquivOfLe inf_le_right
  intro hcyc
  exact hTnc ((Sylow.equiv T U).isCyclic.mpr (eU.isCyclic.mpr hcyc))

theorem normal_intersection_relIndex_odd
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (L : Subgroup G) (hLnormal : L.Normal) :
    Odd (((S : Subgroup G) ⊓ L).relIndex L) := by
  let : L.Normal := hLnormal
  obtain ⟨U, hU⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 L S
  have hnot : ¬ 2 ∣ (S : Subgroup G).relIndex L := by
    have h := U.not_dvd_index
    change ¬ 2 ∣ (U : Subgroup L).index at h
    rw [hU] at h
    exact h
  rw [Subgroup.inf_relIndex_right]
  exact Nat.coprime_two_left.mp ((Nat.prime_two.coprime_iff_not_dvd).2 hnot)

theorem sylow_not_le_index_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (J : Subgroup G) (hJindex : J.index = 2) :
    ¬ (S : Subgroup G) ≤ J := by
  intro hle
  have hdiv := Subgroup.index_dvd_of_le hle
  rw [hJindex] at hdiv
  exact S.not_dvd_index hdiv

theorem sylow_intersection_index_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (J : Subgroup G) (hJindex : J.index = 2) :
    ((S : Subgroup G) ⊓ J).relIndex (S : Subgroup G) = 2 := by
  let : J.Normal := Subgroup.normal_of_index_eq_two hJindex
  have hdiv : J.relIndex (S : Subgroup G) ∣ 2 := by
    simpa only [hJindex] using
      Subgroup.relIndex_dvd_index_of_normal J (S : Subgroup G)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact False.elim (sylow_not_le_index_two S J hJindex
      (Subgroup.relIndex_eq_one.mp hone))
  · simpa only [Subgroup.inf_relIndex_left] using htwo

theorem noncyclic_normal_dihedral_fills_index_two
    {G : Type u} [Group G] [Finite G]
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (T : Sylow 2 L) (hTnc : ¬ IsCyclic T) :
    3 ≤ k ∧
      (S : Subgroup G) ⊓ L = (S : Subgroup G) ⊓ J ∧
      ((S : Subgroup G) ⊓ L).relIndex (S : Subgroup G) = 2 ∧
      Odd (L.relIndex J) ∧
      Nonempty (↥((S : Subgroup G) ⊓ L) ≃* DihedralGroup (2 ^ (k - 2))) ∧
      L.index.factorization 2 = 1 ∧ 2 ^ L.index.factorization 2 = 2 := by
  let : L.Normal := hLnormal
  let : J.Normal := Subgroup.normal_of_index_eq_two hJindex
  let P : Subgroup G := (S : Subgroup G) ⊓ L
  let I : Subgroup G := (S : Subgroup G) ⊓ J
  let N : Subgroup S := P.subgroupOf (S : Subgroup G)
  have hPnc : ¬ IsCyclic P := normal_intersection_not_isCyclic S L hLnormal T hTnc
  let eN : N ≃* P := Subgroup.subgroupOfEquivOfLe inf_le_left
  have hNnormal : N.Normal := by
    simpa only [N, P, Subgroup.inf_subgroupOf_left] using
      (inferInstance : (L.subgroupOf (S : Subgroup G)).Normal)
  have hNnc : ¬ IsCyclic N := fun h => hPnc (eN.isCyclic.mp h)
  have hNproper : N ≠ ⊤ := by
    intro htop
    have hSP : (S : Subgroup G) ≤ P := Subgroup.subgroupOf_eq_top.mp htop
    exact sylow_not_le_index_two S J hJindex (hSP.trans (inf_le_right.trans hLJ))
  have hPindex_le : P.relIndex (S : Subgroup G) ≤ 2 :=
    normal_noncyclic_subgroup_dihedral_of_mulEquiv_index_le_two
      (by omega : 1 ≤ k - 1) eS N hNnormal hNnc
  have hPIle : P ≤ I := inf_le_inf_left (S : Subgroup G) hLJ
  have hIindex : I.relIndex (S : Subgroup G) = 2 :=
    sylow_intersection_index_two S J hJindex
  have hPindex : P.relIndex (S : Subgroup G) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_of_le_left (S : Subgroup G) hPIle
    rw [hIindex] at hdvd
    have hpos : 0 < P.relIndex (S : Subgroup G) := by
      change 0 < N.index
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N))
    have hlow := Nat.le_of_dvd hpos hdvd
    omega
  have hPI : P = I := by
    have hmul := Subgroup.relIndex_mul_relIndex P I (S : Subgroup G) hPIle inf_le_left
    rw [hIindex, hPindex] at hmul
    have hrel : P.relIndex I = 1 := by omega
    exact le_antisymm hPIle (Subgroup.relIndex_eq_one.mp hrel)
  obtain ⟨eModel⟩ := proper_normal_noncyclic_equiv
    (by omega : 1 ≤ k - 1) eS N hNnormal hNnc hNproper
  have hsub : k - 1 - 1 = k - 2 := by omega
  have eP : P ≃* DihedralGroup (2 ^ (k - 2)) := by
    rw [hsub] at eModel
    exact eN.symm.trans eModel
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k = 2 := by omega
    have eP1 : P ≃* DihedralGroup 1 := by
      have hparam : 2 ^ (k - 2) = 1 := by rw [hk2]; norm_num
      rw [← hparam]
      exact eP
    exact hPnc (eP1.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr rfl))
  have hPoddJ : Odd (P.relIndex J) := by
    rw [hPI]
    exact normal_intersection_relIndex_odd S J inferInstance
  have hodd : Odd (L.relIndex J) := by
    have hmul := Subgroup.relIndex_mul_relIndex P L J inf_le_right hLJ
    have hoddmul : Odd (P.relIndex L * L.relIndex J) := hmul.symm ▸ hPoddJ
    exact (Nat.odd_mul.mp hoddmul).2
  have hfactorization : L.index.factorization 2 = 1 := by
    have hmul := Subgroup.relIndex_mul_index hLJ
    rw [hJindex] at hmul
    rw [← hmul, Nat.factorization_mul hodd.pos.ne' (by norm_num : 2 ≠ 0),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat,
      Nat.prime_two.factorization_self, zero_add]
  refine ⟨hk3, hPI, hPindex, hodd, ⟨eP⟩, hfactorization, ?_⟩
  rw [hfactorization]
  norm_num

theorem k_eq_two_impossible
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup 2)
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (T : Sylow 2 L) (hTnc : ¬ IsCyclic T) : False := by
  have h := noncyclic_normal_dihedral_fills_index_two
    2 (by norm_num) S eS L hLnormal J hJindex hLJ T hTnc
  omega

theorem k_eq_three_intersection_isKleinFour
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup 4)
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (T : Sylow 2 L) (hTnc : ¬ IsCyclic T) :
    IsKleinFour ↥((S : Subgroup G) ⊓ L) := by
  obtain ⟨eP⟩ := (noncyclic_normal_dihedral_fills_index_two
    3 (by norm_num) S eS L hLnormal J hJindex hLJ T hTnc).2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
    norm_num
  · rw [Monoid.exponent_eq_of_mulEquiv eP, DihedralGroup.exponent]
    norm_num

end

end CFSG.Semidihedral.DihedralNormalIndex
