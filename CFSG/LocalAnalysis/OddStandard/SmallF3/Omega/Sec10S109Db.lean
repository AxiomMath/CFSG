module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem exists_mem_normalizer_of_lt_pGroup [Finite G] {H P : Subgroup G}
    (hP : IsPGroup 2 P) (hHP : H < P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ normalizer (H : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hHP.ne (le_antisymm hHP.le fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < normalizer (IP : Set P) := Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (H : Set G)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hHP.le]
    exact hxN
  exact mem_subgroupOf.mp hxsub

theorem sec10D_sylow [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    {g : G} (hz2 : z * z = 1) (htS : t ∈ S) (hctx : Sec109Ctx G t L S z K1 K2 g)
    (hsc : IsStrClosedModZ t z (S ⊔ zpowers g)) :
    IsSylow2Of (S ⊔ zpowers g) (centralizer ({z} : Set G)) := by
  have hT2 : IsPGroup 2 ↥(S ⊔ zpowers g) := sec10D_T_pgroup hctx
  have hTH : S ⊔ zpowers g ≤ centralizer ({z} : Set G) := sec10D_T_le_H hz2 hctx
  have hSt : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hgT : g ∈ S ⊔ zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have htT : t ∈ S ⊔ zpowers g := Subgroup.mem_sup_left htS
  have hgz : g⁻¹ * z * g = z := by
    have h := sec10D_g_comm_z hz2 hctx
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [h]
      _ = z := by group
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylow2Of_ge hT2 hTH
  have hQT : Q = S ⊔ zpowers g := by
    by_contra hne
    have hlt : S ⊔ zpowers g < Q := lt_of_le_of_ne hTQ (Ne.symm hne)
    obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_of_lt_pGroup hQ.2.1 hlt
    have hxH : x ∈ centralizer ({z} : Set G) := hQ.1 hxQ
    have hxi : x⁻¹ * t * x ∈ S ⊔ zpowers g := by
      have h := (Subgroup.mem_set_normalizer_iff.mp (inv_mem hxN) t).mp htT
      simpa using h
    have hcl : x⁻¹ * t * x = t ∨ x⁻¹ * t * x = t * z := hsc x hxH (Subgroup.mem_sup_left hxi)
    have hy : ∃ y ∈ Q, y ∉ S ⊔ zpowers g ∧ y ∈ normalizer ((S ⊔ zpowers g : Subgroup G) : Set G) ∧
        y * t = t * y := by
      rcases hcl with h | h
      · refine ⟨x, hxQ, hxT, hxN, ?_⟩
        calc x * t = x * (x⁻¹ * t * x) := by rw [h]
          _ = t * x := by group
      · refine ⟨x * g, Q.mul_mem hxQ (hTQ hgT), fun hxg => hxT ?_,
          mul_mem hxN (Subgroup.le_normalizer hgT), ?_⟩
        · have := (S ⊔ zpowers g).mul_mem hxg ((S ⊔ zpowers g).inv_mem hgT)
          simpa using this
        · have hconj : (x * g)⁻¹ * t * (x * g) = t := by
            calc (x * g)⁻¹ * t * (x * g) = g⁻¹ * (x⁻¹ * t * x) * g := by group
              _ = g⁻¹ * (t * z) * g := by rw [h]
              _ = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
              _ = (t * z) * z := by rw [hctx.swap, hgz]
              _ = t := by rw [mul_assoc, hz2, mul_one]
          calc x * g * t = x * g * ((x * g)⁻¹ * t * (x * g)) := by rw [hconj]
            _ = t * (x * g) := by group
    obtain ⟨y, hyQ, hyT, hyN, hyt⟩ := hy
    have hyC : y ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyt
    have hyS : y ∈ normalizer (S : Set G) := by
      have h1 : y ∈ normalizer ((S ⊔ zpowers g : Subgroup G) : Set G) ⊓
          normalizer ((centralizer ({t} : Set G) : Subgroup G) : Set G) :=
        ⟨hyN, Subgroup.le_normalizer hyC⟩
      have h2 := Subgroup.inf_normalizer_le_normalizer_inf h1
      rwa [sec10D_T_cent_t hctx] at h2
    have hQ'2 : IsPGroup 2 ↥(S ⊔ zpowers y) :=
      IsPGroup.to_sup_of_normal_left' hctx.sylow.2.1
        (hQ.2.1.to_le (Subgroup.zpowers_le.mpr hyQ)) (Subgroup.zpowers_le.mpr hyS)
    have hQ'le : S ⊔ zpowers y ≤ centralizer ({t} : Set G) :=
      sup_le hSt (Subgroup.zpowers_le.mpr hyC)
    have hQ'eq : S ⊔ zpowers y = S := hctx.sylow.eq_of_le hQ'le hQ'2 le_sup_left
    have hyS' : y ∈ S := hQ'eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    exact hyT (Subgroup.mem_sup_left hyS')
  exact hQT ▸ hQ

end CFSG.OddStandard.SmallF3.Omega
