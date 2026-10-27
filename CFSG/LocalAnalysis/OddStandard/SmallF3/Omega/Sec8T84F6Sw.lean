module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma conjAct_smul_eq_map (g : G) (H : Subgroup G) :
    ConjAct.toConjAct g • H = H.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

private lemma IsElemAb2.map_conj {A : Subgroup G} {k : ℕ} (h : IsElemAb2 A k) (b : G) :
    IsElemAb2 (A.map (MulAut.conj b).toMonoidHom) k :=
  ⟨CFSG.Open.IsElemAbelian.map h.1 _, by
    rw [Subgroup.card_map_of_injective (K := A) (MulAut.conj b).injective, h.2]⟩

private lemma normal_subgroupOf_map_conj {A T : Subgroup G} (hAT : A ≤ T)
    (hA : (A.subgroupOf T).Normal) {b : G} (hb : b ∈ normalizer (T : Set G)) :
    ((A.map (MulAut.conj b).toMonoidHom).subgroupOf T).Normal := by
  have hle : (A.map (MulAut.conj b).toMonoidHom) ≤ T := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hb]
    exact Subgroup.map_mono hAT
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hh
  refine Subgroup.mem_map.mpr ⟨(b⁻¹ * k * b) * e * (b⁻¹ * k * b)⁻¹, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff hAT).mp hA e (b⁻¹ * k * b) he
      ((Subgroup.mem_normalizer_iff''.mp hb k).mp hk)
  · show b * ((b⁻¹ * k * b) * e * (b⁻¹ * k * b)⁻¹) * b⁻¹ = k * (b * e * b⁻¹) * k⁻¹
    group

theorem sec8t84_swap_contra {T E E0 : Subgroup G} (hTS : IsSylow2Of T ⊤) (hne : E ≠ E0)
    (hET : E ≤ T) (hE0T : E0 ≤ T) (hEn : (E.subgroupOf T).Normal)
    (hE0n : (E0.subgroupOf T).Normal) (hE8 : IsElemAb2 E 8) (hE08 : IsElemAb2 E0 8)
    (honly : ∀ A : Subgroup G, A ≤ T → IsElemAb2 A 8 → (A.subgroupOf T).Normal →
      A = E ∨ A = E0)
    (hconj : ∃ u : G, E0 = E.map (MulAut.conj u).toMonoidHom) : False := by
  have hTN_E : T ≤ normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hET).mp hEn
  have hTN_E0 : T ≤ normalizer (E0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE0T).mp hE0n
  obtain ⟨u, hu⟩ := hconj
  let T' : Subgroup G := T.map (MulAut.conj u).toMonoidHom
  have hT'le : T' ≤ normalizer (E0 : Set G) := by
    show T.map (MulAut.conj u).toMonoidHom ≤ normalizer (E0 : Set G)
    calc T.map (MulAut.conj u).toMonoidHom
        ≤ (normalizer (E : Set G)).map (MulAut.conj u).toMonoidHom :=
          Subgroup.map_mono hTN_E
      _ ≤ normalizer ((E : Subgroup G).map (MulAut.conj u).toMonoidHom) :=
          Subgroup.le_normalizer_map _
      _ = normalizer (E0 : Set G) := by rw [← hu]
  have hT'S : IsSylow2Of T' ⊤ := by
    have h := hTS.conjugate u⁻¹
    have hconv : CFSG.conjugate T u⁻¹ = T' := by
      rw [CFSG.conjugate, inv_inv]
    have htop : CFSG.conjugate (⊤ : Subgroup G) u⁻¹ = ⊤ := by
      simp [CFSG.conjugate]
    rwa [hconv, htop] at h
  let N0 : Subgroup G := normalizer (E0 : Set G)
  have hTN0 : IsSylow2Of T N0 := by
    have hrel : T.relIndex N0 ∣ T.relIndex ⊤ :=
      ⟨N0.relIndex ⊤, (Subgroup.relIndex_mul_relIndex (H := T) (K := N0) (L := ⊤)
        hTN_E0 le_top).symm⟩
    exact ⟨hTN_E0, hTS.2.1, fun h2 => hTS.2.2 (dvd_trans h2 hrel)⟩
  have hT'N0 : IsSylow2Of T' N0 := by
    have hrel : T'.relIndex N0 ∣ T'.relIndex ⊤ :=
      ⟨N0.relIndex ⊤, (Subgroup.relIndex_mul_relIndex (H := T') (K := N0) (L := ⊤)
        hT'le le_top).symm⟩
    exact ⟨hT'le, hT'S.2.1, fun h2 => hT'S.2.2 (dvd_trans h2 hrel)⟩
  obtain ⟨n, hnN0, hn⟩ := IsSylow2Of.exists_conj_mem hT'N0 hTN0
  have hnT' : T'.map (MulAut.conj n).toMonoidHom = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (hn (MulAut.conj n y)).mpr (by simpa [MulAut.conj_apply, mul_assoc] using hy)
    · intro hx
      refine Subgroup.mem_map.mpr ⟨n⁻¹ * x * n, (hn x).mp hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  let a : G := n * u
  have huE : ConjAct.toConjAct u • E = E0 := (conjAct_smul_eq_map u E).trans hu.symm
  have hnE0 : ConjAct.toConjAct n • E0 = E0 := Subgroup.conjAct_pointwise_smul_eq_self hnN0
  have haE_smul : ConjAct.toConjAct a • E = E0 := by
    show ConjAct.toConjAct (n * u) • E = E0
    rw [map_mul, mul_smul, huE, hnE0]
  have haE : E.map (MulAut.conj a).toMonoidHom = E0 := by
    have h := conjAct_smul_eq_map a E
    rw [haE_smul] at h
    exact h.symm
  have haN : a ∈ normalizer (T : Set G) := by
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    show ConjAct.toConjAct (n * u) • T = T
    rw [map_mul, mul_smul]
    have huT : ConjAct.toConjAct u • T = T' := conjAct_smul_eq_map u T
    have hnT : ConjAct.toConjAct n • T' = T := (conjAct_smul_eq_map n T').trans hnT'
    rw [huT, hnT]
  have hperm : ∀ b ∈ normalizer (T : Set G),
      (E.map (MulAut.conj b).toMonoidHom = E ∨ E.map (MulAut.conj b).toMonoidHom = E0) ∧
      (E0.map (MulAut.conj b).toMonoidHom = E ∨ E0.map (MulAut.conj b).toMonoidHom = E0) := by
    intro b hb
    have hle : ∀ A : Subgroup G, A ≤ T → (A.map (MulAut.conj b).toMonoidHom) ≤ T := by
      intro A hA
      rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hb]
      exact Subgroup.map_mono hA
    exact ⟨honly (E.map (MulAut.conj b).toMonoidHom) (hle E hET)
        (IsElemAb2.map_conj hE8 b) (normal_subgroupOf_map_conj hET hEn hb),
      honly (E0.map (MulAut.conj b).toMonoidHom) (hle E0 hE0T)
        (IsElemAb2.map_conj hE08 b) (normal_subgroupOf_map_conj hE0T hE0n hb)⟩
  have haE0 : E0.map (MulAut.conj a).toMonoidHom = E := by
    rcases (hperm a haN).2 with h | h
    · exact h
    · exfalso
      apply hne
      have hmap : E.map (MulAut.conj a).toMonoidHom =
          E0.map (MulAut.conj a).toMonoidHom := by rw [haE, h]
      have h1 : (E.map (MulAut.conj a).toMonoidHom).comap (MulAut.conj a).toMonoidHom = E :=
        Subgroup.comap_map_eq_self_of_injective (MulAut.conj a).injective E
      have h2 : (E0.map (MulAut.conj a).toMonoidHom).comap (MulAut.conj a).toMonoidHom = E0 :=
        Subgroup.comap_map_eq_self_of_injective (MulAut.conj a).injective E0
      have h3 := congrArg (fun S : Subgroup G => S.comap (MulAut.conj a).toMonoidHom) hmap
      rwa [h1, h2] at h3
  have haE0_smul : ConjAct.toConjAct a • E0 = E := (conjAct_smul_eq_map a E0).trans haE0
  have hfixE2 : (ConjAct.toConjAct a ^ 2) • E = E := by
    rw [pow_two, mul_smul, haE_smul, haE0_smul]
  have hfixE02 : (ConjAct.toConjAct a ^ 2) • E0 = E0 := by
    rw [pow_two, mul_smul, haE0_smul, haE_smul]
  let N : Subgroup G := normalizer (T : Set G)
  have hTN : IsSylow2Of T N := by
    have hrel : T.relIndex N ∣ T.relIndex ⊤ :=
      ⟨N.relIndex ⊤, (Subgroup.relIndex_mul_relIndex (H := T) (K := N) (L := ⊤)
        T.le_normalizer le_top).symm⟩
    exact ⟨T.le_normalizer, hTS.2.1, fun h2 => hTS.2.2 (dvd_trans h2 hrel)⟩
  haveI : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let q : ↥N ⧸ T.subgroupOf N := QuotientGroup.mk' (T.subgroupOf N) ⟨a, haN⟩
  have hq_dvd : orderOf q ∣ T.relIndex N := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard q
  have hq_odd : Odd (orderOf q) := by
    have hNodd : Odd (T.relIndex N) := by
      rw [← Nat.not_even_iff_odd]
      exact fun h => hTN.2.2 (even_iff_two_dvd.mp h)
    exact Odd.of_dvd_nat hNodd hq_dvd
  have ha_pow_mem : a ^ orderOf q ∈ T := by
    have hq1 : q ^ orderOf q = 1 := pow_orderOf_eq_one q
    have hker : (⟨a, haN⟩ ^ orderOf q) ∈ (QuotientGroup.mk' (T.subgroupOf N)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      change q ^ orderOf q = 1
      exact hq1
    rw [QuotientGroup.ker_mk'] at hker
    simpa [Subgroup.mem_subgroupOf] using hker
  have hpowE : E.map (MulAut.conj (a ^ orderOf q)).toMonoidHom = E0 := by
    have hfixkE0 : ∀ k : ℕ, (ConjAct.toConjAct a ^ (2 * k)) • E0 = E0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          change (ConjAct.toConjAct a ^ (2 * (k + 1))) • E0 = E0
          have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
          rw [h2, pow_add, mul_smul, hfixE02, ih]
    obtain ⟨k, hk⟩ := hq_odd
    have hmain : ConjAct.toConjAct (a ^ orderOf q) • E = E0 := by
      rw [hk, map_pow, pow_succ, mul_smul, haE_smul, hfixkE0 k]
    have h := conjAct_smul_eq_map (a ^ orderOf q) E
    rw [hmain] at h
    exact h.symm
  have hpowE_fix : E.map (MulAut.conj (a ^ orderOf q)).toMonoidHom = E := by
    have hmem : a ^ orderOf q ∈ normalizer (E : Set G) := hTN_E ha_pow_mem
    have h := conjAct_smul_eq_map (a ^ orderOf q) E
    rw [Subgroup.conjAct_pointwise_smul_eq_self hmem] at h
    exact h.symm
  exact hne (hpowE_fix.symm.trans hpowE)

end CFSG.OddStandard.SmallF3.Omega
