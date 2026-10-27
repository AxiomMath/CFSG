module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplQuotA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplFin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem oddCoreIn_le_X (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private lemma s8q_mem_centralizer {V : Subgroup G} (hV : IsElemAb2 V 8) (a : ↥V) :
    (a : G) ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact congrArg Subtype.val (hV.1.1.is_comm.comm ⟨h, hh⟩ a)

private lemma s8q_mk_eq_one_iff {V : Subgroup G}
    (n : ↥(normalizer (V : Set G))) :
    (QuotientGroup.mk n : ↥(normalizer (V : Set G)) ⧸
      (oddCoreIn (normalizer (V : Set G))).subgroupOf (normalizer (V : Set G))) = 1 ↔
      (n : G) ∈ oddCoreIn (normalizer (V : Set G)) := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private lemma s8qρ_mk [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (n : ↥(normalizer (V : Set G))) :
    s8qρ hV (QuotientGroup.mk n) = V.normalizerMonoidHom n := by
  simpa [s8qρ] using QuotientGroup.lift_mk (s8q_le_ker hV) n

private lemma s8qι_mk (V : Subgroup G) (a : ↥V) :
    s8qι V a = QuotientGroup.mk (Subgroup.inclusion Subgroup.le_normalizer a) := rfl

theorem s8q_hι [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    Function.Injective (s8qι V) := by
  intro a b hab
  have hab' : QuotientGroup.mk (Subgroup.inclusion Subgroup.le_normalizer a) =
      QuotientGroup.mk (Subgroup.inclusion Subgroup.le_normalizer b) := hab
  have hmem := (QuotientGroup.eq).mp hab'
  have hOg : (((Subgroup.inclusion Subgroup.le_normalizer a)⁻¹ *
      Subgroup.inclusion Subgroup.le_normalizer b : ↥(normalizer (V : Set G))) : G) ∈
      oddCoreIn (normalizer (V : Set G)) := (Subgroup.mem_subgroupOf).mp hmem
  have hOg' : (a : G)⁻¹ * (b : G) ∈ oddCoreIn (normalizer (V : Set G)) := by
    simpa using hOg
  have hVg' : (a : G)⁻¹ * (b : G) ∈ V := V.mul_mem (V.inv_mem a.2) b.2
  have hbot : (a : G)⁻¹ * (b : G) ∈ (⊥ : Subgroup G) := by
    rw [← s8q_inf_bot hV]
    exact ⟨hOg', hVg'⟩
  have hone : (a : G)⁻¹ * (b : G) = 1 := by simpa using hbot
  exact Subtype.ext (inv_mul_eq_one.mp hone)

theorem s8q_hker [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (hC : centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G))) :
    (s8qρ hV).ker = (s8qι V).range := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective γ
    have hφ : V.normalizerMonoidHom n = 1 := by
      rw [← s8qρ_mk hV n]
      exact hγ
    have hmemker : n ∈ V.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hφ
    rw [V.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmemker
    have hn_sup : (n : G) ∈ V ⊔ oddCoreIn (normalizer (V : Set G)) := by
      rw [← hC]
      exact hmemker
    obtain ⟨v, hv, o, ho, hno⟩ := s8_mem_sup_of_commute
      (A := V) (B := oddCoreIn (normalizer (V : Set G)))
      (fun a ha b hb => (s8q_comm hV hb ha).symm) hn_sup
    have hn_eq : n = Subgroup.inclusion Subgroup.le_normalizer ⟨v, hv⟩ *
        ⟨o, oddCoreIn_le_X (normalizer (V : Set G)) ho⟩ := by
      apply Subtype.ext
      simpa using hno
    have hmo : QuotientGroup.mk (⟨o, oddCoreIn_le_X (normalizer (V : Set G)) ho⟩ :
        ↥(normalizer (V : Set G))) = 1 :=
      (s8q_mk_eq_one_iff _).mpr ho
    refine ⟨⟨v, hv⟩, ?_⟩
    have hmkn : QuotientGroup.mk n = s8qι V ⟨v, hv⟩ := by
      rw [hn_eq, QuotientGroup.mk_mul, hmo, mul_one]
      rfl
    exact hmkn.symm
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [MonoidHom.mem_ker]
    have h1 : V.normalizerMonoidHom (Subgroup.inclusion Subgroup.le_normalizer a) = 1 := by
      rw [← MonoidHom.mem_ker, V.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact s8q_mem_centralizer hV a
    change s8qρ hV (QuotientGroup.mk (Subgroup.inclusion Subgroup.le_normalizer a)) = 1
    rw [s8qρ_mk hV (Subgroup.inclusion Subgroup.le_normalizer a)]
    exact h1

theorem s8q_hequi [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (γ : S8Quot (normalizer (V : Set G))) (a : ↥V) :
    γ * s8qι V a * γ⁻¹ = s8qι V (s8qρ hV γ a) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective γ
  calc QuotientGroup.mk n * s8qι V a * (QuotientGroup.mk n)⁻¹
      = QuotientGroup.mk (n * Subgroup.inclusion Subgroup.le_normalizer a * n⁻¹) := by
        rw [s8qι_mk]
        simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    _ = s8qι V (s8qρ hV (QuotientGroup.mk n) a) := by
        rw [s8qρ_mk hV n, s8qι_mk]
        rfl

theorem s8q_range [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    (s8qρ hV).range = autIn (normalizer (V : Set G)) V := by
  rw [autIn, Subgroup.subgroupOf_self, Subgroup.map_top]
  apply le_antisymm
  · intro x hx
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective γ
    exact ⟨n, (s8qρ_mk hV n).symm⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨QuotientGroup.mk n, s8qρ_mk hV n⟩

private lemma s8q_range_normal [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    (s8qι V).range.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  exact ⟨s8qρ hV g a, (s8q_hequi hV g a).symm⟩

theorem s8q_pull [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    {K' : Subgroup (S8Quot (normalizer (V : Set G)))} (h1 : K' ⊓ (s8qι V).range = ⊥)
    (h2 : K' ⊔ (s8qι V).range = ⊤) :
    ∃ K : Subgroup G, K ≤ normalizer (V : Set G) ∧ oddCoreIn (normalizer (V : Set G)) ≤ K ∧
      K ⊓ V = ⊥ ∧ K ⊔ V = normalizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let O := oddCoreIn N
  let mkq : ↥N →* S8Quot N := QuotientGroup.mk' (O.subgroupOf N)
  let K : Subgroup G := (K'.comap mkq).map N.subtype
  have hmem : ∀ x : G, x ∈ K ↔ ∃ n : ↥N, mkq n ∈ K' ∧ (n : G) = x := by
    intro x
    change x ∈ (K'.comap mkq).map N.subtype ↔ ∃ n : ↥N, mkq n ∈ K' ∧ (n : G) = x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, Subgroup.mem_comap.mp hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, Subgroup.mem_comap.mpr hn, rfl⟩
  have hKN : K ≤ N := by
    intro x hx
    obtain ⟨n, _, hnx⟩ := (hmem x).mp hx
    rw [← hnx]
    exact n.2
  have hOK : O ≤ K := by
    intro o ho
    refine (hmem o).mpr ⟨⟨o, oddCoreIn_le_X N ho⟩, ?_, rfl⟩
    have hmo : mkq ⟨o, oddCoreIn_le_X N ho⟩ = 1 :=
      (s8q_mk_eq_one_iff (V := V) ⟨o, oddCoreIn_le_X N ho⟩).mpr ho
    rw [hmo]
    exact K'.one_mem
  have hKV : K ⊓ V = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxK, hxV⟩ := hx
      obtain ⟨n, hnK, hnx⟩ := (hmem x).mp hxK
      have hn_eq : n = Subgroup.inclusion Subgroup.le_normalizer ⟨x, hxV⟩ := by
        apply Subtype.ext
        simpa [Subgroup.coe_inclusion] using hnx
      have hrange : mkq n ∈ (s8qι V).range := by
        rw [hn_eq]
        exact ⟨⟨x, hxV⟩, rfl⟩
      have hbot : mkq n ∈ (⊥ : Subgroup (S8Quot N)) := by
        rw [← h1]
        exact ⟨hnK, hrange⟩
      have hone : mkq n = 1 := by simpa using hbot
      have hxO : x ∈ O := by
        have h1' := (s8q_mk_eq_one_iff (V := V) n).mp hone
        rw [← hnx]
        exact h1'
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← s8q_inf_bot hV]
        exact ⟨hxO, hxV⟩
      simpa using hxbot
    · exact bot_le
  refine ⟨K, hKN, hOK, hKV, ?_⟩
  apply le_antisymm
  · exact sup_le hKN Subgroup.le_normalizer
  · intro g hg
    let n : ↥N := ⟨g, hg⟩
    have hn_coe : (n : G) = g := rfl
    haveI : (s8qι V).range.Normal := s8q_range_normal hV
    have htop : mkq n ∈ K' ⊔ (s8qι V).range := by
      rw [h2]
      exact Subgroup.mem_top _
    obtain ⟨k', hk'K', z, hzrange, hkz⟩ :=
      (Subgroup.mem_sup_of_normal_right).mp htop
    obtain ⟨a, rfl⟩ := hzrange
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective k'
    have hk₀' : mkq k₀ = k' := hk₀
    have hkK : (k₀ : G) ∈ K :=
      (hmem (k₀ : G)).mpr ⟨k₀, by rwa [hk₀'], rfl⟩
    let w : ↥N := k₀ * Subgroup.inclusion Subgroup.le_normalizer a
    have hmkw : mkq w = mkq n := by
      change mkq (k₀ * Subgroup.inclusion Subgroup.le_normalizer a) = mkq n
      rw [map_mul, hk₀']
      rw [← hkz]
      rfl
    have ho_mem : w⁻¹ * n ∈ O.subgroupOf N := by
      have hq : (w : ↥N ⧸ O.subgroupOf N) = (n : ↥N ⧸ O.subgroupOf N) := hmkw
      exact QuotientGroup.eq.mp hq
    have hO : ((w⁻¹ * n : ↥N) : G) ∈ O := (Subgroup.mem_subgroupOf).mp ho_mem
    have hcoe : ((w⁻¹ * n : ↥N) : G) = (a : G)⁻¹ * (k₀ : G)⁻¹ * g := by
      simp only [w, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hn_coe]
      group
    have hg_eq : g = k₀ * (a : G) * ((w⁻¹ * n : ↥N) : G) := by
      rw [hcoe]
      group
    have ho_comm : (a : G) * ((w⁻¹ * n : ↥N) : G) = ((w⁻¹ * n : ↥N) : G) * (a : G) :=
      (s8q_comm hV hO a.2).symm
    have hg_final : g = (k₀ * ((w⁻¹ * n : ↥N) : G)) * (a : G) := by
      calc g = k₀ * ((a : G) * ((w⁻¹ * n : ↥N) : G)) := by
            rw [hg_eq]; group
        _ = k₀ * (((w⁻¹ * n : ↥N) : G) * (a : G)) := by rw [ho_comm]
        _ = (k₀ * ((w⁻¹ * n : ↥N) : G)) * (a : G) := by group
    rw [hg_final]
    exact Subgroup.mul_mem_sup (K.mul_mem hkK (hOK hO)) a.2

end CFSG.OddStandard.SmallF3.Omega