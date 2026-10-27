module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Cover
public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem exists_normalizer_of_conj (hzt : ∃ y : G, y * z * y⁻¹ = z * t) {g : G}
    (hg : g * z * g⁻¹ ∈ centralizer (E : Set G)) :
    ∃ m ∈ normalizer (E : Set G), m * z * m⁻¹ = g * z * g⁻¹ := by
  have hE2 : IsPGroup 2 E := h.cfg.T_pgroup.to_le h.E_le_T
  set X : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom with hX
  have hX2 : IsPGroup 2 X := hE2.map _
  have hXz : X ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_iff.1 hg e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * e * g⁻¹⁻¹ * z = g⁻¹ * (e * (g * z * g⁻¹)) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * e) * g⁻¹⁻¹ := by rw [hc]
      _ = z * (g⁻¹ * e * g⁻¹⁻¹) := by group
  obtain ⟨k, hkH, hk⟩ := h.cfg.exists_conj_into_T hX2 hXz
  have hkz : k * z * k⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 hkH
    calc k * z * k⁻¹ = z * k * k⁻¹ := by rw [this]
      _ = z := by group
  have hEy : E.map (MulAut.conj (k⁻¹ * g⁻¹)).toMonoidHom ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    have := hk (g⁻¹ * e * g⁻¹⁻¹) ⟨e, he, by simp⟩
    simpa [MulAut.conj_apply, mul_assoc] using this
  have heq := h.map_conj_eq_of_le hzt hEy
  have hy : k⁻¹ * g⁻¹ ∈ normalizer (E : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  refine ⟨(k⁻¹ * g⁻¹)⁻¹, inv_mem hy, ?_⟩
  calc (k⁻¹ * g⁻¹)⁻¹ * z * ((k⁻¹ * g⁻¹)⁻¹)⁻¹ = g * (k * z * k⁻¹) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [hkz]

omit [Finite G] in
include h in
theorem t_mem_of_maximal {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) :
    t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : t ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    exact h.t_comm_E he
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.t_order]; norm_num)
  have hSt : S ≤ centralizer (zpowers t : Set G) := fun s hs => by
    rw [mem_centralizer_iff]
    rintro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute t s from mem_centralizer_iff.1 (hSC hs) t h.econfig.t_mem).zpow_left
      k).eq
  have hS2' : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) :=
    hS2.to_sup_of_normal_right' ht2 (hSt.trans (centralizer_le_normalizer _))
  have := hSmax _ hS2' (sup_le hSC (zpowers_le.2 hC)) le_sup_left
  rw [← this]
  exact mem_sup_right (mem_zpowers t)

include h in
theorem fusion_of_dihedral (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) {k : ℕ} (hk : 2 ≤ k) (hSd : Nonempty (S ≃* DihedralGroup (2 ^ k))) {g : G}
    (hg : g * z * g⁻¹ ∈ S) : ∃ s ∈ S, g * z * g⁻¹ = s * z * s⁻¹ := by
  obtain ⟨m, hm, hmz⟩ := h.exists_normalizer_of_conj hzt (hSC hg)
  obtain ⟨c, hc, n, hn, hnz, rfl⟩ := h.normalizer_eq_mul hzt hW haut hT hm
  have hτ : g * z * g⁻¹ = c * z * c⁻¹ := by
    rw [← hmz]
    have hnz' : n * z * n⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.1 hnz]
      group
    calc c * n * z * (c * n)⁻¹ = c * (n * z * n⁻¹) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [hnz']
  obtain ⟨N, hNn, -, hNS, hprod⟩ := h.centralizer_oddCore_dihedral hS2 hSC hSmax hk hSd
  have hcmem : (⟨c, hc⟩ : ↥(centralizer (E : Set G))) ∈
      (N : Set ↥(centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set ↥(centralizer (E : Set G))) := by
    rw [hprod]
    trivial
  obtain ⟨o, ho, s', hs', hos⟩ := Set.mem_mul.1 hcmem
  have hcoe : ((o * s' : ↥(centralizer (E : Set G))) : G) = c := congrArg Subtype.val hos
  let zC : ↥(centralizer (E : Set G)) := ⟨z, h.zpowers_le_cent_E (mem_zpowers z)⟩
  let τC : ↥(centralizer (E : Set G)) := ⟨g * z * g⁻¹, hSC hg⟩
  have hτC : τC = (o * s') * zC * (o * s')⁻¹ := by
    apply Subtype.ext
    show g * z * g⁻¹ = ((o * s' : ↥(centralizer (E : Set G))) : G) * z *
      ((o * s' : ↥(centralizer (E : Set G))) : G)⁻¹
    rw [hcoe]
    exact hτ
  have hzS' : zC ∈ S.subgroupOf (centralizer (E : Set G)) := mem_subgroupOf.2 hzS
  have hτS' : τC ∈ S.subgroupOf (centralizer (E : Set G)) := mem_subgroupOf.2 hg
  have hz2 : s' * zC * s'⁻¹ ∈ S.subgroupOf (centralizer (E : Set G)) :=
    mul_mem (mul_mem hs' hzS') (inv_mem hs')
  have hνS : τC * (s' * zC * s'⁻¹)⁻¹ ∈ S.subgroupOf (centralizer (E : Set G)) :=
    mul_mem hτS' (inv_mem hz2)
  have hνN : τC * (s' * zC * s'⁻¹)⁻¹ ∈ N := by
    have h1 : τC * (s' * zC * s'⁻¹)⁻¹ =
        o * ((s' * zC * s'⁻¹) * o⁻¹ * (s' * zC * s'⁻¹)⁻¹) := by
      rw [hτC]
      group
    rw [h1]
    exact N.mul_mem ho (hNn.conj_mem o⁻¹ (N.inv_mem ho) _)
  have hν1 : τC * (s' * zC * s'⁻¹)⁻¹ = 1 := by
    have : τC * (s' * zC * s'⁻¹)⁻¹ ∈ N ⊓ S.subgroupOf (centralizer (E : Set G)) :=
      ⟨hνN, hνS⟩
    rw [hNS, mem_bot] at this
    exact this
  have hτz : τC = s' * zC * s'⁻¹ := mul_inv_eq_one.1 hν1
  exact ⟨((s' : ↥(centralizer (E : Set G))) : G), mem_subgroupOf.1 hs',
    congrArg Subtype.val hτz⟩

include h in
theorem fusion_of_semidihedral (hzt : ∃ y : G, y * z * y⁻¹ = z * t) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) {n : ℕ} (hn : 4 ≤ n) (hSd : Nonempty (S ≃* CFSG.Open.SemidihedralGroup n))
    {g : G} (hg : g * z * g⁻¹ ∈ S) : ∃ s ∈ S, g * z * g⁻¹ = s * z * s⁻¹ := by
  obtain ⟨f⟩ := hSd
  have htS := h.t_mem_of_maximal hS2 hSC hSmax
  have hn3 : 3 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : CFSG.Semidihedral.z n * CFSG.Semidihedral.z n = 1 := by
    have := pow_orderOf_eq_one (CFSG.Semidihedral.z n)
    rw [CFSG.Semidihedral.orderOf_z n hn3] at this
    simpa [pow_two] using this
  have hcentre : ∀ a : ↥S, f a = CFSG.Semidihedral.z n → ∀ x : ↥S, a * x = x * a := by
    intro a ha x
    apply f.injective
    rw [map_mul, map_mul, ha]
    exact (Subgroup.mem_center_iff.1 (CFSG.Semidihedral.z_mem_center n hn) (f x)).symm
  let zS : ↥S := ⟨z, hzS⟩
  let tS : ↥S := ⟨t, htS⟩
  let τS : ↥S := ⟨g * z * g⁻¹, hg⟩
  have hzord : orderOf zS = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext h.cfg.z_sq
    · intro h1
      exact h.cfg.z_ne (congrArg Subtype.val h1)
  have hτord : orderOf τS = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      apply Subtype.ext
      show g * z * g⁻¹ * (g * z * g⁻¹) = 1
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [h.cfg.z_sq]; group
    · intro h1
      have h2 : g * z * g⁻¹ = 1 := congrArg Subtype.val h1
      exact h.cfg.z_ne (by simpa using h2)
  have hzv : f zS ≠ CFSG.Semidihedral.z n := by
    intro hv
    have hzc := hcentre zS hv
    have hSz : S ≤ centralizer ({z} : Set G) := fun s hs => by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hzc ⟨s, hs⟩).symm
    have hle := h.le_of_two_group hzt hS2 hSC hSz
    have hcard := Subgroup.card_le_of_le hle
    rw [h.card_zpowers_sup] at hcard
    have hS : Nat.card S = 2 ^ n := by
      rw [Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n hn3]
    rw [hS] at hcard
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hv : IsConj (CFSG.Semidihedral.s n) (f zS) :=
    (CFSG.QuasiDihedralFusion.sd_involution_cases hn _
      (by rw [MulEquiv.orderOf_eq]; exact hzord)).resolve_left hzv
  rcases CFSG.QuasiDihedralFusion.sd_involution_cases hn (f τS)
      (by rw [MulEquiv.orderOf_eq]; exact hτord) with hu | hu
  · exfalso
    have htc : ∀ x : ↥S, tS * x = x * tS := fun x =>
      Subtype.ext (mem_centralizer_iff.1 (hSC x.2) t h.econfig.t_mem)
    have hcen : ∀ a : ↥S, (∀ x : ↥S, a * x = x * a) → a ≠ 1 →
        f a = CFSG.Semidihedral.z n := by
      intro a ha ha1
      have hmem : f a ∈ Subgroup.center (CFSG.Open.SemidihedralGroup n) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := f.surjective y
        rw [← map_mul, ← map_mul, ha x]
      rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hmem
      rcases mem_zpowers_sq_eq_one hzz hmem with h1 | h1
      · exact absurd (f.injective (h1.trans (map_one f).symm)) ha1
      · exact h1
    have htS1 : tS ≠ 1 := fun h1 => h.cfg.t_ne (congrArg Subtype.val h1)
    have h1 := hcen tS htc htS1
    have hτc : ∀ x : ↥S, τS * x = x * τS := by
      intro x
      apply f.injective
      rw [map_mul, map_mul, hu]
      exact (Subgroup.mem_center_iff.1 (CFSG.Semidihedral.z_mem_center n hn) (f x)).symm
    have h2 : τS = tS := f.injective (hu.trans h1.symm)
    exact h.cfg.conj_z_ne_t g (congrArg Subtype.val h2)
  · obtain ⟨c, hc⟩ := isConj_iff.1 (hv.symm.trans hu)
    refine ⟨((f.symm c : ↥S) : G), (f.symm c).2, ?_⟩
    have h1 : f (f.symm c * zS * (f.symm c)⁻¹) = f τS := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hc
    have h2 := f.injective h1
    exact (congrArg Subtype.val h2).symm

include h in
theorem fusion_in_sylow (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) {x : G} (hxQ : x ∈ Q) (hxT : x ∉ T)
    (hxN : x ∈ normalizer (T : Set G)) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) {g : G} (hg : g * z * g⁻¹ ∈ S) : ∃ s ∈ S, g * z * g⁻¹ = s * z * s⁻¹ := by
  rcases h.sylow_centralizer_shape' hzt haut hT hQ hTQ hxQ hxT hxN hS2 hSC hSmax hzS with
    ⟨k, hk, hSd⟩ | ⟨n, hn, hSd⟩
  · exact h.fusion_of_dihedral hzt hW haut hT hS2 hSC hSmax hzS hk hSd hg
  · exact h.fusion_of_semidihedral hzt hS2 hSC hSmax hzS hn hSd hg

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
