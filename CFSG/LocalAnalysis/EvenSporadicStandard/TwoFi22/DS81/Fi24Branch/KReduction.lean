module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ChoiceZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KPullback

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Monster.B.Fischer
open scoped commutatorElement
open Fi22TwoB (Cbar t1)

theorem t_mem_Kg_of_comm {G : Type} [Group G] {t z : G} (htz : t * z = z * t) : t ∈ Kg t z :=
  mem_Kg.mpr ⟨rfl, htz⟩

theorem z_mem_Kg_of_comm {G : Type} [Group G] {t z : G} (htz : t * z = z * t) : z ∈ Kg t z :=
  mem_Kg.mpr ⟨htz.symm, rfl⟩

private theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {t c : G} (ht : orderOf t = 2)
    (hc : c ∈ zpowers t) : c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have h := zpow_mod_orderOf t k
  rw [ht] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    simp only [Nat.cast_ofNat, h0, zpow_zero]
  · right
    rw [← h]
    simp only [Nat.cast_ofNat, h1, zpow_one]

section Reduction

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem kData_of_piK {Q : Subgroup (Equiv.Perm (Fin 3510))} (hQ : Fi22TwoBData Q)
    (htz : t * z = z * t) (ht : orderOf t = 2)
    (θ : ↥(Kg t z) →* Equiv.Perm (Fin 3510)) (hrange : θ.range = Cbar)
    (hker : θ.ker = (zpowers t).subgroupOf (Kg t z))
    (hθz : θ ⟨z, z_mem_Kg_of_comm htz⟩ = t1) : KData t z := by
  have htK : t ∈ Kg t z := t_mem_Kg_of_comm htz
  have hzK : z ∈ Kg t z := z_mem_Kg_of_comm htz
  have hker2 : Nat.card θ.ker = 2 := by
    rw [hker, ← ht, ← Nat.card_zpowers]
    exact Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr htK)).toEquiv
  have hkerP : IsPGroup 2 θ.ker := IsPGroup.of_card (n := 1) (by rw [hker2]; norm_num)
  have hQr : Q ≤ θ.range := hrange ▸ hQ.Q_le
  have hVeq : Vtz t z = pullK θ (zpowers t1) := (pullK_zpowers θ htK hzK hker hθz).symm
  have hOKeq : OKg t z = pullK θ Q := by
    unfold OKg
    rw [O2In_eq_pullK hrange hkerP, hQ.O2]
  have hcentral : θ.ker ≤ center ↥(Kg t z) := by
    intro x hx
    rw [hker] at hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have hyt : (y : G) * t = t * (y : G) := (mem_Kg.mp y.2).1
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    have hn' : t ^ n = (x : G) := hn
    show (y : G) * (x : G) = (x : G) * (y : G)
    rw [← hn']
    exact (Commute.zpow_right (show Commute (y : G) t from hyt) n).eq
  have hmemQ : ∀ x (hx : x ∈ OKg t z), θ ⟨x, OKg_le_Kg t z hx⟩ ∈ Q := by
    intro x hx
    rw [hOKeq] at hx
    obtain ⟨_, h⟩ := mem_pullK.mp hx
    exact h
  have hlift : ∀ q ∈ Q, ∃ k : ↥(Kg t z), (k : G) ∈ OKg t z ∧ θ k = q := by
    intro q hq
    obtain ⟨k, hk⟩ := hQr hq
    refine ⟨k, ?_, hk⟩
    rw [hOKeq]
    exact mem_pullK.mpr ⟨k.2, by rw [show (⟨(k : G), k.2⟩ : ↥(Kg t z)) = k from rfl, hk]; exact hq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := Subgroup.card_ker_mul_card_range θ
    rw [hrange, hker2, hQ.card_C] at h
    rw [← h]
    norm_num
  ·
    rw [hOKeq, card_pullK θ hQr, hker2, hQ.card_Q]
    norm_num
  ·
    rw [hVeq, hOKeq]
    exact pullK_mono θ (zpowers_le.mpr hQ.t1_mem)
  ·
    intro x hx
    obtain ⟨hxK, hxC⟩ := mem_inf.mp hx
    rw [hOKeq]
    refine mem_pullK.mpr ⟨hxK, hQ.cent (mem_inf.mpr ⟨?_, ?_⟩)⟩
    · rw [← hrange]
      exact ⟨_, rfl⟩
    · rw [mem_centralizer_iff]
      intro q hq
      obtain ⟨k, hkO, hk⟩ := hlift q hq
      have hkx : (k : G) * x = x * (k : G) := mem_centralizer_iff.mp hxC (k : G) hkO
      rw [← hk, ← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext hkx)
  ·
    intro x hx
    constructor
    · intro hc
      rw [hVeq]
      refine mem_pullK.mpr ⟨OKg_le_Kg t z hx, ?_⟩
      refine (hQ.center _ (hmemQ x hx)).mp ?_
      intro q hq
      obtain ⟨k, hkO, hk⟩ := hlift q hq
      rw [← hk, ← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext (hc (k : G) hkO))
    · intro hxV y hy
      have h := Kg_comm_Vtz (OKg_le_Kg t z hy) hxV
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
  ·
    intro x hx
    rw [hVeq]
    have hx2 : x ^ 2 ∈ Kg t z := pow_mem (OKg_le_Kg t z hx) 2
    refine mem_pullK.mpr ⟨hx2, ?_⟩
    have e : (⟨x ^ 2, hx2⟩ : ↥(Kg t z)) = ⟨x, OKg_le_Kg t z hx⟩ ^ 2 := rfl
    rw [e, map_pow]
    exact hQ.sq _ (hmemQ x hx)
  ·
    intro x hx y hy
    rw [hVeq]
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ Kg t z :=
      mul_mem (mul_mem (mul_mem (OKg_le_Kg t z hx) (OKg_le_Kg t z hy))
        (inv_mem (OKg_le_Kg t z hx))) (inv_mem (OKg_le_Kg t z hy))
    refine mem_pullK.mpr ⟨hxy, ?_⟩
    have e : (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : ↥(Kg t z)) =
        ⟨x, OKg_le_Kg t z hx⟩ * ⟨y, OKg_le_Kg t z hy⟩ * ⟨x, OKg_le_Kg t z hx⟩⁻¹ *
          ⟨y, OKg_le_Kg t z hy⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hQ.comm _ (hmemQ x hx) _ (hmemQ y hy)
  ·
    obtain ⟨X, hX, ρ, hρs, hρk, hU⟩ := hQ.quot
    obtain ⟨π, hπs, hπk⟩ := exists_quot_pullK hrange ρ hρs hρk
    exact ⟨X, hX, π, hπs, by rw [hπk, hOKeq], hU⟩
  ·
    intro B hB _ hBc
    have hBK : B ≤ Kg t z := hB.trans (OKg_le_Kg t z)
    have h1 : Nat.card B = Nat.card (B.subgroupOf (Kg t z)) :=
      (Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).symm
    have h2 := card_le_mul_card_map θ (B.subgroupOf (Kg t z))
    have h3 : Nat.card ((B.subgroupOf (Kg t z)).map θ) ≤ 2 ^ 6 := by
      apply hQ.abelian
      · rintro _ ⟨x, hx, rfl⟩
        exact hmemQ (x : G) (hB hx)
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg θ (Subtype.ext (hBc _ hx _ hy))
    rw [h1]
    calc Nat.card (B.subgroupOf (Kg t z))
        ≤ Nat.card θ.ker * Nat.card ((B.subgroupOf (Kg t z)).map θ) := h2
      _ ≤ 2 * 2 ^ 6 := by rw [hker2]; exact Nat.mul_le_mul_left 2 h3
      _ = 2 ^ 7 := by norm_num
  ·
    obtain ⟨Y', hY'C, hY'perf, hY'idx, hY'lat⟩ := hQ.perfect
    have hY'r : Y' ≤ θ.range := hrange ▸ hY'C
    obtain ⟨Y₀, hY₀perf, hY₀map, hY₀sup⟩ := exists_perfect_comap θ hcentral hY'r hY'perf
    refine ⟨Y₀.map (Kg t z).subtype, map_subtype_le _, ?_, ?_, ?_⟩
    · rw [← map_commutator, hY₀perf]
    · rw [hOKeq, map_subtype_sup_pullK θ hY'r hQr hY₀sup, relIndex_pullK, hrange]
      exact hY'idx
    · intro U hVU hUO hInv
      have hUK : U ≤ Kg t z := hUO.trans (OKg_le_Kg t z)
      have htU : t ∈ U := hVU (subset_closure (Set.mem_insert _ _))
      have hzU : z ∈ U := hVU (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      have hker_le : θ.ker ≤ U.subgroupOf (Kg t z) := by
        rw [hker]
        intro x hx
        exact zpowers_le.mpr htU hx
      have hU₁Q : (U.subgroupOf (Kg t z)).map θ ≤ Q := by
        rintro _ ⟨x, hx, rfl⟩
        exact hmemQ (x : G) (hUO hx)
      have hU₁z : zpowers t1 ≤ (U.subgroupOf (Kg t z)).map θ := by
        rw [zpowers_le]
        exact ⟨⟨z, hzK⟩, hzU, hθz⟩
      have hinv : InvUnder Y' ((U.subgroupOf (Kg t z)).map θ) := by
        rw [← hY₀map]
        exact invUnder_map_pullK θ hInv
      have hcard := hY'lat _ hU₁z hU₁Q hinv
      have hU₁r : (U.subgroupOf (Kg t z)).map θ ≤ θ.range := map_le_range _ _
      have hUeq : pullK θ ((U.subgroupOf (Kg t z)).map θ) = U :=
        pullK_map_subgroupOf θ hUK hker_le
      have hcU : Nat.card U = 2 * Nat.card ((U.subgroupOf (Kg t z)).map θ) := by
        rw [← hUeq, card_pullK θ hU₁r, hker2, hUeq]
      rw [hcU]
      rcases hcard with h | h | h | h
      · left
        rw [h]
        norm_num
      · right; left
        rw [h]
        norm_num
      · right; right; left
        rw [h]
        norm_num
      · right; right; right
        rw [h]
        norm_num

end Reduction

section Main

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

theorem Std.z_mem_Kg (h : Std G L E t) (hz : IsZ E t z) : z ∈ Kg t z :=
  z_mem_Kg_of_comm (h.E_comm t h.t_mem_E z hz.1)

theorem Std.mem_Kg_iff
    (h : Std G L E t) (hz : IsZ E t z) (π : ↥(centralizer ({t} : Set G)) →* fi22R)
    (hπk : π.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)))
    (hπz : ((π ⟨z, h.E_le_H hz.1⟩ : fi22R) : Equiv.Perm (Fin 3510)) = t1)
    (x : ↥(centralizer ({t} : Set G))) :
    (x : G) ∈ Kg t z ↔ ((π x : fi22R) : Equiv.Perm (Fin 3510)) ∈ Cbar := by
  have hcb : ∀ p : fi22R, (p : Equiv.Perm (Fin 3510)) ∈ Cbar ↔
      (p : Equiv.Perm (Fin 3510)) * t1 = t1 * p := by
    intro p
    rw [show Cbar = fi22R ⊓ centralizer {t1} from rfl, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨p.2, h⟩⟩
  rw [hcb]
  set zH : ↥(centralizer ({t} : Set G)) := ⟨z, h.E_le_H hz.1⟩ with hzH
  constructor
  · intro hxK
    have e : x * zH = zH * x := Subtype.ext (mem_Kg.mp hxK).2
    have e' := congrArg
      (fun w : ↥(centralizer ({t} : Set G)) => ((π w : fi22R) : Equiv.Perm (Fin 3510))) e
    simp only [map_mul, Subgroup.coe_mul, hπz] at e'
    exact e'
  · intro hcx
    have hc : π (x * zH * x⁻¹ * zH⁻¹) = 1 := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπz, OneMemClass.coe_one]
      rw [hcx]
      group
    have hmem : x * zH * x⁻¹ * zH⁻¹ ∈ π.ker := hc
    rw [hπk, mem_subgroupOf] at hmem
    have hmem' : (x : G) * z * (x : G)⁻¹ * z⁻¹ ∈ zpowers t := hmem
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_t hmem' with h1 | h1
    · refine mem_Kg.mpr ⟨mem_centralizer_singleton_iff.mp x.2, ?_⟩
      calc (x : G) * z = ((x : G) * z * (x : G)⁻¹ * z⁻¹) * z * (x : G) := by group
        _ = z * (x : G) := by rw [h1, one_mul]
    · exfalso
      have h2 : (x : G) * z * (x : G)⁻¹ = t * z := by
        calc (x : G) * z * (x : G)⁻¹ = ((x : G) * z * (x : G)⁻¹ * z⁻¹) * z := by group
          _ = t * z := by rw [h1]
      exact not_isConj_t_z h hz
        ((isConj_t_tz h.m24 hz).trans (isConj_iff.mpr ⟨(x : G), h2⟩).symm)


theorem Std.exists_piK (h : Std G L E t) (hz : IsZ E t z) :
    ∃ θ : ↥(Kg t z) →* Equiv.Perm (Fin 3510), θ.range = Cbar ∧
      θ.ker = (zpowers t).subgroupOf (Kg t z) ∧ θ ⟨z, h.z_mem_Kg hz⟩ = t1 := by
  obtain ⟨π, hπs, hπk, hπz⟩ := h.exists_piR_z hz
  have hKH : Kg t z ≤ centralizer ({t} : Set G) := inf_le_left
  let θ : ↥(Kg t z) →* Equiv.Perm (Fin 3510) :=
    fi22R.subtype.comp (π.comp (Subgroup.inclusion hKH))
  have hA := h.mem_Kg_iff hz π hπk hπz
  refine ⟨θ, ?_, ?_, hπz⟩
  · apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact (hA (Subgroup.inclusion hKH k)).mp k.2
    · intro c hc
      have hcR : c ∈ fi22R := (mem_inf.mp hc).1
      obtain ⟨x, hx⟩ := hπs ⟨c, hcR⟩
      have hxc : ((π x : fi22R) : Equiv.Perm (Fin 3510)) = c := congrArg Subtype.val hx
      have hxK : (x : G) ∈ Kg t z := (hA x).mpr (hxc ▸ hc)
      exact ⟨⟨x, hxK⟩, hxc⟩
  · ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h3 : Subgroup.inclusion hKH k ∈ π.ker := Subtype.ext h1
      rw [hπk, mem_subgroupOf] at h3
      exact h3
    · intro h1
      have h3 : Subgroup.inclusion hKH k ∈ π.ker := by
        rw [hπk, mem_subgroupOf]
        exact h1
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp h3)

theorem kFacts_of_fi22TwoBFacts (h : Fi22TwoBFacts) : KFacts := by
  intro G _ _ L E t z hStd hz
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨θ, hrange, hker, hθz⟩ := hStd.exists_piK hz
  exact kData_of_piK hQ (hStd.E_comm t hStd.t_mem_E z hz.1) hStd.orderOf_t θ hrange hker hθz

end Main

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
