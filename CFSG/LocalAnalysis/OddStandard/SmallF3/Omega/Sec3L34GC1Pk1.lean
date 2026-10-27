module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Inn

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem conjugate_eq_normalizer_iff {G : Type*} [Group G] {H : Subgroup G} {g : G} :
    CFSG.conjugate H g = H ↔ g ∈ normalizer (H : Set G) := by
  have hmem : ∀ x : G, x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
    intro x
    unfold CFSG.conjugate
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨h, hh, rfl⟩
      have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [e]
      exact hh
    · intro hx
      exact ⟨g * x * g⁻¹, hx, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← hmem, h]
  · intro h
    ext x
    rw [hmem, ← h x]

private theorem l34g_pk1_eq_bot_of_subgroupOf {A : Type} [Group A] {S N : Subgroup A}
    (hNleS : N ≤ S) (h : N.subgroupOf S = ⊥) : N = ⊥ := by
  have h' := congrArg (Subgroup.map S.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hNleS, Subgroup.map_bot] at h'

private theorem l34g_pk1_central {A : Type} [Group A] [Finite A] {S : Subgroup A}
    (hS : SimpleFStarQuotient ↥S) {N : Subgroup A} (hN : IsPGroup 3 ↥N) (hNleS : N ≤ S)
    (hNn : ∀ c ∈ S, ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N = ⊥ := by
  have hNorm : (N.subgroupOf S).Normal := by
    refine ⟨fun n hn s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hNn (s : A) s.2 (n : A) hn
  have hN' : IsPGroup 3 ↥(N.subgroupOf S) :=
    hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNleS).symm
  letI : (N.subgroupOf S).Normal := hNorm
  exact l34g_pk1_eq_bot_of_subgroupOf hNleS (l34g_pGroup_normal_bot hS hN')

private theorem l34g_pk1_aut {A : Type} [Group A] {S : Subgroup A} {x : A} (hx : x * x = 1)
    (hxN : x ∈ normalizer (S : Set A)) (hxSc : ¬ S ≤ centralizer ({x} : Set A)) :
    ∃ a : MulAut ↥S, (∀ s : ↥S, ((a s : ↥S) : A) = x * (s : A) * x⁻¹) ∧ orderOf a = 2 := by
  have ha_apply : ∀ s : ↥S,
      ((S.normalizerMonoidHom ⟨x, hxN⟩ s : ↥S) : A) = x * (s : A) * x⁻¹ := fun s =>
    Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨x, hxN⟩ s
  have haa : S.normalizerMonoidHom ⟨x, hxN⟩ * S.normalizerMonoidHom ⟨x, hxN⟩ = 1 := by
    ext s
    rw [MulAut.mul_apply, MulAut.one_apply, ha_apply (S.normalizerMonoidHom ⟨x, hxN⟩ s),
      ha_apply s]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    rw [hxinv]
    calc x * (x * (s : A) * x) * x = (x * x) * (s : A) * (x * x) := by group
      _ = (s : A) := by rw [hx]; group
  have ha_ne : S.normalizerMonoidHom ⟨x, hxN⟩ ≠ 1 := by
    intro ha1
    apply hxSc
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : S.normalizerMonoidHom ⟨x, hxN⟩ ⟨s, hs⟩ = ⟨s, hs⟩ := by rw [ha1]; rfl
    have h := congrArg (fun t : ↥S => (t : A)) hfix
    rw [ha_apply ⟨s, hs⟩] at h
    have hxc : x * s = s * x := by
      have h' := congrArg (fun t : A => t * x) h
      simpa [mul_assoc] using h'
    exact hxc.symm
  exact ⟨S.normalizerMonoidHom ⟨x, hxN⟩, ha_apply,
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact haa) ha_ne⟩

private theorem l34g_pk1_core {G : Type} [Group G] [Finite G] (hO3 : Asc82FactO3Cent)
    {Inn : Subgroup G} (hInnNormal : Inn.Normal) (hInnCent : centralizer (Inn : Set G) = ⊥)
    (hInnSimple : SimpleFStarQuotient ↥Inn) {a : G} (ha2 : orderOf a = 2) {Nc : Subgroup G}
    (hNc : IsPGroup 3 ↥Nc) (hNcB : Nc ≤ Inn ⊓ centralizer ({a} : Set G))
    (hNcNorm : ∀ c ∈ Inn ⊓ centralizer ({a} : Set G), ∀ n ∈ Nc, c * n * c⁻¹ ∈ Nc) : Nc = ⊥ := by
  let B : Subgroup G := Inn ⊓ centralizer ({a} : Set G)
  have hbot : CFSG.inSubgroup (CFSG.pCore 3) B = ⊥ :=
    hO3 G Inn hInnNormal hInnCent hInnSimple a ha2
  have hNorm : (Nc.subgroupOf B).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hNcNorm (g : G) g.2 (n : G) hn
  have hNcPsub : IsPGroup 3 ↥(Nc.subgroupOf B) :=
    hNc.of_equiv (Subgroup.subgroupOfEquivOfLe hNcB).symm
  have hle : Nc.subgroupOf B ≤ CFSG.pCore 3 ↥B := le_sSup ⟨hNorm, hNcPsub⟩
  have hmap : Nc ≤ CFSG.inSubgroup (CFSG.pCore 3) B := by
    have hmono := Subgroup.map_mono (f := B.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hNcB] at hmono
  rw [hbot] at hmap
  exact eq_bot_iff.mpr hmap

private theorem l34g_pk1_map_normal {A : Type} [Group A] {S : Subgroup A} {x : A}
    {N : Subgroup A} (hNn : ∀ c ∈ S ⊓ centralizer ({x} : Set A), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hc0 : center ↥S = ⊥) {a : MulAut ↥S}
    (ha_apply : ∀ s : ↥S, ((a s : ↥S) : A) = x * (s : A) * x⁻¹) :
    ∀ c ∈ ((MulAut.conj : ↥S →* MulAut ↥S).range ⊓ centralizer ({a} : Set (MulAut ↥S))),
      ∀ n ∈ (N.subgroupOf S).map (MulAut.conj : ↥S →* MulAut ↥S),
        c * n * c⁻¹ ∈ (N.subgroupOf S).map (MulAut.conj : ↥S →* MulAut ↥S) := by
  intro c hc n hn
  obtain ⟨hcInn, hcCent⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨c0, hc0eq⟩ := MonoidHom.mem_range.mp hcInn
  rw [Subgroup.mem_map] at hn
  obtain ⟨n0, hn0, hn0eq⟩ := hn
  rw [Subgroup.mem_map]
  rw [← hn0eq, ← hc0eq]
  refine ⟨c0 * n0 * c0⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    have hc0comm : MulAut.conj c0 * a = a * MulAut.conj c0 := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hcCent
      rwa [← hc0eq] at h
    have hc0fix : a c0 = c0 := (l34g_inn_commute_iff hc0 a c0).mp hc0comm
    have hc0mem : (c0 : A) ∈ centralizer ({x} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun t : ↥S => (t : A)) hc0fix
      rw [ha_apply c0] at h
      calc (c0 : A) * x = (x * (c0 : A) * x⁻¹) * x := by rw [h]
        _ = x * (c0 : A) := by group
    have hn0N : (n0 : A) ∈ N := Subgroup.mem_subgroupOf.mp hn0
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hNn (c0 : A) ⟨c0.2, hc0mem⟩ (n0 : A) hn0N
  · simp only [map_mul, map_inv]

private theorem l34g_pk1_noncentral (hO3 : Asc82FactO3Cent) {A : Type} [Group A] [Finite A]
    {S : Subgroup A} (hS : SimpleFStarQuotient ↥S) {x : A} (hx : x * x = 1)
    (hxN : x ∈ normalizer (S : Set A)) (hxSc : ¬ S ≤ centralizer ({x} : Set A))
    {N : Subgroup A} (hN : IsPGroup 3 ↥N) (hNleS : N ≤ S)
    (hNleC : N ≤ centralizer ({x} : Set A))
    (hNn : ∀ c ∈ S ⊓ centralizer ({x} : Set A), ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N = ⊥ := by
  have hc0 : center ↥S = ⊥ := (l34g_simple_of_simpleFStar hS).2
  obtain ⟨a, ha_apply, ha2⟩ := l34g_pk1_aut hx hxN hxSc
  let Inn : Subgroup (MulAut ↥S) := (MulAut.conj : ↥S →* MulAut ↥S).range
  let N' : Subgroup ↥S := N.subgroupOf S
  let Nc : Subgroup (MulAut ↥S) := N'.map (MulAut.conj : ↥S →* MulAut ↥S)
  have hN' : IsPGroup 3 ↥N' := hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNleS).symm
  have hNc : IsPGroup 3 ↥Nc := hN'.map (MulAut.conj : ↥S →* MulAut ↥S)
  have hNcInn : Nc ≤ Inn := by
    intro e he
    rw [Subgroup.mem_map] at he
    obtain ⟨n, _, rfl⟩ := he
    exact MonoidHom.mem_range.mpr ⟨n, rfl⟩
  have hNcCent : Nc ≤ centralizer ({a} : Set (MulAut ↥S)) := by
    intro e he
    rw [Subgroup.mem_map] at he
    obtain ⟨n, hn, rfl⟩ := he
    rw [Subgroup.mem_centralizer_singleton_iff, l34g_inn_commute_iff hc0 a n]
    have hnN : (n : A) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hnc : (n : A) ∈ centralizer ({x} : Set A) := hNleC hnN
    rw [Subgroup.mem_centralizer_singleton_iff] at hnc
    apply Subtype.ext
    rw [ha_apply n, ← hnc]
    group
  have hNcB : Nc ≤ Inn ⊓ centralizer ({a} : Set (MulAut ↥S)) := le_inf hNcInn hNcCent
  have hNcNorm := l34g_pk1_map_normal hNn hc0 ha_apply
  have hNcbot : Nc = ⊥ :=
    l34g_pk1_core hO3 (l34g_inn_normal ↥S) (l34g_inn_centralizer hc0)
      (l34g_inn_simpleFStar hS) ha2 hNc hNcB hNcNorm
  have hN'bot : N' = ⊥ := by
    have hf : Function.Injective (MulAut.conj : ↥S →* MulAut ↥S) := l34g_conj_injective hc0
    exact (Subgroup.map_eq_bot_iff_of_injective N'
      (f := (MulAut.conj : ↥S →* MulAut ↥S)) hf).mp hNcbot
  exact l34g_pk1_eq_bot_of_subgroupOf hNleS hN'bot

theorem l34g_pk1 (hO3 : Asc82FactO3Cent) {A : Type} [Group A] [Finite A] {S : Subgroup A}
    (hS : SimpleFStarQuotient ↥S) {x : A} (hx : x * x = 1) (hxS : CFSG.conjugate S x = S)
    {N : Subgroup A} (hN : IsPGroup 3 ↥N) (hNle : N ≤ S ⊓ centralizer ({x} : Set A))
    (hNn : ∀ c ∈ S ⊓ centralizer ({x} : Set A), ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N = ⊥ := by
  have hxN : x ∈ normalizer (S : Set A) := conjugate_eq_normalizer_iff.mp hxS
  have hNleS : N ≤ S := hNle.trans inf_le_left
  by_cases hSc : S ≤ centralizer ({x} : Set A)
  · exact l34g_pk1_central hS hN hNleS fun c hc => hNn c ⟨hc, hSc hc⟩
  · exact l34g_pk1_noncentral hO3 hS hx hxN hSc hN hNleS (hNle.trans inf_le_right) hNn

end CFSG.OddStandard.SmallF3.Omega
