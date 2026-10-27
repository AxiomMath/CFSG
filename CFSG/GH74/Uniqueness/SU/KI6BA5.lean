module

public import CFSG.GH74.Uniqueness.SU.KI6BA5A
public import CFSG.GH74.Uniqueness.SU.KI6BRankOne
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

namespace A5Cover

variable {K : Type} [Group K]
variable (e : (K ⧸ center K) ≃* alternatingGroup (Fin 5))

@[expose] def proj : K →* alternatingGroup (Fin 5) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

theorem proj_apply (x : K) : proj e x = e (x : K ⧸ center K) := rfl

theorem proj_surjective : Function.Surjective (proj e) := by
  intro a
  obtain ⟨q, rfl⟩ := e.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, rfl⟩

theorem proj_eq_iff {x y : K} : proj e x = proj e y ↔ x⁻¹ * y ∈ center K := by
  rw [proj_apply, proj_apply, e.injective.eq_iff, QuotientGroup.eq]

theorem proj_eq_one_iff {x : K} : proj e x = 1 ↔ x ∈ center K := by
  rw [proj_apply, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem map_center_aut (β : MulAut K) : (center K).map (β : K →* K) = center K := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_center_iff] at hx ⊢
    intro g
    calc g * β x = β (β.symm g) * β x := by simp
      _ = β (β.symm g * x) := by rw [map_mul]
      _ = β (x * β.symm g) := by rw [hx]
      _ = β x * g := by simp
  · intro hy
    refine ⟨β.symm y, ?_, by simp⟩
    rw [mem_center_iff] at hy ⊢
    intro g
    apply β.injective
    simpa using hy (β g)

@[expose] def barAut (β : MulAut K) : MulAut (alternatingGroup (Fin 5)) :=
  e.symm.trans ((QuotientGroup.congr (center K) (center K) β (map_center_aut β)).trans e)

theorem barAut_proj (β : MulAut K) (x : K) : barAut e β (proj e x) = proj e (β x) := by
  simp [barAut, proj_apply, QuotientGroup.congr_mk]

theorem barAut_mul_self {β : MulAut K} (hβ : β * β = 1) : barAut e β * barAut e β = 1 := by
  ext a
  obtain ⟨x, rfl⟩ := proj_surjective e a
  rw [MulAut.mul_apply, barAut_proj, barAut_proj]
  have : β (β x) = x := by simpa using congrArg (fun f : MulAut K => f x) hβ
  rw [this]
  rfl

theorem mem_iff_proj_mem (hc : IsPGroup 2 ↥(center K)) (S : Sylow 2 K) (x : K) :
    x ∈ (S : Subgroup K) ↔ proj e x ∈ (S : Subgroup K).map (proj e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS : center K ≤ (S : Subgroup K) := hc.le_sylow_of_normal S
  constructor
  · intro hx
    exact Subgroup.mem_map_of_mem _ hx
  · rintro ⟨s, hs, hsx⟩
    have h : s⁻¹ * x ∈ center K := (proj_eq_iff e).mp hsx
    have := (S : Subgroup K).mul_mem hs (hZS h)
    simpa using this

theorem card_map_proj [Finite K] (S : Sylow 2 K) :
    Nat.card ((S : Subgroup K).map (proj e)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sylow.card_eq_multiplicity (S.mapSurjective (proj_surjective e))
  rw [A5Aux.card_alternatingGroup_five, A5Aux.factorization_sixty] at h
  exact h

theorem exists_conj_of_bar (hperf : Group.IsPerfect K) {β : MulAut K}
    (g : alternatingGroup (Fin 5)) (hg : ∀ a, barAut e β a = g * a * g⁻¹) :
    ∃ k : K, ∀ x : K, β x = k * x * k⁻¹ := by
  obtain ⟨k, hk⟩ := proj_surjective e g
  have hmem : ∀ x : K, β x * (k * x * k⁻¹)⁻¹ ∈ center K := by
    intro x
    rw [← proj_eq_one_iff e, map_mul, map_inv, map_mul, map_mul, map_inv, hk,
      ← barAut_proj e β x, hg]
    group
  refine ⟨k, ?_⟩
  let c : K →* center K := MonoidHom.mk' (fun x => ⟨β x * (k * x * k⁻¹)⁻¹, hmem x⟩) (by
    intro x y
    apply Subtype.ext
    show β (x * y) * (k * (x * y) * k⁻¹)⁻¹ =
      (β x * (k * x * k⁻¹)⁻¹) * (β y * (k * y * k⁻¹)⁻¹)
    have hcy := mem_center_iff.mp (hmem y)
    have h1 := hcy (k * x * k⁻¹)⁻¹
    calc β (x * y) * (k * (x * y) * k⁻¹)⁻¹
        = β x * (β y * (k * y * k⁻¹)⁻¹) * (k * x * k⁻¹)⁻¹ := by rw [map_mul]; group
      _ = β x * ((k * x * k⁻¹)⁻¹ * (β y * (k * y * k⁻¹)⁻¹)) := by rw [mul_assoc, ← h1]
      _ = _ := by group)
  have hker : c.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hperf]
    exact Abelianization.commutator_subset_ker c
  intro x
  have h1 : c x = 1 := MonoidHom.mem_ker.mp (hker ▸ mem_top x)
  have h2 : β x * (k * x * k⁻¹)⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem commutatorElement_mul_central {a b c d : K} (hc : c ∈ center K) (hd : d ∈ center K) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' : ∀ y : K, c * y * c⁻¹ = y := fun y => by
    rw [mul_inv_eq_iff_eq_mul]; exact (mem_center_iff.mp hc y).symm
  have hd' : ∀ y : K, d * y * d⁻¹ = y := fun y => by
    rw [mul_inv_eq_iff_eq_mul]; exact (mem_center_iff.mp hd y).symm
  simp only [commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * (b * d) * c⁻¹) * a⁻¹ * (b * d)⁻¹ := by group
    _ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by rw [hc' (b * d)]
    _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hd' a⁻¹]

theorem eq_top_of_map_proj_eq_top (hperf : Group.IsPerfect K) {D : Subgroup K}
    (h : D.map (proj e) = ⊤) : D = ⊤ := by
  have hD : ∀ k : K, ∃ d ∈ D, ∃ c ∈ center K, k = d * c := by
    intro k
    have : proj e k ∈ D.map (proj e) := h ▸ mem_top _
    obtain ⟨d, hd, hdk⟩ := this
    refine ⟨d, hd, d⁻¹ * k, ?_, by group⟩
    exact (proj_eq_iff e).mp hdk
  rw [eq_top_iff, ← Group.isPerfect_def.mp hperf, _root_.commutator_def,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨d₁, hd₁, c₁, hc₁, rfl⟩ := hD g₁
  obtain ⟨d₂, hd₂, c₂, hc₂, rfl⟩ := hD g₂
  rw [commutatorElement_mul_central hc₁ hc₂]
  exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)

theorem eq_one_or_eq_of_mem_zpowers {z c : K} (hz : z * z = 1) (hc : c ∈ zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, zpow_two, hz, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, zpow_two, hz, one_zpow, one_mul, zpow_one]

end A5Cover

theorem a5CoverGeneration : A5CoverGeneration := by
  intro K _ _ hK hrank hc hA5 S β hβ2 hβ D hN hC
  obtain ⟨e⟩ := hA5
  have hperf : Group.IsPerfect K := hK.1
  obtain ⟨σ, hσ⟩ := conjPerm_surjective (n := 5) (Or.inl rfl) (A5Cover.barAut e β)
  have hσ2 : σ * σ = 1 := by
    apply conjPerm_injective (n := 5) (by norm_num)
    rw [map_mul, hσ, map_one]
    exact A5Cover.barAut_mul_self e hβ2
  have hσodd : Equiv.Perm.sign σ = -1 := by
    by_contra hne
    have hσA : σ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact h
      · exact absurd h hne
    obtain ⟨k, hk⟩ := A5Cover.exists_conj_of_bar e hperf (β := β) ⟨σ, hσA⟩ (fun a => by
      rw [← hσ]
      apply Subtype.ext
      rw [conjPerm_apply]
      simp)
    obtain ⟨x, hx⟩ := hβ k
    exact hx (hk x)
  have hP : Nat.card ((S : Subgroup K).map (A5Cover.proj e)) = 4 := A5Cover.card_map_proj e S
  have hNb : normalizer (((S : Subgroup K).map (A5Cover.proj e) : Subgroup _) : Set _) ≤
      D.map (A5Cover.proj e) := by
    intro g hg
    obtain ⟨k, rfl⟩ := A5Cover.proj_surjective e g
    refine ⟨k, hN ?_, rfl⟩
    rw [mem_normalizer_iff]
    intro h
    rw [A5Cover.mem_iff_proj_mem e hc S h, A5Cover.mem_iff_proj_mem e hc S (k * h * k⁻¹)]
    have := mem_normalizer_iff.mp hg (A5Cover.proj e h)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hCb : ∀ x : alternatingGroup (Fin 5), x.1 * σ = σ * x.1 →
      x ∈ D.map (A5Cover.proj e) := by
    intro x hx
    obtain ⟨y, rfl⟩ := A5Cover.proj_surjective e x
    refine ⟨y, hC y ?_, rfl⟩
    rw [← A5Cover.proj_eq_one_iff e, map_mul, map_inv, ← A5Cover.barAut_proj e β y, ← hσ]
    have : conjPerm 5 σ (A5Cover.proj e y) = A5Cover.proj e y := by
      apply Subtype.ext
      rw [conjPerm_apply, ← hx]
      group
    rw [this, mul_inv_cancel]
  exact A5Cover.eq_top_of_map_proj_eq_top e hperf
    (A5Aux.eq_top_of_normalizer_le hP hσ2 hσodd hNb hCb)

theorem a5CoverCentralizer : A5CoverCentralizer := by
  intro K _ _ hK hrank hc hA5 S
  obtain ⟨e⟩ := hA5
  obtain ⟨z, hz, huniq, hZ, -⟩ := rankOne_facts K hK hrank hc
  have hP := A5Cover.card_map_proj e S
  intro x hx
  have hxP : A5Cover.proj e x ∈ (S : Subgroup K).map (A5Cover.proj e) := by
    apply A5Aux.centralizer_le_of_card_four hP
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx s hs)]
  by_contra hxZ
  have hπx : A5Cover.proj e x ≠ 1 := fun h => hxZ ((A5Cover.proj_eq_one_iff e).mp h)
  have hsqx : A5Cover.proj e x * A5Cover.proj e x = 1 := A5Aux.mul_self_eq_one_of_mem hP hxP
  obtain ⟨y, hyS, hy1, hyx⟩ : ∃ y ∈ (S : Subgroup K), A5Cover.proj e y ≠ 1 ∧
      A5Cover.proj e y ≠ A5Cover.proj e x := by
    by_contra hcon
    have hcon' : ∀ s ∈ (S : Subgroup K), A5Cover.proj e s ≠ 1 →
        A5Cover.proj e s = A5Cover.proj e x := by
      intro s hs h1
      by_contra h2
      exact hcon ⟨s, hs, h1, h2⟩
    have hsub : ((S : Subgroup K).map (A5Cover.proj e) : Set (alternatingGroup (Fin 5))) ⊆
        {1, A5Cover.proj e x} := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases h1 : A5Cover.proj e s = 1
      · exact Or.inl h1
      · exact Or.inr (hcon' s hs h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, A5Cover.proj e x} : Set (alternatingGroup (Fin 5))).ncard = 2 :=
      Set.ncard_pair hπx.symm
    have h3 : ((S : Subgroup K).map (A5Cover.proj e) :
        Set (alternatingGroup (Fin 5))).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]; exact hP
    omega
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hzc : z ∈ center K := hZ ▸ mem_zpowers z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ w : K, w * w = 1 → w ≠ 1 → w = z := fun w hw hne =>
    huniq w (orderOf_eq_prime (by rwa [sq]) hne)
  have hZc : ∀ c ∈ center K, c = 1 ∨ c = z := fun c hc' =>
    A5Cover.eq_one_or_eq_of_mem_zpowers hz2 (hZ ▸ hc')
  have hxsq : x * x = z := by
    have hmem : x * x ∈ center K :=
      (A5Cover.proj_eq_one_iff e).mp (by rw [map_mul]; exact hsqx)
    rcases hZc _ hmem with h | h
    · exfalso
      have hx1 : x ≠ 1 := fun h' => hπx (by rw [h', map_one])
      exact hxZ (hinv x h hx1 ▸ hzc)
    · exact h
  have hysq : y * y = z := by
    have hsqy := A5Aux.mul_self_eq_one_of_mem hP (Subgroup.mem_map_of_mem _ hyS)
    have hmem : y * y ∈ center K :=
      (A5Cover.proj_eq_one_iff e).mp (by rw [map_mul]; exact hsqy)
    rcases hZc _ hmem with h | h
    · exfalso
      have hy1' : y ≠ 1 := fun h' => hy1 (by rw [h', map_one])
      have := hinv y h hy1'
      exact hy1 ((A5Cover.proj_eq_one_iff e).mpr (this ▸ hzc))
    · exact h
  have hxy : y * x = x * y := mem_centralizer_iff.mp hx y hyS
  have hxy2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxsq, hysq, hz2]
  have hxyc : x * y ∈ center K := by
    by_cases h1 : x * y = 1
    · rw [h1]; exact one_mem _
    · exact hinv _ hxy2 h1 ▸ hzc
  have hπ : A5Cover.proj e x * A5Cover.proj e y = 1 := by
    rw [← map_mul]; exact (A5Cover.proj_eq_one_iff e).mpr hxyc
  exact hyx (mul_left_cancel (hπ.trans hsqx.symm))

end CFSG.GH74.Uniqueness.SU.K.R6
