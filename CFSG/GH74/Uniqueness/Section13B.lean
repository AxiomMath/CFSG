module

public import CFSG.GH74.Uniqueness.Section13Dict

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A6.Dict.nonempty_equiv {F T : Subgroup X} {n e : ℕ}
    {Tb : Sylow 2 (↥F ⧸ center ↥F)} (h : A6.Dict Z M F n e Tb T) :
    Nonempty (↥T ≃* ↥(Tb : Subgroup (↥F ⧸ center ↥F))) := by
  let f : ↥T →* ↥(Tb : Subgroup (↥F ⧸ center ↥F)) :=
    ((QuotientGroup.mk' (center ↥F)).comp ((Subgroup.inclusion h.le))).codRestrict _
      (fun x => h.mk_mem x.2)
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => by
      have h1 := Subtype.ext_iff.mp hxy
      exact Subtype.ext (h.eq_of_mk_eq x.2 y.2 h1), ?_⟩
    rintro ⟨k, hk⟩
    rw [← h.map] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact ⟨⟨(x : X), hx⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f hf⟩

theorem A6.nonempty_sylow_equiv {K₁ K₂ : Type*} [Group K₁] [Group K₂] [Finite K₁] [Finite K₂]
    {n e₁ e₂ : ℕ} (h₁ : Bender.BenderType K₁ n 3 e₁) (h₂ : Bender.BenderType K₂ n 3 e₂)
    (P₁ : Sylow 2 K₁) (P₂ : Sylow 2 K₂) :
    Nonempty (↥(P₁ : Subgroup K₁) ≃* ↥(P₂ : Subgroup K₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ₁⟩ : Nonempty (K₁ ≃* Theory.Comparator.PSU3Model n) := by
    cases h₁ with
    | unitary n hn e => exact ⟨e⟩
  obtain ⟨ψ₂⟩ : Nonempty (K₂ ≃* Theory.Comparator.PSU3Model n) := by
    cases h₂ with
    | unitary n hn e => exact ⟨e⟩
  let ψ : K₁ ≃* K₂ := ψ₁.trans ψ₂.symm
  let P₁' : Sylow 2 K₂ := P₁.mapSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hP₁' : (P₁' : Subgroup K₂) = (P₁ : Subgroup K₁).map ψ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := ψ.toMonoidHom) ψ.surjective P₁
  have e₁ : ↥(P₁ : Subgroup K₁) ≃* ↥(P₁' : Subgroup K₂) :=
    ((P₁ : Subgroup K₁).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hP₁'.symm)
  exact ⟨e₁.trans (Sylow.equiv P₁' P₂)⟩

theorem A6.exists_R
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n e e' : ℕ} (hL : LData c n 1) {u : X}
    {Lu LA T V : Subgroup X} {Tb : Sylow 2 (↥Lu ⧸ center ↥Lu)}
    {Vb : Sylow 2 (↥LA ⧸ center ↥LA)} (hDu : A6.Dict Z M Lu n e Tb T)
    (hDA : A6.Dict Z M LA n e' Vb V) (hMu' : zHull Z M ≤ Lu) (hMA : zHull Z M ≤ LA)
    (hTu : ∀ s ∈ T, u * s = s * u) {U : Subgroup X} (hUV : U ≤ V)
    (hUc : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v) (hUcard : Nat.card U = (2 ^ n) ^ 2)
    (hUsq : ∀ w ∈ U, w * w ∈ zHull Z M)
    (hUinv : ∀ w ∈ U, u * w * u⁻¹ = w⁻¹) (hTU : ∀ s ∈ T, ∀ w ∈ U, s * w = w * s) :
    ∃ R : Subgroup X, IsPGroup 2 R ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ R ≤ M ∧
      (2 ^ n) ^ 2 ≤ ({x : X | x ∈ R ∧ x * x = 1} : Set X).ncard ∧ (2 ^ n) ^ 3 ≤ Nat.card R ∧
      ∃ x ∈ R, x ∉ zHull Z M ∧ orderOf x = 2 := by
  classical
  obtain ⟨φV⟩ := hDA.nonempty_equiv
  obtain ⟨φT⟩ := hDu.nonempty_equiv
  obtain ⟨ψ⟩ := A6.nonempty_sylow_equiv hDA.bsub.bender hDu.bsub.bender Vb Tb
  let φ : ↥V ≃* ↥T := (φV.trans ψ).trans φT.symm
  have hcenV := fun {x : X} (hx : x ∈ V) => hDA.center_iff S hL hMA hx
  have hcenT := fun {x : X} (hx : x ∈ T) => hDu.center_iff S hL hMu' hx
  have hφc : ∀ v : ↥V, (v : X) ∈ zHull Z M → ((φ v : ↥T) : X) ∈ zHull Z M := by
    intro v hv
    rw [← hcenT (φ v).2]
    intro s hs
    obtain ⟨w, hw⟩ := φ.surjective ⟨s, hs⟩
    have h1 : (v : X) * w = w * v := (hcenV v.2).mpr hv w w.2
    have h2 : v * w = w * v := Subtype.ext h1
    have h3 := congrArg (fun x => ((φ x : ↥T) : X)) h2
    simp only [map_mul, Subgroup.coe_mul, hw] at h3
    exact h3
  have hφc' : ∀ t : ↥T, (t : X) ∈ zHull Z M → ((φ.symm t : ↥V) : X) ∈ zHull Z M := by
    intro t ht
    rw [← hcenV (φ.symm t).2]
    intro s hs
    obtain ⟨w, hw⟩ := φ.symm.surjective ⟨s, hs⟩
    have h1 : (t : X) * w = w * t := (hcenT t.2).mpr ht w w.2
    have h2 : t * w = w * t := Subtype.ext h1
    have h3 := congrArg (fun x => ((φ.symm x : ↥V) : X)) h2
    simp only [map_mul, Subgroup.coe_mul, hw] at h3
    exact h3
  set T₀ : Subgroup X := ((U.subgroupOf V).map φ.toMonoidHom).map T.subtype with hT₀
  have hmemT₀ : ∀ x, x ∈ T₀ ↔ ∃ w ∈ U, ∃ hw : w ∈ V, ((φ ⟨w, hw⟩ : ↥T) : X) = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, w.2, rfl⟩
    · rintro ⟨w, hw, hwV, rfl⟩
      exact ⟨φ ⟨w, hwV⟩, ⟨⟨w, hwV⟩, hw, rfl⟩, rfl⟩
  have hT₀T : T₀ ≤ T := map_subtype_le _
  have hT₀c : ∀ x ∈ T₀, ∀ y ∈ T₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨w₁, hw₁, hw₁V, rfl⟩ := (hmemT₀ x).mp hx
    obtain ⟨w₂, hw₂, hw₂V, rfl⟩ := (hmemT₀ y).mp hy
    have h1 : (⟨w₁, hw₁V⟩ : ↥V) * ⟨w₂, hw₂V⟩ = ⟨w₂, hw₂V⟩ * ⟨w₁, hw₁V⟩ :=
      Subtype.ext (hUc w₁ hw₁ w₂ hw₂)
    have h2 := congrArg (fun x => ((φ x : ↥T) : X)) h1
    simpa only [map_mul, Subgroup.coe_mul] using h2
  have hT₀card : Nat.card T₀ = (2 ^ n) ^ 2 := by
    rw [hT₀, card_map_of_injective T.subtype_injective,
      card_map_of_injective (f := φ.toMonoidHom) φ.injective, A6.card_subgroupOf hUV, hUcard]
  have hT₀sq : ∀ x ∈ T₀, x * x ∈ zHull Z M := by
    intro x hx
    obtain ⟨w, hw, hwV, rfl⟩ := (hmemT₀ x).mp hx
    have h1 := hφc (⟨w, hwV⟩ * ⟨w, hwV⟩) (hUsq w hw)
    simpa only [map_mul, Subgroup.coe_mul] using h1
  have hT₀U : ∀ x ∈ T₀, x ∈ U → x ∈ zHull Z M := by
    intro x hx hxU
    have hxT := hT₀T hx
    have h1 : u * x * u⁻¹ = x := by rw [hTu x hxT, mul_inv_cancel_right]
    have h2 := hUinv x hxU
    rw [h1] at h2
    apply hDu.mem_zHull_of_mul_self S hL hMu' hxT
    calc x * x = x * x⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel x
  have hcomm : ∀ a ∈ T₀, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hTU a (hT₀T ha) b hb
  set R : Subgroup X := T₀ ⊔ U with hR
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Bender.exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Bender.exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 := hcomm a' ha' b hb
    have h2 := hcomm a ha b' hb'
    have h3 := hT₀c a ha a' ha'
    have h4 := hUc b hb b' hb'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h1]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h3, h4]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [h2]
      _ = a' * b' * (a * b) := by group
  have hT₀p : IsPGroup 2 T₀ := hDu.isP.to_le hT₀T
  have hUp : IsPGroup 2 U := hDA.isP.to_le hUV
  have hRp : IsPGroup 2 R :=
    IsPGroup.to_sup_of_normal_right' hT₀p hUp (Bender.le_normalizer_of_commute fun b hb a ha =>
      (hcomm a ha b hb).symm)
  have hRM : R ≤ M := sup_le (hT₀T.trans (hDu.le_M S)) (hUV.trans (hDA.le_M S))
  let μ : ↥T₀ × ↥U →* ↥R :=
    { toFun := fun p => ⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by
        change (p.1 * q.1 : X) * (p.2 * q.2) = (p.1 * p.2) * (q.1 * q.2)
        have := hcomm q.1 q.1.2 p.2 p.2.2
        calc (p.1 * q.1 : X) * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [this]
          _ = (p.1 * p.2) * (q.1 * q.2) := by group) }
  have hμs : Function.Surjective μ := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Bender.exists_mul_of_mem_sup_of_commute hcomm hr
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hμcard : Nat.card μ.ker * Nat.card R = Nat.card T₀ * Nat.card U := by
    have h1 := Subgroup.card_mul_index μ.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hμs, Subgroup.card_top,
      Nat.card_prod] at h1
    exact h1
  have hker : Nat.card μ.ker ≤ 2 ^ n := by
    rw [← hL.m_card]
    refine Nat.card_le_card_of_injective (fun p => ⟨(p.1.1 : X), ?_⟩) ?_
    · have hp0 := Subtype.ext_iff.mp (MonoidHom.mem_ker.mp p.2)
      have hp : (p.1.1 : X) * p.1.2 = 1 := hp0
      have hp1 : (p.1.1 : X) = (p.1.2 : X)⁻¹ := eq_inv_of_mul_eq_one_left hp
      exact hT₀U _ p.1.1.2 (by rw [hp1]; exact inv_mem p.1.2.2)
    · intro p q hpq
      have h10 := Subtype.ext_iff.mp hpq
      have h1 : (p.1.1 : X) = q.1.1 := h10
      have hp0 := Subtype.ext_iff.mp (MonoidHom.mem_ker.mp p.2)
      have hp : (p.1.1 : X) * p.1.2 = 1 := hp0
      have hq0 := Subtype.ext_iff.mp (MonoidHom.mem_ker.mp q.2)
      have hq : (q.1.1 : X) * q.1.2 = 1 := hq0
      have h2 : (p.1.2 : X) = q.1.2 := by
        rw [← h1] at hq
        exact mul_left_cancel (hp.trans hq.symm)
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have hq0 : 0 < 2 ^ n := by positivity
  have hRcard : (2 ^ n) ^ 3 ≤ Nat.card R := by
    rw [hT₀card, hUcard] at hμcard
    have h1 : (2 ^ n) ^ 2 * (2 ^ n) ^ 2 ≤ 2 ^ n * Nat.card R := by
      rw [← hμcard]
      exact Nat.mul_le_mul_right _ hker
    have h2 : 2 ^ n * (2 ^ n) ^ 3 ≤ 2 ^ n * Nat.card R := by
      calc 2 ^ n * (2 ^ n) ^ 3 = (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := by ring
        _ ≤ 2 ^ n * Nat.card R := h1
    exact Nat.le_of_mul_le_mul_left h2 hq0
  let sqH : ↥R →* ↥R :=
    { toFun := fun r => r * r
      map_one' := by simp
      map_mul' := fun r s => Subtype.ext (by
        change (r * s : X) * (r * s) = (r * r) * (s * s)
        have := hRc s s.2 r r.2
        calc (r * s : X) * (r * s) = r * (s * r) * s := by group
          _ = r * (r * s) * s := by rw [this]
          _ = (r * r) * (s * s) := by group) }
  have hsqcard : Nat.card sqH.ker * Nat.card sqH.range = Nat.card R := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange : Nat.card sqH.range ≤ 2 ^ n := by
    rw [← hL.m_card]
    refine Nat.card_le_card_of_injective (fun r => ⟨((r : ↥R) : X), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := r.2
      rw [← hx]
      change (x : X) * x ∈ zHull Z M
      obtain ⟨a, ha, b, hb, hab⟩ := Bender.exists_mul_of_mem_sup_of_commute hcomm x.2
      rw [hab]
      have h1 := hcomm a ha b hb
      have e1 : a * b * (a * b) = (a * a) * (b * b) := by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [h1]
          _ = (a * a) * (b * b) := by group
      rw [e1]
      exact mul_mem (hT₀sq a ha) (hUsq b hb)
    · intro r s hrs
      have h6 := Subtype.ext_iff.mp hrs
      exact Subtype.ext (Subtype.ext h6)
  have hset : ((sqH.ker.map R.subtype : Subgroup X) : Set X) = {x : X | x ∈ R ∧ x * x = 1} := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr0 := Subtype.ext_iff.mp (MonoidHom.mem_ker.mp hr)
      exact ⟨r.2, hr0⟩
    · rintro ⟨hxR, hxx⟩
      exact ⟨⟨x, hxR⟩, MonoidHom.mem_ker.mpr (Subtype.ext hxx), rfl⟩
  have hkercard : ({x : X | x ∈ R ∧ x * x = 1} : Set X).ncard = Nat.card sqH.ker := by
    rw [← hset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      card_map_of_injective R.subtype_injective]
  have hOmega : (2 ^ n) ^ 2 ≤ ({x : X | x ∈ R ∧ x * x = 1} : Set X).ncard := by
    rw [hkercard]
    have h1 : 2 ^ n * (2 ^ n) ^ 2 ≤ 2 ^ n * Nat.card sqH.ker := by
      calc 2 ^ n * (2 ^ n) ^ 2 = (2 ^ n) ^ 3 := by ring
        _ ≤ Nat.card R := hRcard
        _ = Nat.card sqH.ker * Nat.card sqH.range := hsqcard.symm
        _ ≤ Nat.card sqH.ker * 2 ^ n := Nat.mul_le_mul_left _ hrange
        _ = 2 ^ n * Nat.card sqH.ker := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 hq0
  refine ⟨R, hRp, hRc, hRM, hOmega, hRcard, ?_⟩
  by_contra hno
  have hsub : {x : X | x ∈ R ∧ x * x = 1} ⊆ (zHull Z M : Set X) := by
    rintro x ⟨hxR, hxx⟩
    by_contra hxM
    have hx1 : x ≠ 1 := fun h => hxM (h ▸ (zHull Z M).one_mem)
    exact hno ⟨x, hxR, hxM, orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq ((zHull Z M : Subgroup X) : Set X), SetLike.coe_sort_coe,
    hL.m_card] at h1
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hL.hn
  have h5 : 2 ^ n < (2 ^ n) ^ 2 := by
    have := pow_lt_pow_right₀ (show 1 < 2 ^ n by omega) (show 1 < 2 by norm_num)
    simpa using this
  omega

end CFSG.GH74.Uniqueness
