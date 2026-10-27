module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_closure_of_gen {T : Set G} {c : G}
    (h1 : ∀ g ∈ T, c⁻¹ * g * c ∈ closure T) (h2 : ∀ g ∈ T, c * g * c⁻¹ ∈ closure T) :
    c ∈ normalizer ((closure T : Subgroup G) : Set G) := by
  have a1 : ∀ t ∈ closure T, c⁻¹ * t * c ∈ closure T := by
    intro t ht
    have : closure T ≤ (closure T).comap (MulAut.conj c⁻¹).toMonoidHom := by
      rw [closure_le]
      intro g hg
      simpa [MulAut.conj_apply] using h1 g hg
    simpa [MulAut.conj_apply] using this ht
  have a2 : ∀ t ∈ closure T, c * t * c⁻¹ ∈ closure T := by
    intro t ht
    have : closure T ≤ (closure T).comap (MulAut.conj c).toMonoidHom := by
      rw [closure_le]
      intro g hg
      simpa [MulAut.conj_apply] using h2 g hg
    simpa [MulAut.conj_apply] using this ht
  rw [mem_normalizer_iff]
  intro t
  exact ⟨fun ht => a2 t ht, fun ht => by simpa [mul_assoc] using a1 _ ht⟩

theorem exists_invariant_sylow [Finite G] {H A : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ normalizer (H : Set G)) :
    ∃ S : Subgroup G, IsSylow2In S H ∧ A ≤ normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : A →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAH)
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H φ
  let _ : MulAction A (Sylow 2 H) := Sylow.pointwiseMulAction
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 H) := by
    intro h
    have h1 := card_sylow_modEq_one 2 H
    have h2 : Nat.card (Sylow 2 H) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2, Nat.mod_eq_of_lt (Fact.out : Nat.Prime 2).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q₀, hQ₀⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 H) hcard
  refine ⟨(Q₀ : Subgroup H).map H.subtype, ⟨map_subtype_le _, Q₀.isPGroup'.map _, ?_⟩, ?_⟩
  · have e : ((Q₀ : Subgroup H).map H.subtype).subgroupOf H = (Q₀ : Subgroup H) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [Subgroup.relIndex, e]
    exact Q₀.not_dvd_index
  · rw [le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : A) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : A) • y ∈ (Q₀ : Subgroup H) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : A) (Q₀ : Subgroup H) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((H.normalizerMonoidHom) (Subgroup.inclusion hAH ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem eq_one_or_eq_of_mem_zpowers {x y : G} (hx : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hsq : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx]
    simp
  · right
    rw [zpow_add, zpow_mul, zpow_one, zpow_two, hx]
    simp

theorem isPGroup_zpowers_of_mul_self_eq_one {s : G} (hs : s * s = 1) : IsPGroup 2 ↥(zpowers s) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rcases eq_one_or_eq_of_mem_zpowers hs g.2 with h | h <;> rw [Subgroup.coe_pow, h] <;>
    simp [pow_two, hs]

theorem isPGroup_zpowers_of_pow_eq_one [Finite G] {a : G} {n : ℕ} (h : a ^ (2 ^ n) = 1) :
    IsPGroup 2 ↥(zpowers a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem exists_mem_of_mem_sup_zpowers {S : Subgroup G} {s : G} (hs : s * s = 1)
    (hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S) {n : G} (hn : n ∈ zpowers s ⊔ S) :
    ∃ c ∈ S, n = c ∨ n = c * s := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  let W : Subgroup G :=
    { carrier := {n | ∃ c ∈ S, n = c ∨ n = c * s}
      one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
      mul_mem' := by
        rintro a b ⟨c₁, hc₁, ha⟩ ⟨c₂, hc₂, hb⟩
        have h2 : s * c₂ * s⁻¹ ∈ S := hSs c₂ hc₂
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact ⟨c₁ * c₂, mul_mem hc₁ hc₂, Or.inl rfl⟩
        · exact ⟨c₁ * c₂, mul_mem hc₁ hc₂, Or.inr (by rw [mul_assoc])⟩
        · refine ⟨c₁ * (s * c₂ * s⁻¹), mul_mem hc₁ h2, Or.inr ?_⟩
          group
        · refine ⟨c₁ * (s * c₂ * s⁻¹), mul_mem hc₁ h2, Or.inl ?_⟩
          rw [hsinv]
          simp [mul_assoc]
      inv_mem' := by
        rintro a ⟨c, hc, ha⟩
        rcases ha with ha | ha <;> rw [ha]
        · exact ⟨c⁻¹, inv_mem hc, Or.inl rfl⟩
        · refine ⟨s * c⁻¹ * s⁻¹, hSs _ (inv_mem hc), Or.inr ?_⟩
          have e : s * c⁻¹ * s⁻¹ * s = s * c⁻¹ := by group
          rw [e, mul_inv_rev, hsinv] }
  have hle : zpowers s ⊔ S ≤ W := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact ⟨1, one_mem _, Or.inr (by simp)⟩
    · intro a ha
      exact ⟨a, ha, Or.inl rfl⟩
  exact hle hn

theorem mem_closure_pair {s x t : G} (hs : s * s = 1) (hx : x * x = 1) (hsx : s * x = x * s)
    (ht : t ∈ closure ({s, x} : Set G)) : t = 1 ∨ t = s ∨ t = x ∨ t = s * x := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h_sp : s * (s * x) = x := by rw [← mul_assoc, hs, one_mul]
  have h_xs : x * s = s * x := hsx.symm
  have h_xp : x * (s * x) = s := by rw [← mul_assoc, ← hsx, mul_assoc, hx, mul_one]
  have h_ps : s * x * s = x := by rw [mul_assoc, ← hsx, ← mul_assoc, hs, one_mul]
  have h_px : s * x * x = s := by rw [mul_assoc, hx, mul_one]
  have h_pp : s * x * (s * x) = 1 := by rw [← mul_assoc, h_ps, hx]
  induction ht using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · rw [hz]; exact Or.inr (Or.inl rfl)
    · rw [hz]; exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [hs, hx, h_sp, h_xs, h_xp, h_ps, h_px, h_pp]
  | inv a _ ha =>
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · simp
    · rw [hsinv]; simp
    · rw [hxinv]; simp
    · rw [mul_inv_rev, hsinv, hxinv, h_xs]; simp

theorem fusion_of_centralizer [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) {s x : G}
    (hs : s * s = 1) (hx : x * x = 1) (hsx : s * x = x * s) (hne : s ≠ x) (hs1 : s ≠ 1)
    (hx1 : x ≠ 1) (hxS : x ∈ S) (hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S)
    (hxz : ∀ a ∈ S, a * x = x * a)
    (hC : ∀ c ∈ S, c * s = s * c → c ∈ zpowers x) (hbig : ∃ c ∈ S, c ∉ zpowers x) :
    ∃ c ∈ S, c ∈ normalizer ((closure ({s, x} : Set G) : Subgroup G) : Set G) ∧
      c⁻¹ * s * c = s * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  set V : Subgroup G := closure ({s, x} : Set G) with hVdef
  have hsV : s ∈ V := subset_closure (Or.inl rfl)
  have hxV : x ∈ V := subset_closure (Or.inr rfl)
  have hV := fun t (ht : t ∈ V) => mem_closure_pair hs hx hsx ht
  have hsN : s ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hSs h hh, fun hh => ?_⟩
    have := hSs _ hh
    have e : s * (s * h * s⁻¹) * s⁻¹ = h := by
      rw [hsinv]
      calc s * (s * h * s) * s = (s * s) * h * (s * s) := by group
        _ = h := by rw [hs]; simp
    rwa [e] at this
  have hspg : IsPGroup 2 (zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hs) hs1]
    simp
  set T : Subgroup G := zpowers s ⊔ S with hTdef
  have hTp : IsPGroup 2 T :=
    IsPGroup.to_sup_of_normal_right' hspg hS (by rw [zpowers_le]; exact hsN)
  have hsT : s ∈ T := le_sup_left (a := zpowers s) (b := S) (mem_zpowers s)
  have hST : S ≤ T := le_sup_right
  have hVT : V ≤ T := by
    rw [hVdef, closure_le]
    rintro t (rfl | rfl)
    · exact hsT
    · exact hST hxS
  obtain ⟨c₀, hc₀S, hc₀⟩ := hbig
  have hc₀V : c₀ ∉ V := by
    intro hcV
    rcases hV c₀ hcV with h | h | h | h
    · exact hc₀ (h ▸ one_mem _)
    · have : s ∈ S := h ▸ hc₀S
      have := hC s this rfl
      rcases eq_one_or_eq_of_mem_zpowers hx this with h1 | h1
      · exact hs1 h1
      · exact hne h1
    · exact hc₀ (h ▸ mem_zpowers x)
    · have h' : s * x ∈ S := h ▸ hc₀S
      have hsS : s ∈ S := by
        have := mul_mem h' (inv_mem hxS)
        rwa [mul_inv_cancel_right] at this
      have := hC s hsS rfl
      rcases eq_one_or_eq_of_mem_zpowers hx this with h1 | h1
      · exact hs1 h1
      · exact hne h1
  have hnil : Group.IsNilpotent T := IsPGroup.isNilpotent hTp
  have hNC : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent
  set V' : Subgroup T := V.subgroupOf T with hV'
  have hV'top : V' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hc₀V ?_
    have : (⟨c₀, hST hc₀S⟩ : T) ∈ V' := by rw [h]; exact mem_top _
    exact this
  obtain ⟨n, hn, hnV'⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp (hNC V' hV'top)).2
  have hnV : (n : G) ∉ V := fun h => hnV' h
  have hconj : ∀ t ∈ V, (n : G) * t * (n : G)⁻¹ ∈ V ∧ (n : G)⁻¹ * t * n ∈ V := by
    intro t ht
    have htT : t ∈ T := hVT ht
    have ht' : (⟨t, htT⟩ : T) ∈ V' := ht
    have h1 := (mem_normalizer_iff.mp hn ⟨t, htT⟩).mp ht'
    have hn' : n⁻¹ ∈ normalizer V' := inv_mem hn
    have h2 := (mem_normalizer_iff.mp hn' ⟨t, htT⟩).mp ht'
    exact ⟨by simpa using Subgroup.mem_subgroupOf.mp h1,
      by simpa using Subgroup.mem_subgroupOf.mp h2⟩
  have hex : ∃ c ∈ S, (∀ t ∈ V, c * t * c⁻¹ ∈ V ∧ c⁻¹ * t * c ∈ V) ∧ c ∉ V := by
    obtain ⟨c, hcS, hc⟩ := exists_mem_of_mem_sup_zpowers hs hSs n.2
    rcases hc with hc | hc
    · refine ⟨c, hcS, fun t ht => ?_, fun h => hnV (hc ▸ h)⟩
      have := hconj t ht
      rw [hc] at this
      exact this
    · refine ⟨c, hcS, fun t ht => ?_, fun h => ?_⟩
      · have hc' : c = (n : G) * s := by rw [hc, mul_assoc, hs, mul_one]
        have hs' : ∀ v ∈ V, s * v * s ∈ V := fun v hv =>
          mul_mem (mul_mem hsV hv) hsV
        obtain ⟨h1, h2⟩ := hconj t ht
        have e1 : c * t * c⁻¹ = (n : G) * (s * t * s) * (n : G)⁻¹ := by
          calc c * t * c⁻¹ = (n : G) * s * t * ((n : G) * s)⁻¹ := by rw [← hc']
            _ = (n : G) * s * t * (s⁻¹ * (n : G)⁻¹) := by rw [mul_inv_rev]
            _ = (n : G) * s * t * (s * (n : G)⁻¹) := by rw [hsinv]
            _ = (n : G) * (s * t * s) * (n : G)⁻¹ := by group
        have e2 : c⁻¹ * t * c = s * ((n : G)⁻¹ * t * n) * s := by
          calc c⁻¹ * t * c = ((n : G) * s)⁻¹ * t * ((n : G) * s) := by rw [← hc']
            _ = (s⁻¹ * (n : G)⁻¹) * t * ((n : G) * s) := by rw [mul_inv_rev]
            _ = (s * (n : G)⁻¹) * t * ((n : G) * s) := by rw [hsinv]
            _ = s * ((n : G)⁻¹ * t * n) * s := by group
        refine ⟨?_, ?_⟩
        · rw [e1]; exact (hconj _ (hs' t ht)).1
        · rw [e2]; exact hs' _ h2
      · apply hnV
        have : (n : G) = c * s := hc
        rw [this]
        exact mul_mem h hsV
  obtain ⟨c, hcS, hcN, hcV⟩ := hex
  have hcx : c⁻¹ * x * c = x := by
    have := hxz c hcS
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [← this]
      _ = x := by group
  have htV : c⁻¹ * s * c ∈ V := (hcN s hsV).2
  have hne1 : c⁻¹ * s * c ≠ 1 := by
    intro h
    apply hs1
    have : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
    rw [this, h]; group
  have hneX : c⁻¹ * s * c ≠ x := by
    intro h
    apply hne
    calc s = c * (c⁻¹ * s * c) * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [h]
      _ = x := by
        have := hcx
        calc c * x * c⁻¹ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [hcx]
          _ = x := by group
  have hVx : ∀ y ∈ zpowers x, y ∈ V := fun y hy => (zpowers_le.mpr hxV) hy
  have hneS : c⁻¹ * s * c ≠ s := by
    intro h
    apply hcV
    have hcs : c * s = s * c := by
      calc c * s = c * (c⁻¹ * s * c) := by rw [h]
        _ = s * c := by group
    exact hVx c (hC c hcS hcs)
  rcases hV _ htV with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hneS
  · exact absurd h hneX
  · refine ⟨c, hcS, ?_, h⟩
    exact mem_normalizer_closure_of_gen (fun g hg => (hcN g (subset_closure hg)).2)
      (fun g hg => (hcN g (subset_closure hg)).1)

theorem fusion_of_inverted {s x a : G} (hs : s * s = 1) (hx : x * x = 1) (hsx : s * x = x * s)
    (hax : a * x = x * a) (ha2 : a * a = x) (hinv : s * a * s⁻¹ = a⁻¹) :
    a ∈ normalizer ((closure ({s, x} : Set G) : Subgroup G) : Set G) ∧ a⁻¹ * s * a = s * x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hsa : s * a = a⁻¹ * s := by
    calc s * a = s * a * s⁻¹ * s := by group
      _ = a⁻¹ * s := by rw [hinv]
  have hainv : a⁻¹ = a * x := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ha2, hx]
  have haa : a⁻¹ * a⁻¹ = x := by rw [← mul_inv_rev, ha2, hxinv]
  have h1 : a⁻¹ * s * a = s * x := by
    calc a⁻¹ * s * a = a⁻¹ * (s * a) := by group
      _ = a⁻¹ * (a⁻¹ * s) := by rw [hsa]
      _ = (a⁻¹ * a⁻¹) * s := by group
      _ = x * s := by rw [haa]
      _ = s * x := hsx.symm
  have h2 : a * s * a⁻¹ = s * x := by
    calc a * s * a⁻¹ = a * s * (a * x) := by rw [hainv]
      _ = a * (s * a) * x := by group
      _ = a * (a⁻¹ * s) * x := by rw [hsa]
      _ = s * x := by group
  have hx1 : a⁻¹ * x * a = x := by
    calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
      _ = a⁻¹ * (a * x) := by rw [hax]
      _ = x := by group
  have hx2 : a * x * a⁻¹ = x := by
    calc a * x * a⁻¹ = (a * x) * a⁻¹ := rfl
      _ = (x * a) * a⁻¹ := by rw [hax]
      _ = x := by group
  have hsxm : s * x ∈ closure ({s, x} : Set G) :=
    mul_mem (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl))
  refine ⟨mem_normalizer_closure_of_gen (fun g hg => ?_) (fun g hg => ?_), h1⟩
  · rcases hg with rfl | rfl
    · rw [h1]; exact hsxm
    · rw [hx1]; exact subset_closure (Or.inr rfl)
  · rcases hg with rfl | rfl
    · rw [h2]; exact hsxm
    · rw [hx2]; exact subset_closure (Or.inr rfl)

theorem swap_of_two_fusions {s x g₁ g₂ : G} (hx : x * x = 1) (hsx : s * x = x * s)
    (h1x : g₁⁻¹ * x * g₁ = x) (h1s : g₁⁻¹ * s * g₁ = s * x)
    (h2s : g₂⁻¹ * s * g₂ = s) (h2x : g₂⁻¹ * x * g₂ = x * s) (hs : s * s = 1) :
    ∃ g : G, g⁻¹ * x * g = s ∧ g⁻¹ * s * g = x := by
  have h3 : s * (x * s) = x := by rw [← hsx, ← mul_assoc, hs, one_mul]
  refine ⟨g₁ * g₂ * g₁, ?_, ?_⟩
  · calc (g₁ * g₂ * g₁)⁻¹ * x * (g₁ * g₂ * g₁)
        = g₁⁻¹ * (g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂) * g₁ := by group
      _ = g₁⁻¹ * (g₂⁻¹ * x * g₂) * g₁ := by rw [h1x]
      _ = g₁⁻¹ * (x * s) * g₁ := by rw [h2x]
      _ = (g₁⁻¹ * x * g₁) * (g₁⁻¹ * s * g₁) := by group
      _ = x * (s * x) := by rw [h1x, h1s]
      _ = s := by rw [← mul_assoc, ← hsx, mul_assoc, hx, mul_one]
  · calc (g₁ * g₂ * g₁)⁻¹ * s * (g₁ * g₂ * g₁)
        = g₁⁻¹ * (g₂⁻¹ * (g₁⁻¹ * s * g₁) * g₂) * g₁ := by group
      _ = g₁⁻¹ * (g₂⁻¹ * (s * x) * g₂) * g₁ := by rw [h1s]
      _ = g₁⁻¹ * ((g₂⁻¹ * s * g₂) * (g₂⁻¹ * x * g₂)) * g₁ := by group
      _ = g₁⁻¹ * (s * (x * s)) * g₁ := by rw [h2s, h2x]
      _ = g₁⁻¹ * x * g₁ := by rw [h3]
      _ = x := h1x

end CFSG.GH74.GLS.Stage1.Thm2.Recip
