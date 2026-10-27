module

public import CFSG.Holt.H78.Lemma16Base
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Holt.H78

open Subgroup

namespace L16

variable {S : Type*} [Group S]

theorem conj_mem_sup_of {K₁ K₂ : Subgroup S} {a : S} (h₁ : ∀ x ∈ K₁, a * x * a⁻¹ ∈ K₁)
    (h₂ : ∀ x ∈ K₂, a * x * a⁻¹ ∈ K₂) {x : S} (hx : x ∈ K₁ ⊔ K₂) : a * x * a⁻¹ ∈ K₁ ⊔ K₂ := by
  have hle : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj a).toMonoidHom :=
    sup_le (fun y hy => mem_sup_left (h₁ y hy)) (fun y hy => mem_sup_right (h₂ y hy))
  exact hle hx

theorem map_mem_sup_of {φ : MulAut S} {K₁ K₂ : Subgroup S} (h₁ : ∀ x ∈ K₁, φ x ∈ K₁)
    (h₂ : ∀ x ∈ K₂, φ x ∈ K₂) {x : S} (hx : x ∈ K₁ ⊔ K₂) : φ x ∈ K₁ ⊔ K₂ := by
  have hle : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap φ.toMonoidHom :=
    sup_le (fun y hy => mem_sup_left (h₁ y hy)) (fun y hy => mem_sup_right (h₂ y hy))
  exact hle hx

namespace Setting

variable {φ : MulAut S} {A T R : Subgroup S} {N : ℕ} (h : Setting φ A T R N)
include h

theorem of_le {R' : Subgroup S} (hRR' : R ≤ R') (hR'T : R' ≤ T)
    (hn : ∀ a ∈ A, ∀ r ∈ R', a * r * a⁻¹ ∈ R') : Setting φ A T R' N where
  pgroup := h.pgroup
  le_TA := h.le_TA
  le_RT := hR'T
  normT := h.normT
  normR := hn
  mapA := h.mapA
  mapR r hr := by
    have : φ r = r * (r⁻¹ * φ r) := by group
    rw [this]; exact mul_mem hr (hRR' (h.trivT r (hR'T hr)))
  trivT t ht := hRR' (h.trivT t ht)
  sq := h.sq
  index := h.index
  three_le := h.three_le
  semi := h.semi
  order := h.order

theorem conj_mem_autComm_sup {a x : S} (ha : a ∈ A) (hx : x ∈ autComm φ A ⊔ R) :
    a * x * a⁻¹ ∈ autComm φ A ⊔ R :=
  conj_mem_sup_of (fun _ hy => conj_mem_autComm ha hy) (fun _ hy => h.normR a ha _ hy) hx

theorem map_mem_autComm_sup {x : S} (hx : x ∈ autComm φ A ⊔ R) : φ x ∈ autComm φ A ⊔ R :=
  map_mem_sup_of (fun _ hy => map_mem_autComm h.mapA hy) h.mapR hx

theorem autComm_sup_le : autComm φ A ⊔ R ≤ A :=
  sup_le (autComm_le h.mapA) (h.le_RT.trans h.le_TA)

theorem eq_autComm_sup [Finite S] {V : Subgroup S} (hVA : V ≤ A)
    (hVn : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) (hφV : ∀ v ∈ V, φ v ∈ V) (hRV : R ≤ V)
    (hVT : V ⊓ T ≤ R) (hAVT : ∀ a ∈ A, ∃ v ∈ V, ∃ t ∈ T, a = v * t) :
    V = autComm φ A ⊔ R := by
  have hle : autComm φ A ≤ V :=
    autComm_le_of h.le_TA hVn hφV hAVT (fun t ht => hRV (h.trivT t ht))
  refine le_antisymm (fun v hv => ?_) (sup_le hle hRV)
  obtain ⟨c, hc, t, ht, rfl⟩ := h.exists_autComm_mul (hVA hv)
  have htV : t ∈ V := by
    have : t = c⁻¹ * (c * t) := by group
    rw [this]; exact mul_mem (inv_mem (hle hc)) hv
  exact mul_mem (mem_sup_left hc) (mem_sup_right (hVT ⟨htV, ht⟩))

theorem autComm_sup_eq [Finite S] : autComm φ A ⊔ T = A := by
  refine le_antisymm (sup_le (autComm_le h.mapA) h.le_TA) (fun a ha => ?_)
  obtain ⟨c, hc, t, ht, rfl⟩ := h.exists_autComm_mul ha
  exact mul_mem (mem_sup_left hc) (mem_sup_right ht)

theorem exists_central [Finite S] (hRT : R ≠ T) :
    ∃ t ∈ T, t ∉ R ∧ t ^ 2 ∈ R ∧ ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ R := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : (R.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.normR g g.2 n hn⟩
  have hTn : (T.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.normT g g.2 n hn⟩
  let π : A →* A ⧸ R.subgroupOf A := QuotientGroup.mk' (R.subgroupOf A)
  have hπ : ∀ x : A, π x = 1 ↔ (x : S) ∈ R := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQ : IsPGroup 2 (A ⧸ R.subgroupOf A) := (h.pgroup.to_subgroup A).to_quotient _
  have : Group.IsNilpotent (A ⧸ R.subgroupOf A) := hQ.isNilpotent
  have hHn : ((T.subgroupOf A).map π).Normal := hTn.map π (QuotientGroup.mk'_surjective _)
  have hHne : (T.subgroupOf A).map π ≠ ⊥ := by
    obtain ⟨t, htT, htR⟩ : ∃ t ∈ T, t ∉ R := by
      by_contra hc
      push Not at hc
      exact hRT (le_antisymm h.le_RT hc)
    intro hbot
    have hmem : π ⟨t, h.le_TA htT⟩ ∈ (T.subgroupOf A).map π :=
      ⟨⟨t, h.le_TA htT⟩, Subgroup.mem_subgroupOf.2 htT, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ] at hmem
    exact htR hmem
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  have h2dvd : 2 ∣ Nat.card ((T.subgroupOf A).map π ⊓ Subgroup.center _ : Subgroup _) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1
      (hQ.to_subgroup ((T.subgroupOf A).map π ⊓ Subgroup.center _))
    rcases m with _ | m
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hm)) hZ
    · rw [hm, pow_succ]; exact dvd_mul_left 2 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  obtain ⟨t', ht'T, hπt'⟩ := Subgroup.mem_map.1 y.2.1
  have hyc := Subgroup.mem_center_iff.1 y.2.2
  have hy1 : (y : A ⧸ R.subgroupOf A) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    omega
  have hy2 : (y : A ⧸ R.subgroupOf A) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one]; rfl
  refine ⟨t', Subgroup.mem_subgroupOf.1 ht'T, fun htR => hy1 ?_, ?_, fun a ha => ?_⟩
  · rw [← hπt']; exact (hπ t').2 htR
  · have : π (t' ^ 2) = 1 := by rw [map_pow, hπt', hy2]
    exact (hπ _).1 this
  · have : π (⟨a, ha⟩ * t' * ⟨a, ha⟩⁻¹ * t'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπt', hyc]
      group
    exact (hπ _).1 this

def adjoin {t : S} (ht : t ∈ A) (ht2 : t ^ 2 ∈ R) : Subgroup S where
  carrier := {x | x ∈ R ∨ t⁻¹ * x ∈ R}
  mul_mem' := by
    have htt : t * t ∈ R := by rw [← pow_two]; exact ht2
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · refine Or.inr ?_
      have e : t⁻¹ * (x * y) = (t⁻¹ * x * t⁻¹⁻¹) * (t⁻¹ * y) := by group
      rw [e]; exact mul_mem (h.normR _ (inv_mem ht) _ hx) hy
    · refine Or.inr ?_
      have e : t⁻¹ * (x * y) = (t⁻¹ * x) * y := by group
      rw [e]; exact mul_mem hx hy
    · refine Or.inl ?_
      have e : x * y = (t * t) * ((t⁻¹ * (t⁻¹ * x) * t⁻¹⁻¹) * (t⁻¹ * y)) := by group
      rw [e]; exact mul_mem htt (mul_mem (h.normR _ (inv_mem ht) _ hx) hy)
  one_mem' := Or.inl (one_mem R)
  inv_mem' := by
    have htt : t * t ∈ R := by rw [← pow_two]; exact ht2
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have e : t⁻¹ * x⁻¹ = (t⁻¹ * (t⁻¹ * x)⁻¹ * t⁻¹⁻¹) * (t * t)⁻¹ := by group
      rw [e]; exact mul_mem (h.normR _ (inv_mem ht) _ (inv_mem hx)) (inv_mem htt)

theorem exists_chief [Finite S] (hRT : R ≠ T) :
    ∃ R' : Subgroup S, R ≤ R' ∧ R' ≤ T ∧ R ≠ R' ∧ (∀ a ∈ A, ∀ r ∈ R', a * r * a⁻¹ ∈ R') ∧
      ∀ x ∈ R', ∀ y ∈ R', x ∉ R → y ∉ R → x * y ∈ R := by
  obtain ⟨t, htT, htR, ht2, htc⟩ := h.exists_central hRT
  have htA := h.le_TA htT
  have htt : t * t ∈ R := by rw [← pow_two]; exact ht2
  refine ⟨h.adjoin htA ht2, fun x hx => Or.inl hx, ?_, ?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact h.le_RT hx
    · have : x = t * (t⁻¹ * x) := by group
      rw [this]; exact mul_mem htT (h.le_RT hx)
  · intro hR
    have : t ∈ h.adjoin htA ht2 := Or.inr (by rw [inv_mul_cancel]; exact one_mem R)
    rw [← hR] at this
    exact htR this
  · rintro a ha x (hx | hx)
    · exact Or.inl (h.normR a ha x hx)
    · refine Or.inr ?_
      have e : t⁻¹ * (a * x * a⁻¹) =
          (t⁻¹ * (a * t * a⁻¹ * t⁻¹) * t⁻¹⁻¹) * (a * (t⁻¹ * x) * a⁻¹) := by group
      rw [e]
      exact mul_mem (h.normR _ (inv_mem htA) _ (htc a ha)) (h.normR a ha _ hx)
  · rintro x (hx | hx) y (hy | hy) hxR hyR
    · exact absurd hx hxR
    · exact absurd hx hxR
    · exact absurd hy hyR
    · have e : x * y = (t * t) * ((t⁻¹ * (t⁻¹ * x) * t⁻¹⁻¹) * (t⁻¹ * y)) := by group
      rw [e]; exact mul_mem htt (mul_mem (h.normR _ (inv_mem htA) _ hx) hy)

theorem settingU [Finite S] {R' : Subgroup S} (h' : Setting φ A T R' N) (hRR' : R ≤ R')
    (hIH : (autComm φ A ⊔ R') ⊓ T = R') : Setting φ (autComm φ A ⊔ R') R' R N where
  pgroup := h.pgroup
  le_TA := le_sup_right
  le_RT := hRR'
  normT u hu r hr := h'.normR u (h'.autComm_sup_le hu) r hr
  normR u hu r hr := h.normR u (h'.autComm_sup_le hu) r hr
  mapA _ hu := h'.map_mem_autComm_sup hu
  mapR := h.mapR
  trivT t ht := h.trivT t (h'.le_RT ht)
  sq u hu := by
    rw [← hIH]; exact ⟨pow_mem hu 2, h.sq u (h'.autComm_sup_le hu)⟩
  index := by
    have hUA := h'.autComm_sup_le
    have hTn : (T.subgroupOf A).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact h.normT g g.2 n hn⟩
    have hsup : (autComm φ A ⊔ R') ⊔ T = A := le_antisymm (sup_le hUA h.le_TA)
      (h.autComm_sup_eq.symm.le.trans (sup_le_sup_right le_sup_left T))
    have e1 : R'.relIndex (autComm φ A ⊔ R') =
        ((autComm φ A ⊔ R') ⊓ T).relIndex (autComm φ A ⊔ R') := by rw [hIH]
    have e2 : T.relIndex (autComm φ A ⊔ R') = T.relIndex A := by
      rw [← Subgroup.relIndex_subgroupOf hUA, ← Subgroup.relIndex_sup_right,
        ← Subgroup.subgroupOf_sup hUA h.le_TA, hsup, Subgroup.subgroupOf_self,
        Subgroup.relIndex_top_right]
      rfl
    rw [e1, Subgroup.inf_relIndex_left, e2, h.index]
  three_le := h.three_le
  semi j u hu hT := by
    rcases h.semi j u (h'.autComm_sup_le hu) (h'.le_RT hT) with hu' | h1
    · left; rw [← hIH]; exact ⟨hu, hu'⟩
    · exact Or.inr h1
  order := h.order

theorem inf_eq [Finite S] : (autComm φ A ⊔ R) ⊓ T = R := by
  suffices H : ∀ n : ℕ, ∀ R : Subgroup S, Nat.card T - Nat.card R = n →
      Setting φ A T R N → (autComm φ A ⊔ R) ⊓ T = R from H _ R rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn h
  by_cases hRT : R = T
  · subst hRT; exact inf_eq_right.2 le_sup_right
  obtain ⟨R', hRR', hR'T, hne, hR'n, hR'2⟩ := h.exists_chief hRT
  have h' := h.of_le hRR' hR'T hR'n
  have hlt : Nat.card T - Nat.card R' < n := by
    have h1 : Nat.card R < Nat.card R' := Subgroup.card_lt_of_lt (lt_of_le_of_ne hRR' hne)
    have h2 : Nat.card R' ≤ Nat.card T := Subgroup.card_le_of_le hR'T
    omega
  have hIH := ih _ hlt R' rfl h'
  have hUs := h.settingU h' hRR' hIH
  have hbase := hUs.inf_eq_of_two hR'2
  have hUn : ∀ a ∈ A, ∀ u ∈ autComm φ A ⊔ R', a * u * a⁻¹ ∈ autComm φ A ⊔ R' :=
    fun a ha u hu => h'.conj_mem_autComm_sup ha hu
  have hVn : ∀ x ∈ A, ∀ v ∈ autComm φ (autComm φ A ⊔ R') ⊔ R,
      x * v * x⁻¹ ∈ autComm φ (autComm φ A ⊔ R') ⊔ R := by
    intro x hx
    have hV₁ : (autComm φ (autComm φ A ⊔ R') ⊔ R).map (MulAut.conj x).toMonoidHom =
        autComm φ (autComm φ A ⊔ R') ⊔ R := by
      apply hUs.eq_autComm_sup
      · rintro _ ⟨v, hv, rfl⟩
        exact hUn x hx v (hUs.autComm_sup_le hv)
      · rintro u hu _ ⟨v, hv, rfl⟩
        have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ autComm φ A ⊔ R' := hUn x⁻¹ (inv_mem hx) u hu
        refine ⟨(x⁻¹ * u * x⁻¹⁻¹) * v * (x⁻¹ * u * x⁻¹⁻¹)⁻¹,
          hUs.conj_mem_autComm_sup hu' hv, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro _ ⟨v, hv, rfl⟩
        have hc : x⁻¹ * φ x ∈ autComm φ A ⊔ R' := mem_sup_left (twist_mem_autComm hx)
        refine ⟨(x⁻¹ * φ x) * φ v * (x⁻¹ * φ x)⁻¹,
          hUs.conj_mem_autComm_sup hc (hUs.map_mem_autComm_sup hv), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
        group
      · intro r hr
        refine ⟨x⁻¹ * r * x⁻¹⁻¹, mem_sup_right (h.normR _ (inv_mem hx) r hr), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro _ ⟨⟨v, hv, rfl⟩, hvR'⟩
        have hvR' : v ∈ R' := by
          have := hR'n _ (inv_mem hx) _ hvR'
          simpa [MulAut.conj_apply, mul_assoc] using this
        have hvR : v ∈ R := by rw [← hbase]; exact ⟨hv, hvR'⟩
        exact h.normR x hx v hvR
      · intro u hu
        obtain ⟨c, hc, r', hr', he⟩ := hUs.exists_autComm_mul (hUn x⁻¹ (inv_mem hx) u hu)
        refine ⟨(MulAut.conj x).toMonoidHom c, ⟨c, mem_sup_left hc, rfl⟩, x * r' * x⁻¹,
          hR'n x hx r' hr', ?_⟩
        have hu' : u = x * (x⁻¹ * u * x⁻¹⁻¹) * x⁻¹ := by group
        rw [hu', he]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    intro v hv
    have : x * v * x⁻¹ ∈ (autComm φ (autComm φ A ⊔ R') ⊔ R).map (MulAut.conj x).toMonoidHom :=
      ⟨v, hv, rfl⟩
    rwa [hV₁] at this
  have hle : autComm φ A ≤ autComm φ (autComm φ A ⊔ R') ⊔ R := by
    apply autComm_le_of h.le_TA hVn (fun v hv => hUs.map_mem_autComm_sup hv)
    · intro a ha
      obtain ⟨c, hc, t, ht, rfl⟩ := h.exists_autComm_mul ha
      obtain ⟨c', hc', r', hr', rfl⟩ := hUs.exists_autComm_mul
        (mem_sup_left hc : c ∈ autComm φ A ⊔ R')
      exact ⟨c', mem_sup_left hc', r' * t, mul_mem (hR'T hr') ht, by group⟩
    · intro t ht
      exact mem_sup_right (h.trivT t ht)
  refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right h.le_RT)
  have hyV : y ∈ autComm φ (autComm φ A ⊔ R') ⊔ R := sup_le hle le_sup_right hy.1
  have hyR' : y ∈ R' := by rw [← hIH]; exact ⟨hUs.autComm_sup_le hyV, hy.2⟩
  rw [← hbase]
  exact ⟨hyV, hyR'⟩

end Setting

end L16

section Main

open L16

variable {S : Type*} [Group S] [Finite S]

theorem lemma_1_6_rel (hS : IsPGroup 2 S) (φ : MulAut S) {T R : Subgroup S} [T.Normal]
    [R.Normal] {N : ℕ} (hRT : R ≤ T) (hφR : ∀ r ∈ R, φ r ∈ R) (hφT : ∀ t ∈ T, t⁻¹ * φ t ∈ R)
    (hsq : ∀ x : S, x ^ 2 ∈ T) (hidx : T.index = 2 ^ N) (hN : 3 ≤ N)
    (hsemi : ∀ (j : ℕ) (x : S), x⁻¹ * (φ ^ j) x ∈ T → x ∈ T ∨ φ ^ j = 1)
    (hk : orderOf φ = 2 ^ N - 1 ∨ (3 * orderOf φ = 2 ^ N - 1 ∧ 6 ≤ N)) :
    ∃! U : Subgroup S, U.Normal ∧ U.map φ.toMonoidHom = U ∧ R ≤ U ∧ T ⊓ U = R ∧ T ⊔ U = ⊤ := by
  have h : Setting φ ⊤ T R N :=
    { pgroup := hS
      le_TA := le_top
      le_RT := hRT
      normT := fun a _ t ht => ‹T.Normal›.conj_mem t ht a
      normR := fun a _ r hr => ‹R.Normal›.conj_mem r hr a
      mapA := fun _ _ => mem_top _
      mapR := hφR
      trivT := hφT
      sq := fun a _ => hsq a
      index := by rw [Subgroup.relIndex_top_right]; exact hidx
      three_le := hN
      semi := fun j a _ => hsemi j a
      order := hk }
  have hmap : ∀ {V : Subgroup S}, (∀ v ∈ V, φ v ∈ V) → V.map φ.toMonoidHom = V := fun {V} hV =>
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨v, hv, rfl⟩; exact hV v hv)
      (by rw [Subgroup.card_map_of_injective φ.injective])
  refine ⟨autComm φ ⊤ ⊔ R, ⟨⟨fun n hn g => h.conj_mem_autComm_sup (mem_top g) hn⟩,
    hmap (fun _ hv => h.map_mem_autComm_sup hv), le_sup_right, by rw [inf_comm]; exact h.inf_eq,
    ?_⟩, ?_⟩
  · apply eq_top_iff.2
    calc (⊤ : Subgroup S) = autComm φ ⊤ ⊔ T := h.autComm_sup_eq.symm
      _ ≤ T ⊔ (autComm φ ⊤ ⊔ R) := sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  · rintro V ⟨hVn, hVφ, hRV, hTV, hTVtop⟩
    refine h.eq_autComm_sup le_top (fun a _ v hv => hVn.conj_mem v hv a)
      (fun v hv => hVφ ▸ Subgroup.mem_map_of_mem _ hv) hRV (by rw [inf_comm, hTV]) ?_
    intro a _
    have ha : a ∈ V ⊔ T := by rw [sup_comm, hTVtop]; exact mem_top a
    obtain ⟨v, hv, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    exact ⟨v, hv, t, ht, rfl⟩

end Main

end CFSG.Holt.H78

