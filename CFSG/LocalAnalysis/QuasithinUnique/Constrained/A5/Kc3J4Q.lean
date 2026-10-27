
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Block

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

section Cohomology

theorem alt5_exists_apply : ∀ x : Fin 5, ∃ σ : Perm (Fin 5), σ.sign = 1 ∧ σ 4 = x := by
  decide +kernel

theorem a4_split : ∀ σ : Perm (Fin 5), σ 4 = 4 → σ.sign = 1 →
    ∃ a : Perm (Fin 5), a 4 = 4 ∧ a.sign = 1 ∧ a ^ 3 = 1 ∧ (a⁻¹ * σ) ^ 3 = 1 := by
  decide +kernel

theorem fixed_vector_zero : ∀ x : Fin 5 → ZMod 2, isEven x →
    (∀ σ : Perm (Fin 5), σ.sign = 1 → pact σ x = x) → x = 0 := by
  decide +kernel

theorem zmod_two_add_self_thrice (a : ZMod 2) : a + a + a = a := by
  revert a
  decide

theorem zmod_two_sub_shift (a b c : ZMod 2) : a - b = (b + c) - (a + c) := by
  revert a b c
  decide

theorem zmod_two_five_smul (c : ZMod 2) : c + 5 • c = 0 := by
  revert c
  decide

variable {Γ : Type*} [Group Γ]

theorem h1_alt5_delta5 (ρ : Γ →* Alt5) (hρ : Function.Surjective ρ) (δ : Γ → evenWeight 5)
    (hcoc : ∀ g h, δ (g * h) = δ g + vact (ρ g : Perm (Fin 5)) (δ h))
    (hker : ∀ k, ρ k = 1 → δ k = 0) :
    ∃ v : evenWeight 5, ∀ g, δ g = vact (ρ g : Perm (Fin 5)) v - v := by
  have hlift : ∀ τ : Perm (Fin 5), τ.sign = 1 → ∃ g : Γ, (ρ g : Perm (Fin 5)) = τ := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hρ ⟨τ, Equiv.Perm.mem_alternatingGroup.2 hτ⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hsign : ∀ g : Γ, (ρ g : Perm (Fin 5)).sign = 1 := fun g =>
    Equiv.Perm.mem_alternatingGroup.1 (ρ g).2
  have hmul : ∀ g h : Γ, (ρ (g * h) : Perm (Fin 5)) = (ρ g : Perm (Fin 5)) * ρ h := fun g h => by
    simp
  have hcoc' : ∀ (g h : Γ) (x : Fin 5), (δ (g * h)).1 x =
      (δ g).1 x + (δ h).1 ((ρ g : Perm (Fin 5))⁻¹ x) := fun g h x => by
    rw [hcoc]
    rfl
  have hcube : ∀ g : Γ, (ρ g : Perm (Fin 5)) 4 = 4 → (ρ g : Perm (Fin 5)) ^ 3 = 1 →
      (δ g).1 4 = 0 := by
    intro g h4 h3
    have hinv4 : (ρ g : Perm (Fin 5))⁻¹ 4 = 4 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact h4.symm
    have hk : ρ (g * g * g) = 1 := by
      apply Subtype.ext
      rw [hmul, hmul]
      rw [pow_three'] at h3
      exact h3
    have h0 := congrArg (fun u : evenWeight 5 => u.1 4) (hker _ hk)
    simp only [hcoc'] at h0
    have hgg : (ρ (g * g) : Perm (Fin 5))⁻¹ 4 = 4 := by
      rw [hmul, mul_inv_rev, Equiv.Perm.mul_apply, hinv4, hinv4]
    rw [hgg, hinv4] at h0
    have h00 : (δ g).1 4 + (δ g).1 4 + (δ g).1 4 = 0 := h0
    rwa [zmod_two_add_self_thrice] at h00
  have hstab : ∀ h : Γ, (ρ h : Perm (Fin 5)) 4 = 4 → (δ h).1 4 = 0 := by
    intro h h4
    obtain ⟨a, ha4, ha1, ha3, hb3⟩ := a4_split (ρ h : Perm (Fin 5)) h4 (hsign h)
    obtain ⟨g, hg⟩ := hlift a ha1
    have hb : (ρ (g⁻¹ * h) : Perm (Fin 5)) = a⁻¹ * (ρ h : Perm (Fin 5)) := by
      rw [← hg]
      simp
    have hinv4 : a⁻¹ 4 = 4 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact ha4.symm
    have hb4 : (ρ (g⁻¹ * h) : Perm (Fin 5)) 4 = 4 := by
      rw [hb, Equiv.Perm.mul_apply, h4, hinv4]
    have h1 := hcube g (by rw [hg]; exact ha4) (by rw [hg]; exact ha3)
    have h2 := hcube (g⁻¹ * h) hb4 (by rw [hb]; exact hb3)
    have h5 := hcoc' g (g⁻¹ * h) 4
    rw [mul_inv_cancel_left, hg, hinv4, h1, h2] at h5
    rw [h5]
    simp
  have hgx : ∀ x : Fin 5, ∃ g : Γ, (ρ g : Perm (Fin 5)) 4 = x := by
    intro x
    obtain ⟨τ, hτ, hτx⟩ := alt5_exists_apply x
    obtain ⟨g, hg⟩ := hlift τ hτ
    exact ⟨g, by rw [hg]; exact hτx⟩
  choose gx hgx using hgx
  have hind : ∀ (g : Γ) (x : Fin 5), (ρ g : Perm (Fin 5)) 4 = x →
      (δ g).1 x = (δ (gx x)).1 x := by
    intro g x hgxx
    have hinvx : (ρ (gx x) : Perm (Fin 5))⁻¹ x = 4 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hgx x).symm
    have hh : (ρ ((gx x)⁻¹ * g) : Perm (Fin 5)) 4 = 4 := by
      rw [map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      rw [hgxx, hinvx]
    have h0 := hstab _ hh
    have h1 := hcoc' (gx x) ((gx x)⁻¹ * g) x
    rw [mul_inv_cancel_left, hinvx, h0] at h1
    rw [h1]
    simp
  have hmain : ∀ (g : Γ) (x : Fin 5), (δ g).1 x =
      (δ (gx x)).1 x - (δ (gx ((ρ g : Perm (Fin 5))⁻¹ x))).1 ((ρ g : Perm (Fin 5))⁻¹ x) := by
    intro g x
    set y : Fin 5 := (ρ g : Perm (Fin 5))⁻¹ x with hy
    have hgy : (ρ (g * gx y) : Perm (Fin 5)) 4 = x := by
      rw [hmul, Equiv.Perm.mul_apply, hgx y, hy]
      simp
    have h1 := hind (g * gx y) x hgy
    rw [hcoc' g (gx y) x, ← hy] at h1
    rw [← h1]
    ring
  set w : Fin 5 → ZMod 2 := fun x => (δ (gx x)).1 x with hw
  set c : ZMod 2 := ∑ x, w x with hc
  have hv : (fun x => w x + c) ∈ evenWeight 5 := by
    show ∑ x, (w x + c) = 0
    rw [Finset.sum_add_distrib, ← hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact zmod_two_five_smul c
  refine ⟨⟨fun x => w x + c, hv⟩, fun g => ?_⟩
  apply Subtype.ext
  funext x
  rw [hmain g x]
  exact zmod_two_sub_shift _ _ _

end Cohomology

section Core

@[expose] def D5Core {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ V : Subgroup G, V ≤ L ∧ IsPGroup 2 V ∧ L ≤ Subgroup.normalizer (V : Set G) ∧
    ∃ α : ↥L →* ↥(alternatingGroup (Fin 5)), Function.Surjective α ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ V) ∧
      ∃ β : ↥V ≃* Multiplicative ↥(evenWeight 5),
        ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
          Multiplicative.toAdd (β w) =
            Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
              (Multiplicative.toAdd (β v))

theorem d5Core_or_central_of_d5Plus {G : Type} [Group G] {L : Subgroup G} (hD : D5Plus L) :
    D5Core L ∨ ∃ z ∈ L, orderOf z = 2 ∧ ∀ l ∈ L, l * z = z * l := by
  obtain ⟨V, Q, hVQ, hQL, hQ2, -, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := hD
  have hconjV : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
  have hβconj : ∀ (l : ↥L) (v : ↥V) (hw : (l : G) * (v : G) * (l : G)⁻¹ ∈ V),
      Multiplicative.toAdd (β ⟨(l : G) * (v : G) * (l : G)⁻¹, hw⟩) =
        vact ((α l : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) (Multiplicative.toAdd (β v)) :=
    fun l v hw => hβ l v ⟨_, hw⟩ rfl
  have hQV : ∀ q ∈ Q, ∀ v ∈ V, q * v = v * q := by
    intro q hq v hv
    have h1 : α ⟨q, hQL hq⟩ = 1 := (hαQ _).2 hq
    have h2 := hβconj ⟨q, hQL hq⟩ ⟨v, hv⟩ (hconjV q (hQL hq) v hv)
    rw [h1] at h2
    have h3 : β ⟨q * v * q⁻¹, hconjV q (hQL hq) v hv⟩ = β ⟨v, hv⟩ :=
      Multiplicative.toAdd.injective (by rw [h2]; rfl)
    have h5 : q * v * q⁻¹ = v := congrArg Subtype.val (β.injective h3)
    rwa [mul_inv_eq_iff_eq_mul] at h5
  have hfix : ∀ v ∈ V, (∀ l ∈ L, l * v = v * l) → v = 1 := by
    intro v hv hcomm
    have hu : ∀ τ : Perm (Fin 5), τ.sign = 1 →
        pact τ (Multiplicative.toAdd (β ⟨v, hv⟩)).1 = (Multiplicative.toAdd (β ⟨v, hv⟩)).1 := by
      intro τ hτ
      obtain ⟨l, hl⟩ := hα ⟨τ, Equiv.Perm.mem_alternatingGroup.2 hτ⟩
      have h2 : (l : G) * v * (l : G)⁻¹ = v := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hcomm l l.2
      have h3 : (⟨(l : G) * ((⟨v, hv⟩ : ↥V) : G) * (l : G)⁻¹, hconjV l l.2 v hv⟩ : ↥V) =
          ⟨v, hv⟩ := Subtype.ext h2
      have h1 := hβconj l ⟨v, hv⟩ (hconjV l l.2 v hv)
      rw [h3, hl] at h1
      exact (congrArg Subtype.val h1).symm
    have h0 := fixed_vector_zero _ (Multiplicative.toAdd (β ⟨v, hv⟩)).2 hu
    have h1 : Multiplicative.toAdd (β ⟨v, hv⟩) = 0 := Subtype.ext h0
    have h2 : β ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective h1
    have h3 : (⟨v, hv⟩ : ↥V) = 1 := β.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    have hVQc : ⁅V, Q⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hQV q hq v hv
    have h1 : ⁅⁅Q, L⁆, Q⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono_left hQLV).trans hVQc.le)
    have h2 : ⁅⁅L, Q⁆, Q⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L Q]
      exact h1
    have h3 : ⁅⁅Q, Q⁆, L⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    intro x hx y hy
    have hc : ⁅x, y⁆ ∈ V := hQLV (Subgroup.commutator_mem_commutator hx (hQL hy))
    have hcL : ∀ l ∈ L, l * ⁅x, y⁆ = ⁅x, y⁆ * l := fun l hl =>
      Subgroup.mem_centralizer_iff.1 (h3 (Subgroup.commutator_mem_commutator hx hy)) l hl
    exact commutatorElement_eq_one_iff_mul_comm.1 (hfix _ hc hcL)
  have hcomm : ∀ (l : ↥L) (q : G), q ∈ Q → ⁅(l : G), q⁆ ∈ V := by
    intro l q hq
    have h := V.inv_mem (hQLV (Subgroup.commutator_mem_commutator hq l.2))
    rwa [commutatorElement_inv] at h
  have hsplit : ∀ q ∈ Q, ∃ v ∈ V, ∀ l ∈ L, l * (q * v⁻¹) = (q * v⁻¹) * l := by
    intro q hq
    set δ : ↥L → evenWeight 5 := fun l =>
      Multiplicative.toAdd (β ⟨⁅(l : G), q⁆, hcomm l q hq⟩) with hδ
    have hcoc : ∀ g h : ↥L, δ (g * h) =
        δ g + vact ((α g : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) (δ h) := by
      intro g h
      have key : (⟨⁅((g * h : ↥L) : G), q⁆, hcomm (g * h) q hq⟩ : ↥V) =
          ⟨(g : G) * ⁅(h : G), q⁆ * (g : G)⁻¹, hconjV g g.2 _ (hcomm h q hq)⟩ *
            ⟨⁅(g : G), q⁆, hcomm g q hq⟩ := by
        apply Subtype.ext
        show ⁅(g : G) * (h : G), q⁆ = (g : G) * ⁅(h : G), q⁆ * (g : G)⁻¹ * ⁅(g : G), q⁆
        simp only [commutatorElement_def]
        group
      have h1 := hβconj g ⟨⁅(h : G), q⁆, hcomm h q hq⟩ (hconjV g g.2 _ (hcomm h q hq))
      show Multiplicative.toAdd (β ⟨⁅((g * h : ↥L) : G), q⁆, hcomm (g * h) q hq⟩) = _
      rw [key, map_mul, toAdd_mul, h1]
      exact add_comm _ _
    have hker : ∀ k : ↥L, α k = 1 → δ k = 0 := by
      intro k hk
      have hkQ : (k : G) ∈ Q := (hαQ k).1 hk
      have h1 : ⁅(k : G), q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hQab _ hkQ q hq)
      have h2 : (⟨⁅(k : G), q⁆, hcomm k q hq⟩ : ↥V) = 1 := Subtype.ext h1
      show Multiplicative.toAdd (β ⟨⁅(k : G), q⁆, hcomm k q hq⟩) = 0
      rw [h2, map_one]
      rfl
    obtain ⟨u, hu⟩ := h1_alt5_delta5 α hα δ hcoc hker
    set v0 : ↥V := β.symm (Multiplicative.ofAdd u) with hv0
    refine ⟨(v0 : G), v0.2, fun l hl => ?_⟩
    have hβv0 : Multiplicative.toAdd (β v0) = u := by simp [hv0]
    have hw : (l : G) * (v0 : G) * (l : G)⁻¹ ∈ V := hconjV l hl v0 v0.2
    have e1 : (⟨⁅l, q⁆, hcomm ⟨l, hl⟩ q hq⟩ : ↥V) = ⟨l * (v0 : G) * l⁻¹, hw⟩ * v0⁻¹ := by
      apply β.injective
      apply Multiplicative.toAdd.injective
      have h1 : δ ⟨l, hl⟩ = vact ((α ⟨l, hl⟩ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) u - u :=
        hu ⟨l, hl⟩
      have h2 := hβconj ⟨l, hl⟩ v0 hw
      show δ ⟨l, hl⟩ = _
      rw [h1, map_mul, map_inv, toAdd_mul, toAdd_inv, hβv0, sub_eq_add_neg]
      rw [hβv0] at h2
      rw [h2]
    have e2 : ⁅l, q⁆ = l * (v0 : G) * l⁻¹ * (v0 : G)⁻¹ := congrArg Subtype.val e1
    have hqv : q * (v0 : G)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem (hVQ v0.2))
    have hcV : ⁅l, q⁆ ∈ V := hcomm ⟨l, hl⟩ q hq
    have hcx := hQV _ hqv _ hcV
    have h_q : l * q * l⁻¹ = ⁅l, q⁆ * q := by
      simp only [commutatorElement_def]
      group
    have h_v : l * (v0 : G) * l⁻¹ = ⁅l, q⁆ * (v0 : G) := by
      rw [e2]
      group
    have hx : l * (q * (v0 : G)⁻¹) * l⁻¹ = q * (v0 : G)⁻¹ := by
      calc l * (q * (v0 : G)⁻¹) * l⁻¹ = (l * q * l⁻¹) * (l * (v0 : G) * l⁻¹)⁻¹ := by group
        _ = (⁅l, q⁆ * q) * (⁅l, q⁆ * (v0 : G))⁻¹ := by rw [h_q, h_v]
        _ = ⁅l, q⁆ * (q * (v0 : G)⁻¹) * ⁅l, q⁆⁻¹ := by group
        _ = q * (v0 : G)⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hcx.symm
    exact mul_inv_eq_iff_eq_mul.1 hx
  by_cases hQV' : ∀ q ∈ Q, q ∈ V
  · left
    refine ⟨V, hVQ.trans hQL, hQ2.to_le hVQ, hLV, α, hα, fun l => ?_, β, hβ⟩
    rw [hαQ l]
    exact ⟨fun h => hQV' _ h, fun h => hVQ h⟩
  · right
    push Not at hQV'
    obtain ⟨q, hq, hqV⟩ := hQV'
    obtain ⟨v, hv, hvc⟩ := hsplit q hq
    have hq'Q : q * v⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem (hVQ hv))
    have hq'V : q * v⁻¹ ∉ V := fun h => hqV (by simpa using V.mul_mem h hv)
    have hq'1 : q * v⁻¹ ≠ 1 := fun h => hq'V (h ▸ V.one_mem)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ2) ⟨q * v⁻¹, hq'Q⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hq'1 (orderOf_eq_one_iff.1 (by simpa using hk))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨(q * v⁻¹) ^ 2 ^ j, hQL (Q.pow_mem hq'Q _), ?_, fun l hl =>
      (Commute.pow_right (hvc l hl) _).eq⟩
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hk, pow_succ]; exact Dvd.intro 2 rfl), hk,
      pow_succ]
    exact Nat.mul_div_cancel_left 2 (by positivity)

theorem d5Plus_core_or_central {G : Type} [Group G] {L : Subgroup G} (hD : D5Plus L)
    (_hp : ⁅L, L⁆ = L) : D5Core L ∨ ∃ z ∈ L, orderOf z = 2 ∧ ∀ l ∈ L, l * z = z * l :=
  d5Core_or_central_of_d5Plus hD

end Core

end CFSG.QuasithinUnique.A5
