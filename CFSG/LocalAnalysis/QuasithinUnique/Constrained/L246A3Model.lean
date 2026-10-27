
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace L246

@[expose] def rot3 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

theorem sign_rot3 : Equiv.Perm.sign rot3 = 1 := by decide

@[expose] def sigma3 : ↥(alternatingGroup (Fin 3)) :=
  ⟨rot3, Equiv.Perm.mem_alternatingGroup.2 sign_rot3⟩

theorem sigma3_pow_three : sigma3 ^ 3 = 1 := by decide

theorem sigma3_ne_one : sigma3 ≠ 1 := by decide

theorem alt3_cases : ∀ γ : ↥(alternatingGroup (Fin 3)), γ = 1 ∨ γ = sigma3 ∨ γ = sigma3 ^ 2 := by
  decide

theorem card_alt3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem sigma3_inv0 : ((sigma3 : Equiv.Perm (Fin 3))⁻¹) 0 = 2 := by decide

theorem sigma3_inv1 : ((sigma3 : Equiv.Perm (Fin 3))⁻¹) 1 = 0 := by decide

theorem sigma3_inv2 : ((sigma3 : Equiv.Perm (Fin 3))⁻¹) 2 = 1 := by decide

theorem alt3_pow (τ : ↥(alternatingGroup (Fin 3))) : ∃ k : ℕ, k < 3 ∧ τ = sigma3 ^ k := by
  rcases alt3_cases τ with h | h | h
  · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  · exact ⟨2, by norm_num, h⟩

theorem zmod2_mid (a b c : ZMod 2) (h : a + b + c = 0) : b = a + c := by
  revert a b c
  decide

section Algebra

variable {S : Type} [CommGroup S]

theorem sq_mul_self {x : S} (hS : x ^ 2 = 1) : x * x = 1 := by
  rw [← pow_two]
  exact hS

theorem pow_val_add (hS : ∀ x : S, x ^ 2 = 1) (x : S) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have h2 : x * x = 1 := sq_mul_self (hS x)
  have ha : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  have hb : b.val = 0 ∨ b.val = 1 := by have := ZMod.val_lt b; omega
  rw [ZMod.val_add]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, h2]

theorem key_id (hS : ∀ x : S, x ^ 2 = 1) (s t : S) (a b : ZMod 2) :
    s ^ b.val * t ^ (a + b).val = t ^ a.val * (s * t) ^ b.val := by
  have ht : t * t = 1 := sq_mul_self (hS t)
  have ha : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  have hb : b.val = 0 ∨ b.val = 1 := by have := ZMod.val_lt b; omega
  rw [ZMod.val_add]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp only [ha, hb]
    norm_num
    rw [mul_comm s t, ← mul_assoc, ht, one_mul]

@[expose] def gFun (hS : ∀ x : S, x ^ 2 = 1) (s t : S) : G6.PermMod 3 →* S where
  toFun x := s ^ (Multiplicative.toAdd x 0).val * t ^ (Multiplicative.toAdd x 2).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [pow_val_add hS s, pow_val_add hS t]
    exact mul_mul_mul_comm _ _ _ _

theorem gFun_apply (hS : ∀ x : S, x ^ 2 = 1) (s t : S) (x : G6.PermMod 3) :
    gFun hS s t x = s ^ (Multiplicative.toAdd x 0).val * t ^ (Multiplicative.toAdd x 2).val := rfl

end Algebra

section Model

variable {S : Type} [CommGroup S]

theorem permAct_sigma3_zero (x : G6.PermMod 3) :
    Multiplicative.toAdd (G6.permAct 3 (sigma3 : Equiv.Perm (Fin 3)) x) 0 =
      Multiplicative.toAdd x 2 := by
  rw [G6.permAct_apply, sigma3_inv0]

theorem permAct_sigma3_two (x : G6.PermMod 3) :
    Multiplicative.toAdd (G6.permAct 3 (sigma3 : Equiv.Perm (Fin 3)) x) 2 =
      Multiplicative.toAdd x 1 := by
  rw [G6.permAct_apply, sigma3_inv2]

theorem sum_coords_of_mem (x : G6.PermMod 3) (hx : x ∈ G6.coreMod 3) :
    Multiplicative.toAdd x 1 = Multiplicative.toAdd x 0 + Multiplicative.toAdd x 2 := by
  have hsum : Multiplicative.toAdd x 0 + Multiplicative.toAdd x 1 + Multiplicative.toAdd x 2 = 0 := by
    have := (G6.mem_coreMod).1 hx
    simpa [Fin.sum_univ_three] using this
  exact zmod2_mid _ _ _ hsum

theorem gFun_sigma3 (hS : ∀ x : S, x ^ 2 = 1) (c : MulAut S) (s t : S)
    (hct : c s = t) (hcw : c t = s * t) (x : G6.PermMod 3) (hx : x ∈ G6.coreMod 3) :
    gFun hS s t (G6.permAct 3 (sigma3 : Equiv.Perm (Fin 3)) x) = c (gFun hS s t x) := by
  have h1 := sum_coords_of_mem x hx
  rw [gFun_apply, gFun_apply, permAct_sigma3_zero, permAct_sigma3_two, h1, map_mul, map_pow,
    map_pow, hct, hcw]
  exact key_id hS s t _ _

theorem gFun_injective (hS : ∀ x : S, x ^ 2 = 1) (s t : S) (hs : s ≠ 1) (ht : t ≠ 1) (hst : s ≠ t)
    (x : G6.PermMod 3) (hx : x ∈ G6.coreMod 3) (h : gFun hS s t x = 1) : x = 1 := by
  have h1 := sum_coords_of_mem x hx
  rw [gFun_apply] at h
  have ha : (Multiplicative.toAdd x 0).val = 0 ∨ (Multiplicative.toAdd x 0).val = 1 := by
    have := ZMod.val_lt (Multiplicative.toAdd x 0); omega
  have hb : (Multiplicative.toAdd x 2).val = 0 ∨ (Multiplicative.toAdd x 2).val = 1 := by
    have := ZMod.val_lt (Multiplicative.toAdd x 2); omega
  have hz : ∀ a : ZMod 2, a.val = 0 → a = 0 := fun a h0 => (ZMod.val_eq_zero a).1 h0
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hz _ ha
    · show Multiplicative.toAdd x 1 = 0
      rw [h1, hz _ ha, hz _ hb, add_zero]
    · exact hz _ hb
  · exfalso
    rw [ha, hb] at h
    simp at h
    exact ht h
  · exfalso
    rw [ha, hb] at h
    simp at h
    exact hs h
  · exfalso
    rw [ha, hb] at h
    simp at h
    apply hst
    have h2 : s * t = 1 := h
    calc s = s * (t * t) := by rw [sq_mul_self (hS t), mul_one]
      _ = (s * t) * t := by rw [mul_assoc]
      _ = t := by rw [h2, one_mul]

theorem exists_altDn_three (hS : ∀ x : S, x ^ 2 = 1) [Nontrivial S]
    (Γ : Subgroup (MulAut S)) (hΓ : Nat.card Γ = 3)
    (hirr : ∀ J : Subgroup S, (∀ γ ∈ Γ, ∀ x ∈ J, γ x ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∃ π : ↥(alternatingGroup (Fin 3)) →* ↥Γ, Function.Injective π ∧
      (FFModel.altDn 3).RealizesVia Γ ⊤ ⊥ π := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : ↥(alternatingGroup (Fin 3)) ≃* ↥Γ := mulEquivOfPrimeCardEq card_alt3 hΓ
  obtain ⟨c, hc⟩ : ∃ c : MulAut S, c = ((e sigma3 : ↥Γ) : MulAut S) := ⟨_, rfl⟩
  have hpow : ∀ k : ℕ, ((e (sigma3 ^ k) : ↥Γ) : MulAut S) = c ^ k := by
    intro k
    rw [hc, map_pow, Subgroup.coe_pow]
  have hc3 : c ^ 3 = 1 := by
    have h := hpow 3
    rw [sigma3_pow_three, map_one] at h
    exact h.symm
  have hcne : c ≠ 1 := by
    intro h
    apply sigma3_ne_one
    apply e.injective
    apply Subtype.ext
    rw [map_one, ← hc]
    exact h
  have hcc : ∀ x : S, c (c (c x)) = x := by
    intro x
    have h3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
    exact congrArg (fun f : MulAut S => f x) h3'
  have hirr' : ∀ J : Subgroup S, (∀ x ∈ J, c x ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hirr J
    intro γ hγ x hx
    obtain ⟨τ, hτ⟩ := e.surjective ⟨γ, hγ⟩
    obtain ⟨k, -, rfl⟩ := alt3_pow τ
    have hγτ : γ = c ^ k := (congrArg Subtype.val hτ).symm.trans (hpow k)
    rw [hγτ]
    clear hγτ hτ
    induction k generalizing x with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ]
      exact ih (c x) (hJ x hx)
  have hfix : ∀ x : S, c x = x → x = 1 := by
    intro x hx
    let F : Subgroup S :=
      { carrier := {y | c y = y}
        one_mem' := map_one c
        mul_mem' := fun {a b} ha hb => by
          show c (a * b) = a * b
          rw [map_mul, show c a = a from ha, show c b = b from hb]
        inv_mem' := fun {a} ha => by
          show c a⁻¹ = a⁻¹
          rw [map_inv, show c a = a from ha] }
    rcases hirr' F (fun y hy => by
        show c (c y) = c y
        exact congrArg c (show c y = y from hy)) with h | h
    · have hx' : x ∈ F := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact hx'
    · exfalso
      apply hcne
      ext y
      have hy : y ∈ F := by rw [h]; trivial
      exact hy
  obtain ⟨s, hs1⟩ := exists_ne (1 : S)
  have ht1 : c s ≠ 1 := fun h => hs1 (c.injective (h.trans (map_one c).symm))
  have hst : s ≠ c s := fun h => hs1 (hfix s h.symm)
  have hcw : c (c s) = s * c s := by
    have hst2 : (s * c s) * (s * c s) = 1 := by
      rw [mul_mul_mul_comm, sq_mul_self (hS s), sq_mul_self (hS (c s)), mul_one]
    have hprod : s * c s * c (c s) = 1 := by
      apply hfix
      rw [map_mul, map_mul, hcc s]
      show c s * c (c s) * s = s * c s * c (c s)
      rw [mul_comm (c s * c (c s)) s, ← mul_assoc]
    calc c (c s) = (s * c s) * (s * c s) * c (c s) := by rw [hst2, one_mul]
      _ = (s * c s) * (s * c s * c (c s)) := by rw [mul_assoc]
      _ = s * c s := by rw [hprod, mul_one]
  let g : ↥(G6.coreMod 3) →* S := (gFun hS s (c s)).comp (G6.coreMod 3).subtype
  have hgσ : ∀ x : ↥(G6.coreMod 3),
      c (g x) = g (G6.coreAct 3 (sigma3 : Equiv.Perm (Fin 3)) x) := fun x =>
    (gFun_sigma3 hS c s (c s) rfl hcw x.1 x.2).symm
  have hgk : ∀ (k : ℕ) (x : ↥(G6.coreMod 3)),
      (c ^ k) (g x) = g (G6.coreAct 3 ((sigma3 ^ k : ↥(alternatingGroup (Fin 3))) :
        Equiv.Perm (Fin 3)) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      have h1 : ((sigma3 ^ 0 : ↥(alternatingGroup (Fin 3))) : Equiv.Perm (Fin 3)) = 1 := by simp
      rw [h1, map_one]
      rfl
    | succ k ih =>
      intro x
      have h1 : ((sigma3 ^ (k + 1) : ↥(alternatingGroup (Fin 3))) : Equiv.Perm (Fin 3)) =
          (sigma3 : Equiv.Perm (Fin 3)) * ((sigma3 ^ k : ↥(alternatingGroup (Fin 3))) :
            Equiv.Perm (Fin 3)) := by
        rw [pow_succ']
        rfl
      rw [pow_succ', h1, map_mul]
      show c ((c ^ k) (g x)) = g (G6.coreAct 3 (sigma3 : Equiv.Perm (Fin 3))
        (G6.coreAct 3 ((sigma3 ^ k : ↥(alternatingGroup (Fin 3))) : Equiv.Perm (Fin 3)) x))
      rw [ih x, hgσ]
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (gFun_injective hS s (c s) hs1 ht1 hst x.1 x.2 hx)
  have hgsurj : Function.Surjective g := by
    have hnb : g.range ≠ ⊥ := by
      intro hb
      have hsmem : s ∈ g.range := by
        refine ⟨⟨Multiplicative.ofAdd ![1, 1, 0], ?_⟩, ?_⟩
        · show ∑ i : Fin 3, Multiplicative.toAdd (Multiplicative.ofAdd (![1, 1, 0] : Fin 3 → ZMod 2)) i
            = 0
          decide
        · show s ^ (1 : ZMod 2).val * (c s) ^ (0 : ZMod 2).val = s
          have h1 : (1 : ZMod 2).val = 1 := rfl
          have h0 : (0 : ZMod 2).val = 0 := rfl
          rw [h1, h0]
          simp
      rw [hb, Subgroup.mem_bot] at hsmem
      exact hs1 hsmem
    rcases hirr' g.range (by
        rintro _ ⟨x, rfl⟩
        exact ⟨G6.coreAct 3 (sigma3 : Equiv.Perm (Fin 3)) x, (hgσ x).symm⟩) with h | h
    · exact absurd h hnb
    · exact MonoidHom.range_eq_top.1 h
  let gE : ↥(FFModel.altDn 3).sec ≃* S := MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hgeq : ∀ (τ : ↥(alternatingGroup (Fin 3))) (x : ↥(G6.coreMod 3)),
      ((e τ : ↥Γ) : MulAut S) (g x) = g (G6.coreAct 3 (τ : Equiv.Perm (Fin 3)) x) := by
    intro τ x
    obtain ⟨k, -, rfl⟩ := alt3_pow τ
    rw [hpow k]
    exact hgk k x
  have hodd : Odd 3 := ⟨1, rfl⟩
  let tE : ↥(⊤ : Subgroup S) ≃* S := Subgroup.topEquiv
  refine ⟨e.toMonoidHom, e.injective, ?_⟩
  unfold FFModel.RealizesVia
  refine ⟨e.surjective, bot_le, inf_le_right, fun _ _ _ => trivial,
    fun h z hz => ?_, fun γ m hm => G6.permAct_mem_coreMod _ hm, fun γ m hm => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · rw [altDn_ker_eq_bot hodd] at hm ⊢
    rw [Subgroup.mem_bot.1 hm, Subgroup.mem_bot]
    exact map_one (G6.permAct 3 (Subtype.val γ))
  · refine ⟨(QuotientGroup.mk' _).comp (gE.symm.toMonoidHom.comp tE.toMonoidHom),
      (QuotientGroup.mk'_surjective _).comp (gE.symm.surjective.comp tE.surjective),
      fun u => ?_, fun γ u m hu hm hβ => ?_⟩
    · show (QuotientGroup.mk (gE.symm (tE u)) :
          ↥(FFModel.altDn 3).sec ⧸ (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, altDn_ker_subgroupOf_eq_bot hodd, Subgroup.mem_bot,
        map_eq_one_iff _ gE.symm.injective, Subgroup.mem_bot]
      exact ⟨fun h => h, fun h => h⟩
    ·
      have hβ' : gE.symm (tE u) = m := by
        have h1 := QuotientGroup.eq.1 hβ
        rw [altDn_ker_subgroupOf_eq_bot hodd, Subgroup.mem_bot] at h1
        exact inv_mul_eq_one.1 h1
      have hum : g m = (u : S) := by
        have h1 := gE.apply_symm_apply (tE u)
        rw [hβ'] at h1
        exact h1
      have key : g ⟨(FFModel.altDn 3).act γ m.1, hm⟩ = ((e γ : ↥Γ) : MulAut S) (u : S) := by
        have h2 := hgeq γ m
        rw [hum] at h2
        exact h2.symm
      have key' : gE.symm (tE ⟨((e.toMonoidHom γ : ↥Γ) : MulAut S) (u : S), hu⟩) =
          ⟨(FFModel.altDn 3).act γ m.1, hm⟩ := by
        apply gE.injective
        rw [MulEquiv.apply_symm_apply]
        exact key.symm
      show (QuotientGroup.mk (gE.symm (tE ⟨((e.toMonoidHom γ : ↥Γ) : MulAut S) (u : S), hu⟩)) :
          ↥(FFModel.altDn 3).sec ⧸ (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec) =
        QuotientGroup.mk ⟨(FFModel.altDn 3).act γ m.1, hm⟩
      rw [key']

end Model

end L246

end CFSG.QuasithinUnique
