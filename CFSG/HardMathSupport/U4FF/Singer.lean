module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.QuasithinUnique.Setup.Family

theorem orderOf_two_le_finrank_of_orderOf_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    (x : W ≃ₗ[ZMod 2] W) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hx : orderOf x = ℓ) :
    orderOf (2 : ZMod ℓ) ≤ Module.finrank (ZMod 2) W := by
  classical
  set g : Module.End (ZMod 2) W := (x : W →ₗ[ZMod 2] W)
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓ1 : ℓ ≠ 1 := hℓ.ne_one
  have hpow : x ^ ℓ = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hgpow : g ^ ℓ = 1 := by
    apply LinearMap.ext
    intro w
    have h : (x ^ ℓ) w = w := by simp [hpow]
    rw [LinearEquiv.pow_apply] at h
    rw [Module.End.pow_apply, Module.End.one_apply]
    exact h
  have hfs : Module.End.IsFinitelySemisimple g :=
    (isSemisimple_of_pow_eq_one g hℓodd hgpow).isFinitelySemisimple
  have hgne : ∃ w : W, g w ≠ w := by
    by_contra hcon
    push_neg at hcon
    have hx1 : x = 1 := LinearEquiv.ext fun w => hcon w
    exact hℓ1 (hx.symm.trans (orderOf_eq_one_iff.2 hx1))
  obtain ⟨p, hpx, hp0, hpnt, hpmin⟩ : ∃ p : Submodule (ZMod 2) W,
      (∀ w ∈ p, g w ∈ p) ∧ p ≠ ⊥ ∧ (∃ w ∈ p, g w ≠ w) ∧
        ∀ q : Submodule (ZMod 2) W, (∀ w ∈ q, g w ∈ q) → q ≠ ⊥ → (∃ w ∈ q, g w ≠ w) →
          Module.finrank (ZMod 2) p ≤ Module.finrank (ZMod 2) q := by
    obtain ⟨w₀, hw₀⟩ := hgne
    have htop : (⊤ : Submodule (ZMod 2) W) ≠ ⊥ := by
      intro h
      have hw0 : w₀ ∈ (⊥ : Submodule (ZMod 2) W) := by
        rw [← h]
        exact Submodule.mem_top
      rw [Submodule.mem_bot] at hw0
      apply hw₀
      rw [hw0, map_zero]
    have hex : ∃ k : ℕ, ∃ q : Submodule (ZMod 2) W,
        ((∀ w ∈ q, g w ∈ q) ∧ q ≠ ⊥ ∧ ∃ w ∈ q, g w ≠ w) ∧ Module.finrank (ZMod 2) q = k :=
      ⟨Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) W), ⊤,
        ⟨fun w _ => Submodule.mem_top, htop, w₀, Submodule.mem_top, hw₀⟩, rfl⟩
    obtain ⟨p, hpc, hpk⟩ := Nat.find_spec hex
    refine ⟨p, hpc.1, hpc.2.1, hpc.2.2, fun q hqx hq0 hqnt => ?_⟩
    have hle := Nat.find_min' hex ⟨q, ⟨hqx, hq0, hqnt⟩, rfl⟩
    omega
  have hsimp : ∀ T : Submodule (ZMod 2) W, T ≤ p → (∀ w ∈ T, g w ∈ T) → T = ⊥ ∨ T = p := by
    intro T hTp hTx
    by_contra hcon
    push_neg at hcon
    obtain ⟨hT0, hTp'⟩ := hcon
    have hpinv : p ∈ Module.End.invtSubmodule g :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem g).2 hpx
    have hTinv : T ∈ Module.End.invtSubmodule g :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem g).2 hTx
    obtain ⟨r, hrp, hrinv, hdisj, hsup⟩ :=
      Module.End.isFinitelySemisimple_iff.1 hfs p hpinv inferInstance T hTinv hTp
    have hrx : ∀ w ∈ r, g w ∈ r := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem g).1 hrinv
    have hr0 : r ≠ ⊥ := by
      intro h
      apply hTp'
      rw [h, sup_bot_eq] at hsup
      exact hsup
    have hrp' : r ≠ p := by
      intro h
      apply hT0
      rw [h, disjoint_iff, inf_eq_left.2 hTp] at hdisj
      exact hdisj
    have hTlt : T < p := lt_of_le_of_ne hTp hTp'
    have hrlt : r < p := lt_of_le_of_ne hrp hrp'
    have hfT : Module.finrank (ZMod 2) T < Module.finrank (ZMod 2) p :=
      Submodule.finrank_lt_finrank_of_lt hTlt
    have hfr : Module.finrank (ZMod 2) r < Module.finrank (ZMod 2) p :=
      Submodule.finrank_lt_finrank_of_lt hrlt
    have hTtriv : ∀ w ∈ T, g w = w := by
      intro w hw
      by_contra hne
      have h1 := hpmin T hTx hT0 ⟨w, hw, hne⟩
      omega
    have hrtriv : ∀ w ∈ r, g w = w := by
      intro w hw
      by_contra hne
      have h1 := hpmin r hrx hr0 ⟨w, hw, hne⟩
      omega
    obtain ⟨w, hwp, hwne⟩ := hpnt
    apply hwne
    have hw' : w ∈ T ⊔ r := by
      rw [hsup]
      exact hwp
    obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 hw'
    rw [← hts, map_add, hTtriv t ht, hrtriv s hs]
  haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.2 hp0
  let γ : Module.End (ZMod 2) p := g.restrict hpx
  have hγw : ∀ w : p, ((γ w : p) : W) = g w := fun w => rfl
  have hγapp : ∀ (k : ℕ) (w : p), (((γ ^ k) w : p) : W) = (g ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, hγw, pow_succ, Module.End.mul_apply]
  have hγK : γ ^ ℓ = 1 :=
    LinearMap.ext fun w => Subtype.ext (by rw [hγapp, hgpow]; rfl)
  have hfinord : IsOfFinOrder γ := isOfFinOrder_iff_pow_eq_one.2 ⟨ℓ, hℓ.pos, hγK⟩
  have hγsimple : ∀ T : Submodule (ZMod 2) p, (∀ s ∈ T, γ s ∈ T) → T = ⊥ ∨ T = ⊤ := by
    intro T hT
    have hTx : ∀ w ∈ T.map p.subtype, g w ∈ T.map p.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨γ s, hT s hs, rfl⟩
    rcases hsimp (T.map p.subtype) (by rintro _ ⟨s, _, rfl⟩; exact s.2) hTx with h | h
    · left
      apply Submodule.map_injective_of_injective p.injective_subtype
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective p.injective_subtype
      rw [h, Submodule.map_subtype_top]
  have hcard := simple_cyclic_card γ hfinord hγsimple
  have hγord : orderOf γ = ℓ := by
    have hγdvd : orderOf γ ∣ ℓ := orderOf_dvd_of_pow_eq_one hγK
    rcases (Nat.dvd_prime hℓ).1 hγdvd with h1 | h1
    · exfalso
      have hγ1 : γ = 1 := orderOf_eq_one_iff.1 h1
      obtain ⟨w, hwp, hwne⟩ := hpnt
      apply hwne
      have h2 : ((γ ⟨w, hwp⟩ : p) : W) = ((1 : Module.End (ZMod 2) p) ⟨w, hwp⟩ : W) := by
        rw [hγ1]
      exact h2
    · exact h1
  rw [hγord] at hcard
  have hcard2 : Nat.card p = 2 ^ Module.finrank (ZMod 2) p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hfo : Module.finrank (ZMod 2) p = orderOf (2 : ZMod ℓ) :=
    Nat.pow_right_injective (le_refl 2) (hcard2.symm.trans hcard)
  rw [← hfo]
  exact Submodule.finrank_le p

end CFSG.HardMathSupport.U4FF
