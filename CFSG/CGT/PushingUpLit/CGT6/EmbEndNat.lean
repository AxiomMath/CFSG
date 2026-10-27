module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFiveM2
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

@[expose] noncomputable def slAct (f : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (Fq f) → Multiplicative (Fin 2 → Fq f) →
      Multiplicative (Fin 2 → Fq f) :=
  fun s x => Multiplicative.ofAdd
    ((s : Matrix (Fin 2) (Fin 2) (Fq f)).mulVec (Multiplicative.toAdd x))

section Card

theorem card_sl2_fq {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Fq f)) = 2 ^ f * (2 ^ (2 * f) - 1) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 f (by omega),
    ← pow_mul, mul_comm f 2]

theorem sl2_order_inj {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k)
    (h : 2 ^ f * (2 ^ (2 * f) - 1) = 2 ^ k * (2 ^ (2 * k) - 1)) : f = k := by
  have key : ∀ a b : ℕ, 1 ≤ a → a < b → 2 ^ a * (2 ^ (2 * a) - 1) < 2 ^ b * (2 ^ (2 * b) - 1) := by
    intro a b ha hab
    have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h2 : 2 ^ (2 * a) < 2 ^ (2 * b) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : 4 ≤ 2 ^ (2 * a) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (2 * a) - 1 < 2 ^ (2 * b) - 1 := by omega
    calc 2 ^ a * (2 ^ (2 * a) - 1) < 2 ^ b * (2 ^ (2 * a) - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 (by omega)
      _ ≤ 2 ^ b * (2 ^ (2 * b) - 1) := Nat.mul_le_mul_left _ h4.le
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (key f k hf hlt).ne
  · exact absurd h.symm (key k f hk hlt).ne

variable {V : Type} [CommGroup V]

theorem YSL.card_eq {Y : Subgroup (MulAut V)} {f : ℕ} (hf : 1 ≤ f) (h : YSL Y f) :
    Nat.card ↥Y = 2 ^ f * (2 ^ (2 * f) - 1) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_sl2_fq hf]

theorem YSL.center_eq_bot {Y : Subgroup (MulAut V)} {f : ℕ} (h : YSL Y f) :
    Subgroup.center ↥Y = ⊥ := by
  obtain ⟨e⟩ := h
  have h1 : (Subgroup.center ↥Y).map e.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Fq f)) := Subgroup.map_center_eq e
  rw [sl2_center_eq_bot] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem not_natOmegaMinus_of_ysl {Y : Subgroup (MulAut V)} {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n)
    (h : YSL Y f) (hΩ : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) : f = 2 * n := by
  obtain ⟨-, θ, -⟩ := hΩ
  have h1 := Nat.card_congr θ.toEquiv
  rw [h.card_eq hf, card_sl2_fq (by omega)] at h1
  exact sl2_order_inj hf (by omega) h1

end Card

section Section

variable {V : Type} [CommGroup V] [Finite V]

theorem natSection_of_classX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : InClassX ↥(yuHol Y)) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    IsNatSectionBy (slAct f) Y (commV Y) (commV Y ⊓ fixV Y) ∨
      (f = 2 ∧ IsNatSectionBy (altAct 5) Y (commV Y) (commV Y ⊓ fixV Y)) := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨hshort, halt | hsl⟩ := hX
  ·
    obtain ⟨n, hn1, φ, ψ, hsum, hsurj, hker, hequiv⟩ := halt
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans (hY.center_eq_bot ▸ le_rfl)
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    obtain ⟨eY⟩ := hY
    have hcard := Nat.card_congr θ.toEquiv
    rw [Nat.card_congr eY.toEquiv, card_sl2_fq (by omega)] at hcard
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn : n = 1 := by omega
      subst hn
      have h3 : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [h3] at hcard
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      have h5 : 16 ≤ 2 ^ (2 * f) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 4 * 15 ≤ 2 ^ f * (2 ^ (2 * f) - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    have hiso : alternatingGroup (Fin (2 * n + 1)) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f) :=
      θ.symm.trans eY
    obtain ⟨h5, hf2⟩ := alt_sl2_iso (by omega) hf hiso
    have hn : n = 2 := by omega
    subst hn
    subst hf2
    refine Or.inr ⟨rfl, ?_⟩
    let ρ : ↥Y →* MulAut V := Y.subtype
    let θ' : ↥Y →* Equiv.Perm (Fin (2 * 2 + 1)) :=
      (alternatingGroup (Fin (2 * 2 + 1))).subtype.comp (yuTheta Y φ)
    let A₀ : Subgroup V := commV Y ⊓ fixV Y
    have hB : ∀ g : ↥Y, ∀ b ∈ commV Y, ρ g b ∈ commV Y := fun g b hb =>
      apply_mem_commV_self Y g.2 hb
    have hshortU := shortU_eq_range Y φ hV hshort
    let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
      (yuInc Y).codRestrict (shortU ↥(yuHol Y)) (yuInc_mem_shortU Y hV)
    let β : ↥(commV Y) →* ↥(G6.coreMod (2 * 2 + 1)) :=
      (ψ.comp ι).codRestrict (G6.coreMod (2 * 2 + 1)) (fun u => (G6.mem_coreMod).2 (hsum _))
    have hβs : Function.Surjective β := by
      intro w
      obtain ⟨x, hx⟩ := hsurj (Multiplicative.toAdd (w : G6.PermMod (2 * 2 + 1)))
        (G6.mem_coreMod.mp w.2)
      obtain ⟨u, hu⟩ : (x : ↥(yuHol Y)) ∈ (yuInc Y).range := hshortU ▸ x.2
      refine ⟨u, Subtype.ext ?_⟩
      show ψ (ι u) = (w : G6.PermMod (2 * 2 + 1))
      have : ι u = x := Subtype.ext hu
      rw [this, hx]
      rfl
    have hβk : β.ker = A₀.subgroupOf (commV Y) := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : (ψ.comp ι) u = 1 := congrArg Subtype.val h
        have h2 : ι u ∈ ψ.ker := h1
        rw [hker, Subgroup.mem_subgroupOf] at h2
        have h3 : yuInc Y u ∈ Subgroup.center ↥(yuHol Y) := h2.2
        refine ⟨u.2, fun g hg => ?_⟩
        exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h3
      · rintro ⟨-, hu⟩
        apply Subtype.ext
        show ψ (ι u) = 1
        have h2 : ι u ∈ ψ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          refine ⟨yuInc_mem_shortU Y hV u, Subgroup.mem_center_iff.mpr ?_⟩
          intro x
          have h4 := conj_yuInc Y x u
          have h5 : (⟨x.1.right u, apply_mem_commV_self Y x.2.2 u.2⟩ : ↥(commV Y)) = u :=
            Subtype.ext (hu x.1.right x.2.2)
          rw [h5] at h4
          exact mul_inv_eq_iff_eq_mul.mp h4
        exact h2
    have hβe : ∀ (g : ↥Y) (b : ↥(commV Y)), β ⟨ρ g b, hB g b b.2⟩ =
        G6.coreAct (2 * 2 + 1) (θ' g) (β b) := by
      intro g b
      have hu : yuInc Y b ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV b
      have hu' : yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y) :=
        (shortU_normal (L := ↥(yuHol Y))).conj_mem _ hu _
      have h1 := hequiv (yuSec Y g : ↥(yuHol Y)) (yuInc Y b) hu hu'
      have h2 : (⟨yuSec Y g * yuInc Y b * (yuSec Y g)⁻¹, hu'⟩ : ↥(shortU ↥(yuHol Y))) =
          ι ⟨ρ g b, hB g b b.2⟩ := by
        apply Subtype.ext
        exact conj_yuInc Y (yuSec Y g) b
      rw [h2] at h1
      apply Subtype.ext
      show ψ (ι ⟨ρ g b, hB g b b.2⟩) = G6.permAct (2 * 2 + 1) (θ' g) (ψ (ι b))
      rw [h1]
      apply Multiplicative.toAdd.injective
      funext i
      rfl
    refine ⟨fun x hx p hp => apply_mem_commV_self Y hx hp, θ, β, hβs, hβk, ?_⟩
    intro x p hp
    exact hβe x p
  ·
    obtain ⟨n, hn1, φ, ψ, hsurj, hker, hequiv⟩ := hsl
    have hU := shortU_eq_range Y φ hV hshort
    obtain ⟨βV, hβs, hβk, hβe⟩ := sl_nat_data Y hV φ ψ hsurj hker hequiv hU
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans (hY.center_eq_bot ▸ le_rfl)
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    have hcard := Nat.card_congr θ.toEquiv
    rw [hY.card_eq (by omega), card_sl2_fq hn1] at hcard
    have hnf : f = n := sl2_order_inj (by omega) hn1 hcard
    subst hnf
    refine Or.inl ⟨fun x hx p hp => apply_mem_commV_self Y hx hp, θ, βV, hβs, hβk, ?_⟩
    intro x p hp
    exact hβe x p

theorem card_sl_model {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Multiplicative (Fin 2 → Fq n)) = 2 ^ (2 * n) := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → Fq n) ≃ _), Nat.card_fun,
    GaloisField.card 2 n (by omega), ← pow_mul]
  simp [mul_comm]

theorem card_commV_of_natSL (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (hsl : IsNaturalSLTwoModule ↥(yuHol Y) n) (hn : 1 ≤ n) :
    Nat.card ↥(commV Y) = Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * n) := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨φ, ψ, hsurj, hker, hequiv⟩ := hsl
  have hU := shortU_eq_range Y φ hV hshort
  obtain ⟨βV, hβs, hβk, -⟩ := sl_nat_data Y hV φ ψ hsurj hker hequiv hU
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk, card_sl_model hn] at h1
  have h2 : Nat.card ↥((commV Y ⊓ fixV Y).subgroupOf (commV Y)) =
      Nat.card ↥(commV Y ⊓ fixV Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1.symm

end Section

end CFSG.CGT.PushingUpLit.CGT6
