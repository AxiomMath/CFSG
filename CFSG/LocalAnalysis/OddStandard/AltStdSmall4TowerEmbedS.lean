module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbedBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Struct

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup HbarCoords
open scoped Matrix

private theorem cGL_eq_MS : GL62.cGL = GL62.z₀ * GL62.dg e12 * GL62.gS *
    (GL62.z₀ * GL62.dg e12 * GL62.gS) := by
  refine Units.ext ?_
  decide

private theorem cGL_eq_MG : GL62.cGL = GL62.z₀ * GL62.gG * GL62.dg cyc3 * GL62.gG * GL62.z₀ *
    GL62.dg cyc3 * GL62.dg cyc3 * GL62.gG * GL62.dg cyc3 * GL62.gG := by
  refine Units.ext ?_
  decide

private theorem gS_eq_MG : GL62.gS = GL62.dg e12 * GL62.dg cyc3 * GL62.gG * GL62.z₀ *
    GL62.dg cyc3 * GL62.dg e12 * GL62.dg cyc3 * GL62.gG * GL62.z₀ * GL62.dg cyc3 * GL62.dg e12 *
    GL62.gG := by
  refine Units.ext ?_
  decide

theorem cGL_mem_MS : GL62.cGL ∈ GL62.MS := by
  have h1 := z0_mem_MS
  have h2 := dg_mem_MS e12
  have h3 := gS_mem_MS
  rw [cGL_eq_MS]
  exact mul_mem (mul_mem (mul_mem h1 h2) h3) (mul_mem (mul_mem h1 h2) h3)

theorem cGL_mem_MG : GL62.cGL ∈ GL62.MG := by
  have h1 : GL62.z₀ ∈ GL62.MG := mem_sup_left z0_mem_B₀
  have h2 : GL62.dg cyc3 ∈ GL62.MG := mem_sup_left (dg_mem_B₀ _)
  have h3 : GL62.gG ∈ GL62.MG := mem_sup_right (mem_zpowers _)
  rw [cGL_eq_MG]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h1 h3)
    h2) h3) h1) h2) h2) h3) h2) h3

theorem MS_le_MG : GL62.MS ≤ GL62.MG := by
  refine sup_le le_sup_left (zpowers_le.2 ?_)
  have h1 : GL62.z₀ ∈ GL62.MG := mem_sup_left z0_mem_B₀
  have h2 : GL62.dg e12 ∈ GL62.MG := mem_sup_left (dg_mem_B₀ _)
  have h3 : GL62.dg cyc3 ∈ GL62.MG := mem_sup_left (dg_mem_B₀ _)
  have h4 : GL62.gG ∈ GL62.MG := mem_sup_right (mem_zpowers _)
  rw [gS_eq_MG]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem h2 h3) h4) h1) h3) h2) h3) h4) h1) h3) h2) h4

theorem cGL_mulVec_eq_self {x : Fin 6 → ZMod 2}
    (h : (GL62.cGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x = x) : x = 0 := by
  obtain ⟨v, w, rfl⟩ := exists_eq_append x
  rw [GL62.cGL_mulVec] at h
  have h1 := congrArg GL62.fst h
  have h2 := congrArg GL62.snd h
  simp only [GL62.fst_append, GL62.snd_append] at h1 h2
  have hv : v = 0 := by
    have : v + w = 0 + w := by rw [h2, zero_add]
    exact add_right_cancel this
  subst hv
  subst h1
  exact GL62.ext_halves (by rw [GL62.fst_append]; rfl) (by rw [GL62.snd_append]; rfl)

section Frattini

variable {H : Type*} [Group H] [Finite H] (ρ : H →* GL (Fin 6) (ZMod 2))

theorem exists_three_lift {g : H} (hg : ρ g = GL62.cGL) :
    ∃ c : H, ρ c = GL62.cGL ∧ ∃ a : ℕ, c ^ 3 ^ a = 1 := by
  obtain ⟨a, r, hr, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  refine ⟨g ^ (r * r), ?_, a, ?_⟩
  · have h3 : (r * r) % 3 = 1 := by
      rw [Nat.mul_mod]
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h <;> rw [h]
    rw [map_pow, hg, pow_eq_pow_mod (r * r) GL62.cGL_pow_three, h3, pow_one]
  · rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hm, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem exists_frattini
    (hnorm : ∀ h : H, ρ h ∈ normalizer (zpowers GL62.cGL : Set (GL (Fin 6) (ZMod 2))))
    {c : H} (hc : ρ c = GL62.cGL) {a : ℕ} (ha : c ^ 3 ^ a = 1) :
    ∃ Y P : Subgroup H, Y ⊔ ρ.ker = ⊤ ∧ IsPGroup 3 P ∧ c ∈ P ∧
      Y ≤ normalizer (P : Set H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup H := (zpowers GL62.cGL).comap ρ with hD
  have hDn : D.Normal := ⟨fun d hd h => by
    rw [hD, mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hnorm h) _).1 hd⟩
  have hcD : c ∈ D := by rw [hD, mem_comap, hc]; exact mem_zpowers _
  set cD : D := ⟨c, hcD⟩
  have hzp : IsPGroup 3 (zpowers cD) := by
    rintro ⟨_, j, rfl⟩
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  set P' : Subgroup H := (P : Subgroup D).map D.subtype with hP'
  have hfr := Sylow.normalizer_sup_eq_top P
  have hcP' : c ∈ P' := ⟨cD, hP (mem_zpowers cD), rfl⟩
  refine ⟨normalizer (P' : Set H), P', ?_, P.isPGroup'.map D.subtype, hcP', le_rfl⟩
  have hDle : D ≤ ρ.ker ⊔ normalizer (P' : Set H) := by
    intro d hd
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (show ρ d ∈ zpowers GL62.cGL from hd)
    have h1 : d * c ^ (-k) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hc, ← hk, zpow_neg, mul_inv_cancel]
    have h2 : c ^ k ∈ normalizer (P' : Set H) := le_normalizer (zpow_mem hcP' k)
    have h3 : d = d * c ^ (-k) * c ^ k := by group
    rw [h3]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h2)
  rw [eq_top_iff, ← hfr]
  exact sup_le le_sup_left (hDle.trans (sup_le le_sup_right le_sup_left))

end Frattini

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} {Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)}

private theorem exists_mul_of_mem_cent {O : Subgroup G} (hOC : O ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ T ⊔ O) : ∃ o ∈ O, ∃ t ∈ T, o * t = x := by
  have hle : T ≤ normalizer (O : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro o
    constructor
    · intro ho
      rw [mem_centralizer_iff.1 (hOC ho) t ht, mul_inv_cancel_right]
      exact ho
    · intro ho
      have h2 := mem_centralizer_iff.1 (hOC ho) t ht
      have h3 : t * o * t⁻¹ = o := by
        have : t * (t * o * t⁻¹) = t * o := by rw [h2]; group
        exact mul_left_cancel this
      rw [← h3]
      exact ho
  rw [sup_comm] at hx
  exact (WF9.mem_sup_iff_of_le_normalizer hle).1 hx

variable {hn : 8 ≤ n} {κ : GL (Fin 3) (ZMod 2) →* G} {E₀ : Subgroup G}

theorem mem_oddCoreOf_of_normalizes (hH : HData θ hn z T) (hc : ModIso.TCoords z T κ E₀ cT)
    (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    {ĉ : normalizer (T : Set G)} (hĉ : Ψ (AltStdBal.normAct T ĉ) = GL62.cGL)
    {P : Subgroup (normalizer (T : Set G))} (hP : IsPGroup 3 P) (hĉP : ĉ ∈ P)
    {y : normalizer (T : Set G)} (hy : y ∈ normalizer (P : Set (normalizer (T : Set G))))
    (hy1 : Ψ (AltStdBal.normAct T y) = 1) :
    (y : G) ∈ AltStdSec.oddCoreOf (normalizer (T : Set G)) := by
  set O := AltStdSec.oddCoreOf (normalizer (T : Set G)) with hO
  have hOC : O ≤ centralizer (T : Set G) := by rw [hH.cent]; exact le_sup_right
  have hTO : T ⊓ O = ⊥ := inf_eq_bot_of_coprime (by
    rw [hH.n0.card_eq, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _))
  have hyC : (y : G) ∈ centralizer (T : Set G) :=
    (mem_ker_normAct_iff y).1 (Ψ.injective (by rw [hy1, map_one]))
  rw [hH.cent] at hyC
  obtain ⟨o, ho, t, ht, hyot⟩ := exists_mul_of_mem_cent hOC hyC
  have hq : y * ĉ * y⁻¹ * ĉ⁻¹ ∈ P := mul_mem ((mem_normalizer_iff.1 hy ĉ).1 hĉP) (inv_mem hĉP)
  obtain ⟨b, hb⟩ := hP ⟨_, hq⟩
  have hb' : ((y : G) * ĉ * (y : G)⁻¹ * (ĉ : G)⁻¹) ^ 3 ^ b = 1 := by
    have h := congrArg (fun x : P => ((x : normalizer (T : Set G)) : G)) hb
    simpa using h
  have huT : t * ((ĉ : G) * t⁻¹ * (ĉ : G)⁻¹) ∈ T :=
    mul_mem ht ((mem_normalizer_iff.1 ĉ.2 _).1 (inv_mem ht))
  have hvO : o * ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹) ∈ O :=
    mul_mem ho (ModIso.conj_mem_oddCoreOf' ĉ.2 (inv_mem ho))
  have hto : t * o = o * t := mem_centralizer_iff.1 (hOC ho) t ht
  have e1 : t⁻¹ * o⁻¹ = o⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hto]
  have e2 : t * ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹) = ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹) * t :=
    mem_centralizer_iff.1 (hOC (ModIso.conj_mem_oddCoreOf' ĉ.2 (inv_mem ho))) t ht
  have hqvu : (y : G) * ĉ * (y : G)⁻¹ * (ĉ : G)⁻¹ =
      (o * ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹)) * (t * ((ĉ : G) * t⁻¹ * (ĉ : G)⁻¹)) := by
    rw [← hyot]
    calc o * t * ĉ * (o * t)⁻¹ * (ĉ : G)⁻¹ = o * t * ĉ * (t⁻¹ * o⁻¹) * (ĉ : G)⁻¹ := by
          rw [mul_inv_rev]
      _ = o * t * ĉ * (o⁻¹ * t⁻¹) * (ĉ : G)⁻¹ := by rw [e1]
      _ = o * (t * ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹)) * ((ĉ : G) * t⁻¹ * (ĉ : G)⁻¹) := by group
      _ = o * (((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹) * t) * ((ĉ : G) * t⁻¹ * (ĉ : G)⁻¹) := by rw [e2]
      _ = _ := by group
  set u := t * ((ĉ : G) * t⁻¹ * (ĉ : G)⁻¹) with hu
  set v := o * ((ĉ : G) * o⁻¹ * (ĉ : G)⁻¹) with hv
  have huv : Commute v u := (mem_centralizer_iff.1 (hOC hvO) u huT).symm
  rw [hqvu, huv.mul_pow] at hb'
  have hu2 : u ^ 2 = 1 := hH.elem u huT
  have hu3 : u ^ 3 ^ b = u := by
    obtain ⟨k, hk⟩ := (by decide : Odd 3).pow (n := b)
    rw [hk, pow_succ, pow_mul, hu2, one_pow, one_mul]
  rw [hu3] at hb'
  have huO : u ∈ O := by
    rw [eq_inv_of_mul_eq_one_right hb']
    exact inv_mem (pow_mem hvO _)
  have hu1 : u = 1 := by
    have h := mem_inf.2 ⟨huT, huO⟩
    rwa [hTO, mem_bot] at h
  have hct : (ĉ : G) * t * (ĉ : G)⁻¹ = t := by
    have h1 : (ĉ : G) * t⁻¹ * (ĉ : G)⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hu1
    have h2 := congrArg (·⁻¹) h1
    simpa [mul_assoc] using h2
  obtain ⟨x, rfl⟩ := exists_cT6_eq hc ht
  rw [conj_cT6 hΨ, hĉ] at hct
  have hx0 := cGL_mulVec_eq_self (cT6_injective hc hct)
  rw [← hyot, hx0, cT6_zero hc, mul_one]
  exact ho

theorem exists_sl_compl (hH : HData θ hn z T) (hzz : z * z = 1) (hc : ModIso.TCoords z T κ E₀ cT)
    (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    (hX : (Hbar T).map Ψ.toMonoidHom = GL62.MS ∨ (Hbar T).map Ψ.toMonoidHom = GL62.MG) :
    ∃ X : Subgroup G, X ≤ normalizer (T : Set G) ∧ z ∈ X ∧
      (∀ x ∈ X, x ∈ centralizer (T : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 → x = 1) ∧
      normalizer (T : Set G) ≤ X ⊔ centralizer (T : Set G) := by
  set N := normalizer (T : Set G) with hN
  set O := AltStdSec.oddCoreOf N with hO
  set ρ : N →* GL (Fin 6) (ZMod 2) := Ψ.toMonoidHom.comp (AltStdBal.normAct T) with hρ
  have hOC : O ≤ centralizer (T : Set G) := by rw [hH.cent]; exact le_sup_right
  have hTC : T ≤ centralizer (T : Set G) := by rw [hH.cent]; exact le_sup_left
  have hON : O ≤ N := map_subtype_le _
  have hTO : T ⊓ O = ⊥ := inf_eq_bot_of_coprime (by
    rw [hH.n0.card_eq, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _))
  have hzN : z ∈ N := hH.n0.norm
  have hOnorm : ∀ g ∈ N, ∀ x ∈ O, g * x * g⁻¹ ∈ O := fun g hg x hx =>
    ModIso.conj_mem_oddCoreOf' hg hx
  have hTnorm : ∀ g ∈ N, ∀ x ∈ T, g * x * g⁻¹ ∈ T := fun g hg x hx =>
    (mem_normalizer_iff.1 hg x).1 hx
  have hrange : ∀ h : N, ρ h ∈ (Hbar T).map Ψ.toMonoidHom := fun h => ⟨_, ⟨h, rfl⟩, rfl⟩
  have hcM : GL62.cGL ∈ (Hbar T).map Ψ.toMonoidHom := by
    rcases hX with h | h <;> rw [h]
    · exact cGL_mem_MS
    · exact cGL_mem_MG
  have hMnorm : (Hbar T).map Ψ.toMonoidHom ≤
      normalizer (zpowers GL62.cGL : Set (GL (Fin 6) (ZMod 2))) := by
    rcases hX with h | h <;> rw [h]
    · exact GL62.MS_le_normalizer
    · exact GL62.MG_le_normalizer
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hcM
  obtain ⟨ĉ, hĉ, a, ha⟩ := exists_three_lift ρ (g := g) hg
  obtain ⟨Y, P, hYK, hP, hĉP, hYP⟩ := exists_frattini ρ (fun h => hMnorm (hrange h)) hĉ ha
  set YG : Subgroup G := Y.map N.subtype with hYG
  have hYGN : YG ≤ N := map_subtype_le Y
  have hYGO : ∀ y ∈ YG, y ∈ centralizer (T : Set G) → y ∈ O := by
    rintro _ ⟨y, hy, rfl⟩ hyC
    have h1 : AltStdBal.normAct T y = 1 := (mem_ker_normAct_iff y).2 hyC
    exact mem_oddCoreOf_of_normalizes hH hc hΨ hĉ hP hĉP (hYP hy) (by rw [h1, map_one])
  have hNY : ∀ g ∈ N, ∃ y ∈ YG, ∃ k ∈ centralizer (T : Set G), y * k = g := by
    intro g hg
    have h1 : (⟨g, hg⟩ : N) ∈ ((Y ⊔ ρ.ker : Subgroup N) : Set N) := by rw [hYK]; trivial
    rw [mul_normal] at h1
    obtain ⟨y, hy, k, hk, hyk⟩ := h1
    refine ⟨y, ⟨y, hy, rfl⟩, k, ?_, congrArg Subtype.val hyk⟩
    have hk1 : AltStdBal.normAct T k = 1 := Ψ.injective (by
      rw [map_one]
      exact hk)
    exact (mem_ker_normAct_iff k).1 hk1
  have hYGnO : YG ≤ normalizer (O : Set G) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hOnorm y (hYGN hy) x hx, fun hx => ?_⟩
    have h := hOnorm y⁻¹ (inv_mem (hYGN hy)) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at h
  set Xp : Subgroup G := O ⊔ YG with hXp
  have hXpN : Xp ≤ N := sup_le hON hYGN
  have hXpC : ∀ x ∈ Xp, x ∈ centralizer (T : Set G) → x ∈ O := by
    intro x hx hxC
    obtain ⟨o, ho, y, hy, rfl⟩ := (WF9.mem_sup_iff_of_le_normalizer hYGnO).1 hx
    have hyC : y ∈ centralizer (T : Set G) := by
      have h := mul_mem (inv_mem (hOC ho)) hxC
      rwa [inv_mul_cancel_left] at h
    exact mul_mem ho (hYGO y hy hyC)
  have hXpT : ∀ x ∈ Xp, x ∈ T → x = 1 := by
    intro x hx hxT
    have h := mem_inf.2 ⟨hxT, hXpC x hx (hTC hxT)⟩
    rwa [hTO, mem_bot] at h
  have hNT : ∀ g ∈ N, ∃ t ∈ T, ∃ x ∈ Xp, t * x = g := by
    intro g hg
    obtain ⟨y, hy, k, hk, rfl⟩ := hNY g hg
    rw [hH.cent] at hk
    obtain ⟨o, ho, t, ht, rfl⟩ := exists_mul_of_mem_cent hOC hk
    have hyo : y * o ∈ N := mul_mem (hYGN hy) (hON ho)
    refine ⟨(y * o) * t * (y * o)⁻¹, hTnorm _ hyo t ht, y * o * (y⁻¹ * y), ?_, by group⟩
    rw [inv_mul_cancel, mul_one]
    have h := hOnorm y (hYGN hy) o ho
    have h2 : y * o = (y * o * y⁻¹) * y := by group
    rw [h2]
    exact mul_mem (mem_sup_left h) (mem_sup_right hy)
  obtain ⟨t, ht, x, hx, htx⟩ := hNT z hzN
  have hxz : x = t⁻¹ * z := by rw [← htx]; group
  have hx2 : (t⁻¹ * z) ^ 2 = 1 := by
    have hmem : (t⁻¹ * z) * (t⁻¹ * z) ∈ T := by
      have h1 : (t⁻¹ * z) * (t⁻¹ * z) = t⁻¹ * (z * t⁻¹ * z⁻¹) * (z * z) := by group
      rw [h1, hzz, mul_one]
      exact mul_mem (inv_mem ht) (hTnorm z hzN _ (inv_mem ht))
    rw [sq]
    exact hXpT _ (mul_mem (hxz ▸ hx) (hxz ▸ hx)) hmem
  obtain ⟨s, hs, hsz⟩ := hH.inv t⁻¹ (inv_mem ht) hx2
  have hsN : s ∈ N := le_normalizer hs
  refine ⟨Xp.map (MulAut.conj s⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (inv_mem hsN) (hXpN hx)) (inv_mem (inv_mem hsN))
  · refine ⟨x, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hxz, ← hsz]
    group
  · rintro _ ⟨x, hx, rfl⟩ hxC k hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxC hk ⊢
    have hcomm := mem_centralizer_iff.1 hxC s hs
    have hx' : s⁻¹ * x * s = x := by
      calc s⁻¹ * x * s = (s⁻¹ * x * s) * s * s⁻¹ := by group
        _ = s * (s⁻¹ * x * s) * s⁻¹ := by rw [← hcomm]
        _ = x := by group
    rw [hx'] at hxC hk ⊢
    have hxO := hXpC x hx hxC
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hdO : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have hcop : Nat.Coprime (orderOf x) (Nat.card O) :=
      Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left k (coprime_card_oddCoreOf _))
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdO)
  · intro g hg
    obtain ⟨t', ht', x, hx, rfl⟩ := hNT g hg
    have h1 : t' * x = (t' * s) * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [h1]
    refine mul_mem (mul_mem (mem_sup_right (hTC (mul_mem ht' hs))) (mem_sup_left ⟨x, hx, ?_⟩))
      (mem_sup_right (hTC (inv_mem hs)))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

end CFSG.OddStandard.AltStdSmall4.Tower
