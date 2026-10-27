module

public import CFSG.CGT.PushingUpLit.A78S4.Pair

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem le_normalizer_sup {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) : X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  intro x hx
  apply mem_normalizer_of_cj
  have e1 : cj x (A ⊔ B) = cj x A ⊔ cj x B := Subgroup.map_sup _ _ _
  rw [e1, cj_eq_of_mem_normalizer_set (hA hx), cj_eq_of_mem_normalizer_set (hB hx)]

end Helpers

section Side

variable {G : Type} [Group G] [Finite G] {L T J : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.sup_le_normalizer_Z (h : A78Side G L T J e) :
    L ⊔ T ≤ Subgroup.normalizer
      ((oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · refine le_normalizer_of_conj fun l hl z hz => ?_
    have h1 : l * z * l⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.1 hz.2 l hl]
      group
    rw [h1]
    exact hz
  · refine le_normalizer_of_conj fun t ht z hz => ?_
    refine Subgroup.mem_inf.2 ⟨h.conj_V (Subgroup.mem_sup_right ht) hz.1,
      Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have htl : t⁻¹ * l * t ∈ L := by
      simpa using conj_mem_of_mem_normalizer (inv_mem (h.sylow.le ht)) hl
    have hzl := Subgroup.mem_centralizer_iff.1 hz.2 _ htl
    calc l * (t * z * t⁻¹) = t * ((t⁻¹ * l * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * l * t)) * t⁻¹ := by rw [hzl]
      _ = t * z * t⁻¹ * l := by group

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.s4_cent (h : A78Side G L T J e)
    (D : NatCoordK G (L ⊔ oTwoIn (L ⊔ T)) (oTwoIn (L ⊔ T))
      (oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)) (GaloisField 2 e)) :
    ∀ t ∈ T, (∀ v ∈ oTwoIn (L ⊔ T), t * v * t⁻¹ * v⁻¹ ∈
      oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)) → t ∈ oTwoIn (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := oTwoIn (L ⊔ T) with hV
  set Z := V ⊓ Subgroup.centralizer (L : Set G) with hZ
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := h.sup_le_normalizer_V
  have hLTZ : L ⊔ T ≤ Subgroup.normalizer (Z : Set G) := h.sup_le_normalizer_Z
  have hLTK : ∀ m ∈ L ⊔ T, m ∈ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (Z : Set G) := fun m hm => ⟨hLTV hm, hLTZ hm⟩
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht l hl =>
    conj_mem_of_mem_normalizer (h.sylow.le ht) hl
  let K : Subgroup G :=
    { carrier := {g | g ∈ L ⊔ T ∧ ∀ v ∈ V, D.κ (g * v * g⁻¹) = D.κ v}
      one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
      mul_mem' := fun {g k} hg hk => ⟨mul_mem hg.1 hk.1, fun v hv => by
        have e1 : g * k * v * (g * k)⁻¹ = g * (k * v * k⁻¹) * g⁻¹ := by group
        rw [e1, hg.2 _ (conj_mem_of_mem_normalizer (hLTV hk.1) hv), hk.2 v hv]⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun v hv => by
        have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V := conj_mem_of_mem_normalizer (hLTV (inv_mem hg.1)) hv
        have h1 := hg.2 _ hv'
        rw [show g * (g⁻¹ * v * g⁻¹⁻¹) * g⁻¹ = v by group] at h1
        exact h1.symm⟩ }
  have hKLT : K ≤ L ⊔ T := fun g hg => hg.1
  have hKn : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conj fun m hm g hg => ⟨mul_mem (mul_mem hm hg.1) (inv_mem hm),
      fun v hv => ?_⟩
    have hv' : m⁻¹ * v * m ∈ V := by
      simpa using conj_mem_of_mem_normalizer (hLTV (inv_mem hm)) hv
    have h1 := hg.2 _ hv'
    have hgv : g * (m⁻¹ * v * m) * g⁻¹ ∈ V := conj_mem_of_mem_normalizer (hLTV hg.1) hv'
    have h2 := NatCoordK.κ_conj_congr (hLTK m hm) hgv hv' h1
    have e1 : m * g * m⁻¹ * v * (m * g * m⁻¹)⁻¹ = m * (g * (m⁻¹ * v * m) * g⁻¹) * m⁻¹ := by group
    rw [e1, h2]
    congr 1
    group
  obtain ⟨n, hn⟩ := h.sylow.isPGroup.exists_card_eq
  have hK2 : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := (mem_sup_iff_of_normalizes hTL).1 hk.1
    obtain ⟨l', hl', hpow⟩ := A78L3.exists_pow_mul_eq hTL hl ht (2 ^ n)
    have ht1 : t ^ 2 ^ n = 1 := by
      have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
      rw [hn] at this
      exact congrArg Subtype.val this
    rw [ht1, mul_one] at hpow
    have hpK : (l * t) ^ 2 ^ n ∈ K := pow_mem hk _
    rw [hpow] at hpK
    have hl'L : l' ∈ L ⊔ V := Subgroup.mem_sup_left hl'
    have hρ : D.ρ l' = 1 := by
      refine CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec fun w => ?_
      obtain ⟨v, hv, rfl⟩ := D.κ_surj w
      have h1 := hpK.2 v hv
      rw [D.conj l' hl'L v hv] at h1
      rw [h1]
      simp
    have hl'V : l' ∈ V := (D.ρ_eq_one l' hl'L).1 hρ
    refine ⟨n + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ, pow_mul, hpow, pow_two]
    exact (elemAb2_of_isElemAbelian h.elem l' hl'V l' hl'V).2
  have hKV : K ≤ V := CGT6.le_oTwoIn_of_normal hKLT hKn hK2
  intro t ht hc
  refine hKV ⟨Subgroup.mem_sup_right ht, fun v hv => ?_⟩
  exact (D.κ_eq_iff (h.conj_V (Subgroup.mem_sup_right ht) hv) hv).2 (hc v hv)

end Side

section Cfg

variable {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4Side₀ (cfg : A78Cfg G L₁ L₂ T e) :
    S4Side G (L₁ ⊔ oTwoIn (L₁ ⊔ T)) (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
      (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G)) T e := by
  obtain ⟨D⟩ := cfg.side₁.nonempty_natCoordK
  exact
    { jst := cfg.jStructure
      nat := ⟨D⟩
      Z_cent := by
        rw [← cfg.side₁.inf_centralizer_sup_V]
        exact inf_le_right
      sylowJ := cfg.side₁.sylowJ
      J_le_T := cfg.hyg.J_le
      pT := cfg.side₁.sylow.isPGroup
      T_le_L := le_normalizer_sup cfg.side₁.sylow.le (le_sup_right.trans cfg.hyg.sup₁)
      T_le_V := le_sup_right.trans cfg.hyg.sup₁
      T_le_W := le_sup_right.trans cfg.hyg.sup₂
      cent := cfg.side₁.s4_cent D }

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4Pair₀ (cfg : A78Cfg G L₁ L₂ T e) :
    S4Pair G (L₁ ⊔ oTwoIn (L₁ ⊔ T)) (L₂ ⊔ oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
      (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G))
      (oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G)) T e where
  side₁ := cfg.s4Side₀
  side₂ := cfg.symm.s4Side₀
  nl₁ := le_normalizer_sup cfg.hyg.nl₁ le_rfl
  nl₂ := le_normalizer_sup cfg.hyg.nl₂ le_rfl
  O2 := fun P hPT hP2 h₁ h₂ hT => by
    have hle : P ≤ oTwoIn (L₁ ⊔ L₂ ⊔ T) := CGT6.le_oTwoIn_of_normal (hPT.trans le_sup_right)
      (sup_le (sup_le (le_sup_left.trans h₁) (le_sup_left.trans h₂)) hT) hP2
    rw [cfg.hyg.O2_top] at hle
    exact le_bot_iff.1 hle

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_V_le (cfg : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥) : oTwoIn (L₁ ⊔ T) ≤ L₁ := by
  have P := cfg.s4Pair₀
  obtain ⟨D⟩ := P.side₁.nat
  have hVL : ∀ v ∈ oTwoIn (L₁ ⊔ T), ∀ l ∈ L₁, v * l * v⁻¹ ∈ L₁ := fun v hv l hl =>
    conj_mem_of_mem_normalizer (cfg.side₁.sylow.le (cfg.hyg.V₁_le hv)) hl
  have hcomm : ⁅oTwoIn (L₁ ⊔ T), oTwoIn (L₂ ⊔ T)⁆ ≤ L₁ := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    have hwJ : w ∈ L₁ ⊔ oTwoIn (L₁ ⊔ T) := cfg.side₁.sylowJ.le (Subgroup.mem_sup_right hw)
    obtain ⟨l, hl, v', hv', rfl⟩ := (mem_sup_iff_of_normalizes hVL).1 hwJ
    have hvv : v' * v⁻¹ = v⁻¹ * v' := cfg.side₁.comm_V v' hv' _ (inv_mem hv)
    have e1 : ⁅v, l * v'⁆ = (v * l * v⁻¹) * l⁻¹ := by
      simp only [commutatorElement_def]
      calc v * (l * v') * v⁻¹ * (l * v')⁻¹ = v * l * (v' * v⁻¹) * v'⁻¹ * l⁻¹ := by group
        _ = v * l * (v⁻¹ * v') * v'⁻¹ * l⁻¹ := by rw [hvv]
        _ = v * l * v⁻¹ * l⁻¹ := by group
    rw [e1]
    exact mul_mem (hVL v hv l hl) (inv_mem hl)
  have hZL : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≤ L₁ :=
    (P.Z_le_comm hZ).trans hcomm
  have hsurj : ∀ g, ∃ l ∈ L₁, D.ρ l = g := by
    intro g
    obtain ⟨l, hl, hlg⟩ := D.ρ_surj g
    obtain ⟨l₁, hl₁, v, hv, rfl⟩ := (mem_sup_iff_of_normalizes hVL).1 hl
    refine ⟨l₁, hl₁, ?_⟩
    rw [← hlg, D.ρ_mul l₁ (Subgroup.mem_sup_left hl₁) v (Subgroup.mem_sup_right hv),
      (D.ρ_eq_one v (Subgroup.mem_sup_right hv)).2 hv, mul_one]
  have hcommL : ∀ w ∈ oTwoIn (L₁ ⊔ T), ∀ l ∈ L₁, w * (l * w⁻¹ * l⁻¹) ∈ L₁ := by
    intro w hw l hl
    have : w * (l * w⁻¹ * l⁻¹) = (w * l * w⁻¹) * l⁻¹ := by group
    rw [this]
    exact mul_mem (hVL w hw l hl) (inv_mem hl)
  have h0 : ∀ x : GaloisField 2 e, ∃ g ∈ L₁, g ∈ oTwoIn (L₁ ⊔ T) ∧ D.κ g = ![x, 0] := by
    intro x
    obtain ⟨w, hw, hwx⟩ := D.κ_surj ![0, -x]
    obtain ⟨l, hl, hlu⟩ := hsurj (CFSG.SL2MinimalFaithful.unipotent 1)
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcommL w hw l hl,
      mul_mem hw (D.norm l (Subgroup.mem_sup_left hl) _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw (Subgroup.mem_sup_left hl), hlu, hwx,
      CFSG.SL2MinimalFaithful.coe_unipotent]
    ext i
    fin_cases i <;> simp
  have h1 : ∀ y : GaloisField 2 e, ∃ g ∈ L₁, g ∈ oTwoIn (L₁ ⊔ T) ∧ D.κ g = ![0, y] := by
    intro y
    obtain ⟨w, hw, hwy⟩ := D.κ_surj ![-y, 0]
    let u : SpecialLinearGroup (Fin 2) (GaloisField 2 e) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩
    obtain ⟨l, hl, hlu⟩ := hsurj u
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcommL w hw l hl,
      mul_mem hw (D.norm l (Subgroup.mem_sup_left hl) _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw (Subgroup.mem_sup_left hl), hlu, hwy]
    ext i
    fin_cases i <;> simp [u]
  intro v hv
  obtain ⟨g₀, hg₀L, hg₀V, hg₀⟩ := h0 (D.κ v 0)
  obtain ⟨g₁, hg₁L, hg₁V, hg₁⟩ := h1 (D.κ v 1)
  have hκ : D.κ v = D.κ (g₀ * g₁) := by
    rw [D.κ_mul g₀ hg₀V g₁ hg₁V, hg₀, hg₁]
    ext i
    fin_cases i <;> simp
  have hz := (D.κ_eq_iff hv (mul_mem hg₀V hg₁V)).1 hκ
  have e : v = (v * (g₀ * g₁)⁻¹) * (g₀ * g₁) := by group
  rw [e]
  exact mul_mem (hZL hz) (mul_mem hg₀L hg₁L)

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4Pair (cfg : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥) :
    S4Pair G L₁ L₂ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T))
      (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G))
      (oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G)) T e := by
  have h₁ := cfg.s4_V_le hZ
  have h₂ := cfg.symm.s4_V_le (cfg.s4Pair₀.Z₂_ne_bot hZ)
  have P := cfg.s4Pair₀
  rw [sup_eq_left.2 h₁, sup_eq_left.2 h₂] at P
  exact P

end Cfg

end CFSG.CGT.PushingUpLit.A78S4
