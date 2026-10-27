module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Fix
public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Table
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

section TransvData

variable {G : Type*} [Group G] {F : Type*} [Field F]

structure TransvData (W S₀ : Subgroup G) (ι : G → F × F) (κ : G → F) : Prop where
  W_le_S₀ : W ≤ S₀
  S₀_norm_W : ∀ s ∈ S₀, ∀ w ∈ W, s * w * s⁻¹ ∈ W
  ι_add : ∀ w ∈ W, ∀ w' ∈ W, ι (w * w') = ι w + ι w'
  ι_inj : ∀ w ∈ W, ∀ w' ∈ W, ι w = ι w' → w = w'
  ι_surj : ∀ p : F × F, ∃ w ∈ W, ι w = p
  κ_add : ∀ s ∈ S₀, ∀ s' ∈ S₀, κ (s * s') = κ s + κ s'
  κ_eq_zero_iff : ∀ s ∈ S₀, κ s = 0 ↔ s ∈ W
  κ_surj : ∀ b : F, ∃ s ∈ S₀, κ s = b
  conj_ι : ∀ s ∈ S₀, ∀ w ∈ W, ι (s * w * s⁻¹) = ((ι w).1 + κ s * (ι w).2, (ι w).2)

namespace TransvData

variable {W S₀ : Subgroup G} {ι : G → F × F} {κ : G → F} (T : TransvData W S₀ ι κ)

include T

theorem ι_one : ι 1 = 0 := by
  have h := T.ι_add 1 W.one_mem 1 W.one_mem
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem ι_inv {w : G} (hw : w ∈ W) : ι w⁻¹ = -ι w := by
  have h := T.ι_add w hw w⁻¹ (W.inv_mem hw)
  rw [mul_inv_cancel, T.ι_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem κ_one : κ 1 = 0 := by
  have h := T.κ_add 1 S₀.one_mem 1 S₀.one_mem
  rw [one_mul] at h
  exact left_eq_add.mp h

theorem κ_inv {s : G} (hs : s ∈ S₀) : κ s⁻¹ = -κ s := by
  have h := T.κ_add s hs s⁻¹ (S₀.inv_mem hs)
  rw [mul_inv_cancel, T.κ_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem comm_W {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W) : w * w' = w' * w := by
  refine T.ι_inj _ (W.mul_mem hw hw') _ (W.mul_mem hw' hw) ?_
  rw [T.ι_add w hw w' hw', T.ι_add w' hw' w hw, add_comm]

theorem commute_iff {s w : G} (hs : s ∈ S₀) (hw : w ∈ W) :
    s * w = w * s ↔ κ s * (ι w).2 = 0 := by
  have h1 := T.conj_ι s hs w hw
  have hsw := T.S₀_norm_W s hs w hw
  constructor
  · intro h
    have h2 : s * w * s⁻¹ = w := by rw [h]; group
    rw [h2] at h1
    have h3 := congrArg Prod.fst h1
    simp only at h3
    linear_combination -h3
  · intro hz
    have h2 : s * w * s⁻¹ = w :=
      T.ι_inj _ hsw w hw (by rw [h1, hz, add_zero])
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2

theorem mem_W₀_iff {w : G} :
    w ∈ W ⊓ centralizer (S₀ : Set G) ↔ w ∈ W ∧ (ι w).2 = 0 := by
  rw [mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨hw, hc⟩
    refine ⟨hw, ?_⟩
    obtain ⟨s, hs, hκ⟩ := T.κ_surj 1
    have := (T.commute_iff hs hw).1 (hc s hs)
    rwa [hκ, one_mul] at this
  · rintro ⟨hw, hy⟩
    exact ⟨hw, fun s hs => (T.commute_iff hs hw).2 (by rw [hy, mul_zero])⟩

theorem comm_mem_W {s s' : G} (hs : s ∈ S₀) (hs' : s' ∈ S₀) : s * s' * s⁻¹ * s'⁻¹ ∈ W := by
  refine (T.κ_eq_zero_iff _ (S₀.mul_mem (S₀.mul_mem (S₀.mul_mem hs hs') (S₀.inv_mem hs))
    (S₀.inv_mem hs'))).1 ?_
  rw [T.κ_add _ (S₀.mul_mem (S₀.mul_mem hs hs') (S₀.inv_mem hs)) _ (S₀.inv_mem hs'),
    T.κ_add _ (S₀.mul_mem hs hs') _ (S₀.inv_mem hs), T.κ_add _ hs _ hs', T.κ_inv hs, T.κ_inv hs']
  ring

theorem comm_mem_W₀_of_torus (hF : Nat.card F = 16) {n : G}
    (hnS : ∀ s ∈ S₀, n * s * n⁻¹ ∈ S₀)
    {a b : F} (ha : orderOf a = 15)
    (hι : ∀ w ∈ W, ι (n * w * n⁻¹) = (a * (ι w).1 + b * (ι w).2, a⁻¹ * (ι w).2))
    (hκ : ∀ s ∈ S₀, κ (n * s * n⁻¹) = a ^ 2 * κ s) :
    ∀ s ∈ S₀, ∀ s' ∈ S₀, s * s' * s⁻¹ * s'⁻¹ ∈ W ⊓ centralizer (S₀ : Set G) := by
  have hWS := T.W_le_S₀
  have ha' : ∀ s ∈ S₀, ∀ x ∈ W, (ι (s * x * s⁻¹)).2 = (ι x).2 := fun s hs x hx => by
    rw [T.conj_ι s hs x hx]
  have hadd : ∀ w ∈ W, ∀ w' ∈ W, (ι (w * w')).2 = (ι w).2 + (ι w').2 := fun w hw w' hw' => by
    rw [T.ι_add w hw w' hw']
    rfl
  have hinv : ∀ w ∈ W, (ι w⁻¹).2 = -(ι w).2 := fun w hw => by
    rw [T.ι_inv hw]
    rfl
  have hb : ∀ w ∈ W, ∀ s' ∈ S₀, (ι (w * s' * w⁻¹ * s'⁻¹)).2 = 0 := by
    intro w hw s' hs'
    have h1 : s' * w⁻¹ * s'⁻¹ ∈ W := T.S₀_norm_W s' hs' w⁻¹ (W.inv_mem hw)
    have h2 : w * s' * w⁻¹ * s'⁻¹ = w * (s' * w⁻¹ * s'⁻¹) := by group
    rw [h2, hadd w hw _ h1, ha' s' hs' _ (W.inv_mem hw), hinv w hw]
    ring
  have hb' : ∀ s ∈ S₀, ∀ w ∈ W, (ι (s * w * s⁻¹ * w⁻¹)).2 = 0 := by
    intro s hs w hw
    have h1 : s * w * s⁻¹ ∈ W := T.S₀_norm_W s hs w hw
    rw [hadd _ h1 _ (W.inv_mem hw), ha' s hs w hw, hinv w hw]
    ring
  obtain ⟨cc, hcc⟩ : ∃ cc : G → G → F, ∀ x y, cc x y = (ι (x * y * x⁻¹ * y⁻¹)).2 :=
    ⟨fun x y => (ι (x * y * x⁻¹ * y⁻¹)).2, fun _ _ => rfl⟩
  have hc1 : ∀ s ∈ S₀, ∀ w ∈ W, ∀ s' ∈ S₀, cc (s * w) s' = cc s s' := by
    intro s hs w hw s' hs'
    have h1 : w * s' * w⁻¹ * s'⁻¹ ∈ W := T.comm_mem_W (hWS hw) hs'
    have h2 : s * (w * s' * w⁻¹ * s'⁻¹) * s⁻¹ ∈ W := T.S₀_norm_W s hs _ h1
    have h3 : s * s' * s⁻¹ * s'⁻¹ ∈ W := T.comm_mem_W hs hs'
    have h4 : s * w * s' * (s * w)⁻¹ * s'⁻¹
        = (s * (w * s' * w⁻¹ * s'⁻¹) * s⁻¹) * (s * s' * s⁻¹ * s'⁻¹) := by group
    rw [hcc, hcc, h4, hadd _ h2 _ h3, ha' s hs _ h1, hb w hw s' hs', zero_add]
  have hc2 : ∀ s ∈ S₀, ∀ s' ∈ S₀, ∀ w ∈ W, cc s (s' * w) = cc s s' := by
    intro s hs s' hs' w hw
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := T.comm_mem_W hs (hWS hw)
    have h2 : s' * (s * w * s⁻¹ * w⁻¹) * s'⁻¹ ∈ W := T.S₀_norm_W s' hs' _ h1
    have h3 : s * s' * s⁻¹ * s'⁻¹ ∈ W := T.comm_mem_W hs hs'
    have h4 : s * (s' * w) * s⁻¹ * (s' * w)⁻¹
        = (s * s' * s⁻¹ * s'⁻¹) * (s' * (s * w * s⁻¹ * w⁻¹) * s'⁻¹) := by group
    rw [hcc, hcc, h4, hadd _ h3 _ h2, ha' s' hs' _ h1, hb' s hs w hw, add_zero]
  have hd1 : ∀ s₁ ∈ S₀, ∀ s₂ ∈ S₀, ∀ s' ∈ S₀, cc (s₁ * s₂) s' = cc s₁ s' + cc s₂ s' := by
    intro s₁ hs₁ s₂ hs₂ s' hs'
    have h1 : s₂ * s' * s₂⁻¹ * s'⁻¹ ∈ W := T.comm_mem_W hs₂ hs'
    have h2 : s₁ * (s₂ * s' * s₂⁻¹ * s'⁻¹) * s₁⁻¹ ∈ W := T.S₀_norm_W s₁ hs₁ _ h1
    have h3 : s₁ * s' * s₁⁻¹ * s'⁻¹ ∈ W := T.comm_mem_W hs₁ hs'
    have h4 : s₁ * s₂ * s' * (s₁ * s₂)⁻¹ * s'⁻¹
        = (s₁ * (s₂ * s' * s₂⁻¹ * s'⁻¹) * s₁⁻¹) * (s₁ * s' * s₁⁻¹ * s'⁻¹) := by group
    rw [hcc, hcc, hcc, h4, hadd _ h2 _ h3, ha' s₁ hs₁ _ h1, add_comm]
  have hd2 : ∀ s ∈ S₀, ∀ s₁ ∈ S₀, ∀ s₂ ∈ S₀, cc s (s₁ * s₂) = cc s s₁ + cc s s₂ := by
    intro s hs s₁ hs₁ s₂ hs₂
    have h1 : s * s₂ * s⁻¹ * s₂⁻¹ ∈ W := T.comm_mem_W hs hs₂
    have h2 : s₁ * (s * s₂ * s⁻¹ * s₂⁻¹) * s₁⁻¹ ∈ W := T.S₀_norm_W s₁ hs₁ _ h1
    have h3 : s * s₁ * s⁻¹ * s₁⁻¹ ∈ W := T.comm_mem_W hs hs₁
    have h4 : s * (s₁ * s₂) * s⁻¹ * (s₁ * s₂)⁻¹
        = (s * s₁ * s⁻¹ * s₁⁻¹) * (s₁ * (s * s₂ * s⁻¹ * s₂⁻¹) * s₁⁻¹) := by group
    rw [hcc, hcc, hcc, h4, hadd _ h3 _ h2, ha' s₁ hs₁ _ h1]
  have he : ∀ s ∈ S₀, ∀ s' ∈ S₀, cc (n * s * n⁻¹) (n * s' * n⁻¹) = a⁻¹ * cc s s' := by
    intro s hs s' hs'
    have h4 : n * s * n⁻¹ * (n * s' * n⁻¹) * (n * s * n⁻¹)⁻¹ * (n * s' * n⁻¹)⁻¹
        = n * (s * s' * s⁻¹ * s'⁻¹) * n⁻¹ := by group
    rw [hcc, hcc, h4, hι _ (T.comm_mem_W hs hs')]
  choose lift hlmem hlκ using T.κ_surj
  have hi1 : ∀ s ∈ S₀, ∀ s' ∈ S₀, cc s s' = cc (lift (κ s)) s' := by
    intro s hs s' hs'
    have hl := hlmem (κ s)
    have hw : (lift (κ s))⁻¹ * s ∈ W := by
      rw [← T.κ_eq_zero_iff _ (S₀.mul_mem (S₀.inv_mem hl) hs),
        T.κ_add _ (S₀.inv_mem hl) _ hs, T.κ_inv hl, hlκ]
      ring
    have h := hc1 _ hl _ hw s' hs'
    rwa [mul_inv_cancel_left] at h
  have hi2 : ∀ s ∈ S₀, ∀ s' ∈ S₀, cc s s' = cc s (lift (κ s')) := by
    intro s hs s' hs'
    have hl := hlmem (κ s')
    have hw : (lift (κ s'))⁻¹ * s' ∈ W := by
      rw [← T.κ_eq_zero_iff _ (S₀.mul_mem (S₀.inv_mem hl) hs'),
        T.κ_add _ (S₀.inv_mem hl) _ hs', T.κ_inv hl, hlκ]
      ring
    have h := hc2 s hs _ hl _ hw
    rwa [mul_inv_cancel_left] at h
  obtain ⟨β, hβ⟩ : ∃ β : F → F → F, ∀ x y, β x y = cc (lift x) (lift y) :=
    ⟨fun x y => cc (lift x) (lift y), fun _ _ => rfl⟩
  have hβ' : ∀ s ∈ S₀, ∀ s' ∈ S₀, ∀ x y, κ s = x → κ s' = y → β x y = cc s s' := by
    rintro s hs s' hs' x y rfl rfl
    rw [hβ, hi1 s hs s' hs', hi2 _ (hlmem _) s' hs']
  have hx : ∀ x x' y, β (x + x') y = β x y + β x' y := by
    intro x x' y
    have hsum : lift x * lift x' ∈ S₀ := S₀.mul_mem (hlmem x) (hlmem x')
    have hκsum : κ (lift x * lift x') = x + x' := by
      rw [T.κ_add _ (hlmem x) _ (hlmem x'), hlκ, hlκ]
    calc β (x + x') y = cc (lift x * lift x') (lift y) :=
          hβ' _ hsum _ (hlmem y) _ _ hκsum (hlκ y)
      _ = cc (lift x) (lift y) + cc (lift x') (lift y) :=
          hd1 _ (hlmem x) _ (hlmem x') _ (hlmem y)
      _ = β x y + β x' y := by
          rw [← hβ' _ (hlmem x) _ (hlmem y) _ _ (hlκ x) (hlκ y),
            ← hβ' _ (hlmem x') _ (hlmem y) _ _ (hlκ x') (hlκ y)]
  have hy : ∀ x y y', β x (y + y') = β x y + β x y' := by
    intro x y y'
    have hsum : lift y * lift y' ∈ S₀ := S₀.mul_mem (hlmem y) (hlmem y')
    have hκsum : κ (lift y * lift y') = y + y' := by
      rw [T.κ_add _ (hlmem y) _ (hlmem y'), hlκ, hlκ]
    calc β x (y + y') = cc (lift x) (lift y * lift y') :=
          hβ' _ (hlmem x) _ hsum _ _ (hlκ x) hκsum
      _ = cc (lift x) (lift y) + cc (lift x) (lift y') :=
          hd2 _ (hlmem x) _ (hlmem y) _ (hlmem y')
      _ = β x y + β x y' := by
          rw [← hβ' _ (hlmem x) _ (hlmem y) _ _ (hlκ x) (hlκ y),
            ← hβ' _ (hlmem x) _ (hlmem y') _ _ (hlκ x) (hlκ y')]
  have ha15 : a ^ 15 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  have hinv14 : a⁻¹ = a ^ 14 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha15)
  have hw : ∀ x y, β (a ^ 2 * x) (a ^ 2 * y) = a ^ 14 * β x y := by
    intro x y
    have hx' : κ (n * lift x * n⁻¹) = a ^ 2 * x := by rw [hκ _ (hlmem x), hlκ]
    have hy' : κ (n * lift y * n⁻¹) = a ^ 2 * y := by rw [hκ _ (hlmem y), hlκ]
    calc β (a ^ 2 * x) (a ^ 2 * y) = cc (n * lift x * n⁻¹) (n * lift y * n⁻¹) :=
          hβ' _ (hnS _ (hlmem x)) _ (hnS _ (hlmem y)) _ _ hx' hy'
      _ = a⁻¹ * cc (lift x) (lift y) := he _ (hlmem x) _ (hlmem y)
      _ = a ^ 14 * β x y := by
          rw [hinv14, ← hβ' _ (hlmem x) _ (hlmem y) _ _ (hlκ x) (hlκ y)]
  have hzero := Weights16.biadditive_U_U_Lambda hF ha (β := β) hx hy hw
  intro s hs s' hs'
  refine T.mem_W₀_iff.2 ⟨T.comm_mem_W hs hs', ?_⟩
  exact (hcc s s').symm.trans ((hβ' s hs s' hs' _ _ rfl rfl).symm.trans (hzero _ _))


theorem freeSeries [CharP F 2] (hF : Nat.card F = 16) {t : G}
    (htS : ∀ s ∈ S₀, t * s * t⁻¹ ∈ S₀) (htW : ∀ w ∈ W, t * w * t⁻¹ ∈ W)
    {p s' t' l : F} (hp : p * p ^ 4 = 1) (ht' : t' * t' ^ 4 = 1) (hl : l * l ^ 4 = 1)
    (hι : ∀ w ∈ W, ι (t * w * t⁻¹) = (p * (ι w).1 ^ 4 + s' * (ι w).2 ^ 4, t' * (ι w).2 ^ 4))
    (hκ : ∀ s ∈ S₀, κ (t * s * t⁻¹) = l * κ s ^ 4) :
    FreeSeries (MulAut.conj t) S₀ := by
  have h2 : ∀ x : F, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have hσ : ∀ g : G, MulAut.conj t g = t * g * t⁻¹ := fun g => MulAut.conj_apply t g
  obtain ⟨W₀, hmem⟩ : ∃ W₀ : Subgroup G, ∀ w, w ∈ W₀ ↔ w ∈ W ∧ (ι w).2 = 0 :=
    ⟨W ⊓ centralizer (S₀ : Set G), fun w => T.mem_W₀_iff⟩
  have hW₀W : ∀ {n : G}, n ∈ W₀ → n ∈ W := fun hn => ((hmem _).1 hn).1
  have a1 : ∀ w ∈ W, ∀ w' ∈ W, (ι (w * w')).1 = (ι w).1 + (ι w').1 :=
    fun w hw w' hw' => congrArg Prod.fst (T.ι_add w hw w' hw')
  have a2 : ∀ w ∈ W, ∀ w' ∈ W, (ι (w * w')).2 = (ι w).2 + (ι w').2 :=
    fun w hw w' hw' => congrArg Prod.snd (T.ι_add w hw w' hw')
  have i1 : ∀ w ∈ W, (ι w⁻¹).1 = -(ι w).1 := fun w hw => congrArg Prod.fst (T.ι_inv hw)
  have i2 : ∀ w ∈ W, (ι w⁻¹).2 = -(ι w).2 := fun w hw => congrArg Prod.snd (T.ι_inv hw)
  have c1 : ∀ w ∈ W, (ι (t * w * t⁻¹)).1 = p * (ι w).1 ^ 4 + s' * (ι w).2 ^ 4 :=
    fun w hw => congrArg Prod.fst (hι w hw)
  have c2 : ∀ w ∈ W, (ι (t * w * t⁻¹)).2 = t' * (ι w).2 ^ 4 :=
    fun w hw => congrArg Prod.snd (hι w hw)
  have o1 : (ι 1).1 = 0 := congrArg Prod.fst T.ι_one
  have o2 : (ι 1).2 = 0 := congrArg Prod.snd T.ι_one
  have hW₀_inv : ∀ n ∈ W₀, t * n * t⁻¹ ∈ W₀ := by
    intro n hn
    obtain ⟨hnW, hn2⟩ := (hmem n).1 hn
    refine (hmem _).2 ⟨htW n hnW, ?_⟩
    rw [c2 n hnW, hn2]
    simp
  have L1 : FreeLayer (MulAut.conj t) W S₀ :=
    { le := T.W_le_S₀
      normal := T.S₀_norm_W
      invT := fun g hg => by rw [hσ]; exact htS g hg
      invN := fun n hn => by rw [hσ]; exact htW n hn
      comm := fun g hg h hh => T.comm_mem_W hg hh
      sq := fun g hg => (T.κ_eq_zero_iff _ (S₀.mul_mem hg hg)).1
        (by rw [T.κ_add g hg g hg]; exact h2 _)
      free := by
        intro g hg hgW
        have hσg : t * g * t⁻¹ ∈ S₀ := htS g hg
        rw [hσ] at hgW
        have h0 := (T.κ_eq_zero_iff _ (S₀.mul_mem (S₀.inv_mem hg) hσg)).2 hgW
        rw [T.κ_add _ (S₀.inv_mem hg) _ hσg, T.κ_inv hg, hκ g hg] at h0
        obtain ⟨y, hy⟩ := Weights16.exists_eq_add_semilinear hF hl
          (show l * κ g ^ 4 = κ g by linear_combination h0)
        obtain ⟨f, hfS, hfκ⟩ := T.κ_surj y
        have hσf : t * f * t⁻¹ ∈ S₀ := htS f hfS
        refine ⟨f, hfS, ?_⟩
        rw [hσ]
        refine (T.κ_eq_zero_iff _ (S₀.mul_mem (S₀.inv_mem hg) (S₀.mul_mem hfS hσf))).1 ?_
        rw [T.κ_add _ (S₀.inv_mem hg) _ (S₀.mul_mem hfS hσf), T.κ_inv hg,
          T.κ_add _ hfS _ hσf, hκ f hfS, hfκ]
        linear_combination -hy }
  have L2 : FreeLayer (MulAut.conj t) W₀ W :=
    { le := fun n hn => hW₀W hn
      normal := fun g hg n hn => by
        rw [T.comm_W hg (hW₀W hn), mul_inv_cancel_right]
        exact hn
      invT := fun g hg => by rw [hσ]; exact htW g hg
      invN := fun n hn => by rw [hσ]; exact hW₀_inv n hn
      comm := fun g hg h hh => by
        rw [T.comm_W hg hh, mul_inv_cancel_right, mul_inv_cancel]
        exact W₀.one_mem
      sq := fun g hg => (hmem _).2 ⟨W.mul_mem hg hg, by rw [a2 g hg g hg]; exact h2 _⟩
      free := by
        intro g hg hgW₀
        have hσg : t * g * t⁻¹ ∈ W := htW g hg
        rw [hσ] at hgW₀
        have h0 := ((hmem _).1 hgW₀).2
        rw [a2 _ (W.inv_mem hg) _ hσg, i2 _ hg, c2 g hg] at h0
        obtain ⟨y, hy⟩ := Weights16.exists_eq_add_semilinear hF ht'
          (show t' * (ι g).2 ^ 4 = (ι g).2 by linear_combination h0)
        obtain ⟨f, hfW, hfι⟩ := T.ι_surj (0, y)
        have hf2 : (ι f).2 = y := congrArg Prod.snd hfι
        have hσf : t * f * t⁻¹ ∈ W := htW f hfW
        refine ⟨f, hfW, ?_⟩
        rw [hσ]
        refine (hmem _).2 ⟨W.mul_mem (W.inv_mem hg) (W.mul_mem hfW hσf), ?_⟩
        rw [a2 _ (W.inv_mem hg) _ (W.mul_mem hfW hσf), i2 _ hg, a2 _ hfW _ hσf, c2 f hfW, hf2]
        linear_combination -hy }
  have L3 : FreeLayer (MulAut.conj t) ⊥ W₀ :=
    { le := bot_le
      normal := fun g _ n hn => by
        rw [Subgroup.mem_bot.1 hn]
        simp
      invT := fun g hg => by rw [hσ]; exact hW₀_inv g hg
      invN := fun n hn => by
        rw [Subgroup.mem_bot.1 hn, map_one]
        exact Subgroup.one_mem _
      comm := fun g hg h hh => by
        rw [T.comm_W (hW₀W hg) (hW₀W hh), mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      sq := fun g hg => by
        obtain ⟨hgW, hg2⟩ := (hmem _).1 hg
        refine Subgroup.mem_bot.2 (T.ι_inj _ (W.mul_mem hgW hgW) 1 W.one_mem ?_)
        refine Prod.ext ?_ ?_
        · rw [a1 g hgW g hgW, o1]
          exact h2 _
        · rw [a2 g hgW g hgW, o2, hg2, add_zero]
      free := by
        intro g hg hg1
        obtain ⟨hgW, hg2⟩ := (hmem _).1 hg
        have hfix : t * g * t⁻¹ = g := by
          have h1 := Subgroup.mem_bot.1 hg1
          rw [hσ] at h1
          exact (inv_mul_eq_one.1 h1).symm
        have h1 := c1 g hgW
        rw [hfix] at h1
        obtain ⟨x, hx⟩ := Weights16.exists_eq_add_semilinear hF hp
          (show p * (ι g).1 ^ 4 = (ι g).1 by
            linear_combination -h1 - s' * (ι g).2 ^ 3 * hg2)
        obtain ⟨f, hfW, hfι⟩ := T.ι_surj (x, 0)
        have hf1 : (ι f).1 = x := congrArg Prod.fst hfι
        have hf2 : (ι f).2 = 0 := congrArg Prod.snd hfι
        have hσf : t * f * t⁻¹ ∈ W := htW f hfW
        refine ⟨f, (hmem f).2 ⟨hfW, hf2⟩, ?_⟩
        rw [hσ]
        refine Subgroup.mem_bot.2 (T.ι_inj _ (W.mul_mem (W.inv_mem hgW) (W.mul_mem hfW hσf)) 1
          W.one_mem ?_)
        refine Prod.ext ?_ ?_
        · rw [a1 _ (W.inv_mem hgW) _ (W.mul_mem hfW hσf), i1 _ hgW, a1 _ hfW _ hσf, c1 f hfW,
            hf1, hf2, o1]
          linear_combination -hx
        · rw [a2 _ (W.inv_mem hgW) _ (W.mul_mem hfW hσf), i2 _ hgW, a2 _ hfW _ hσf, c2 f hfW,
            hf2, hg2, o2]
          ring }
  exact FreeSeries.step L1 (FreeSeries.step L2 (FreeSeries.step L3 FreeSeries.bot))

end TransvData

end TransvData

end CFSG.OddStandard.Seitz77
