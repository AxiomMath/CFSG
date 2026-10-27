module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Defs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem isInvariant_mono {ρ : Representation (ZMod 2) G W} {H H' : Subgroup G}
    {Y : Submodule (ZMod 2) W} (h : H' ≤ H) (hY : GeneralFF.IsInvariant ρ H Y) : GeneralFF.IsInvariant ρ H' Y :=
  fun a ha u hu => hY a (h ha) u hu

theorem relFix_le {ρ : Representation (ZMod 2) G W} {B : Subgroup G}
    {Y₀ Y₁ : Submodule (ZMod 2) W} : relFix ρ B Y₀ Y₁ ≤ Y₁ :=
  fun _ h => h.1

theorem secChi_add (ρ : Representation (ZMod 2) G W) (f : Polynomial (ZMod 2)) (x y : G)
    (Z₀ Z₁ Z₂ : Submodule (ZMod 2) W) :
    secChi ρ f x y Z₀ Z₂ = secChi ρ f x y Z₀ Z₁ + secChi ρ f x y Z₁ Z₂ := by
  unfold secChi; ring

theorem secChi_self (ρ : Representation (ZMod 2) G W) (f : Polynomial (ZMod 2)) (x y : G)
    (Z : Submodule (ZMod 2) W) : secChi ρ f x y Z Z = 0 := by
  unfold secChi; ring

theorem secCod_add_le [Finite W] {ρ : Representation (ZMod 2) G W} {B : Subgroup G}
    {Z₀ Z₁ Z₂ : Submodule (ZMod 2) W} (h₀₁ : Z₀ ≤ Z₁) (h₁₂ : Z₁ ≤ Z₂)
    (hZ₁ : GeneralFF.IsInvariant ρ B Z₁) :
    secCod ρ B Z₀ Z₁ + secCod ρ B Z₁ Z₂ ≤ secCod ρ B Z₀ Z₂ := by
  have hsub1 : relFix ρ B Z₀ Z₂ ⊓ Z₁ ≤ relFix ρ B Z₀ Z₁ :=
    fun y hy => ⟨hy.2, hy.1.2⟩
  have hsub2 : relFix ρ B Z₀ Z₂ ⊔ Z₁ ≤ relFix ρ B Z₁ Z₂ := by
    refine sup_le ?_ ?_
    · intro y hy
      exact ⟨hy.1, fun b hb => h₀₁ (hy.2 b hb)⟩
    · intro y hy
      exact ⟨h₁₂ hy, fun b hb => Z₁.sub_mem (hZ₁ b hb y hy) hy⟩
  have key := Submodule.finrank_sup_add_finrank_inf_eq (relFix ρ B Z₀ Z₂) Z₁
  have m1 := Submodule.finrank_mono hsub1
  have m2 := Submodule.finrank_mono hsub2
  have l1 : Module.finrank (ZMod 2) (relFix ρ B Z₀ Z₁) ≤ Module.finrank (ZMod 2) Z₁ :=
    Submodule.finrank_mono relFix_le
  have l2 : Module.finrank (ZMod 2) (relFix ρ B Z₁ Z₂) ≤ Module.finrank (ZMod 2) Z₂ :=
    Submodule.finrank_mono relFix_le
  have l3 : Module.finrank (ZMod 2) (relFix ρ B Z₀ Z₂) ≤ Module.finrank (ZMod 2) Z₂ :=
    Submodule.finrank_mono relFix_le
  unfold secCod
  omega

theorem secCod_mono_sub [Finite W] {ρ : Representation (ZMod 2) G W} {B : Subgroup G}
    {Y₀ Z₀ Z₁ Y₁ : Submodule (ZMod 2) W} (h₁ : Y₀ ≤ Z₀) (h₂ : Z₀ ≤ Z₁) (h₃ : Z₁ ≤ Y₁)
    (hZ₀ : GeneralFF.IsInvariant ρ B Z₀) (hZ₁ : GeneralFF.IsInvariant ρ B Z₁) :
    secCod ρ B Z₀ Z₁ ≤ secCod ρ B Y₀ Y₁ := by
  have a := secCod_add_le (ρ := ρ) (B := B) (h₁.trans h₂) h₃ hZ₁
  have b := secCod_add_le (ρ := ρ) (B := B) h₁ h₂ hZ₀
  omega

theorem secTrivial_trans {ρ : Representation (ZMod 2) G W} {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    {Z₀ Z₁ Z₂ : Submodule (ZMod 2) W} (h₀ : SecTrivial ρ K Z₀ Z₁) (h₁ : SecTrivial ρ K Z₁ Z₂) :
    SecTrivial ρ K Z₀ Z₂ := by
  have hmul : ∀ g ∈ K, ∀ h ∈ K, ∀ v ∈ Z₂,
      (Submodule.Quotient.mk (ρ (g * h) v - v) : W ⧸ Z₀) =
        Submodule.Quotient.mk (ρ g v - v) + Submodule.Quotient.mk (ρ h v - v) := by
    intro g hg h hh v hv
    have h1 : ρ h v - v ∈ Z₁ := h₁ h hh v hv
    have h2 : ρ g (ρ h v - v) - (ρ h v - v) ∈ Z₀ := h₀ g hg _ h1
    have e : ρ (g * h) v - v =
        (ρ g v - v) + (ρ h v - v) + (ρ g (ρ h v - v) - (ρ h v - v)) := by
      simp only [map_mul, Module.End.mul_apply, map_sub]; abel
    rw [e, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero Z₀).2 h2, add_zero]
  have hinv : ∀ g ∈ K, ∀ v ∈ Z₂,
      (Submodule.Quotient.mk (ρ g⁻¹ v - v) : W ⧸ Z₀) =
        -Submodule.Quotient.mk (ρ g v - v) := by
    intro g hg v hv
    have := hmul g hg g⁻¹ (K.inv_mem hg) v hv
    rw [mul_inv_cancel, map_one] at this
    simp only [Module.End.one_apply, sub_self, Submodule.Quotient.mk_zero] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  let S : Subgroup G :=
    { carrier := {g | g ∈ K ∧ ∀ v ∈ Z₂, (Submodule.Quotient.mk (ρ g v - v) : W ⧸ Z₀) = 0}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, fun v hv => by
        rw [hmul a ha.1 b hb.1 v hv, ha.2 v hv, hb.2 v hv, add_zero]⟩
      one_mem' := ⟨K.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, fun v hv => by
        rw [hinv a ha.1 v hv, ha.2 v hv, neg_zero]⟩ }
  have hcomm : ⁅K, K⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    have hmem : ⁅k₁, k₂⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
    refine ⟨hmem, fun v hv => ?_⟩
    rw [commutatorElement_def, hmul _ (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) _
      (K.inv_mem hk₂) v hv, hmul _ (K.mul_mem hk₁ hk₂) _ (K.inv_mem hk₁) v hv,
      hmul _ hk₁ _ hk₂ v hv, hinv k₁ hk₁ v hv, hinv k₂ hk₂ v hv]
    abel
  rw [hK] at hcomm
  intro k hk v hv
  exact (Submodule.Quotient.mk_eq_zero Z₀).1 ((hcomm hk).2 v hv)

@[expose] def SecOracle (ρ : Representation (ZMod 2) G W) (K B : Subgroup G)
    (f : Polynomial (ZMod 2)) (x y : G) (c γp γm : ℕ) (Y₀ Y₁ : Submodule (ZMod 2) W) : Prop :=
  ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Y₀ ≤ Z₀ → Z₁ ≤ Y₁ → IsMinSec ρ (K ⊔ B) Z₀ Z₁ →
    secCod ρ B Z₀ Z₁ ≤ secCod ρ B Y₀ Y₁ →
    (SecTrivial ρ K Z₀ Z₁ ∧ secChi ρ f x y Z₀ Z₁ = 0) ∨
    (secChi ρ f x y Z₀ Z₁ = c ∧ γp ≤ secCod ρ B Z₀ Z₁) ∨
    (secChi ρ f x y Z₀ Z₁ = -c ∧ γm ≤ secCod ρ B Z₀ Z₁)

theorem secChi_exists [Finite W] (ρ : Representation (ZMod 2) G W) {K B : Subgroup G}
    (hK : ⁅K, K⁆ = K) (f : Polynomial (ZMod 2)) (x y : G) (c γp γm : ℕ)
    {Y₀ Y₁ : Submodule (ZMod 2) W} (horacle : SecOracle ρ K B f x y c γp γm Y₀ Y₁) :
    ∀ n : ℕ, ∀ Z₀ Z₁ : Submodule (ZMod 2) W,
      Module.finrank (ZMod 2) Z₁ - Module.finrank (ZMod 2) Z₀ = n → Y₀ ≤ Z₀ → Z₀ ≤ Z₁ →
      Z₁ ≤ Y₁ → GeneralFF.IsInvariant ρ (K ⊔ B) Z₀ → GeneralFF.IsInvariant ρ (K ⊔ B) Z₁ →
      ∃ np nm : ℕ, secChi ρ f x y Z₀ Z₁ = (c : ℤ) * ((np : ℤ) - nm) ∧
        γp * np + γm * nm ≤ secCod ρ B Z₀ Z₁ ∧ (np + nm = 0 → SecTrivial ρ K Z₀ Z₁) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Z₀ Z₁ hn hY₀ hle hY₁ hZ₀ hZ₁
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    refine ⟨0, 0, ?_, ?_, fun _ => ?_⟩
    · simp [secChi_self]
    · simp
    · intro k hk v hv
      exact Z₀.sub_mem (hZ₀ k (Subgroup.mem_sup_left hk) v hv) hv
  · by_cases hex : ∃ Z, GeneralFF.IsInvariant ρ (K ⊔ B) Z ∧ Z₀ < Z ∧ Z < Z₁
    · obtain ⟨Z, hZ, h0Z, hZ1⟩ := hex
      have hfr0 : Module.finrank (ZMod 2) Z₀ < Module.finrank (ZMod 2) Z :=
        Submodule.finrank_lt_finrank_of_lt h0Z
      have hfr1 : Module.finrank (ZMod 2) Z < Module.finrank (ZMod 2) Z₁ :=
        Submodule.finrank_lt_finrank_of_lt hZ1
      obtain ⟨ap, am, ha1, ha2, ha3⟩ := ih (Module.finrank (ZMod 2) Z -
        Module.finrank (ZMod 2) Z₀) (by omega) Z₀ Z rfl hY₀ h0Z.le (hZ1.le.trans hY₁) hZ₀ hZ
      obtain ⟨bp, bm, hb1, hb2, hb3⟩ := ih (Module.finrank (ZMod 2) Z₁ -
        Module.finrank (ZMod 2) Z) (by omega) Z Z₁ rfl (hY₀.trans h0Z.le) hZ1.le hY₁ hZ hZ₁
      refine ⟨ap + bp, am + bm, ?_, ?_, ?_⟩
      · rw [secChi_add ρ f x y Z₀ Z Z₁, ha1, hb1]; push_cast; ring
      · have := secCod_add_le (ρ := ρ) (B := B) h0Z.le hZ1.le (isInvariant_mono le_sup_right hZ)
        nlinarith [ha2, hb2, this]
      · intro hsum
        have h1 : ap + am = 0 := by omega
        have h2 : bp + bm = 0 := by omega
        exact secTrivial_trans hK (ha3 h1) (hb3 h2)
    · have hmin : IsMinSec ρ (K ⊔ B) Z₀ Z₁ :=
        ⟨hZ₀, hZ₁, hlt, fun Z hZ h1 h2 => by
          by_contra hne
          push Not at hne
          exact hex ⟨Z, hZ, lt_of_le_of_ne h1 hne.1.symm, lt_of_le_of_ne h2 hne.2⟩⟩
      have hcod : secCod ρ B Z₀ Z₁ ≤ secCod ρ B Y₀ Y₁ :=
        secCod_mono_sub hY₀ hle hY₁ (isInvariant_mono le_sup_right hZ₀)
          (isInvariant_mono le_sup_right hZ₁)
      rcases horacle Z₀ Z₁ hY₀ hY₁ hmin hcod with ⟨ht, hχ⟩ | ⟨hχ, hγ⟩ | ⟨hχ, hγ⟩
      · exact ⟨0, 0, by simp [hχ], by simp, fun _ => ht⟩
      · exact ⟨1, 0, by simp [hχ], by simpa using hγ, fun h => by omega⟩
      · exact ⟨0, 1, by simp [hχ], by simpa using hγ, fun h => by omega⟩

theorem secChi_ne_zero [Finite W] (ρ : Representation (ZMod 2) G W) (K B : Subgroup G)
    (hK : ⁅K, K⁆ = K) (f : Polynomial (ZMod 2)) (x y : G) (c γp γm : ℕ) (hc : 0 < c)
    {Y₀ Y₁ : Submodule (ZMod 2) W} (h₀ : GeneralFF.IsInvariant ρ (K ⊔ B) Y₀)
    (h₁ : GeneralFF.IsInvariant ρ (K ⊔ B) Y₁) (hle : Y₀ ≤ Y₁) (hnt : ¬ SecTrivial ρ K Y₀ Y₁)
    (horacle : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Y₀ ≤ Z₀ → Z₁ ≤ Y₁ → IsMinSec ρ (K ⊔ B) Z₀ Z₁ →
      secCod ρ B Z₀ Z₁ ≤ secCod ρ B Y₀ Y₁ →
      (SecTrivial ρ K Z₀ Z₁ ∧ secChi ρ f x y Z₀ Z₁ = 0) ∨
      (secChi ρ f x y Z₀ Z₁ = c ∧ γp ≤ secCod ρ B Z₀ Z₁) ∨
      (secChi ρ f x y Z₀ Z₁ = -c ∧ γm ≤ secCod ρ B Z₀ Z₁))
    (hγ : secCod ρ B Y₀ Y₁ < γp + γm) (hγp : 1 ≤ γp) (hγm : 1 ≤ γm) :
    secChi ρ f x y Y₀ Y₁ ≠ 0 := by
  have _ := hγp
  have _ := hγm
  obtain ⟨np, nm, h1, h2, h3⟩ := secChi_exists ρ hK f x y c γp γm horacle _ Y₀ Y₁ rfl
    le_rfl hle le_rfl h₀ h₁
  have hne : np + nm ≠ 0 := fun h => hnt (h3 h)
  have hone : np = 0 ∨ nm = 0 := by
    by_contra hcon
    push Not at hcon
    have a : γp ≤ γp * np := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hcon.1)
    have b : γm ≤ γm * nm := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hcon.2)
    omega
  intro hχ
  rw [h1] at hχ
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdiff : (np : ℤ) - nm = 0 := by
    rcases mul_eq_zero.1 hχ with h | h
    · exact absurd h hc'
    · exact h
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
