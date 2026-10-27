module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSwap
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallResidual
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore oddCoreLift)
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute)

section TypeFree

variable {Y : Type*} [Group Y]

theorem factor_eq_of_mul_eq_mul_of_inf_eq_bot {A B : Subgroup Y} (hAB : A ⊓ B = ⊥)
    {a₁ a₂ b₁ b₂ : Y} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h : a₁ * b₁ = a₂ * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
      _ = b₂ * b₁⁻¹ := by group
  have hmem : a₂⁻¹ * a₁ ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, h1 ▸ mul_mem hb₂ (inv_mem hb₁)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have ha : a₁ = a₂ := by
    calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
      _ = a₂ := by rw [hmem, mul_one]
  refine ⟨ha, ?_⟩
  rw [ha] at h
  exact mul_left_cancel h

theorem eq_or_eq_conj_of_fix_of_swap [Finite Y] {A D : Subgroup Y} {s : Y} (hs2 : s * s = 1)
    (hAs : A.map (MulAut.conj s).toMonoidHom ≤ centralizer (A : Set Y))
    (hinf : A ⊓ A.map (MulAut.conj s).toMonoidHom = ⊥)
    (hAsimp : IsSimpleGroup A) (hAnab : ∃ a b : A, a * b ≠ b * a)
    (hDAB : D ≤ A ⊔ A.map (MulAut.conj s).toMonoidHom)
    (hsD : ∀ d ∈ D, s * d = d * s) (hcard : Nat.card D = Nat.card A)
    (φ : MulAut Y) (hφP : (A ⊔ A.map (MulAut.conj s).toMonoidHom).map φ.toMonoidHom =
      A ⊔ A.map (MulAut.conj s).toMonoidHom)
    (hφD : ∀ d ∈ D, φ d = d) (hφs : φ s = s) :
    (∀ x ∈ A ⊔ A.map (MulAut.conj s).toMonoidHom, φ x = x) ∨
      (∀ x ∈ A ⊔ A.map (MulAut.conj s).toMonoidHom, φ x = s * x * s⁻¹) := by
  set B : Subgroup Y := A.map (MulAut.conj s).toMonoidHom with hB
  set P : Subgroup Y := A ⊔ B with hP
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (hAs hb)) a ha
  have hdec : ∀ x ∈ P, ∃ a ∈ A, ∃ b ∈ B, x = a * b := fun x hx =>
    exists_mul_of_mem_sup_of_commute hAB hx
  have hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ B := fun a ha => ⟨a, ha, rfl⟩
  have hsB : ∀ b ∈ B, s * b * s⁻¹ ∈ A := by
    rintro _ ⟨a, ha, rfl⟩
    have h : s * (s * a * s⁻¹) * s⁻¹ = a := by
      calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s * s)⁻¹ := by group
        _ = a := by rw [hs2]; group
    change s * (s * a * s⁻¹) * s⁻¹ ∈ A
    rw [h]
    exact ha
  have hDB : ∀ d ∈ D, d ∈ B → d = 1 := by
    intro d hd hdB
    have hdA : d ∈ A := by
      have h := hsB d hdB
      rwa [hsD d hd, mul_inv_cancel_right] at h
    have : d ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hdA, hdB⟩
    rwa [hinf, Subgroup.mem_bot] at this
  have hsurj : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ D := by
    classical
    let g : D → A := fun d => ⟨(hdec d (hDAB d.2)).choose, (hdec d (hDAB d.2)).choose_spec.1⟩
    have hg : ∀ d : D, ∃ b ∈ B, (d : Y) = (g d : Y) * b := fun d =>
      (hdec d (hDAB d.2)).choose_spec.2
    have hinj : Function.Injective g := by
      intro d₁ d₂ h12
      obtain ⟨b₁, hb₁, h₁⟩ := hg d₁
      obtain ⟨b₂, hb₂, h₂⟩ := hg d₂
      have hmem : (d₁ : Y)⁻¹ * d₂ ∈ B := by
        rw [h₁, h₂, h12]
        have : ((g d₂ : Y) * b₁)⁻¹ * ((g d₂ : Y) * b₂) = b₁⁻¹ * b₂ := by group
        rw [this]
        exact mul_mem (inv_mem hb₁) hb₂
      have h1 := hDB _ (mul_mem (inv_mem d₁.2) d₂.2) hmem
      apply Subtype.ext
      calc (d₁ : Y) = d₁ * ((d₁ : Y)⁻¹ * d₂) := by rw [h1, mul_one]
        _ = d₂ := by group
    have hbij := hinj.bijective_of_nat_card_le hcard.symm.le
    intro a ha
    obtain ⟨d, hd⟩ := hbij.2 ⟨a, ha⟩
    obtain ⟨b, hb, hdb⟩ := hg d
    refine ⟨b, hb, ?_⟩
    have h1 : (g d : Y) = a := congrArg Subtype.val hd
    rw [← h1, ← hdb]
    exact d.2
  have hkey : ∀ θ : MulAut Y, (∀ d ∈ D, θ d = d) → θ s = s → (∀ a ∈ A, θ a ∈ A) →
      ∀ x ∈ P, θ x = x := by
    intro θ hθD hθs hθA
    have hθB : ∀ b ∈ B, θ b ∈ B := by
      rintro _ ⟨a, ha, rfl⟩
      change θ (s * a * s⁻¹) ∈ B
      rw [map_mul, map_mul, map_inv, hθs]
      exact hsA _ (hθA a ha)
    have hfixA : ∀ a ∈ A, θ a = a := by
      intro a ha
      obtain ⟨b, hb, hd⟩ := hsurj a ha
      have h1 := hθD _ hd
      rw [map_mul] at h1
      exact (factor_eq_of_mul_eq_mul_of_inf_eq_bot hinf (hθA a ha) ha (hθB b hb) hb h1).1
    have hfixB : ∀ b ∈ B, θ b = b := by
      rintro _ ⟨a, ha, rfl⟩
      change θ (s * a * s⁻¹) = s * a * s⁻¹
      rw [map_mul, map_mul, map_inv, hθs, hfixA a ha]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    rw [map_mul, hfixA a ha, hfixB b hb]
  have hAP : A ≤ P := le_sup_left
  have hAnorm : ∀ x ∈ P, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx a ha
    obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := hdec x hx
    have h1 : b₀ * a * b₀⁻¹ = a := by rw [← hAB a ha b₀ hb₀]; group
    have : a₀ * b₀ * a * (a₀ * b₀)⁻¹ = a₀ * (b₀ * a * b₀⁻¹) * a₀⁻¹ := by group
    rw [this, h1]
    exact mul_mem (mul_mem ha₀ ha) (inv_mem ha₀)
  have hφpre : ∀ x ∈ P, ∃ x' ∈ P, φ x' = x := by
    intro x hx
    rw [← hφP] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    exact ⟨x', hx', hxx⟩
  have hφmem : ∀ x ∈ P, φ x ∈ P := by
    intro x hx
    rw [← hφP]
    exact ⟨x, hx, rfl⟩
  have hNnorm : ∀ x ∈ P, ∀ a ∈ A, x * φ a * x⁻¹ ∈ A.map φ.toMonoidHom := by
    intro x hx a ha
    obtain ⟨x', hx', rfl⟩ := hφpre x hx
    refine ⟨x' * a * x'⁻¹, hAnorm x' hx' a ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hcardN : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective φ.injective
  have hZ : center A = ⊥ := by
    have := hAsimp
    obtain ⟨x, y, hxy⟩ := hAnab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) with h' | h'
    · exact h'
    · exact absurd (Subgroup.mem_center_iff.1 (h' ▸ mem_top y) x) hxy
  have hcase : (∀ a ∈ A, φ a ∈ A) ∨ (∀ a ∈ A, φ a ∈ B) := by
    have hNA : ((A.map φ.toMonoidHom).subgroupOf A).Normal := by
      constructor
      intro n hn g
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨a, ha, han⟩ := hn
      have h1 := hNnorm g (hAP g.2) a ha
      rw [show φ a = (n : Y) from han] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    have := hAsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.map φ.toMonoidHom).subgroupOf A) with
      h | h
    · right
      intro a ha
      have hφaP : φ a ∈ P := hφmem a (hAP ha)
      obtain ⟨a₀, ha₀, b₀, hb₀, hφa⟩ := hdec _ hφaP
      have hcomm : ∀ a' ∈ A, a' * φ a = φ a * a' := by
        intro a' ha'
        have hc1 : φ a * a' * (φ a)⁻¹ * a'⁻¹ ∈ A :=
          mul_mem (hAnorm _ hφaP a' ha') (inv_mem ha')
        have hc2 : φ a * a' * (φ a)⁻¹ * a'⁻¹ ∈ A.map φ.toMonoidHom := by
          have h1 : a' * (φ a)⁻¹ * a'⁻¹ ∈ A.map φ.toMonoidHom := by
            have := hNnorm a' (hAP ha') a⁻¹ (inv_mem ha)
            rwa [map_inv] at this
          have : φ a * a' * (φ a)⁻¹ * a'⁻¹ = φ a * (a' * (φ a)⁻¹ * a'⁻¹) := by group
          rw [this]
          exact mul_mem ⟨a, ha, rfl⟩ h1
        have hc : (⟨_, hc1⟩ : A) ∈ (A.map φ.toMonoidHom).subgroupOf A := mem_subgroupOf.2 hc2
        rw [h, Subgroup.mem_bot] at hc
        have hc' : φ a * a' * (φ a)⁻¹ * a'⁻¹ = 1 := congrArg Subtype.val hc
        calc a' * φ a = (φ a * a' * (φ a)⁻¹ * a'⁻¹)⁻¹ * (φ a * a') := by group
          _ = φ a * a' := by rw [hc', inv_one, one_mul]
      have ha₀1 : a₀ = 1 := by
        have hz : (⟨a₀, ha₀⟩ : A) ∈ center A := by
          rw [Subgroup.mem_center_iff]
          intro a'
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          have e1 := hcomm a' a'.2
          have e2 := hAB a' a'.2 b₀ hb₀
          rw [hφa] at e1
          calc (a' : Y) * a₀ = a' * (a₀ * b₀) * b₀⁻¹ := by group
            _ = a₀ * b₀ * a' * b₀⁻¹ := by rw [e1]
            _ = a₀ * (b₀ * a') * b₀⁻¹ := by group
            _ = a₀ * (a' * b₀) * b₀⁻¹ := by rw [e2]
            _ = a₀ * a' := by group
        rw [hZ, Subgroup.mem_bot] at hz
        exact congrArg Subtype.val hz
      rw [hφa, ha₀1, one_mul]
      exact hb₀
    · left
      have hle : A ≤ A.map φ.toMonoidHom := by
        intro a ha
        have : (⟨a, ha⟩ : A) ∈ (A.map φ.toMonoidHom).subgroupOf A := h ▸ mem_top _
        exact mem_subgroupOf.1 this
      have heq : A = A.map φ.toMonoidHom := Subgroup.eq_of_le_of_card_ge hle hcardN.le
      intro a ha
      rw [heq]
      exact ⟨a, ha, rfl⟩
  rcases hcase with hA | hA
  · exact .inl (hkey φ hφD hφs hA)
  · right
    set θ : MulAut Y := φ.trans (MulAut.conj s) with hθ
    have hθapp : ∀ x, θ x = s * φ x * s⁻¹ := fun x => rfl
    have hθD : ∀ d ∈ D, θ d = d := by
      intro d hd
      rw [hθapp, hφD d hd, hsD d hd, mul_inv_cancel_right]
    have hθs : θ s = s := by
      rw [hθapp, hφs, mul_inv_cancel_right]
    have hθA : ∀ a ∈ A, θ a ∈ A := fun a ha => by
      rw [hθapp]
      exact hsB _ (hA a ha)
    intro x hx
    have h := hkey θ hθD hθs hθA x hx
    rw [hθapp] at h
    calc φ x = s⁻¹ * (s * φ x * s⁻¹) * s := by group
      _ = s * x * s⁻¹ := by rw [h, hsinv]

theorem commute_of_mem_sup_of_mem_inf {A B O : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAO : A ⊓ O = ⊥) (hBO : B ⊓ O = ⊥)
    (hOA : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) (hOB : ∀ b ∈ B, ∀ o ∈ O, b * o * b⁻¹ ∈ O)
    {x : Y} (hxP : x ∈ A ⊔ B) (hxO : x ∈ O) {y : Y} (hy : y ∈ A ⊔ B) : x * y = y * x := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hx⟩ := exists_mul_of_mem_sup_of_commute hAB hxP
  have hnA : ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro a ha
    have h1 : b₀ * a * b₀⁻¹ = a := by rw [← hAB a ha b₀ hb₀]; group
    have : x * a * x⁻¹ = a₀ * (b₀ * a * b₀⁻¹) * a₀⁻¹ := by rw [hx]; group
    rw [this, h1]
    exact mul_mem (mul_mem ha₀ ha) (inv_mem ha₀)
  have hnB : ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro b hb
    have hb' : b₀ * b * b₀⁻¹ ∈ B := mul_mem (mul_mem hb₀ hb) (inv_mem hb₀)
    have h1 : a₀ * (b₀ * b * b₀⁻¹) * a₀⁻¹ = b₀ * b * b₀⁻¹ := by
      rw [hAB a₀ ha₀ _ hb']; group
    have : x * b * x⁻¹ = a₀ * (b₀ * b * b₀⁻¹) * a₀⁻¹ := by rw [hx]; group
    rw [this, h1]
    exact hb'
  have hcA : ∀ a ∈ A, x * a = a * x := by
    intro a ha
    have hc1 : x * a * x⁻¹ * a⁻¹ ∈ A := mul_mem (hnA a ha) (inv_mem ha)
    have hc2 : x * a * x⁻¹ * a⁻¹ ∈ O := by
      have : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [this]
      exact mul_mem hxO (hOA a ha _ (inv_mem hxO))
    have hc : x * a * x⁻¹ * a⁻¹ ∈ A ⊓ O := Subgroup.mem_inf.2 ⟨hc1, hc2⟩
    rw [hAO, Subgroup.mem_bot] at hc
    calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
      _ = a * x := by rw [hc, one_mul]
  have hcB : ∀ b ∈ B, x * b = b * x := by
    intro b hb
    have hc1 : x * b * x⁻¹ * b⁻¹ ∈ B := mul_mem (hnB b hb) (inv_mem hb)
    have hc2 : x * b * x⁻¹ * b⁻¹ ∈ O := by
      have : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [this]
      exact mul_mem hxO (hOB b hb _ (inv_mem hxO))
    have hc : x * b * x⁻¹ * b⁻¹ ∈ B ⊓ O := Subgroup.mem_inf.2 ⟨hc1, hc2⟩
    rw [hBO, Subgroup.mem_bot] at hc
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [hc, one_mul]
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hy
  calc x * (a * b) = (x * a) * b := by group
    _ = (a * x) * b := by rw [hcA a ha]
    _ = a * (x * b) := by group
    _ = a * (b * x) := by rw [hcB b hb]
    _ = a * b * x := by group

end TypeFree

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem map_subtype_map_conj_eq_map_conj_coe {H : Subgroup G} (A : Subgroup H) (s : H) :
    (A.map (MulAut.conj s).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj (s : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem card_sup_eq_mul_of_commute_of_inf_eq_bot {Y : Type*} [Group Y] [Finite Y]
    {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup Y) = Nat.card A * Nat.card B := by
  set f := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => show Commute (A.subtype a) (B.subtype b) from hc a a.2 b b.2) with hf
  have hrange : f.range = A ⊔ B := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : Y) * b = 1 := hab
    have ha : (a : Y) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.2 ⟨a.2, ?_⟩
      have : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem b.2
    rw [hinf, Subgroup.mem_bot] at ha
    have hb : (b : Y) = 1 := by rw [ha, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem xab_mem_centralizer_of_swap
    (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hswap : LinearTwoSwapKindAt e t a b X₀ htX)
    (hord : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) ^ 2 ∣ Nat.card L) :
    ((e.symm (xab hab 1) : L) : G) ∈
      centralizer (centralizerPerfectCore (modelToG e X₀) : Set G) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set X : Subgroup G := modelToG e X₀ with hXdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  set D : Subgroup G := modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) with hDdef
  have hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype :=
    rfl
  obtain ⟨Kc, hKc, hDKK, hne, hcomm, hZ, hiso⟩ := hswap
  obtain ⟨-, -, hcent, hinf, hsup, hOinf, -, ⟨φK⟩⟩ := neighbourCore_swap_linear_two hset hK e hn
    htC ht hab hX₀ hX₀c hX htX hDe hKc hDKK hne hcomm hiso
  obtain ⟨-, -, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e hn htC hab hX₀ hX₀c hX hDe
  obtain ⟨-, hDX, hDq, -⟩ := neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  set H : Subgroup G := centralizer (X : Set G) with hH
  set A : Subgroup H := oddCoreLift Kc with hA
  set AG : Subgroup G := A.map H.subtype with hAG
  set j : G := ((e.symm (xab hab 1) : L) : G) with hj
  have hEX : centralizerPerfectCore X = AG ⊔ AG.map (MulAut.conj t).toMonoidHom := by
    rw [centralizerPerfectCore_eq_map_perfectCore_top, ← hsup, Subgroup.map_sup,
      map_subtype_map_conj_eq_map_conj_coe]
  have hjL : j ∈ L := (e.symm (xab hab 1)).2
  have hjt : j * t = t * j := (mem_centralizer_iff.1 htC) j hjL
  have hjD : ∀ d ∈ D, j * d = d * j := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := (mem_modelToG e).1 hd
    have hdisj : Disjoint ({a, b} : Finset (Fin n)) ({a, b}ᶜ : Finset (Fin n)) :=
      disjoint_compl_right
    have h := (commute_blockSL_of_disjoint hdisj (xab hab 1) (xab_mem_rootSL2 hab 1) d₀ hd₀).eq
    have h' : e.symm (xab hab 1) * e.symm d₀ = e.symm d₀ * e.symm (xab hab 1) := by
      rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  have htD : ∀ d ∈ D, t * d = d * t := fun d hd =>
    ((mem_centralizer_iff.1 htC) d (modelToG_le e _ hd)).symm
  have hjX : j ∈ normalizer (X : Set G) := map_symm_mem_normalizer e
    (mem_normalizer_of_mem_rootSL2_two hK (by omega) hab hX₀ hX₀c (xab_mem_rootSL2 hab 1))
  have hjH : j ∈ normalizer (H : Set G) := mem_normalizer_centralizer_of_mem_normalizer hjX
  have hjE : j ∈ normalizer (centralizerPerfectCore X : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ hjH

  have hAGt : AG.map (MulAut.conj t).toMonoidHom =
      (A.map (MulAut.conj (⟨t, htX⟩ : H)).toMonoidHom).map H.subtype :=
    (map_subtype_map_conj_eq_map_conj_coe A ⟨t, htX⟩).symm
  have hAs : AG.map (MulAut.conj t).toMonoidHom ≤ centralizer (AG : Set G) := by
    rw [hAGt]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((mem_centralizer_iff.1 (hcent hy)) x hx)
  have hcommG : ∀ x ∈ AG, ∀ y ∈ AG.map (MulAut.conj t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (hAs hy)) x hx
  have hinfG : AG ⊓ AG.map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hAGt, hAG, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hinf, Subgroup.map_bot]
  obtain ⟨ψ⟩ := hiso
  have hKcs : IsSimpleGroup Kc ∧ ∃ x y : Kc, x * y ≠ y * x := by
    obtain ⟨-, hs, x, y, hxy⟩ := hKc.1
    have : IsSimpleGroup (Kc ⧸ center Kc) := hs
    let eK : Kc ⧸ center Kc ≃* Kc := (QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot
    refine ⟨eK.symm.isSimpleGroup, eK x, eK y, fun h => hxy (eK.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have : IsSimpleGroup Kc := hKcs.1
  set eA : AG ≃* Kc := (A.equivMapOfInjective H.subtype H.subtype_injective).symm.trans φK
    with heA
  have hAGs : IsSimpleGroup AG := eA.isSimpleGroup
  have hAGnab : ∃ x y : AG, x * y ≠ y * x := by
    obtain ⟨-, x, y, hxy⟩ := hKcs
    refine ⟨eA.symm x, eA.symm y, fun h => hxy (eA.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hDq.1
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDX hDperf
  have hcardI : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hDc : Nat.card D = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) := by
    rw [hDdef, natCard_modelToG_eq, ← Nat.card_congr (blockSLEquivOfEquiv (K := K)
      (by rw [hcardI]; omega) (Finset.equivFinOfCardEq hcardI)).toEquiv]
  have hAGc : Nat.card AG = Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) := by
    rw [Nat.card_congr ((eA.trans ψ).trans eDb).toEquiv]
  have hcard : Nat.card D = Nat.card AG := by rw [hDc, hAGc]
  have hφP : (AG ⊔ AG.map (MulAut.conj t).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      AG ⊔ AG.map (MulAut.conj t).toMonoidHom := by
    rw [← hEX]
    exact mem_normalizer_iff_map_conj_eq.1 hjE
  have hφD : ∀ d ∈ D, MulAut.conj j d = d := by
    intro d hd
    rw [MulAut.conj_apply, hjD d hd, mul_inv_cancel_right]
  have hφs : MulAut.conj j t = t := by
    rw [MulAut.conj_apply, hjt, mul_inv_cancel_right]
  rcases eq_or_eq_conj_of_fix_of_swap ht2 hAs hinfG hAGs hAGnab (hEX ▸ hDE) htD hcard
      (MulAut.conj j) hφP hφD hφs with h1 | h2
  · rw [mem_centralizer_iff]
    intro y hy
    rw [hEX] at hy
    have h := h1 y hy
    rw [MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · exfalso
    set OG : Subgroup G := (oddCore H).map H.subtype with hOG
    have hOH : ∀ h ∈ H, ∀ o ∈ OG, h * o * h⁻¹ ∈ OG := by
      rintro h hh _ ⟨o, ho, rfl⟩
      exact ⟨⟨h, hh⟩ * o * ⟨h, hh⟩⁻¹,
        (inferInstance : (oddCore H).Normal).conj_mem o ho ⟨h, hh⟩, rfl⟩
    have hAGH : AG ≤ H := map_subtype_le _
    have hAGtH : AG.map (MulAut.conj t).toMonoidHom ≤ H := by
      rw [hAGt]
      exact map_subtype_le _
    have hAO : AG ⊓ OG = ⊥ := by
      rw [hAG, hOG, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hOinf, Subgroup.map_bot]
    have hBO : AG.map (MulAut.conj t).toMonoidHom ⊓ OG = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨y, hy, rfl⟩, hyO⟩
      have hyO' : t⁻¹ * (t * y * t⁻¹) * (t⁻¹)⁻¹ ∈ OG := hOH _ (inv_mem htX) _ hyO
      have hyy : t⁻¹ * (t * y * t⁻¹) * (t⁻¹)⁻¹ = y := by group
      rw [hyy] at hyO'
      have hmem : y ∈ AG ⊓ OG := Subgroup.mem_inf.2 ⟨hy, hyO'⟩
      rw [hAO, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      change t * y * t⁻¹ = 1
      rw [hmem, mul_one, mul_inv_cancel]
    have hB : ∀ x ∈ centralizerPerfectCore X, x ∈ OG → ∀ y ∈ centralizerPerfectCore X,
        x * y = y * x := by
      intro x hx hxO y hy
      rw [hEX] at hx hy
      exact commute_of_mem_sup_of_mem_inf hcommG hAO hBO (fun a ha => hOH a (hAGH ha))
        (fun b hb => hOH b (hAGtH hb)) hx hxO hy
    have hact : ∀ x ∈ centralizerPerfectCore X, j * x * j⁻¹ * (t * x * t⁻¹)⁻¹ ∈ OG := by
      intro x hx
      rw [hEX] at hx
      have h := h2 x hx
      rw [MulAut.conj_apply] at h
      rw [h, mul_inv_cancel]
      exact one_mem _
    obtain ⟨-, -, hdvd⟩ := card_dvd_of_acts_as_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX
      hB hact
    have hAGtc : Nat.card (AG.map (MulAut.conj t).toMonoidHom) = Nat.card AG :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    rw [hEX, card_sup_eq_mul_of_commute_of_inf_eq_bot hcommG hinfG, hAGtc, hAGc, ← sq] at hdvd
    exact hord hdvd

theorem rootSL2_le_centralizer_of_swap
    (hset : SeitzSetting G L)
    {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hswap : LinearTwoSwapKindAt e t a b X₀ htX)
    (hord : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin (n - 2)) K) ^ 2 ∣ Nat.card L) :
    modelToG e (rootSL2 (K := K) a b) ≤
      centralizer (centralizerPerfectCore (modelToG e X₀) : Set G) := by
  have hjC := xab_mem_centralizer_of_swap hset hK e hn htC ht hab hX₀ hX₀c htX hswap hord
  have hXC : modelToG e X₀ ≤ centralizer (centralizerPerfectCore (modelToG e X₀) : Set G) :=
    le_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _)
  rw [modelToG, rootSL2_eq_sup_zpowers_xab_two hK (by omega) hab hX₀ hX₀c, Subgroup.map_sup,
    Subgroup.map_sup]
  refine sup_le hXC ?_
  rw [Subgroup.map_map, MonoidHom.map_zpowers, zpowers_le]
  exact hjC

theorem card_specialLinearGroup_fin_three_eq {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem card_specialLinearGroup_fin_five_eq {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) K) = 9999360 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

omit [Finite G] in
theorem card_eq_of_mulEquiv_projectiveSL_five {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) : Nat.card L = 9999360 := by
  rw [Nat.card_congr e.toEquiv, ← card_specialLinearGroup_fin_five_eq hK]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨proj_injective_of_natCard_eq_two hK,
    LinearFlag.proj_surjective 5 K⟩)).symm

theorem rootSL2_le_centralizer_of_swap_five
    (hset : SeitzSetting G L)
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 5} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hswap : LinearTwoSwapKindAt e t a b X₀ htX) :
    modelToG e (rootSL2 (K := K) a b) ≤
      centralizer (centralizerPerfectCore (modelToG e X₀) : Set G) := by
  refine rootSL2_le_centralizer_of_swap hset hK e le_rfl htC ht hab hX₀ hX₀c htX hswap ?_
  rw [show (5 - 2 : ℕ) = 3 from rfl, card_specialLinearGroup_fin_three_eq hK,
    card_eq_of_mulEquiv_projectiveSL_five hK e]
  decide

theorem le_centralizerPerfectCore_of_inf_centralizer_eq_bot {X W₀ : Subgroup G} {y : G}
    (hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v) (hW₀X : W₀ ≤ centralizer (X : Set G))
    (hyE : y ∈ centralizerPerfectCore X) (hyW₀ : y ∈ normalizer (W₀ : Set G))
    (hW₀y : W₀ ⊓ centralizer ({y} : Set G) = ⊥) : W₀ ≤ centralizerPerfectCore X := by
  intro w hw
  obtain ⟨w', hw', hw'eq⟩ := exists_commutator_eq_of_inf_centralizer_eq_bot hWc hyW₀ hW₀y hw
  rw [← hw'eq]
  have hn : w' ∈ normalizer (centralizerPerfectCore X : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer (hW₀X hw'))
  exact mul_mem ((mem_normalizer_iff.1 hn y).1 hyE) (inv_mem hyE)

end Swap

end CFSG.SeitzReduction.LinearPilot
