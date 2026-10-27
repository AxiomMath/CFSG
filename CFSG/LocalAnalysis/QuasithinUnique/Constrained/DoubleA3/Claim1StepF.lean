module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsMaxModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

section Induced

variable {G : Type} [Group G] {A : Subgroup G} {φ : ↥A ≃* ↥A6Models.psl29}

@[expose] def InducesModel (A : Subgroup G) (φ : ↥A ≃* ↥A6Models.psl29) (g : G) (b : P10) : Prop :=
  ∀ k k' : ↥A, (k' : G) = g⁻¹ * (k : G) * g →
    ((φ k' : ↥A6Models.psl29) : P10) = b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹

theorem InducesModel.one : InducesModel A φ 1 1 := by
  intro k k' h
  have hk : k' = k := Subtype.ext (by simpa using h)
  rw [hk]
  simp

theorem InducesModel.of_mem (a : ↥A) :
    InducesModel A φ (a : G) (((φ a : ↥A6Models.psl29) : P10))⁻¹ := by
  intro k k' hk'
  have hk : k' = a⁻¹ * k * a := Subtype.ext (by simpa using hk')
  rw [hk]
  simp

theorem InducesModel.mul {g h : G} {b c : P10} (hg : g ∈ normalizer (A : Set G))
    (h₁ : InducesModel A φ g b) (h₂ : InducesModel A φ h c) :
    InducesModel A φ (g * h) (c * b) := by
  intro k k' hk'
  have hk₁ : g⁻¹ * (k : G) * g ∈ A := by
    have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hg) (k : G)).mp k.2
    simpa using this
  have e1 : ((φ ⟨g⁻¹ * (k : G) * g, hk₁⟩ : ↥A6Models.psl29) : P10) =
      b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹ := h₁ k ⟨g⁻¹ * (k : G) * g, hk₁⟩ rfl
  have e2 : ((φ k' : ↥A6Models.psl29) : P10) =
      c * ((φ ⟨g⁻¹ * (k : G) * g, hk₁⟩ : ↥A6Models.psl29) : P10) * c⁻¹ :=
    h₂ ⟨g⁻¹ * (k : G) * g, hk₁⟩ k' (by
      show (k' : G) = h⁻¹ * (g⁻¹ * (k : G) * g) * h
      rw [hk']
      group)
  rw [e2, e1]
  group

theorem InducesModel.inv {g : G} {b : P10} (h : InducesModel A φ g b) :
    InducesModel A φ g⁻¹ b⁻¹ := by
  intro k k' hk'
  have hk : (k : G) = g⁻¹ * (k' : G) * g := by rw [hk']; group
  have h1 := h k' k hk
  rw [h1]
  group

theorem InducesModel.centralizes {g : G} (hg : g ∈ normalizer (A : Set G))
    (h : InducesModel A φ g 1) : ∀ a ∈ A, a * g = g * a := by
  intro a ha
  have hk' : g⁻¹ * a * g ∈ A := by
    have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hg) a).mp ha
    simpa using this
  have h1 := h ⟨a, ha⟩ ⟨g⁻¹ * a * g, hk'⟩ rfl
  simp only [one_mul, inv_one, mul_one] at h1
  have h2 : (⟨g⁻¹ * a * g, hk'⟩ : ↥A) = ⟨a, ha⟩ := φ.injective (Subtype.ext h1)
  have h3 : g⁻¹ * a * g = a := congrArg Subtype.val h2
  calc a * g = g * (g⁻¹ * a * g) := by group
    _ = g * a := by rw [h3]

theorem InducesModel.exists_ind {g : G} (hg : g ∈ normalizer (A : Set G)) :
    ∃ b ∈ A6Models.autA6, InducesModel A φ g b := by
  obtain ⟨α, hα⟩ := exists_conjAut hg
  obtain ⟨b, hb, hφ⟩ := exists_aut_model φ α
  refine ⟨b, hb, fun k k' hk' => ?_⟩
  have hk : k' = α k := Subtype.ext (hk'.trans (hα k).symm)
  rw [hk]
  exact hφ k

theorem InducesModel.unique {g : G} {b c : P10} (hb : b ∈ A6Models.autA6)
    (hc : c ∈ A6Models.autA6) (hg : g ∈ normalizer (A : Set G)) (h₁ : InducesModel A φ g b)
    (h₂ : InducesModel A φ g c) : b = c := by
  have hw : c⁻¹ * b ∈ A6Models.autA6 := A6Models.autA6.mul_mem (A6Models.autA6.inv_mem hc) hb
  have hw1 : c⁻¹ * b = 1 := by
    refine centralizer_psl29 hw fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have hk' : g⁻¹ * (k : G) * g ∈ A := by
      have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hg) (k : G)).mp k.2
      simpa using this
    have e1 := h₁ k ⟨g⁻¹ * (k : G) * g, hk'⟩ rfl
    have e2 := h₂ k ⟨g⁻¹ * (k : G) * g, hk'⟩ rfl
    rw [hk] at e1 e2
    have e3 : b * x * b⁻¹ = c * x * c⁻¹ := e1.symm.trans e2
    calc c⁻¹ * b * x = c⁻¹ * (b * x * b⁻¹) * b := by group
      _ = c⁻¹ * (c * x * c⁻¹) * b := by rw [e3]
      _ = x * (c⁻¹ * b) := by group
  calc b = c * (c⁻¹ * b) := by group
    _ = c := by rw [hw1, mul_one]

@[expose] def indSub (A : Subgroup G) (φ : ↥A ≃* ↥A6Models.psl29) (Y : Subgroup G)
    (hY : Y ≤ normalizer (A : Set G)) : Subgroup P10 where
  carrier := {b | b ∈ A6Models.autA6 ∧ ∃ g ∈ Y, InducesModel A φ g b}
  mul_mem' := by
    intro b₁ b₂ hb₁ hb₂
    obtain ⟨hb₁, g₁, hg₁, h₁⟩ := hb₁
    obtain ⟨hb₂, g₂, hg₂, h₂⟩ := hb₂
    exact ⟨A6Models.autA6.mul_mem hb₁ hb₂, g₂ * g₁, Y.mul_mem hg₂ hg₁,
      InducesModel.mul (hY hg₂) h₂ h₁⟩
  one_mem' := ⟨A6Models.autA6.one_mem, 1, Y.one_mem, InducesModel.one⟩
  inv_mem' := by
    intro b hb
    obtain ⟨hb, g, hg, h⟩ := hb
    exact ⟨A6Models.autA6.inv_mem hb, g⁻¹, Y.inv_mem hg, InducesModel.inv h⟩

end Induced

theorem exists_psl29_not_mem_P0 : ∃ k ∈ A6Models.psl29, k ∉ P0 := by
  by_contra hcon
  push Not at hcon
  have hle : A6Models.psl29 ≤ P0 := fun k hk => hcon k hk
  have h := Subgroup.card_le_of_le hle
  rw [card_psl29, card_P0] at h
  omega

section StepF

variable {G : Type} [Group G]

theorem stepF_core {A X W : Subgroup G} (φ : ↥A ≃* ↥A6Models.psl29)
    (hAX : A ≤ X) (hXN : X ≤ normalizer (A : Set G))
    (hsurj : ∀ b ∈ A6Models.autA6, ∃ g ∈ X, InducesModel A φ g b)
    {z r : G} (hzA : z ∈ A) (hzb : ((φ ⟨z, hzA⟩ : ↥A6Models.psl29) : P10) = zb)
    (hrX : r ∈ X) (hr2 : r * r = 1) (hrz : r * z = z * r)
    (hrz1 : ∃ a ∈ A, a * (r * z) ≠ (r * z) * a)
    (hzW : ∀ g ∈ X, g * z = z * g → g ∈ W) (hrW : ∀ g ∈ X, g * r = r * g → g ∈ W) :
    A ≤ W := by
  have hz2 : z * z = 1 := by
    have h : (⟨z, hzA⟩ : ↥A) * ⟨z, hzA⟩ = 1 := by
      apply φ.injective
      apply Subtype.ext
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one]
      rw [hzb]
      exact zb_sq
    exact congrArg Subtype.val h
  have hzN : z ∈ normalizer (A : Set G) := Subgroup.le_normalizer hzA
  have hrN : r ∈ normalizer (A : Set G) := hXN hrX
  obtain ⟨br, hbrA, hbr⟩ := InducesModel.exists_ind (φ := φ) hrN
  have hzconj : (z : G) = r⁻¹ * z * r := by
    calc z = r⁻¹ * (r * z) := by group
      _ = r⁻¹ * (z * r) := by rw [hrz]
      _ = r⁻¹ * z * r := by group
  have hbr_comm : br * zb = zb * br := by
    have h := hbr ⟨z, hzA⟩ ⟨z, hzA⟩ hzconj
    rw [hzb] at h
    calc br * zb = (br * zb * br⁻¹) * br := by group
      _ = zb * br := by rw [← h]
  have hbrP : br ∈ P0 :=
    centralizer_le_P0_of_central zb_mem_P0 zb_ne_one zb_central hbrA hbr_comm
  have hbr2 : br * br = 1 := by
    have hmul : InducesModel A φ (r * r) (br * br) := InducesModel.mul hrN hbr hbr
    rw [hr2] at hmul
    exact InducesModel.unique (A6Models.autA6.mul_mem hbrA hbrA) A6Models.autA6.one_mem
      (Subgroup.one_mem _) hmul InducesModel.one
  have hbzb : br ≠ zb := by
    intro hbz
    obtain ⟨a, haA, hane⟩ := hrz1
    apply hane
    have hz_ind : InducesModel A φ z (zb)⁻¹ := by
      have h := InducesModel.of_mem (φ := φ) ⟨z, hzA⟩
      rw [hzb] at h
      exact h
    have hzbinv : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right zb_sq
    rw [hzbinv] at hz_ind
    have hrzind : InducesModel A φ (r * z) (zb * br) := InducesModel.mul hrN hbr hz_ind
    rw [hbz, zb_sq] at hrzind
    exact InducesModel.centralizes (Subgroup.mul_mem _ hrN hzN) hrzind a haA
  have hex : ∃ k ∈ A6Models.psl29, k * br = br * k ∧ k ∉ P0 := by
    by_cases hb1 : br = 1
    · obtain ⟨k, hk, hkP⟩ := exists_psl29_not_mem_P0
      exact ⟨k, hk, by rw [hb1]; simp, hkP⟩
    · exact invol_cent_not_P0 hbrP hb1 hbzb hbr2
  obtain ⟨k, hk, hkbr, hkP⟩ := hex
  have hXW : X ⊓ W ≤ normalizer (A : Set G) := inf_le_left.trans hXN
  have hP0 : ∀ p ∈ P0, p ∈ indSub A φ (X ⊓ W) hXW := by
    intro p hp
    have hpA : p ∈ A6Models.autA6 := P0_le_autA6 hp
    obtain ⟨g, hgX, hg⟩ := hsurj p hpA
    have hgN : g ∈ normalizer (A : Set G) := hXN hgX
    have hz' : g⁻¹ * z * g ∈ A := by
      have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hgN) z).mp hzA
      simpa using this
    have h1 := hg ⟨z, hzA⟩ ⟨g⁻¹ * z * g, hz'⟩ rfl
    rw [hzb] at h1
    have h2 : p * zb * p⁻¹ = zb := by
      calc p * zb * p⁻¹ = (zb * p) * p⁻¹ := by rw [← zb_central p hp]
        _ = zb := by group
    rw [h2] at h1
    have h3 : (⟨g⁻¹ * z * g, hz'⟩ : ↥A) = ⟨z, hzA⟩ :=
      φ.injective (Subtype.ext (h1.trans hzb.symm))
    have h4 : g⁻¹ * z * g = z := congrArg Subtype.val h3
    have hgz : g * z = z * g := by
      calc g * z = g * (g⁻¹ * z * g) := by rw [h4]
        _ = z * g := by group
    exact ⟨hpA, g, ⟨hgX, hzW g hgX hgz⟩, hg⟩
  have hkW : k ∈ indSub A φ (X ⊓ W) hXW := by
    set a₀ : ↥A := φ.symm ⟨k, hk⟩ with ha₀
    have hφa₀ : ((φ a₀ : ↥A6Models.psl29) : P10) = k := by simp [ha₀]
    have hr' : r⁻¹ * (a₀ : G) * r ∈ A := by
      have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hrN) (a₀ : G)).mp a₀.2
      simpa using this
    have h1 := hbr a₀ ⟨r⁻¹ * (a₀ : G) * r, hr'⟩ rfl
    rw [hφa₀] at h1
    have h2 : br * k * br⁻¹ = k := by
      calc br * k * br⁻¹ = (k * br) * br⁻¹ := by rw [← hkbr]
        _ = k := by group
    rw [h2] at h1
    have h3 : (⟨r⁻¹ * (a₀ : G) * r, hr'⟩ : ↥A) = a₀ :=
      φ.injective (Subtype.ext (h1.trans hφa₀.symm))
    have h4 : r⁻¹ * (a₀ : G) * r = a₀ := congrArg Subtype.val h3
    have hra : (a₀ : G) * r = r * (a₀ : G) := by
      calc (a₀ : G) * r = r * (r⁻¹ * (a₀ : G) * r) := by group
        _ = r * (a₀ : G) := by rw [h4]
    have ha₀X : (a₀ : G) ∈ X := hAX a₀.2
    have ha₀W : (a₀ : G) ∈ W := hrW _ ha₀X hra
    have hind := InducesModel.of_mem (φ := φ) a₀
    rw [hφa₀] at hind
    have hkinv : k⁻¹ ∈ indSub A φ (X ⊓ W) hXW :=
      ⟨A6Models.autA6.inv_mem (psl29_le_autA6 hk), (a₀ : G), ⟨ha₀X, ha₀W⟩, hind⟩
    have := (indSub A φ (X ⊓ W) hXW).inv_mem hkinv
    rwa [inv_inv] at this
  have hPsl : A6Models.psl29 ≤ indSub A φ (X ⊓ W) hXW := P0_overgroup hP0 hk hkP hkW
  intro a ha
  have hy : ((φ ⟨a, ha⟩ : ↥A6Models.psl29) : P10) ∈ indSub A φ (X ⊓ W) hXW :=
    hPsl (φ ⟨a, ha⟩).2
  obtain ⟨-, g, ⟨hgX, hgW⟩, hg⟩ := hy
  have hgN : g ∈ normalizer (A : Set G) := hXN hgX
  have haN : a ∈ normalizer (A : Set G) := Subgroup.le_normalizer ha
  have hAind := InducesModel.of_mem (φ := φ) ⟨a, ha⟩
  have hmul : InducesModel A φ (g * a) ((((φ ⟨a, ha⟩ : ↥A6Models.psl29) : P10))⁻¹ *
      ((φ ⟨a, ha⟩ : ↥A6Models.psl29) : P10)) := InducesModel.mul hgN hg hAind
  rw [inv_mul_cancel] at hmul
  have hcent := InducesModel.centralizes (Subgroup.mul_mem _ hgN haN) hmul
  have hgaX : g * a ∈ X := X.mul_mem hgX (hAX ha)
  have hgaW : g * a ∈ W := hzW (g * a) hgaX (hcent z hzA).symm
  have hae : a = g⁻¹ * (g * a) := by group
  rw [hae]
  exact W.mul_mem (W.inv_mem hgW) hgaW

end StepF

end CFSG.QuasithinUnique.DoubleA3
