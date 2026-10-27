module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Pre
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer
public import CFSG.GH74.GLS.C3.Layer1.Thm1P33d

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

section TV

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem card_sup_le_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  classical
  let φ : ↥A × ↥B → ↥(A ⊔ B) := fun ab =>
    ⟨(ab.1 : G) * (ab.2 : G), Subgroup.mul_mem _ (Subgroup.mem_sup_left ab.1.2)
      (Subgroup.mem_sup_right ab.2.2)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Thm1P310.exists_mul_of_mem_sup h hw
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective φ hsurj
  rwa [Nat.card_prod] at this

theorem Pre35.twoPart_xf_le (E : Pre35 x y K T V W f z) :
    twoPartCard (centralizer ({x * f} : Set G)) ≤ twoPartCard (centralizer ({f} : Set G)) := by
  have hxf1 : x * f ≠ 1 := by
    intro h
    apply E.hxf_ne
    have : x = f⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right E.hf2)
  have hmem : IsFMember x K T (x * f) := by
    refine ⟨T.mul_mem E.cfg.x_mem_T E.cfg.mem.1,
      orderOf_mul_eq_two_of_commute E.cfg.hx2 E.cfg.hf2 E.cfg.hxf hxf1, ?_, ?_, ?_⟩
    · intro p hp
      have h1 : f * p = p * f := E.hfP p hp
      have h2 : p * x = x * p := E.hxcommK p hp.2
      calc x * f * p = x * (f * p) := by group
        _ = x * (p * f) := by rw [h1]
        _ = (x * p) * f := by group
        _ = (p * x) * f := by rw [h2]
        _ = p * (x * f) := by group
    · intro h
      apply E.hf1
      have := mul_left_cancel (a := x) (b := f) (c := 1) (by rw [mul_one]; exact h)
      exact this
    · have hcent : K ⊓ centralizer ({x * f} : Set G) = K ⊓ centralizer ({f} : Set G) := by
        ext k
        constructor
        · rintro ⟨hkK, hk⟩
          refine ⟨hkK, mem_centralizer_singleton_iff.2 ?_⟩
          have h1 := mem_centralizer_singleton_iff.1 hk
          have h2 : k * x = x * k := E.hxcommK k hkK
          have h3 : x * (k * f) = x * (f * k) := by
            calc x * (k * f) = (x * k) * f := by group
              _ = (k * x) * f := by rw [h2]
              _ = k * (x * f) := by group
              _ = (x * f) * k := h1
              _ = x * (f * k) := by group
          exact mul_left_cancel h3
        · rintro ⟨hkK, hk⟩
          refine ⟨hkK, mem_centralizer_singleton_iff.2 ?_⟩
          have h1 := mem_centralizer_singleton_iff.1 hk
          have h2 : k * x = x * k := E.hxcommK k hkK
          calc k * (x * f) = (k * x) * f := by group
            _ = (x * k) * f := by rw [h2]
            _ = x * (k * f) := by group
            _ = x * (f * k) := by rw [h1]
            _ = x * f * k := by group
      rw [hcent]
      exact E.cfg.mem.2.2.2.2
  have hF1 : FMax1 x y K (x * f) := ⟨⟨E.cfg.hu2, T, E.cfg.setup, hmem⟩, E.cfg.fmax.1.1.2⟩
  have hF2 : FMax2 x y K (x * f) := ⟨hF1, E.cfg.fmax.1.2⟩
  exact E.cfg.fmax.2 x y K (x * f) hF2

theorem Pre35.false_of_T_eq_V (E : Pre35 x y K T V W f z) (hVW : V ≠ W) (hTV : T = V) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥W := E.cfg.sylowW.isPGroup
  obtain ⟨b₀, hb₀W, hb₀N, hb₀V⟩ := exists_mem_normalizer_not_mem E.cfg.V_le_W hVW hW2
  have hb₀2 : ∃ k : ℕ, b₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hW2 ⟨b₀, hb₀W⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨b, hb, hbV, hb2⟩ := exists_pow_not_mem_sq_mem hb₀2 hb₀V
  have hbW : b ∈ W := (zpowers_le).2 hb₀W hb
  have hbN : b ∈ normalizer (V : Set G) := (zpowers_le).2 hb₀N hb
  have hbb : b * b ∈ V := by rw [← sq]; exact hb2
  set Z : Subgroup G := zCenter V with hZ
  set X : Subgroup G := zpowers x ⊔ zpowers f with hX
  have hxZ : x ∈ Z := by
    refine ⟨E.cfg.x_mem_V, fun h hh => ?_⟩
    exact mem_centralizer_singleton_iff.1 (E.hTC (hTV ▸ hh))
  have hfZ : f ∈ Z := by
    refine ⟨E.cfg.f_mem_V, fun h hh => ?_⟩
    exact mem_centralizer_singleton_iff.1 (E.cfg.sylowV.le hh)
  have hXZ : X ≤ Z := sup_le ((zpowers_le).2 hxZ) ((zpowers_le).2 hfZ)
  have hZ8 : Nat.card ↥Z ≤ 8 := by
    have hZle : Z ≤ zpowers z ⊔ X := by
      intro c hc
      have hcT : c ∈ T := hTV ▸ hc.1
      exact E.zCenter_le c hcT (fun t ht => (hc.2 t (hTV ▸ ht)).symm)
    have h1 := Subgroup.card_le_of_le hZle
    have h2 : Nat.card ↥(zpowers z ⊔ X) ≤ Nat.card ↥(zpowers z) * Nat.card ↥X := by
      apply card_sup_le_of_commute
      intro a ha e he
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (show Commute z e from (E.hXcomm he z E.cfg.z_mem.1).symm) i).eq
    have hXc : Nat.card ↥X = 4 := E.hkleinCard
    rw [Nat.card_zpowers, E.cfg.z_mem.2.1, hXc] at h2
    omega
  have hτZ : ∀ w ∈ Z, b * w * b⁻¹ ∈ Z := (zCenter_conj hbN).1
  have hτ2 : ∀ w ∈ Z, b * (b * w * b⁻¹) * b⁻¹ = w := by
    intro w hw
    have h1 : (b * b) * w = w * (b * b) := hw.2 _ hbb
    calc b * (b * w * b⁻¹) * b⁻¹ = (b * b) * w * (b * b)⁻¹ := by group
      _ = w := by rw [h1]; group
  set Y : Subgroup G := X.map (MulAut.conj b).toMonoidHom with hY
  have hYZ : Y ≤ Z := by
    rintro _ ⟨e, he, rfl⟩
    exact hτZ e (hXZ he)
  have hZcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := fun u hu v hv => (hu.2 v hv.1).symm
  have hXY : ∃ u ∈ X ⊓ Y, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    let φ : ↥X × ↥Y → ↥Z := fun ey =>
      ⟨(ey.1 : G) * (ey.2 : G), Z.mul_mem (hXZ ey.1.2) (hYZ ey.2.2)⟩
    have hinj : Function.Injective φ := by
      rintro ⟨⟨e, he⟩, ⟨e', he'⟩⟩ ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ h
      have h1 : e * e' = a * a' := congrArg Subtype.val h
      have h2 : a⁻¹ * e = a' * e'⁻¹ := by
        calc a⁻¹ * e = a⁻¹ * (e * e') * e'⁻¹ := by group
          _ = a⁻¹ * (a * a') * e'⁻¹ := by rw [h1]
          _ = a' * e'⁻¹ := by group
      have h3 : a⁻¹ * e ∈ X ⊓ Y := ⟨X.mul_mem (X.inv_mem ha) he, h2 ▸ Y.mul_mem ha' (Y.inv_mem he')⟩
      have h4 := hcon _ h3
      have hae : e = a := by
        have := congrArg (fun w : G => a * w) h4
        simpa using this
      subst hae
      have h5 : e' = a' := mul_left_cancel h1
      subst h5
      rfl
    have h16 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_prod] at h16
    have hYcard : Nat.card ↥Y = 4 := by
      rw [hY, Subgroup.card_map_of_injective (MulAut.conj b).injective, hX, E.hkleinCard]
    rw [hYcard, hX, E.hkleinCard] at h16
    omega
  have hXsq : ∀ u ∈ X, u * u = 1 := by
    intro u hu
    rcases klein_cases E.hx2 E.hf2 E.cfg.hxf hu with h | h | h | h <;> rw [h]
    · simp
    · exact E.hx2
    · exact E.hf2
    · calc x * f * (x * f) = x * (f * x) * f := by group
        _ = x * (x * f) * f := by rw [E.cfg.hxf]
        _ = (x * x) * (f * f) := by group
        _ = 1 := by rw [E.hx2, E.hf2, one_mul]
  have hfix : ∃ u₀ ∈ X, u₀ ≠ 1 ∧ b * u₀ * b⁻¹ = u₀ := by
    obtain ⟨u, ⟨huX, huY⟩, hu1⟩ := hXY
    obtain ⟨u₁, hu₁X, hu₁⟩ := huY
    have hu₁' : b * u₁ * b⁻¹ = u := by simpa [MulAut.conj_apply] using hu₁
    have hτu : b * u * b⁻¹ = u₁ := by
      rw [← hu₁']
      exact hτ2 u₁ (hXZ hu₁X)
    by_cases hf : b * u * b⁻¹ = u
    · exact ⟨u, huX, hu1, hf⟩
    · refine ⟨u * u₁, X.mul_mem huX hu₁X, ?_, ?_⟩
      · intro h
        apply hf
        rw [hτu]
        have h2 : u₁ = u⁻¹ := by
          have := congrArg (fun w : G => u⁻¹ * w) h
          simpa using this
        rw [h2]
        exact inv_eq_of_mul_eq_one_right (hXsq u huX)
      · have : b * (u * u₁) * b⁻¹ = (b * u * b⁻¹) * (b * u₁ * b⁻¹) := by group
        rw [this, hτu, hu₁']
        exact hZcomm _ (hXZ hu₁X) _ (hXZ huX)
  obtain ⟨u₀, hu₀X, hu₀1, hbu₀⟩ := hfix
  set N₂ : Subgroup G := V ⊔ zpowers b with hN₂
  have hN₂W : N₂ ≤ W := sup_le E.cfg.V_le_W ((zpowers_le).2 hbW)
  have hN₂2 : IsPGroup 2 ↥N₂ := hW2.to_le hN₂W
  have hVN₂ : V ≤ N₂ := le_sup_left
  have hbN₂ : b ∈ N₂ := Subgroup.mem_sup_right (mem_zpowers b)
  have hN₂C : N₂ ≤ centralizer ({u₀} : Set G) := by
    refine sup_le (fun v hv => ?_) ((zpowers_le).2 ?_)
    · exact mem_centralizer_singleton_iff.2 ((hXZ hu₀X).2 v hv)
    · rw [mem_centralizer_singleton_iff]
      calc b * u₀ = (b * u₀ * b⁻¹) * b := by group
        _ = u₀ * b := by rw [hbu₀]
  have hne : N₂ ≠ V := fun h => hbV (h ▸ hbN₂)
  rcases klein_cases E.hx2 E.hf2 E.cfg.hxf hu₀X with h | h | h | h
  · exact hu₀1 h
  ·
    subst h
    have hTN : T ≤ N₂ := hTV ▸ hVN₂
    exact hne ((E.cfg.setup.sylowT.eq_of_le hTN hN₂C hN₂2).trans hTV)
  ·
    subst h
    exact hne (E.cfg.sylowV.eq_of_le hVN₂ hN₂C hN₂2)
  ·
    subst h
    obtain ⟨S, hS, hN₂S⟩ := EvenSporTransfer.exists_isSylowOf_ge hN₂C hN₂2
    have h1 : Nat.card ↥N₂ ≤ Nat.card ↥S := Subgroup.card_le_of_le hN₂S
    have h2 : Nat.card ↥S = twoPartCard (centralizer ({x * f} : Set G)) := hS.card_eq
    have h3 : Nat.card ↥V = twoPartCard (centralizer ({f} : Set G)) := E.cfg.sylowV.card_eq
    have h4 := E.twoPart_xf_le
    have h5 : Nat.card ↥V < Nat.card ↥N₂ :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hVN₂) (fun heq =>
        hne (Subgroup.eq_of_le_of_card_ge hVN₂ heq.symm.le).symm)
    omega

end TV

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end
