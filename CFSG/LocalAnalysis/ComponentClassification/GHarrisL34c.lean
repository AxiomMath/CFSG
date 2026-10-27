module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34b
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31c

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem z_comm_of_mem_M {g : G} (hg : g ∈ D.M) : g⁻¹ * D.z * g = D.z := by
  have := mem_centralizer_singleton_iff.mp hg
  calc g⁻¹ * D.z * g = g⁻¹ * (D.z * g) := by group
    _ = g⁻¹ * (g * D.z) := by rw [this]
    _ = D.z := by group

omit [Finite G] in
theorem mem_normalizer_pair {x w : G} (hx : x ∈ D.M)
    (h1 : x * w * x⁻¹ = w ∨ x * w * x⁻¹ = w * D.z)
    (h2 : x⁻¹ * w * x = w ∨ x⁻¹ * w * x = w * D.z) :
    x ∈ normalizer ({w, w * D.z} : Set G) := by
  have hzx : x * D.z * x⁻¹ = D.z := by
    have := D.z_comm_of_mem_M (inv_mem hx)
    rwa [inv_inv] at this
  have hzx' : x⁻¹ * D.z * x = D.z := D.z_comm_of_mem_M hx
  have hzz : D.z * D.z = 1 := D.z_mul_z
  refine mem_normalizer_of_conj ?_ ?_
  · intro y hy
    rcases hy with hy | hy <;> rw [hy]
    · rcases h1 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [show x * (w * D.z) * x⁻¹ = (x * w * x⁻¹) * (x * D.z * x⁻¹) by group, hzx]
      rcases h1 with h | h <;> rw [h]
      · exact Or.inr rfl
      · left; rw [mul_assoc, hzz, mul_one]
  · intro y hy
    rcases hy with hy | hy <;> rw [hy]
    · rcases h2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rw [show x⁻¹ * (w * D.z) * x = (x⁻¹ * w * x) * (x⁻¹ * D.z * x) by group, hzx']
      rcases h2 with h | h <;> rw [h]
      · exact Or.inr rfl
      · left; rw [mul_assoc, hzz, mul_one]

theorem exists_normalizer_of_weaklyClosed {H : Subgroup G} (hHS : H ≤ (D.S : Subgroup G))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ = b ∨ a * b * a⁻¹ = b * D.z)
    (hwc : ∀ k ∈ D.M, (∀ e ∈ H, k⁻¹ * e * k ∈ (D.S : Subgroup G)) → ∀ e ∈ H, k⁻¹ * e * k ∈ H)
    (hmz : ∀ w ∈ H, w ≠ 1 → w ≠ D.z → ∃ s ∈ (D.S : Subgroup G), s⁻¹ * (w * D.z) * s = w)
    (hSH : ∀ s ∈ (D.S : Subgroup G), ∀ e ∈ H, s⁻¹ * e * s ∈ H)
    {u g : G} (hu : u ∈ H) (hg : g ∈ D.M) (hug : g⁻¹ * u * g ∈ H) :
    ∃ h ∈ D.M, (∀ e ∈ H, h⁻¹ * e * h ∈ H) ∧ h⁻¹ * u * h = g⁻¹ * u * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := g⁻¹ * u * g with hw
  set T : Set G := {w, w * D.z} with hT
  set K := D.M ⊓ normalizer T with hK
  have hHM : H ≤ D.M := hHS.trans D.S_le_M
  have hHK : H ≤ K := fun x hx => mem_inf.mpr ⟨hHM hx, D.mem_normalizer_pair (hHM hx)
    (hcomm x hx w hug) (hcomm x⁻¹ (inv_mem hx) w hug |>.imp (by rw [inv_inv]; exact id)
      (by rw [inv_inv]; exact id))⟩
  set Hg := H.map (MulAut.conj g⁻¹).toMonoidHom with hHg
  have hHgK : Hg ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    change g⁻¹ * x * g⁻¹⁻¹ ∈ K
    rw [inv_inv]
    have hgz := D.z_comm_of_mem_M hg
    have key : ∀ y ∈ H, (g⁻¹ * y * g) * w * (g⁻¹ * y * g)⁻¹ = w ∨
        (g⁻¹ * y * g) * w * (g⁻¹ * y * g)⁻¹ = w * D.z := by
      intro y hy
      rw [hw, show g⁻¹ * y * g * (g⁻¹ * u * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * u * y⁻¹) * g by
        group]
      rcases hcomm y hy u hu with h | h <;> rw [h]
      · exact Or.inl rfl
      · right
        rw [show g⁻¹ * (u * D.z) * g = g⁻¹ * u * g * (g⁻¹ * D.z * g) by group, hgz]
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) (hHM hx)) hg,
      D.mem_normalizer_pair (mul_mem (mul_mem (inv_mem hg) (hHM hx)) hg) (key x hx) ?_⟩
    rw [show (g⁻¹ * x * g)⁻¹ = g⁻¹ * x⁻¹ * g by group]
    have := key x⁻¹ (inv_mem hx)
    rwa [show (g⁻¹ * x⁻¹ * g)⁻¹ = g⁻¹ * x * g by group] at this
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 K
  have hH2 : IsPGroup 2 H := D.S.isPGroup'.to_le hHS
  obtain ⟨c₁, hc₁K, hc₁⟩ := exists_conj_le_of_isSylowOf hP hHK hH2
  obtain ⟨c₂, hc₂K, hc₂⟩ := exists_conj_le_of_isSylowOf hP hHgK (hH2.map _)
  have hSM : IsSylowOf 2 (D.S : Subgroup G) D.M := (isSylowOf_top D.S).of_le D.S_le_M le_top
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isSylowOf hSM (hP.le.trans inf_le_left) hP.isPGroup
  obtain ⟨hc₁M, hc₁T⟩ := mem_inf.mp hc₁K
  obtain ⟨hc₂M, hc₂T⟩ := mem_inf.mp hc₂K
  have h1 : ∀ e ∈ H, (m * c₁) * e * (m * c₁)⁻¹ ∈ H := by
    have := hwc (m * c₁)⁻¹ (inv_mem (mul_mem hmM hc₁M)) fun e he => by
      rw [inv_inv, show m * c₁ * e * (m * c₁)⁻¹ = m * (c₁ * e * c₁⁻¹) * m⁻¹ by group]
      exact hm _ (hc₁ e he)
    intro e he
    simpa only [inv_inv] using this e he
  have h2 : ∀ e ∈ H, (m * c₂ * g⁻¹) * e * (m * c₂ * g⁻¹)⁻¹ ∈ H := by
    have := hwc (m * c₂ * g⁻¹)⁻¹ (inv_mem (mul_mem (mul_mem hmM hc₂M) (inv_mem hg)))
      fun e he => by
        rw [inv_inv, show m * c₂ * g⁻¹ * e * (m * c₂ * g⁻¹)⁻¹ =
          m * (c₂ * (g⁻¹ * e * g⁻¹⁻¹) * c₂⁻¹) * m⁻¹ by group]
        exact hm _ (hc₂ _ ⟨e, he, rfl⟩)
    intro e he
    simpa only [inv_inv] using this e he
  set h₀ := g * c₂⁻¹ * c₁ with hh₀
  have hh₀M : h₀ ∈ D.M := mul_mem (mul_mem hg (inv_mem hc₂M)) hc₁M
  have hh₀H : ∀ e ∈ H, h₀⁻¹ * e * h₀ ∈ H := by
    intro e he
    have hinv : ∀ y ∈ H, (m * c₁)⁻¹ * y * (m * c₁) ∈ H := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := exists_conj_eq_of_maps (H := H) (k := (m * c₁)⁻¹)
        (fun x hx => by simpa only [inv_inv] using h1 x hx) y hy
      rw [← hxy, show (m * c₁)⁻¹ * ((m * c₁)⁻¹⁻¹ * x * (m * c₁)⁻¹) * (m * c₁) = x by group]
      exact hx
    have := hinv _ (h2 e he)
    rwa [show (m * c₁)⁻¹ * (m * c₂ * g⁻¹ * e * (m * c₂ * g⁻¹)⁻¹) * (m * c₁) =
      h₀⁻¹ * e * h₀ by rw [hh₀]; group] at this
  have hu₀ : h₀⁻¹ * u * h₀ ∈ T := by
    have hw2 : c₂ * w * c₂⁻¹ ∈ T := by
      have := conj_mem_of_mem_normalizer (inv_mem hc₂T) (show w ∈ T from Or.inl rfl)
      rwa [inv_inv] at this
    have := conj_mem_of_mem_normalizer hc₁T hw2
    rwa [show c₁⁻¹ * (c₂ * w * c₂⁻¹) * c₁ = h₀⁻¹ * u * h₀ by rw [hh₀, hw]; group] at this
  rcases hu₀ with h' | h'
  · exact ⟨h₀, hh₀M, hh₀H, h'⟩
  ·
    have hw1 : w ≠ 1 := by
      intro hw1
      have : h₀⁻¹ * u * h₀ = D.z := by rw [h', hw1, one_mul]
      apply D.z_ne_one
      have hu1 : u = 1 := by
        have h3 : u = g * w * g⁻¹ := by rw [hw]; group
        rw [h3, hw1]; group
      rw [← this, hu1]; group
    have hwz : w ≠ D.z := by
      intro hwz
      have hu : u = D.z := by
        have h3 : u = g * w * g⁻¹ := by rw [hw]; group
        rw [h3, hwz]
        have := D.z_comm_of_mem_M (inv_mem hg)
        rwa [inv_inv] at this
      have : h₀⁻¹ * u * h₀ = D.z := by rw [hu]; exact D.z_comm_of_mem_M hh₀M
      rw [this, hwz] at h'
      apply D.z_ne_one
      have := congrArg (fun y => D.z⁻¹ * y) h'
      simpa using this.symm
    obtain ⟨s, hs, hsw⟩ := hmz w hug hw1 hwz
    refine ⟨h₀ * s, mul_mem hh₀M (D.S_le_M hs), fun e he => ?_, ?_⟩
    · rw [show (h₀ * s)⁻¹ * e * (h₀ * s) = s⁻¹ * (h₀⁻¹ * e * h₀) * s by group]
      exact hSH s hs _ (hh₀H e he)
    · rw [show (h₀ * s)⁻¹ * u * (h₀ * s) = s⁻¹ * (h₀⁻¹ * u * h₀) * s by group, h', hsw]

omit [Finite G] in
theorem conj_comm_E : ∀ a ∈ D.E, ∀ b ∈ D.E,
    a * b * a⁻¹ = b ∨ a * b * a⁻¹ = b * D.z := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rcases SE.commZ_E b a⁻¹ hb (SE.Esub.inv_mem ha) with h | h <;> unfold SE.comm at h
  · left
    rw [← map_inv, ← map_mul, ← map_mul,
      show a * b * a⁻¹ = b * (b⁻¹ * a⁻¹⁻¹ * b * a⁻¹) by group, h, mul_one]
  · right
    rw [← map_inv, ← map_mul, ← map_mul,
      show a * b * a⁻¹ = b * (b⁻¹ * a⁻¹⁻¹ * b * a⁻¹) by group, h, map_mul]

omit [Finite G] in
theorem conj_comm_F : ∀ a ∈ D.F, ∀ b ∈ D.F,
    a * b * a⁻¹ = b ∨ a * b * a⁻¹ = b * D.z := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rcases SE.commZ_F b a⁻¹ hb (SE.Fsub.inv_mem ha) with h | h <;> unfold SE.comm at h
  · left
    rw [← map_inv, ← map_mul, ← map_mul,
      show a * b * a⁻¹ = b * (b⁻¹ * a⁻¹⁻¹ * b * a⁻¹) by group, h, mul_one]
  · right
    rw [← map_inv, ← map_mul, ← map_mul,
      show a * b * a⁻¹ = b * (b⁻¹ * a⁻¹⁻¹ * b * a⁻¹) by group, h, map_mul]

omit [Finite G] in
theorem exists_S_conj_mul_z_E {w : G} (hw : w ∈ D.E) (hw1 : w ≠ 1) (hwz : w ≠ D.z) :
    ∃ s ∈ (D.S : Subgroup G), s⁻¹ * (w * D.z) * s = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨i, hi⟩ := SE.exists_gen_conj_mul_z_E w₀ hw₀ (fun h => hw1 (by rw [h, map_one]))
    (fun h => hwz (by rw [h]))
  exact ⟨D.toG (SE.gen i), D.toG_mem _, by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hi]⟩

omit [Finite G] in
theorem exists_S_conj_mul_z_F {w : G} (hw : w ∈ D.F) (hw1 : w ≠ 1) (hwz : w ≠ D.z) :
    ∃ s ∈ (D.S : Subgroup G), s⁻¹ * (w * D.z) * s = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨i, hi⟩ := SE.exists_gen_conj_mul_z_F w₀ hw₀ (fun h => hw1 (by rw [h, map_one]))
    (fun h => hwz (by rw [h]))
  exact ⟨D.toG (SE.gen i), D.toG_mem _, by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hi]⟩

theorem exists_normalizer_E {u g : G} (hu : u ∈ D.E)
    (hg : g ∈ D.M) (hug : g⁻¹ * u * g ∈ D.E) :
    ∃ h ∈ D.M, (∀ e ∈ D.E, h⁻¹ * e * h ∈ D.E) ∧ h⁻¹ * u * h = g⁻¹ * u * g :=
  D.exists_normalizer_of_weaklyClosed D.E_le_S D.conj_comm_E
    (fun _ hk hS => D.conj_E_mem_E hk hS) (fun _ hw hw1 hwz => D.exists_S_conj_mul_z_E hw hw1 hwz)
    (fun _ hs _ he => D.conj_mem_E hs he) hu hg hug

theorem exists_normalizer_F {u g : G} (hu : u ∈ D.F)
    (hg : g ∈ D.M) (hug : g⁻¹ * u * g ∈ D.F) :
    ∃ h ∈ D.M, (∀ f ∈ D.F, h⁻¹ * f * h ∈ D.F) ∧ h⁻¹ * u * h = g⁻¹ * u * g :=
  D.exists_normalizer_of_weaklyClosed D.F_le_S D.conj_comm_F
    (fun _ hk hS => D.conj_F_mem_F hk hS) (fun _ hw hw1 hwz => D.exists_S_conj_mul_z_F hw hw1 hwz)
    (fun _ hs _ hf => D.conj_mem_F hs hf) hu hg hug

end GHSylow

end CFSG.ComponentClassification.GHarris
