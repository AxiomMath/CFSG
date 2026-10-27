module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

namespace Nine

@[expose] def tau (z c : G) : G := z * c * z⁻¹ * c⁻¹

theorem tau_mul (z c d : G) : tau z (c * d) = tau z c * (c * tau z d * c⁻¹) := by
  simp only [tau]
  group

theorem tau_inv (z c : G) : tau z c⁻¹ = c⁻¹ * (tau z c)⁻¹ * c := by
  simp only [tau]
  group

theorem tau_conj {z b : G} (h : z * b = b * z) (c : G) :
    tau z (b * c * b⁻¹) = b * tau z c * b⁻¹ := by
  calc tau z (b * c * b⁻¹) = (z * b) * c * (z * b)⁻¹ * b * c⁻¹ * b⁻¹ := by
        simp only [tau]
        group
    _ = (b * z) * c * (b * z)⁻¹ * b * c⁻¹ * b⁻¹ := by rw [h]
    _ = b * tau z c * b⁻¹ := by
        simp only [tau]
        group

theorem conj_z_eq (z c : G) : c * z * c⁻¹ = (tau z c)⁻¹ * z := by
  simp only [tau]
  group

theorem conj_mem_of_tau_mem {A B C : Subgroup G} {z c b : G} (hAC : A ≤ C)
    (hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hker : ∀ x ∈ C, tau z x = 1 → x ∈ A)
    (honto : ∀ a ∈ A, ∃ y ∈ C, tau z y = a)
    (hdich : (∀ x ∈ C, x * x = 1) ∨ (∀ x ∈ C, z * x * z⁻¹ = x⁻¹))
    (hc : c ∈ C) (hcτ : tau z c ∈ A ⊓ B) (hb : b ∈ B) (hbb : b * b = 1) (hbz : z * b = b * z)
    (hbC : ∀ x ∈ C, b * x * b⁻¹ ∈ C) (hbA : ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    (hcomm : b ∉ A → (∀ a ∈ A, a * (b * a⁻¹ * b⁻¹) ∈ B) ∧
      ∀ x ∈ A ⊓ B, ∃ a ∈ A, x = a * (b * a⁻¹ * b⁻¹)) :
    c * b * c⁻¹ ∈ B := by
  by_cases hbA' : b ∈ A
  · rw [hCc c hc b (hAC hbA'), mul_inv_cancel_right]
    exact hb
  obtain ⟨hc₁, hc₂⟩ := hcomm hbA'
  have hτA : tau z c ∈ A := (mem_inf.1 hcτ).1
  have hτB : tau z c ∈ B := (mem_inf.1 hcτ).2
  obtain ⟨a₀, ha₀, he⟩ := hc₂ _ hcτ
  obtain ⟨y, hy, hya⟩ := honto a₀ ha₀
  obtain ⟨u, hu⟩ : ∃ u, u = y * (b * y⁻¹ * b⁻¹) := ⟨_, rfl⟩
  have huC : u ∈ C := by
    rw [hu]
    exact C.mul_mem hy (hbC _ (C.inv_mem hy))
  have hτu : tau z u = tau z c := by
    have h₁ : y⁻¹ * a₀⁻¹ * y = a₀⁻¹ := by
      rw [mul_assoc, ← hCc y hy _ (hAC (A.inv_mem ha₀)), inv_mul_cancel_left]
    have h₂ : y * (b * a₀⁻¹ * b⁻¹) = b * a₀⁻¹ * b⁻¹ * y :=
      hCc y hy _ (hAC (hbA _ (A.inv_mem ha₀)))
    rw [he, hu, tau_mul, tau_conj hbz, tau_inv, hya, h₁, h₂, mul_inv_cancel_right]
  have hu₂ : u * u ∈ B := by
    rcases hdich with hel | hinv
    · rw [hel u huC]
      exact B.one_mem
    · have : u * u = (tau z c)⁻¹ := by
        rw [← hτu, tau, hinv u huC, mul_inv_rev, inv_inv]
      rw [this]
      exact B.inv_mem hτB
  obtain ⟨a, ha⟩ : ∃ a, a = c * u⁻¹ := ⟨_, rfl⟩
  have haA : a ∈ A := by
    rw [ha]
    refine hker _ (C.mul_mem hc (C.inv_mem huC)) ?_
    have h₃ : u⁻¹ * (tau z c)⁻¹ * u = (tau z c)⁻¹ := by
      rw [mul_assoc, ← hCc u huC _ (hAC (A.inv_mem hτA)), inv_mul_cancel_left]
    have h₄ : c * (tau z c)⁻¹ * c⁻¹ = (tau z c)⁻¹ := by
      rw [hCc c hc _ (hAC (A.inv_mem hτA)), mul_inv_cancel_right]
    rw [tau_mul, tau_inv, hτu, h₃, h₄, mul_inv_cancel]
  have h₅ : b * u⁻¹ * b⁻¹ = u := by
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    calc b * u⁻¹ * b⁻¹ = (b * b) * (y * b⁻¹ * y⁻¹ * b⁻¹) := by
          rw [hu]
          group
      _ = u := by
          rw [hbb, one_mul, hu, hbinv]
          group
  have h₆ : u * b * u⁻¹ = u * u * b := by
    calc u * b * u⁻¹ = u * (b * u⁻¹ * b⁻¹) * b := by group
      _ = u * u * b := by rw [h₅]
  have h₇ : a * (u * u) = u * u * a := hCc a (hAC haA) _ (C.mul_mem huC huC)
  have h₈ : c * b * c⁻¹ = u * u * (a * (b * a⁻¹ * b⁻¹)) * b := by
    calc c * b * c⁻¹ = a * (u * b * u⁻¹) * a⁻¹ := by
          rw [ha]
          group
      _ = a * (u * u) * (b * a⁻¹ * b⁻¹) * b := by
          rw [h₆]
          group
      _ = u * u * (a * (b * a⁻¹ * b⁻¹)) * b := by
          rw [h₇]
          group
  rw [h₈]
  exact B.mul_mem (B.mul_mem hu₂ (hc₁ a haA)) hb

theorem mem_normalizer_of_conj {K : Subgroup G} {g : G} (h₁ : ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, g⁻¹ * x * g ∈ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  have := h₂ _ hx
  simpa [mul_assoc] using this

theorem conj_mem_sup {B : Subgroup G} {z g : G} (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (hz : g * z * g⁻¹ ∈ B ⊔ zpowers z) : ∀ x ∈ B ⊔ zpowers z, g * x * g⁻¹ ∈ B ⊔ zpowers z := by
  have hle : B ⊔ zpowers z ≤ (B ⊔ zpowers z).comap (MulAut.conj g : G →* G) := by
    refine sup_le (fun b hb => ?_) ?_
    · rw [mem_comap, MonoidHom.coe_ofClass, MulAut.conj_apply]
      exact mem_sup_left (hB b hb)
    · rw [zpowers_le, mem_comap, MonoidHom.coe_ofClass, MulAut.conj_apply]
      exact hz
  intro x hx
  have := hle hx
  rwa [mem_comap, MonoidHom.coe_ofClass, MulAut.conj_apply] at this

theorem mem_egM_of_conj {K : Subgroup G} {z g : G} (h₁ : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h₂ : ∀ k ∈ K, g⁻¹ * k * g ∈ K) (hz₁ : g * z * g⁻¹ ∈ K ⊔ zpowers z)
    (hz₂ : g⁻¹ * z * g ∈ K ⊔ zpowers z) : g ∈ egM K z := by
  refine mem_normalizer_of_conj (conj_mem_sup h₁ hz₁) fun x hx => ?_
  have h₂' : ∀ k ∈ K, g⁻¹ * k * g⁻¹⁻¹ ∈ K := fun k hk => by
    rw [inv_inv]
    exact h₂ k hk
  have := conj_mem_sup h₂' (by rw [inv_inv]; exact hz₂) x hx
  rwa [inv_inv] at this

variable [Finite G] {L A B C : Subgroup G} {z : G}

theorem mul_self_z (hs : LocalSetting G L z) : z * z = 1 := by
  rw [← pow_two, ← hs.order_z, pow_orderOf_eq_one]

theorem comm_z_of_mem (hs : LocalSetting G L z) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl

theorem mem_of_tau_eq_one (hs : LocalSetting G L z)
    (hcent : ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A) (hAL : A ≤ L) (hAC : A ≤ C)
    (hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hzC : z ∉ C) {c : G} (hc : c ∈ C)
    (h1 : tau z c = 1) : c ∈ A := by
  have hzc : c ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h2 : z * c * z⁻¹ = c := mul_inv_eq_one.1 h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hs.centralizer_eq] at hzc
  obtain ⟨l, hl, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hzc
  rcases eq_one_or_eq_of_mul_self (mul_self_z hs) hw with rfl | hwz
  · rw [mul_one] at hc ⊢
    exact hcent l hl fun a ha => hCc l hc a (hAC ha)
  · rw [hwz] at hc
    exfalso
    have hlA : l ∈ A := by
      refine hcent l hl fun a ha => ?_
      have h3 : l * z * a = a * (l * z) := hCc _ hc a (hAC ha)
      have h4 : a * z = z * a := comm_z_of_mem hs (hAL ha)
      calc l * a = l * z * a * z⁻¹ := by rw [mul_assoc l z a, ← h4]; group
        _ = a * l := by rw [h3]; group
    apply hzC
    have : z = l⁻¹ * (l * z) := by group
    rw [this]
    exact C.mul_mem (C.inv_mem (hAC hlA)) hc

theorem mem_egM_of_mem (hs : LocalSetting G L z) (hF : CompatFacts L A B) {b : G}
    (hb : b ∈ B) : b ∈ egM A z := by
  have hbN := hF.B_le_NA hb
  have hbz : b * z * b⁻¹ = z := by
    rw [comm_z_of_mem hs hbN.2, mul_inv_cancel_right]
  have hbz' : b⁻¹ * z * b = z := by
    rw [mul_assoc, ← comm_z_of_mem hs hbN.2, inv_mul_cancel_left]
  refine mem_egM_of_conj (fun a ha => (mem_normalizer_iff.1 hbN.1 a).1 ha)
    (fun a ha => (mem_normalizer_iff''.1 hbN.1 a).1 ha) ?_ ?_
  · rw [hbz]
    exact mem_sup_right (mem_zpowers z)
  · rw [hbz']
    exact mem_sup_right (mem_zpowers z)

theorem mem_egM_of_tau_mem (hs : LocalSetting G L z)
    (hcent : ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A) (hB2 : ∀ b ∈ B, b * b = 1)
    (hF : CompatFacts L A B) (hC : CData A z C) {c : G} (hc : c ∈ C)
    (hcτ : tau z c ∈ A ⊓ B) : c ∈ egM B z := by
  have hAL : A ≤ L := fun a ha => (hF.A_le_NB ha).2
  have hker : ∀ x ∈ C, tau z x = 1 → x ∈ A := fun x hx h1 =>
    mem_of_tau_eq_one hs hcent hAL hC.A_le hC.comm hC.z_not_mem hx h1
  have hconj : ∀ g ∈ C, tau z g ∈ A ⊓ B → ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hg hgτ b hb
    have hbN := hF.B_le_NA hb
    exact conj_mem_of_tau_mem hC.A_le hC.comm hker hC.onto hC.dichotomy hg hgτ hb (hB2 b hb)
      (comm_z_of_mem hs hbN.2).symm (hC.norm b (mem_egM_of_mem hs hF hb))
      (fun a ha => (mem_normalizer_iff.1 hbN.1 a).1 ha) (hF.comm_A b hb)
  have hτA : tau z c ∈ A := (mem_inf.1 hcτ).1
  have hcτ' : tau z c⁻¹ ∈ A ⊓ B := by
    rw [tau_inv, mul_assoc, ← hC.comm c hc _ (hC.A_le (A.inv_mem hτA)), inv_mul_cancel_left]
    exact inv_mem hcτ
  refine mem_egM_of_conj (hconj c hc hcτ) (fun b hb => ?_) ?_ ?_
  · have := hconj _ (C.inv_mem hc) hcτ' b hb
    rwa [inv_inv] at this
  · rw [conj_z_eq]
    exact mul_mem (mem_sup_left (inv_mem (mem_inf.1 hcτ).2)) (mem_sup_right (mem_zpowers z))
  · have := conj_z_eq z c⁻¹
    rw [inv_inv] at this
    rw [this]
    exact mul_mem (mem_sup_left (inv_mem (mem_inf.1 hcτ').2)) (mem_sup_right (mem_zpowers z))

end Nine

theorem caseTwoB_of_facts [Finite G] {L A B C : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hcent : ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A) (hB2 : ∀ b ∈ B, b * b = 1)
    (hF : CompatFacts L A B) (hC : CData A z C) :
    ¬ egM B z ≤ centralizer ({z} : Set G) := by
  intro hle
  obtain ⟨b₁, hb₁, hb₁1⟩ : ∃ b₁ ∈ A ⊓ B, b₁ ≠ 1 := by
    have h4 := hF.card_inf
    by_contra h
    have h' : A ⊓ B = ⊥ := (eq_bot_iff_forall _).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [h', card_bot] at h4
    exact absurd h4 (by decide)
  obtain ⟨c, hc, hcτ⟩ := hC.onto b₁ (mem_inf.1 hb₁).1
  have hcM : c ∈ egM B z := by
    refine Nine.mem_egM_of_tau_mem hs hcent hB2 hF hC hc ?_
    rw [Nine.tau, hcτ]
    exact hb₁
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (hle hcM)
  apply hb₁1
  rw [← hcτ, ← hcz]
  group

theorem caseTwoB [Finite G] {L A B C : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hA : SextetFacts L A) (hB : OctadBasics L B) (hF : CompatFacts L A B) (hC : CData A z C) :
    ¬ egM B z ≤ centralizer ({z} : Set G) :=
  caseTwoB_of_facts hs hA.cent hB.elem.2 hF hC

end CFSG.EvenSporadicStandard.M24Std
