module

public import CFSG.LargeExtraspecial.S5Odd
public import CFSG.LargeExtraspecial.S5C
public import CFSG.LargeExtraspecial.S5Gen4
public import CFSG.LargeExtraspecial.S5Q
public import CFSG.LargeExtraspecial.S4EightRes5
public import CFSG.LargeExtraspecial.S5R

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem conj_mem_inf_centralizer (H : S4.Hyp4 S g) {F : Subgroup S.O}
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {t s x : S.O} (ht : t ∈ S.Lbar g)
    (hs : s ∈ S.Lbar g) (hx : x ∈ F ⊓ centralizer ({t} : Set S.O)) :
    s * x * s⁻¹ ∈ F ⊓ centralizer ({t} : Set S.O) := by
  refine Subgroup.mem_inf.mpr ⟨hnorm s hs x (Subgroup.mem_inf.mp hx).1, ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hxt := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hst : s * t = t * s := S4.Lbar_comm S H.conj_mem hs ht
  have hts : t * s⁻¹ = s⁻¹ * t := by
    calc t * s⁻¹ = s⁻¹ * (s * t) * s⁻¹ := by group
      _ = s⁻¹ * (t * s) * s⁻¹ := by rw [hst]
      _ = s⁻¹ * t := by group
  calc s * x * s⁻¹ * t = s * x * (s⁻¹ * t) := by group
    _ = s * x * (t * s⁻¹) := by rw [hts]
    _ = s * (x * t) * s⁻¹ := by group
    _ = s * (t * x) * s⁻¹ := by rw [hxt]
    _ = (s * t) * x * s⁻¹ := by group
    _ = (t * s) * x * s⁻¹ := by rw [hst]
    _ = t * (s * x * s⁻¹) := by group

theorem mem_Nbar_self (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ Nbar S g t := by
  refine ⟨Lbar_le_Rbar ht ht, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hth, rfl⟩ := hv
    exact fix_of_mem_normalizer_mul H h (Subgroup.le_normalizer hth)
  | zero => exact map_zero _
  | add u w _ _ hu hw => rw [map_add, hu, hw]
  | smul c u _ hu => rw [map_smul, hu]

theorem mem_Rbar_of_inv {t : S.O} (ht : t ∈ S.Lbar g) {w s : S.O} (hwM : w ∈ S.Mbar)
    (hwt : w * t = t * w) (hs : s ∈ S.Lbar g) (hinv : s * w * s⁻¹ = w⁻¹)
    (hodd : Odd (orderOf w)) : w ∈ Rbar S g t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hwM
  have htk : t ∈ S.Lbar ((k : G) * g) := by
    have := conj_mem_Lbar_mul S k ht
    rwa [hwt, mul_inv_cancel_right] at this
  have h1 : S.ρ k * s * (S.ρ k)⁻¹ ∈ Rbar S g t :=
    Lbar_mul_le_Rbar htk (conj_mem_Lbar_mul S k hs)
  have h2 : s⁻¹ ∈ Rbar S g t := Lbar_le_Rbar ht (inv_mem hs)
  refine mem_of_sq_mem hodd ?_
  have hw : s * (S.ρ k)⁻¹ * s⁻¹ = S.ρ k := by
    have := congrArg (·⁻¹) hinv
    simpa [mul_assoc] using this
  have e : (S.ρ k) ^ 2 = S.ρ k * s * (S.ρ k)⁻¹ * s⁻¹ := by
    calc (S.ρ k) ^ 2 = S.ρ k * S.ρ k := pow_two _
      _ = S.ρ k * (s * (S.ρ k)⁻¹ * s⁻¹) := by rw [hw]
      _ = S.ρ k * s * (S.ρ k)⁻¹ * s⁻¹ := by group
  rw [e]
  exact mul_mem h1 h2

theorem le_Rbar_of_commute (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    ∀ n : ℕ, ∀ F : Subgroup S.O, Nat.card F ≤ n → F ≤ S.Mbar → Odd (Nat.card F) →
      (∀ x ∈ F, x * t = t * x) → (∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) →
      (∀ x ∈ F, (∀ s ∈ S.Lbar g, s * x = x * s) → x = 1) → F ≤ Rbar S g t := by
  intro n
  induction n with
  | zero =>
    intro F hF
    have := Nat.card_pos (α := F)
    omega
  | succ n ih =>
    intro F hcard hFM hodd hFt hnorm hCF
    by_cases hall : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x = x * s
    · intro x hx
      rw [hCF x hx fun s hs => hall s hs x hx]
      exact one_mem _
    push Not at hall
    obtain ⟨s, hs, x₀, hx₀, hsx₀⟩ := hall
    have hss : s * s = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hs
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    obtain ⟨F', hF'⟩ : ∃ F' : Subgroup S.O, F' = F ⊓ centralizer ({s} : Set S.O) := ⟨_, rfl⟩
    have hF'F : F' ≤ F := hF' ▸ inf_le_left
    have hlt : Nat.card F' < Nat.card F := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hF'F fun h => hsx₀ ?_)
      have hx₀' : x₀ ∈ F' := h ▸ hx₀
      rw [hF'] at hx₀'
      exact (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx₀').2).symm
    have hF'R : F' ≤ Rbar S g t := ih F' (by omega) (hF'F.trans hFM)
      (Odd.of_dvd_nat hodd (card_dvd_of_le hF'F)) (fun x hx => hFt x (hF'F hx))
      (fun s' hs' x hx => hF' ▸ conj_mem_inf_centralizer H hnorm hs hs' (hF' ▸ hx))
      (fun x hx hc => hCF x (hF'F hx) hc)
    intro f hf
    have hoddF : ∀ y ∈ F, Odd (orderOf y) := fun y hy =>
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard F hy)
    obtain ⟨u, hu⟩ : ∃ u, u = f⁻¹ * (s * f * s⁻¹) := ⟨_, rfl⟩
    have huF : u ∈ F := hu ▸ mul_mem (inv_mem hf) (hnorm s hs f hf)
    have hsu : s * u * s⁻¹ = u⁻¹ := by
      rw [hu, hsi]
      calc s * (f⁻¹ * (s * f * s)) * s = s * f⁻¹ * s * f * (s * s) := by group
        _ = s * f⁻¹ * s * f := by rw [hss, mul_one]
        _ = s⁻¹ * f⁻¹ * s⁻¹ * f := by rw [hsi]
        _ = (f⁻¹ * (s * f * s))⁻¹ := by group
    obtain ⟨k, hk⟩ := exists_sq_eq_of_odd (hoddF u huF)
    obtain ⟨v, hv⟩ : ∃ v, v = u ^ k := ⟨_, rfl⟩
    have hvF : v ∈ F := hv ▸ pow_mem huF k
    have hsv : s * v * s⁻¹ = v⁻¹ := by
      rw [hv, ← conj_pow, hsu, inv_pow]
    have hvR : v ∈ Rbar S g t := mem_Rbar_of_inv ht (hFM hvF) (hFt v hvF) hs hsv (hoddF v hvF)
    have hcF' : f * v ∈ F' := by
      rw [hF']
      refine Subgroup.mem_inf.mpr ⟨mul_mem hf hvF, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : s * f * s⁻¹ = f * v ^ 2 := by rw [hv, hk, hu]; group
      have h2 : s * (f * v) * s⁻¹ = f * v := by
        calc s * (f * v) * s⁻¹ = (s * f * s⁻¹) * (s * v * s⁻¹) := by group
          _ = f * v := by rw [h1, hsv]; group
      have h3 : s * (f * v) = f * v * s := by
        calc s * (f * v) = s * (f * v) * s⁻¹ * s := by group
          _ = f * v * s := by rw [h2]
      exact h3.symm
    have e : f = (f * v) * v⁻¹ := by group
    rw [e]
    exact mul_mem (hF'R hcF') (inv_mem hvR)

theorem resV_aV_ne_zero (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (r : Rbar S g t) :
    resV H.conj_mem t r (aV ht) ≠ 0 := by
  intro h0
  have := congrArg Subtype.val h0
  rw [coe_resV_apply, ZeroMemClass.coe_zero] at this
  exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne
    ((LinearEquiv.map_eq_zero_iff _).mp this)

theorem timmesfeld_4_8_M (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) {F : Subgroup S.O} (hFM : F ≤ S.Mbar)
    (hodd : Odd (Nat.card F)) (hF1 : F ≠ ⊥) (hFt : ∀ x ∈ F, x * t = t * x)
    (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F)
    (hCF : ∀ x ∈ F, (∀ s ∈ S.Lbar g, s * x = x * s) → x = 1) :
    Nat.card F = 3 ∨ (Nat.card F = 9 ∧ Nat.card (S.Lbar g) = 8 ∧
      ∀ s ∈ S.Lbar g, (∀ x ∈ F, s * x = x * s) → s = 1 ∨ s = t) := by
  classical
  have haQ := H.conj_mem
  have hFR : F ≤ Rbar S g t := le_Rbar_of_commute H ht _ F le_rfl hFM hodd hFt hnorm hCF
  have hR : Rbar S g t ≠ S.Lbar g := by
    intro h
    apply hF1
    have h0 := inf_eq_bot_of_odd_of_isPGroup hodd (S4.isPGroup_Lbar S haQ)
    rw [← h0]
    exact (inf_eq_left.mpr (h ▸ hFR)).symm
  have hLF : S.Lbar g ≤ normalizer (F : Set S.O) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hnorm s hs y, fun hy => ?_⟩
    have := hnorm s⁻¹ (inv_mem hs) _ hy
    simpa [mul_assoc] using this
  rcases timmesfeld_4_8_F H hNo C ht ht1 hR hodd hF1 hFR hLF hCF with h3 | ⟨hVQ, h4, hΩ, h9, -⟩
  · exact Or.inl h3
  right
  obtain ⟨Q, hQ, -, -, -, hsing⟩ := hΩ.exists_form
  have hQa : Q (aV ht) = 0 := (hsing (aV ht) (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
  have hle9 := ncard_singular_le_nine h4 hQ (aV_ne_zero H ht) hQa
  let ψ : F → Vt S g t := fun f => orbV haQ ht (hFR f.2)
  have hψinj : Function.Injective ψ := by
    intro f₁ f₂ h
    apply Subtype.ext
    apply eq_of_mem_of_apply_eq H hodd hFR hLF hCF f₁.2 f₂.2
    have := congrArg Subtype.val h
    simpa only [ψ, coe_orbV] using this
  have hψsing : Set.range ψ ⊆ {v | v ≠ 0 ∧ Q v = 0} := by
    rintro _ ⟨f, rfl⟩
    have hne : ψ f ≠ 0 := resV_aV_ne_zero H ht ⟨f, hFR f.2⟩
    exact ⟨hne, (hsing _ hne).mpr ⟨resV haQ t ⟨f, hFR f.2⟩, ⟨f, hFR f.2, fun _ => rfl⟩, rfl⟩⟩
  have hcard : (Set.range ψ).ncard = 9 := by
    rw [Set.ncard_range_of_injective hψinj, h9]
  have heq : Set.range ψ = {v | v ≠ 0 ∧ Q v = 0} :=
    Set.eq_of_subset_of_ncard_le hψsing (by rw [hcard]; exact hle9) (Set.toFinite _)
  have htrans : ∀ r ∈ Rbar S g t, ∃ f ∈ F, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    intro r hr
    have hv0 := resV_aV_ne_zero H ht ⟨r, hr⟩
    have hv : resV haQ t ⟨r, hr⟩ (aV ht) ∈ {v | v ≠ 0 ∧ Q v = 0} :=
      ⟨hv0, (hsing _ hv0).mpr ⟨_, ⟨r, hr, fun _ => rfl⟩, rfl⟩⟩
    rw [← heq] at hv
    obtain ⟨f, hf⟩ := hv
    refine ⟨f, f.2, ?_⟩
    have := congrArg Subtype.val hf
    simp only [ψ, coe_orbV, coe_resV_apply] at this
    exact this
  have hCL : ∀ s ∈ S.Lbar g, (∀ x ∈ F, s * x = x * s) → s = 1 ∨ s = t := by
    intro s hs hsF
    refine eq_one_or_eq_of_forall H C ht ht1 hVQ hs (fun k hk => ?_) (fun r hr => ?_)
    · obtain ⟨f, hf, hfa⟩ := htrans _ hk
      obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp (hFM hf)
      have hcl : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
          S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) := by
        rw [← ρ_cl_conj_z S j haQ, ← ρ_cl_conj_z S k haQ, hj, hfa]
      rw [Lbar_eq_of_cl_eq S (H.mul j).conj_mem (H.mul j).conj_ne (H.mul k).conj_mem hcl,
        mem_Lbar_mul_iff, hj]
      have e : f⁻¹ * s * f = s := by
        calc f⁻¹ * s * f = f⁻¹ * (s * f) := mul_assoc _ _ _
          _ = f⁻¹ * (f * s) := by rw [hsF f hf]
          _ = s := by group
      rw [e]
      exact hs
    · obtain ⟨f, hf, hfa⟩ := htrans r hr
      exact ⟨f, hFR hf, (hsF f hf).symm, hfa⟩
  have hLN : ∀ τ ∈ S.Lbar g ⊓ Nbar S g t, τ = 1 ∨ τ = t := by
    intro τ hτ
    have hτL : τ ∈ S.Lbar g := (Subgroup.mem_inf.mp hτ).1
    have hτN : τ ∈ Nbar S g t := (Subgroup.mem_inf.mp hτ).2
    refine hCL τ hτL fun f hf => ?_
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (hFM hf)
    have hkt : S.ρ k * t = t * S.ρ k := by rw [hk]; exact hFt f hf
    have h1 : f * τ⁻¹ * f⁻¹ ∈ Nbar S g t := by
      rw [← hk]
      exact conj_mem_Nbar haQ hkt (inv_mem hτN)
    obtain ⟨c, hc⟩ : ∃ c, c = τ * (f * τ⁻¹ * f⁻¹) := ⟨_, rfl⟩
    have hcN : c ∈ Nbar S g t := hc ▸ mul_mem hτN h1
    have hcF : c ∈ F := by
      have := mul_mem (hnorm τ hτL f hf) (inv_mem hf)
      rw [hc]
      simpa [mul_assoc] using this
    have hc1 : c = 1 := eq_one_of_mem_of_apply_eq H hodd hFR hLF hCF hcF
      (hcN.2 _ (cl_a_mem_Vt ht))
    calc τ * f = c * (f * τ) := by rw [hc]; group
      _ = f * τ := by rw [hc1, one_mul]
  have h2 := card_le_two_of_subset hLN
  have hτ := (radConfig H C ht ht1 hVQ hNo hΩ.not_transitive).tau_not_mem
  have h4' := card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ h4 hτ
  have hge : 4 ≤ Nat.card (LmodN S g t) := by
    have := card_spPointRadical_le_two_mul H C ht ht1 hVQ
    rw [card_spPointRadical (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
      (aV_ne_zero H ht), h4] at this
    norm_num at this
    omega
  have hne : S.Lbar g ⊓ Nbar S g t ≠ ⊥ := by
    intro h
    have : t ∈ S.Lbar g ⊓ Nbar S g t := Subgroup.mem_inf.mpr ⟨ht, mem_Nbar_self H ht⟩
    rw [h, mem_bot] at this
    exact ht1 this
  have h2' := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  refine ⟨h9, ?_, hCL⟩
  rw [card_Lbar_eq haQ ht, le_antisymm h2 h2', le_antisymm h4' hge]

end CFSG.LargeExtraspecial.S5
