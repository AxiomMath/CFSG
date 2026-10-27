module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Stage
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.WTriv
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem mul_z_eq {m : G} (hm : m ∈ Λ) : m * H.z = H.z * m⁻¹ := by
  have h1 := h.z_inv (inv_mem hm)
  rw [inv_inv] at h1
  calc m * H.z = (H.z * m⁻¹ * H.z) * H.z := by rw [h1]
    _ = H.z * m⁻¹ * (H.z * H.z) := by group
    _ = H.z * m⁻¹ := by rw [H.z_mul_self, mul_one]

include h in
theorem conj_Λ_zl {s l : G} (hs : s ∈ Λ) :
    s * (H.z * l) * s⁻¹ = H.z * (s⁻¹ * l * s⁻¹) :=
  calc s * (H.z * l) * s⁻¹ = (s * H.z) * l * s⁻¹ := by group
    _ = (H.z * s⁻¹) * l * s⁻¹ := by rw [h.mul_z_eq hs]
    _ = H.z * (s⁻¹ * l * s⁻¹) := by group

include h in
theorem conj_zl {s l : G} (hs : s ∈ S) (hl : l ∈ Λ) :
    ∃ m ∈ Λ, s * (H.z * l) * s⁻¹ = H.z * l * (m * m) := by
  rcases h.cover s hs with hsΛ | hsz
  · refine ⟨s⁻¹, inv_mem hsΛ, ?_⟩
    rw [h.conj_Λ_zl hsΛ, h.comm (inv_mem hsΛ) hl]
    group
  · obtain ⟨t, htΛ, rfl⟩ : ∃ t ∈ Λ, s = t * H.z :=
      ⟨s * H.z, hsz, by rw [mul_assoc, H.z_mul_self, mul_one]⟩
    refine ⟨l⁻¹ * t⁻¹, mul_mem (inv_mem hl) (inv_mem htΛ), ?_⟩
    have e1 : (t * H.z)⁻¹ = H.z * t⁻¹ := by rw [mul_inv_rev, H.z_inv]
    have e2 : (t * l * t) * H.z = H.z * (t * l * t)⁻¹ :=
      h.mul_z_eq (mul_mem (mul_mem htΛ hl) htΛ)
    calc t * H.z * (H.z * l) * (t * H.z)⁻¹ = t * (H.z * H.z) * l * (H.z * t⁻¹) := by
          rw [e1]; group
      _ = t * l * (H.z * t⁻¹) := by rw [H.z_mul_self, mul_one]
      _ = t * l * (t * H.z) := by rw [h.mul_z_eq htΛ]
      _ = (t * l * t) * H.z := by group
      _ = H.z * (t * l * t)⁻¹ := e2
      _ = H.z * l * (l⁻¹ * t⁻¹ * (l⁻¹ * t⁻¹)) := by group

include h in
theorem sq_conj_zl {l m : G} (hl : l ∈ Λ) (hm : m ∈ Λ) :
    ∃ s ∈ S, s * (H.z * l) * s⁻¹ = H.z * l * (m * m) := by
  refine ⟨m⁻¹, h.le (inv_mem hm), ?_⟩
  rw [h.conj_Λ_zl (inv_mem hm), inv_inv, h.comm hm hl]
  group

include h in
theorem z_mul_mem_Λ {x : G} (hx : x ∈ S) (hxΛ : x ∉ Λ) : H.z * x ∈ Λ := by
  have := h.mul_inv_mem_Λ h.z_mem h.z_not_mem hx hxΛ
  rwa [H.z_inv] at this

include h in
theorem N_conj_z_mem {n : G} (hn : n ∈ normalizer (S : Set G)) :
    n * H.z * n⁻¹ ∈ S ∧ n * H.z * n⁻¹ ∉ Λ :=
  h.N_conj_mem hn h.z_mem h.z_not_mem

include h in
theorem exists_move (hS : 2 ∣ S.index) :
    ∃ n ∈ normalizer (S : Set G), ∀ s ∈ S, n * H.z * n⁻¹ ≠ s * H.z * s⁻¹ := by
  by_contra hcon
  push Not at hcon
  refine J1Std.not_two_dvd_index_of_invariant h.pgroup (fun P hP hPC hVP => ?_) hcon hS
  rw [h.centralizer_S] at hVP
  have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact (H.star hP hPC).1)
  rw [← this]
  exact h.V_le

include h in
theorem N_le_normalizer_Λ : normalizer (S : Set G) ≤ normalizer (Λ : Set G) := fun n hn =>
  mem_normalizer_iff.2 fun l => ⟨fun hl => h.N_normalizes_Λ hn hl, fun hl => by
    have := h.N_normalizes_Λ (inv_mem hn) hl
    simpa [mul_assoc] using this⟩

include h in
theorem centralizes_Λ_of_odd_pow {g : G} (hg : g ∈ normalizer (S : Set G)) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hgE : ∀ e ∈ H.E, g * e * g⁻¹ = e) : ∀ l ∈ Λ, g * l * g⁻¹ = l := by
  have hgΛ : g ∈ normalizer (Λ : Set G) := h.N_le_normalizer_Λ hg
  have hpow := J1Std.normalizerMonoidHom_pow_apply hgΛ
  have hψm : Λ.normalizerMonoidHom ⟨g, hgΛ⟩ ^ m = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hpow m a, hgm]
    simp
  have hfix : ∀ a : Λ, a * a = 1 → Λ.normalizerMonoidHom ⟨g, hgΛ⟩ a = a := by
    intro a ha
    exact Subtype.ext (hgE a (h.mem_E_of_sq a.2 (congrArg Subtype.val ha)))
  have h1 := eq_one_of_odd_pow_of_fixes_involutions (fun a b => Subtype.ext (h.comm a.2 b.2))
    (h.pgroup.to_le h.le) (Λ.normalizerMonoidHom ⟨g, hgΛ⟩) hm hψm hfix
  intro l hl
  have h2 := congrArg (fun φ : MulAut Λ => ((φ ⟨l, hl⟩ : Λ) : G)) h1
  exact h2

include h in
theorem centralizes_S_of_odd_pow {g : G} (hg : g ∈ normalizer (S : Set G)) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hgE : ∀ e ∈ H.E, g * e * g⁻¹ = e) (hgz : g * H.z = H.z * g) :
    ∀ s ∈ S, g * s * g⁻¹ = s := by
  have hΛ := h.centralizes_Λ_of_odd_pow hg hm hgm hgE
  intro s hs
  rcases h.cover s hs with hsΛ | hsz
  · exact hΛ s hsΛ
  · have h1 := hΛ (s * H.z) hsz
    have hz : g * H.z * g⁻¹ = H.z := by rw [hgz]; group
    calc g * s * g⁻¹ = (g * (s * H.z) * g⁻¹) * (g * H.z * g⁻¹)⁻¹ := by group
      _ = (s * H.z) * H.z⁻¹ := by rw [h1, hz]
      _ = s := by group

include h in
theorem exists_sigma : ∃ σ : G, H.IsSigma σ ∧ σ ∈ normalizer (S : Set G) := by
  obtain ⟨b, hb7⟩ := H.exists_order7_actB
  obtain ⟨c, hc, hcact⟩ := h.cov b b.2
  obtain ⟨k, hk⟩ := H.exists_isSigma_of_action (mem_centralizer_singleton_iff.1 hc.1) hb7 hcact
  exact ⟨c ^ k, hk, pow_mem hc.2 k⟩

include h in
theorem exists_sigma_aut {σ : G} (hσ : H.IsSigma σ) (hσN : σ ∈ normalizer (S : Set G)) :
    ∃ φ : MulAut Λ, φ ^ 7 = 1 ∧ (∀ a : Λ, φ a = a → a = 1) ∧
      ∀ (i : ℕ) (a : Λ), ((φ ^ i) a : G) = σ ^ i * a * (σ ^ i)⁻¹ := by
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.N_le_normalizer_Λ hσN
  have hpow := J1Std.normalizerMonoidHom_pow_apply hσΛ
  obtain ⟨a, ha⟩ := hσ.exists_pow_eq_one
  have h7odd : Odd (7 ^ a) := Odd.pow (by decide)
  have hg7 : (σ ^ 7) ^ 7 ^ a = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have hcentr : ∀ l ∈ Λ, σ ^ 7 * l * (σ ^ 7)⁻¹ = l :=
    h.centralizes_Λ_of_odd_pow (pow_mem hσN 7) h7odd hg7 fun e he => hσ.pow_seven_apply_E he
  refine ⟨Λ.normalizerMonoidHom ⟨σ, hσΛ⟩, ?_, ?_, hpow⟩
  · refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hpow 7 b]
    exact hcentr b b.2
  · intro b hb
    by_contra hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.pgroup ⟨b.1, h.le b.2⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hne (Subtype.ext (orderOf_eq_one_iff.1 hk))
    have hbΛ : b.1 ^ (2 ^ (k - 1)) ∈ Λ := Subgroup.pow_mem Λ b.2 _
    have hbsq : b.1 ^ (2 ^ (k - 1)) * b.1 ^ (2 ^ (k - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1),
        ← hk]
      exact pow_orderOf_eq_one _
    have hb1 : b.1 ^ (2 ^ (k - 1)) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hσb : σ * b.1 ^ (2 ^ (k - 1)) * σ⁻¹ = b.1 ^ (2 ^ (k - 1)) := by
      have : σ * b.1 * σ⁻¹ = b.1 := congrArg Subtype.val hb
      rw [← conj_pow, this]
    exact hσ.free (h.mem_E_of_sq hbΛ hbsq) hb1 hσb

include h in
theorem card_sq_eq_one : Nat.card {a : Λ // a * a = 1} = 8 := by
  rw [← H.card_E]
  refine Nat.card_congr ⟨fun a => ⟨a.1.1, h.mem_E_of_sq a.1.2 (congrArg Subtype.val a.2)⟩,
    fun e => ⟨⟨e.1, h.E_le e.2⟩, Subtype.ext (H.sq_E e.1 e.2)⟩, fun a => rfl, fun e => rfl⟩

end Stage

end CFSG.EvenSporadicStandard.ReeStd
