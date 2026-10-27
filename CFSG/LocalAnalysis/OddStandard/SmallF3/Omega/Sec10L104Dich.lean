module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Proj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZNorm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10L104_K0_normalizes_K1 {K1 K2 N K0 : Subgroup G}
    (hc12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a)
    (hNc : ∀ n ∈ N, ∀ a ∈ K1 ⊔ K2, n * a = a * n)
    (hdec : ∀ x ∈ K0, ∃ n ∈ N, ∃ k ∈ K1 ⊔ K2, x = n * k) :
    ∀ k ∈ K0, ∀ x ∈ K1, k * x * k⁻¹ ∈ K1 := by
  intro k hk x hx
  obtain ⟨n, hn, k', hk', rfl⟩ := hdec k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc12 hk'
  have hbx : b * x = x * b := (hc12 x hx b hb).symm
  have hax : a * x * a⁻¹ ∈ K1 := K1.mul_mem (K1.mul_mem ha hx) (K1.inv_mem ha)
  have hn1 : n * (a * x * a⁻¹) = (a * x * a⁻¹) * n := hNc n hn _ ((le_sup_left : K1 ≤ K1 ⊔ K2) hax)
  have hbxb : b * x * b⁻¹ = x := by rw [hbx]; group
  have e : n * (a * b) * x * (n * (a * b))⁻¹ = a * x * a⁻¹ := by
    calc n * (a * b) * x * (n * (a * b))⁻¹ = n * (a * (b * x * b⁻¹) * a⁻¹) * n⁻¹ := by group
      _ = n * (a * x * a⁻¹) * n⁻¹ := by rw [hbxb]
      _ = a * x * a⁻¹ := by rw [hn1]; group
  rw [e]
  exact hax

theorem sec10L104_dichotomy [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2)
    {N K0 : Subgroup G} (hNc : ∀ n ∈ N, ∀ a ∈ K1 ⊔ K2, n * a = a * n)
    (hNd : ∀ x ∈ N, x ∈ K1 ⊔ K2 → x = 1)
    (hdec : ∀ x ∈ K0, ∃ n ∈ N, ∃ k ∈ K1 ⊔ K2, x = n * k) (hKK0 : K1 ⊔ K2 ≤ K0)
    {s : G} (hss : s * s = 1) (hsz : s * z = z * s)
    (hsK0 : ∀ x ∈ K0, s * x * s⁻¹ ∈ K0) (hsN : ∀ n ∈ N, s * n * s⁻¹ ∈ N) :
    (∀ x ∈ K1, ∃ n ∈ N, ∃ k ∈ K1, s * x * s⁻¹ = n * k) ∨
      (∀ x ∈ K1, ∃ n ∈ N, ∃ k ∈ K2, s * x * s⁻¹ = n * k) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hc12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  have hK1K : K1 ≤ K1 ⊔ K2 := le_sup_left
  have hK0n1 := sec10L104_K0_normalizes_K1 hc12 hNc hdec
  have hsK0' : ∀ x ∈ K0, s⁻¹ * x * s ∈ K0 := by
    intro x hx
    have h := hsK0 x hx
    rw [hsi] at h ⊢
    exact h
  obtain ⟨π, hπK, hπmul, hπk⟩ :=
    sec10L104_exists_proj (N := N) (K := K1 ⊔ K2) (K0 := K0) hNc hNd hKK0 hdec
  have hK1K0 : ∀ x ∈ K1, s * x * s⁻¹ ∈ K0 := fun x hx => hsK0 x (hKK0 (hK1K hx))
  let Ψ : ↥K1 →* G := MonoidHom.mk' (fun x : ↥K1 => π (s * (x : G) * s⁻¹)) (by
    intro a b
    have ha := hK1K0 (a : G) a.2
    have hb := hK1K0 (b : G) b.2
    have e : s * ((a * b : ↥K1) : G) * s⁻¹ = (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹) := by
      push_cast
      group
    rw [e]
    exact hπmul _ ha _ hb)
  have hΨ : ∀ x : ↥K1, Ψ x = π (s * (x : G) * s⁻¹) := fun x => rfl
  have hback : ∀ y : G, s * (s * y * s⁻¹) * s⁻¹ = y := by
    intro y
    rw [hsi]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
      _ = y := by rw [hss]; group
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨-, n, hn, hna⟩ := hπK _ (hK1K0 (a : G) a.2)
    have h1 : π (s * (a : G) * s⁻¹) = 1 := by rw [← hΨ]; exact ha
    rw [h1, mul_one] at hna
    have hanN : (a : G) ∈ N := by
      have e : (a : G) = s * n * s⁻¹ := by rw [← hna, hback]
      rw [e]
      exact hsN n hn
    exact Subtype.ext (hNd _ hanN (hK1K a.2))
  have hDK : Ψ.range ≤ K1 ⊔ K2 := by
    rintro _ ⟨x, rfl⟩
    exact (hπK _ (hK1K0 (x : G) x.2)).1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzD : z ∈ Ψ.range := by
    refine ⟨⟨z, hzK1⟩, ?_⟩
    rw [hΨ]
    have e : s * z * s⁻¹ = z := by rw [hsz, mul_assoc, mul_inv_cancel, mul_one]
    show π (s * z * s⁻¹) = z
    rw [e]
    exact hπk z (hK1K hzK1)
  have hDnorm : ∀ k ∈ K1 ⊔ K2, ∀ d ∈ Ψ.range, k * d * k⁻¹ ∈ Ψ.range := by
    intro k hk d hd
    obtain ⟨x, rfl⟩ := hd
    have hk0 : k ∈ K0 := hKK0 hk
    have hx0 := hK1K0 (x : G) x.2
    have hx' : (s⁻¹ * k * s) * (x : G) * (s⁻¹ * k * s)⁻¹ ∈ K1 :=
      hK0n1 _ (hsK0' k hk0) _ x.2
    refine ⟨⟨_, hx'⟩, ?_⟩
    have e : s * ((s⁻¹ * k * s) * (x : G) * (s⁻¹ * k * s)⁻¹) * s⁻¹ =
        k * (s * (x : G) * s⁻¹) * k⁻¹ := by group
    have hπconj : π (k * (s * (x : G) * s⁻¹) * k⁻¹) = k * π (s * (x : G) * s⁻¹) * k⁻¹ := by
      rw [hπmul _ (K0.mul_mem hk0 hx0) _ (K0.inv_mem hk0), hπmul _ hk0 _ hx0, hπk k hk,
        hπk k⁻¹ (Subgroup.inv_mem _ hk)]
    show π (s * ((s⁻¹ * k * s) * (x : G) * (s⁻¹ * k * s)⁻¹) * s⁻¹) = _
    rw [e, hπconj]
    rfl
  have hpocket : Sl23PocketIn L z Ψ.range :=
    sec10L104_pocket_of_normal hP5 hpsp hctx hzD hDK hDnorm ⟨MonoidHom.ofInjective hΨinj⟩
  have hdecs : ∀ x ∈ K1, ∃ n ∈ N, s * x * s⁻¹ = n * π (s * x * s⁻¹) := by
    intro x hx
    obtain ⟨-, n, hn, h⟩ := hπK _ (hK1K0 x hx)
    exact ⟨n, hn, h⟩
  have hmem : ∀ x ∈ K1, π (s * x * s⁻¹) ∈ Ψ.range := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  rcases sec10L104_pocket_eq hP5 hpsp hctx hpocket with h | h
  · left
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hdecs x hx
    refine ⟨n, hn, π (s * x * s⁻¹), ?_, hxn⟩
    have := hmem x hx
    rw [h] at this
    exact this
  · right
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hdecs x hx
    refine ⟨n, hn, π (s * x * s⁻¹), ?_, hxn⟩
    have := hmem x hx
    rw [h] at this
    exact this

end CFSG.OddStandard.SmallF3.Omega
