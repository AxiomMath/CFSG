module

public import CFSG.GH74.GLS.Stage4.T6SylP
public import CFSG.GH74.GLS.Stage4.T6Borel

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem card_B₁_dvd (h : T6Ctx N u p) :
    Nat.card ↥(Subgroup.normalizer (N.X₁ : Set G) ⊓ N.K₁) ∣ N.q₁ * (N.q₁ - 1) := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₁
  have := t6_card_normalizer_dvd hinj
  rw [← hX, hrange, hcard] at this
  exact this

theorem card_B₂_dvd (h : T6Ctx N u p) :
    Nat.card ↥(Subgroup.normalizer (N.X₂ : Set G) ⊓ N.K₂) ∣ N.q₂ * (N.q₂ - 1) := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
  have := t6_card_normalizer_dvd hinj
  rw [← hX, hrange, hcard] at this
  exact this

theorem X₁_pGroup (h : T6Ctx N u p) : IsPGroup p ↥N.X₁ := by
  obtain ⟨m, hm⟩ := h.q₁_pow
  exact IsPGroup.of_card (n := m) (by rw [h.sec5.loc.card_X₁, hm])

theorem X₂_pGroup (h : T6Ctx N u p) : IsPGroup p ↥N.X₂ := by
  obtain ⟨n, hn⟩ := h.q₂_pow
  exact IsPGroup.of_card (n := n) (by rw [h.sec5.loc.card_X₂, hn])

theorem X₁_X₂_comm (h : T6Ctx N u p) : ∀ x ∈ N.X₁, ∀ y ∈ N.X₂, x * y = y * x := fun x hx y hy =>
  h.sec5.loc.K_comm x (X₁_le_K₁ h hx) y (X₂_le_K₂ h hy)

theorem Y_inf_K₁ (h : T6Ctx N u p) : (N.X₁ ⊔ N.X₂) ⊓ N.K₁ ≤ N.X₁ := by
  rintro x ⟨hxY, hxK⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm (X₁_X₂_comm h) x).1 hxY
  have hbK₁ : b ∈ N.K₁ := by
    have := N.K₁.mul_mem (N.K₁.inv_mem (X₁_le_K₁ h ha)) hxK
    simpa using this
  rcases t2C_zpowers_cases h.ctx.zz (h.sec5.loc.K_inter ⟨hbK₁, X₂_le_K₂ h hb⟩) with h1 | h1
  · rw [h1, mul_one]; exact ha
  · exact absurd (h1 ▸ hb) (z_not_mem_pGroup h (X₂_pGroup h))

theorem Y_inf_K₂ (h : T6Ctx N u p) : (N.X₁ ⊔ N.X₂) ⊓ N.K₂ ≤ N.X₂ := by
  rintro x ⟨hxY, hxK⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm (X₁_X₂_comm h) x).1 hxY
  have haK₂ : a ∈ N.K₂ := by
    have := N.K₂.mul_mem hxK (N.K₂.inv_mem (X₂_le_K₂ h hb))
    simpa using this
  rcases t2C_zpowers_cases h.ctx.zz (h.sec5.loc.K_inter ⟨X₁_le_K₁ h ha, haK₂⟩) with h1 | h1
  · rw [h1, one_mul]; exact hb
  · exact absurd (h1 ▸ ha) (z_not_mem_pGroup h (X₁_pGroup h))

theorem NK_decomp (h : T6Ctx N u p) {e : G} (heK : e ∈ N.K₁ ⊔ N.K₂)
    (heN : e ∈ Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G)) :
    ∃ k₁ ∈ Subgroup.normalizer (N.X₁ : Set G) ⊓ N.K₁,
      ∃ k₂ ∈ Subgroup.normalizer (N.X₂ : Set G) ⊓ N.K₂, e = k₁ * k₂ := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_comm h.sec5.loc.K_comm e).1 heK
  have hcomm₁ : ∀ x ∈ N.X₁, k₂ * x = x * k₂ := fun x hx =>
    h.sec5.loc.K_comm x (X₁_le_K₁ h hx) k₂ hk₂ |>.symm
  have hcomm₂ : ∀ x ∈ N.X₂, k₁ * x = x * k₁ := fun x hx =>
    h.sec5.loc.K_comm k₁ hk₁ x (X₂_le_K₂ h hx)
  refine ⟨k₁, ⟨?_, hk₁⟩, k₂, ⟨?_, hk₂⟩, rfl⟩
  · apply Subgroup.mem_normalizer_fintype
    intro x hx
    have h1 : k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * x * k₁⁻¹ := by
      calc k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * (k₂ * x) * k₂⁻¹ * k₁⁻¹ := by group
        _ = k₁ * (x * k₂) * k₂⁻¹ * k₁⁻¹ := by rw [hcomm₁ x hx]
        _ = k₁ * x * k₁⁻¹ := by group
    have h2 : k₁ * x * k₁⁻¹ ∈ N.X₁ ⊔ N.X₂ := by
      rw [← h1]
      exact (Subgroup.mem_normalizer_iff.1 heN x).1 (Subgroup.mem_sup_left hx)
    have h3 : k₁ * x * k₁⁻¹ ∈ N.K₁ :=
      N.K₁.mul_mem (N.K₁.mul_mem hk₁ (X₁_le_K₁ h hx)) (N.K₁.inv_mem hk₁)
    exact Y_inf_K₁ h ⟨h2, h3⟩
  · apply Subgroup.mem_normalizer_fintype
    intro x hx
    have h1 : k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₂ * x * k₂⁻¹ := by
      calc k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * (k₂ * x * k₂⁻¹) * k₁⁻¹ := by group
        _ = (k₂ * x * k₂⁻¹) * k₁ * k₁⁻¹ := by
            rw [show k₁ * (k₂ * x * k₂⁻¹) = (k₂ * x * k₂⁻¹) * k₁ from
              h.sec5.loc.K_comm k₁ hk₁ _ (N.K₂.mul_mem (N.K₂.mul_mem hk₂ (X₂_le_K₂ h hx)) (N.K₂.inv_mem hk₂))]
        _ = k₂ * x * k₂⁻¹ := by group
    have h2 : k₂ * x * k₂⁻¹ ∈ N.X₁ ⊔ N.X₂ := by
      rw [← h1]
      exact (Subgroup.mem_normalizer_iff.1 heN x).1 (Subgroup.mem_sup_right hx)
    have h3 : k₂ * x * k₂⁻¹ ∈ N.K₂ :=
      N.K₂.mul_mem (N.K₂.mul_mem hk₂ (X₂_le_K₂ h hx)) (N.K₂.inv_mem hk₂)
    exact Y_inf_K₂ h ⟨h2, h3⟩

theorem two_mul_card_NK_dvd (h : T6Ctx N u p) :
    2 * Nat.card ↥(Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓ (N.K₁ ⊔ N.K₂)) ∣
      Nat.card ↥(Subgroup.normalizer (N.X₁ : Set G) ⊓ N.K₁) *
        Nat.card ↥(Subgroup.normalizer (N.X₂ : Set G) ⊓ N.K₂) := by
  set B₁ : Subgroup G := Subgroup.normalizer (N.X₁ : Set G) ⊓ N.K₁ with hB₁
  set B₂ : Subgroup G := Subgroup.normalizer (N.X₂ : Set G) ⊓ N.K₂ with hB₂
  set NK : Subgroup G :=
    Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓ (N.K₁ ⊔ N.K₂) with hNK
  have hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a := fun a ha b hb =>
    h.sec5.loc.K_comm a ha.2 b hb.2
  let ψ : ↥B₁ × ↥B₂ →* G :=
    MonoidHom.noncommCoprod B₁.subtype B₂.subtype (fun a b => hcomm a a.2 b b.2)
  have hψ : ∀ a b, ψ (a, b) = (a : G) * b := fun _ _ => rfl
  have hNKle : NK ≤ ψ.range := by
    intro e he
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := NK_decomp h he.2 he.1
    exact ⟨(⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩), by rw [hψ]⟩
  have h1 : Nat.card ↥NK ∣ Nat.card ↥ψ.range := Subgroup.card_dvd_of_le hNKle
  have h2 : Nat.card (↥B₁ × ↥B₂) = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hzB₁ : N.z ∈ B₁ := by
    refine ⟨Subgroup.mem_normalizer_fintype (fun n hn => ?_), h.sec5.loc.z_mem_K₁⟩
    have := z_cent_X₁ h hn
    rw [show N.z * n * N.z⁻¹ = n by rw [← this]; group]
    exact hn
  have hzB₂ : N.z ∈ B₂ := by
    refine ⟨Subgroup.mem_normalizer_fintype (fun n hn => ?_), h.sec5.loc.z_mem_K₂⟩
    have := z_cent_X₂ h hn
    rw [show N.z * n * N.z⁻¹ = n by rw [← this]; group]
    exact hn
  have hz2 := h.ctx.zz
  let kz : ↥ψ.ker := ⟨(⟨N.z, hzB₁⟩, ⟨N.z, hzB₂⟩), by
    rw [MonoidHom.mem_ker, hψ]
    exact hz2⟩
  have hkz1 : kz ≠ 1 := by
    intro hk
    apply h.ctx.z_ne
    have := congrArg (fun x : ↥ψ.ker => ((x : ↥B₁ × ↥B₂).1 : ↥B₁)) hk
    simpa [kz] using congrArg Subtype.val this
  have hkz2 : kz ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hz2
    · apply Subtype.ext
      exact hz2
  have hord : orderOf kz = 2 := orderOf_eq_prime hkz2 hkz1
  have h3 : 2 ∣ Nat.card ↥ψ.ker := hord ▸ orderOf_dvd_natCard kz
  have h4 : Nat.card (↥B₁ × ↥B₂) = Nat.card ↥B₁ * Nat.card ↥B₂ := Nat.card_prod _ _
  rw [← h4, h2, mul_comm (Nat.card ↥ψ.range)]
  exact Nat.mul_dvd_mul h3 h1

theorem twoadic_NK (h : T6Ctx N u p) :
    (Nat.card ↥(Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓ (N.K₁ ⊔ N.K₂))).factorization 2
        + 1 ≤ (N.q₁ - 1).factorization 2 + (N.q₂ - 1).factorization 2 := by
  have hd := (two_mul_card_NK_dvd h).trans (mul_dvd_mul (card_B₁_dvd h) (card_B₂_dvd h))
  have hq₁ := h.sec5.loc.q₁_ge
  have hq₂ := h.sec5.loc.q₂_ge
  have ho₁ : ¬ 2 ∣ N.q₁ := h.sec5.loc.q₁_odd.not_two_dvd_nat
  have ho₂ : ¬ 2 ∣ N.q₂ := h.sec5.loc.q₂_odd.not_two_dvd_nat
  have hpos := Nat.card_pos (α := ↥(Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓
    (N.K₁ ⊔ N.K₂)))
  have h1 := (Nat.factorization_le_iff_dvd (by positivity)
    (by have : 0 < N.q₁ * (N.q₁ - 1) * (N.q₂ * (N.q₂ - 1)) := by
          apply Nat.mul_pos <;> apply Nat.mul_pos <;> omega
        exact this.ne')).2 hd 2
  rw [Nat.factorization_mul (by norm_num) hpos.ne', Finsupp.add_apply,
    Nat.factorization_mul (Nat.mul_pos (by omega) (by omega)).ne'
      (Nat.mul_pos (by omega) (by omega)).ne', Finsupp.add_apply,
    Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ho₁, Nat.factorization_eq_zero_of_not_dvd ho₂,
    Nat.Prime.factorization_self Nat.prime_two] at h1
  omega

theorem S_norm_K (h : T6Ctx N u p) {s : G} (hs : s ∈ N.S) :
    ∀ x ∈ N.K₁ ⊔ N.K₂, s * x * s⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
  obtain ⟨h1, h2⟩ := h.Cnorm s (h.sec5.loc.z_cent_S s hs)
  exact t6_norm_sup h1 h2

theorem card_dvd_two_mul_inf_K (h : T6Ctx N u p) {E : Subgroup G}
    (hE : ∀ e ∈ E, e ∈ N.K₁ ⊔ N.K₂ ⊔ N.S) :
    Nat.card ↥E ∣ 2 * Nat.card ↥(E ⊓ (N.K₁ ⊔ N.K₂)) := by
  have hSn : N.S ≤ Subgroup.normalizer ((N.K₁ ⊔ N.K₂ : Subgroup G) : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype (S_norm_K h hs)
  obtain ⟨a, haS, ha⟩ := (Subgroup.relIndex_eq_two_iff.1 h.sec5.loc.S_idx)
  have key : ∀ e ∈ E, e ∉ N.K₁ ⊔ N.K₂ → ∀ e' ∈ E, e' ∉ N.K₁ ⊔ N.K₂ → e' * e⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
    intro e he heK e' he' he'K
    obtain ⟨k, hk, s, hs, rfl⟩ := t6_mem_sup_of_le_normalizer hSn (hE e he)
    obtain ⟨k', hk', s', hs', rfl⟩ := t6_mem_sup_of_le_normalizer hSn (hE e' he')
    have hsK : s ∉ N.S ⊓ (N.K₁ ⊔ N.K₂) := fun hh =>
      heK (Subgroup.mul_mem _ hk hh.2)
    have hs'K : s' ∉ N.S ⊓ (N.K₁ ⊔ N.K₂) := fun hh =>
      he'K (Subgroup.mul_mem _ hk' hh.2)
    have h1 : s * a ∈ N.S ⊓ (N.K₁ ⊔ N.K₂) := by
      rcases ha s hs with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hx
      · exact absurd hx hsK
    have h1' : s' * a ∈ N.S ⊓ (N.K₁ ⊔ N.K₂) := by
      rcases ha s' hs' with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hx
      · exact absurd hx hs'K
    have hss : s' * s⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
      have := (N.S ⊓ (N.K₁ ⊔ N.K₂)).mul_mem h1' ((N.S ⊓ (N.K₁ ⊔ N.K₂)).inv_mem h1)
      have e : s' * a * (s * a)⁻¹ = s' * s⁻¹ := by group
      rw [e] at this
      exact this.2
    have e : k' * s' * (k * s)⁻¹ = k' * (s' * s⁻¹) * k⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk' hss) (Subgroup.inv_mem _ hk)
  have hrel : (N.K₁ ⊔ N.K₂).relIndex E ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hall : ∀ e ∈ E, e ∈ N.K₁ ⊔ N.K₂
    · exact ⟨1, E.one_mem, fun b hb => Or.inr (hall b hb)⟩
    · push Not at hall
      obtain ⟨e₀, he₀, he₀K⟩ := hall
      refine ⟨e₀⁻¹, E.inv_mem he₀, fun b hb => ?_⟩
      by_cases hbK : b ∈ N.K₁ ⊔ N.K₂
      · exact Or.inr hbK
      · exact Or.inl (key e₀ he₀ he₀K b hb hbK)
  have hmul := Subgroup.relIndex_mul_card (N.K₁ ⊔ N.K₂) E
  rw [inf_comm] at hmul
  rw [← hmul]
  exact Nat.mul_dvd_mul_right hrel _

theorem X₁_sup_X₂_le_K (h : T6Ctx N u p) : N.X₁ ⊔ N.X₂ ≤ N.K₁ ⊔ N.K₂ :=
  sup_le_sup (X₁_le_K₁ h) (X₂_le_K₂ h)

theorem F_norm_X₁X₂ (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) :
    ∀ x ∈ N.X₁ ⊔ N.X₂, f * x * f⁻¹ ∈ N.X₁ ⊔ N.X₂ :=
  t6_norm_sup (fun x hx => h.sec5.F5.F_normX₁ f hf x hx) (fun x hx => h.sec5.F5.F_normX₂ f hf x hx)

theorem Y_inf_K (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    (N.X₁ ⊔ N.X₂ ⊔ P₀) ⊓ (N.K₁ ⊔ N.K₂) ≤ N.X₁ ⊔ N.X₂ := by
  rintro y ⟨hyY, hyK⟩
  have hnorm : P₀ ≤ Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype (fun x hx => F_norm_X₁X₂ h (hP₀F hf) x hx)
  obtain ⟨a, ha, f, hf, rfl⟩ := t6_mem_sup_of_le_normalizer hnorm hyY
  have haK : a ∈ N.K₁ ⊔ N.K₂ := X₁_sup_X₂_le_K h ha
  have hfK : f ∈ N.K₁ ⊔ N.K₂ := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haK) hyK
    simpa using this
  have h1 : f ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨hP₀F hf, hfK⟩
  rw [h.sec5.F5.F_inter_K, Subgroup.mem_bot] at h1
  rw [h1, mul_one]
  exact ha

theorem card_two_sub_le (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer ({N.z} : Set G)) (hE2 : IsPGroup 2 ↥E)
    (hEN : ∀ e ∈ E, ∀ y ∈ N.X₁ ⊔ N.X₂ ⊔ P₀, e * y * e⁻¹ ∈ N.X₁ ⊔ N.X₂ ⊔ P₀) :
    Nat.card ↥E ≤ 2 ^ ((N.q₁ - 1).factorization 2 + (N.q₂ - 1).factorization 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEC₁ : ∀ e ∈ E, e ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    intro e he
    obtain ⟨k, hk⟩ := hE2 ⟨e, he⟩
    exact h.C_two e (Subgroup.mem_centralizer_singleton_iff.1 (hEC he))
      ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hdvd1 := card_dvd_two_mul_inf_K h hEC₁
  have hEK : E ⊓ (N.K₁ ⊔ N.K₂) ≤
      Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓ (N.K₁ ⊔ N.K₂) := by
    rintro e ⟨heE, heK⟩
    refine ⟨Subgroup.mem_normalizer_fintype (fun y hy => ?_), heK⟩
    have h1 := hEN e heE y (Subgroup.mem_sup_left hy)
    have hyK : y ∈ N.K₁ ⊔ N.K₂ := X₁_sup_X₂_le_K h hy
    have h2 : e * y * e⁻¹ ∈ N.K₁ ⊔ N.K₂ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ heK hyK) (Subgroup.inv_mem _ heK)
    exact Y_inf_K h hP₀F ⟨h1, h2⟩
  have hdvd2 := Subgroup.card_dvd_of_le hEK
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have h3 : 2 ^ n ∣ 2 * Nat.card ↥(Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓
      (N.K₁ ⊔ N.K₂)) := by
    rw [← hn]
    exact hdvd1.trans (Nat.mul_dvd_mul_left 2 hdvd2)
  have hpos := Nat.card_pos (α := ↥(Subgroup.normalizer ((N.X₁ ⊔ N.X₂ : Subgroup G) : Set G) ⊓
    (N.K₁ ⊔ N.K₂)))
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (Nat.mul_pos (by norm_num) hpos).ne').1 h3
  rw [Nat.factorization_mul (by norm_num) hpos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at h4
  have h5 := twoadic_NK h
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.GH74.GLS.Stage4.Rest.T6
