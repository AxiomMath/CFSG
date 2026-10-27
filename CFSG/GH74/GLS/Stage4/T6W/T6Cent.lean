module

public import CFSG.GH74.GLS.Stage4.T6W.T6Basic
public import CFSG.GH74.GLS.Stage4.T6W.T6Irr

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6W

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

theorem t6_cent_uSub {F : Type} [Field F] (g : SL2 F) (hg : ∀ c : F, g * sl2U c = sl2U c * g) :
    ∃ s : F, g = sl2U s ∨ g = negOne F * sl2U s := by
  obtain ⟨a, b, c, d, hgm⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two _⟩
  have h := hg 1
  have e00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hgm] at e00 e01
  simp [sl2U] at e00 e01
  have hdet := g.2
  rw [Matrix.det_fin_two, hgm] at hdet
  simp at hdet
  have hc : c = 0 := e00
  have hd : d = a := by linear_combination -e01
  subst hc hd
  have ha : (d - 1) * (d + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 ha with h1 | h1
  · refine ⟨b, Or.inl ?_⟩
    have : d = 1 := by linear_combination h1
    subst this
    apply Subtype.ext
    rw [hgm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2U]
  · refine ⟨-b, Or.inr ?_⟩
    have : d = -1 := by linear_combination h1
    subst this
    apply Subtype.ext
    rw [hgm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> simp [sl2U, negOne]

section CentX₂

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem Cent_K₂_X₂ (h : T6CtxW N u p) :
    ∀ k ∈ N.K₂, (∀ x ∈ N.X₂, k * x = x * k) → k ∈ N.X₂ ∨ k * N.z ∈ N.X₂ := by
  intro k hk hc
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
  have hkr := hk
  rw [← hrange] at hkr
  obtain ⟨g, rfl⟩ := hkr
  have hg : ∀ c : F, g * sl2U c = sl2U c * g := by
    intro c
    apply hinj
    rw [map_mul, map_mul]
    exact hc _ (hX ▸ Subgroup.mem_map_of_mem φ (sl2U_mem_uSub c))
  obtain ⟨s, hs | hs⟩ := t6_cent_uSub g hg
  · left
    rw [hs, hX]
    exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub s)
  · right
    have hsX : φ (sl2U s) ∈ N.X₂ := by rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub s)
    have hsK : φ (sl2U s) ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hsX
    have hzs : φ (sl2U s) * N.z = N.z * φ (sl2U s) := h.ctx.C.zc₂ _ hsK
    have hzz := h.ctx.zz
    have : φ g * N.z = φ (sl2U s) := by
      rw [hs, map_mul, hz]
      calc N.z * φ (sl2U s) * N.z = N.z * (φ (sl2U s) * N.z) := by group
        _ = N.z * (N.z * φ (sl2U s)) := by rw [hzs]
        _ = (N.z * N.z) * φ (sl2U s) := by group
        _ = φ (sl2U s) := by rw [hzz, one_mul]
    rw [this]; exact hsX

theorem two_cent_X₂_mem_K (h : T6CtxW N u p) {d : G} (hdz : d * N.z = N.z * d)
    (hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1) (hdX : ∀ x ∈ N.X₂, d * x * d⁻¹ = x) : d ∈ N.K₁ ⊔ N.K₂ := by
  by_contra hdK
  have hd₁ := h.C_two d hdz hd2
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.sec5.loc.q₂_odd
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; exact h.sec5.loc.q₂_ge
  have hdK₂ : ∀ g ∈ φ.range, d * g * d⁻¹ ∈ φ.range := by
    rw [hrange]; exact (h.Cnorm d hdz).2
  have hdXφ : ∀ c : F, d * φ (sl2U c) * d⁻¹ = φ (sl2U c) := by
    intro c
    apply hdX
    rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub c)
  obtain ⟨s, hs⟩ := t6_aut_X hinj hodd h3 hdK₂ hdXφ
  have hx₀X : φ (sl2U s) ∈ N.X₂ := by rw [hX]; exact Subgroup.mem_map_of_mem φ (sl2U_mem_uSub s)
  have hx₀K₂ : φ (sl2U s) ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hx₀X
  have hx₀K : φ (sl2U s) ∈ N.K₁ ⊔ N.K₂ := Subgroup.mem_sup_right hx₀K₂
  have hcent : ∀ k ∈ N.K₂, ((φ (sl2U s))⁻¹ * d) * k = k * ((φ (sl2U s))⁻¹ * d) := by
    intro k hk
    rw [← hrange] at hk
    obtain ⟨g, rfl⟩ := hk
    have h1 := hs g
    calc (φ (sl2U s))⁻¹ * d * φ g = (φ (sl2U s))⁻¹ * (d * φ g * d⁻¹) * d := by group
      _ = (φ (sl2U s))⁻¹ * (φ (sl2U s) * φ g * (φ (sl2U s))⁻¹) * d := by rw [h1]
      _ = φ g * ((φ (sl2U s))⁻¹ * d) := by group
  have hd'C₁ : (φ (sl2U s))⁻¹ * d ∈ N.K₁ ⊔ N.K₂ ⊔ N.S :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hx₀K)) hd₁
  have hd'K : (φ (sl2U s))⁻¹ * d ∉ N.K₁ ⊔ N.K₂ := by
    intro hmem
    apply hdK
    have : d = φ (sl2U s) * ((φ (sl2U s))⁻¹ * d) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx₀K hmem
  exact h.outer₂ _ hd'C₁ hd'K hcent

theorem t6_sylow_max {K T Q : Subgroup G} (hT : IsPGroup 2 ↥T) (hTidx : ¬ 2 ∣ T.relIndex K)
    (hQ : IsPGroup 2 ↥Q) (hQK : Q ≤ K) (hTQ : T ≤ Q) : Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex T Q K hTQ hQK
  have hodd : ¬ 2 ∣ T.relIndex Q := fun hd => hTidx (hd.trans (hmul ▸ dvd_mul_right _ _))
  have hcard : T.relIndex Q * Nat.card ↥T = Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card T Q
    rwa [inf_eq_left.2 hTQ] at this
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  rw [ha, hb] at hcard
  have hdvd : T.relIndex Q ∣ 2 ^ a := ⟨_, by rw [← hcard]⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    apply hodd
    rw [hi]
    exact dvd_pow_self 2 hne
  rw [hi0, pow_zero] at hi
  have : Q ≤ T := Subgroup.relIndex_eq_one.1 hi
  exact le_antisymm this hTQ

theorem Sylow2_C₂ (h : T6CtxW N u p) {T₁ : Subgroup G} (hT₁K : T₁ ≤ N.K₁) (hT₁ : IsPGroup 2 ↥T₁)
    (hT₁idx : ¬ 2 ∣ T₁.relIndex N.K₁) (hzT : N.z ∈ T₁) {E : Subgroup G} (hE : IsPGroup 2 ↥E)
    (hEC : ∀ e ∈ E, ∀ x ∈ N.X₂, e * x * e⁻¹ = x) (hTE : T₁ ≤ E) : E = T₁ := by
  have hloc := h.sec5.loc
  have hz2 := h.ctx.zz
  have hpg := R₂_pGroup N h.prime
  have hstep1 : ∀ d ∈ E, N.z * d * N.z⁻¹ = d → d ∈ T₁ := by
    intro d hdE hdz'
    have hdz : d * N.z = N.z * d := by
      calc d * N.z = (N.z * d * N.z⁻¹) * N.z := by rw [hdz']
        _ = N.z * d := by group
    obtain ⟨j, hj⟩ := hE ⟨d, hdE⟩
    have hd2 : d ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hdK := two_cent_X₂_mem_K h hdz ⟨j, hd2⟩ (hEC d hdE)
    obtain ⟨k₁, hk₁, k₂, hk₂, hdk⟩ := (mem_sup_iff_of_comm hloc.K_comm d).1 hdK
    have hk₂c : ∀ x ∈ N.X₂, k₂ * x = x * k₂ := by
      intro x hx
      have hxK : x ∈ N.K₂ := by rw [hloc.K₂_eq]; exact Subgroup.mem_sup_left hx
      have h1 := hEC d hdE x hx
      have h2 : d * x = x * d := by
        calc d * x = (d * x * d⁻¹) * d := by group
          _ = x * d := by rw [h1]
      have h3 : k₁ * x = x * k₁ := hloc.K_comm k₁ hk₁ x hxK
      rw [hdk] at h2
      apply mul_left_cancel (a := k₁)
      calc k₁ * (k₂ * x) = k₁ * k₂ * x := by group
        _ = x * (k₁ * k₂) := h2
        _ = (x * k₁) * k₂ := by group
        _ = (k₁ * x) * k₂ := by rw [h3]
        _ = k₁ * (x * k₂) := by group
    obtain ⟨k, hkK, x, hxX, hdkx⟩ : ∃ k ∈ N.K₁, ∃ x ∈ N.X₂, d = k * x := by
      rcases Cent_K₂_X₂ h k₂ hk₂ hk₂c with h1 | h1
      · exact ⟨k₁, hk₁, k₂, h1, hdk⟩
      · refine ⟨k₁ * N.z, N.K₁.mul_mem hk₁ hloc.z_mem_K₁, k₂ * N.z, h1, ?_⟩
        have hzk₂ : N.z * k₂ = k₂ * N.z := (h.ctx.C.zc₂ k₂ hk₂).symm
        calc d = k₁ * k₂ := hdk
          _ = k₁ * k₂ * (N.z * N.z) := by rw [hz2, mul_one]
          _ = k₁ * (N.z * k₂) * N.z := by
            calc k₁ * k₂ * (N.z * N.z) = k₁ * (k₂ * N.z) * N.z := by group
              _ = k₁ * (N.z * k₂) * N.z := by rw [hzk₂]
          _ = k₁ * N.z * (k₂ * N.z) := by group
    have hxK₂ : x ∈ N.K₂ := by rw [hloc.K₂_eq]; exact Subgroup.mem_sup_left hxX
    have hcomm : Commute k x := hloc.K_comm k hkK x hxK₂
    have hxpow : x ^ (2 ^ j) = (k ^ (2 ^ j))⁻¹ := by
      have : k ^ (2 ^ j) * x ^ (2 ^ j) = 1 := by rw [← hcomm.mul_pow, ← hdkx, hd2]
      exact eq_inv_of_mul_eq_one_right this
    have hxK₁ : x ^ (2 ^ j) ∈ N.K₁ := by
      rw [hxpow]; exact N.K₁.inv_mem (N.K₁.pow_mem hkK _)
    have hxz : x ^ (2 ^ j) ∈ Subgroup.zpowers N.z :=
      hloc.K_inter ⟨hxK₁, N.K₂.pow_mem hxK₂ _⟩
    have hx1 : x = 1 := by
      have hxodd : Odd (orderOf x) := t6_odd_of_pGroup h.prime h.p_ne_two hpg (X₂_le_R₂ h hxX)
      have hxp : Odd (orderOf (x ^ (2 ^ j))) :=
        Odd.of_dvd_nat hxodd (orderOf_pow_dvd _)
      have hxp1 : x ^ (2 ^ j) = 1 := by
        rcases t2C_zpowers_cases hz2 hxz with h1 | h1
        · exact h1
        · exfalso
          rw [h1, hloc.z_ord] at hxp
          exact absurd hxp (by decide)
      have hdvd : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hxp1
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0, pow_zero] at hi; exact orderOf_eq_one_iff.1 hi
      · exfalso
        rw [hi] at hxodd
        exact (Nat.not_even_iff_odd.2 hxodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
    rw [hx1, mul_one] at hdkx
    have hQ : E ⊓ N.K₁ = T₁ :=
      t6_sylow_max hT₁ hT₁idx (hE.to_le inf_le_left) inf_le_right (le_inf hTE hT₁K)
    rw [← hQ]
    exact ⟨hdE, hdkx ▸ hkK⟩
  have hzE : N.z ∈ E := hTE hzT
  have : Nontrivial ↥E := ⟨⟨⟨N.z, hzE⟩, 1, fun h' => h.ctx.z_ne (by simpa using congrArg Subtype.val h')⟩⟩
  have : Finite ↥E := inferInstance
  have hbot := (IsPGroup.center_nontrivial (p := 2) hE)
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥E))
  have hcc : ∀ e : ↥E, e * (c : ↥E) = (c : ↥E) * e := fun e => Subgroup.mem_center_iff.1 c.2 e
  set c' : G := ((c : ↥E) : G) with hc'
  have hc'E : c' ∈ E := (c : ↥E).2
  have hcomm' : ∀ e ∈ E, e * c' = c' * e := by
    intro e he
    have := congrArg Subtype.val (hcc ⟨e, he⟩)
    simpa using this
  have hcz : N.z * c' * N.z⁻¹ = c' := by
    calc N.z * c' * N.z⁻¹ = (c' * N.z) * N.z⁻¹ := by rw [hcomm' N.z hzE]
      _ = c' := by group
  have hc'T : c' ∈ T₁ := hstep1 c' hc'E hcz
  have hc'z : c' ∈ Subgroup.zpowers N.z := by
    refine h.sylcent₁ T₁ hT₁ hT₁idx c' (hT₁K hc'T) (fun q hq => ?_)
    exact (hcomm' q (hTE hq)).symm
  have hc'ne : c' ≠ 1 := by
    intro h1
    apply hc1
    exact Subtype.ext (Subtype.ext h1)
  have hc'eq : c' = N.z := by
    rcases t2C_zpowers_cases hz2 hc'z with h1 | h1
    · exact absurd h1 hc'ne
    · exact h1
  have hzcent : ∀ e ∈ E, N.z * e * N.z⁻¹ = e := by
    intro e he
    rw [← hc'eq]
    calc c' * e * c'⁻¹ = (e * c') * c'⁻¹ := by rw [hcomm' e he]
      _ = e := by group
  exact le_antisymm (fun e he => hstep1 e he (hzcent e he)) hTE

end CentX₂

end CFSG.GH74.GLS.Stage4.Rest.T6W
