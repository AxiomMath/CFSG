module

public import CFSG.CGT.Foote81L6.Normalizer.Identify
public import CFSG.CGT.Foote81L6.Normalizer.Transvection
public import CFSG.CGT.Foote81L6.Normalizer.SymFacts

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin Equiv

namespace TvHyp

variable {V X : Type} [CommGroup V] [Finite V] [Group X] [Finite X] {ρ : X →* MulAut V}
  {D : Sylow 2 X} {d₀ d₁ : X}

theorem isSymDirect_of_quotient {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (h : TvHyp ρ D d₀ d₁)
    (φ : X ⧸ pPrimeCore 2 X ≃* Perm (Fin n)) (h₀ : φ (QuotientGroup.mk d₀) = swap 0 1)
    (h₁ : φ (QuotientGroup.mk d₁) = swap 2 3) :
    IsSymDirect d₀ d₁ (φ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hπO : ∀ x : X, π x = 1 ↔ x ∈ O := fun x => QuotientGroup.eq_one_iff x
  set X₀ := Subgroup.normalClosure ({d₀} : Set X) with hX₀
  have hd₀inv : d₀⁻¹ = d₀ := inv_eq_of_mul_eq_one_right h.sq₀
  have hπd₀inv : (π d₀)⁻¹ = π d₀ := by rw [← map_inv, hd₀inv]
  obtain ⟨hc3, hc1, hcinv⟩ := perm_cycle_three (n := n) hn
  set xh : X ⧸ O := φ.symm (swap 0 1 * swap 1 2) with hxh
  have hφd₀ : φ (π d₀) = swap 0 1 := h₀
  have hxh3 : xh ^ 3 = 1 := by rw [hxh, ← map_pow, hc3, map_one]
  have hxh1 : xh ≠ 1 := fun h1 => hc1 (by
    rw [← φ.apply_symm_apply (swap 0 1 * swap 1 2), ← hxh, h1, map_one])
  have hxhinv : π d₀ * xh * (π d₀)⁻¹ = xh⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, hφd₀, hxh, MulEquiv.apply_symm_apply, hcinv]
  set K : Subgroup X := (Subgroup.zpowers xh).comap π with hK
  have hOK : O ≤ K := fun o ho => by
    show π o ∈ Subgroup.zpowers xh
    rw [(hπO o).mpr ho]
    exact Subgroup.one_mem _
  have hKodd : Odd (Nat.card K) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card] at h2
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card 2 h2
    have hk' : orderOf (k : X) = 2 := by rw [Subgroup.orderOf_coe, hk]
    have hk2 : (k : X) ^ 2 = 1 := by rw [← hk']; exact pow_orderOf_eq_one _
    have hpk : π k ∈ Subgroup.zpowers xh := k.2
    have hord3 : orderOf (π k) ∣ 3 :=
      (orderOf_dvd_of_mem_zpowers hpk).trans (orderOf_dvd_of_pow_eq_one hxh3)
    have hord2 : orderOf (π k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk2, map_one])
    have h1 : π k = 1 := by
      have := Nat.dvd_gcd hord3 hord2
      norm_num at this
      exact this
    have hkO : (k : X) ∈ O := (hπO _).mp h1
    have := odd_orderOf_of_mem_pPrimeCore hkO
    rw [hk'] at this
    exact absurd this (by decide)
  have hdK : ∀ k ∈ K, d₀ * k * d₀⁻¹ ∈ K := by
    intro k hk
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    show π (d₀ * k * d₀⁻¹) ∈ Subgroup.zpowers xh
    rw [map_mul, map_mul, map_inv, ← hm]
    have e : π d₀ * xh ^ m * (π d₀)⁻¹ = (π d₀ * xh * (π d₀)⁻¹) ^ m := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e, hxhinv]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers xh)) m
  obtain ⟨x', -, hx'3, -, -, hinvK⟩ :=
    exists_inverted_of_transvection h.sq_eq_one h.injective h.transvection hKodd hdK
  obtain ⟨x, hx⟩ := hπs xh
  have hinv_of : ∀ g : X, d₀ * (g * d₀ * g⁻¹ * d₀) * d₀⁻¹ = (g * d₀ * g⁻¹ * d₀)⁻¹ := by
    intro g
    have e1 : (g * d₀ * g⁻¹ * d₀)⁻¹ = d₀⁻¹ * g * d₀⁻¹ * g⁻¹ := by group
    have e2 : d₀ * (g * d₀ * g⁻¹ * d₀) * d₀⁻¹ = d₀ * g * d₀ * g⁻¹ * (d₀ * d₀⁻¹) := by group
    rw [e1, e2, mul_inv_cancel, mul_one, hd₀inv]
  set y₀ := x * d₀ * x⁻¹ * d₀ with hy₀
  have hπy₀ : π y₀ = xh * xh := by
    have e : π d₀ * xh⁻¹ * (π d₀)⁻¹ = xh := by
      calc π d₀ * xh⁻¹ * (π d₀)⁻¹ = (π d₀ * xh * (π d₀)⁻¹)⁻¹ := by group
        _ = xh := by rw [hxhinv, inv_inv]
    calc π y₀ = xh * (π d₀ * xh⁻¹ * (π d₀)⁻¹) := by
          rw [hy₀, map_mul, map_mul, map_mul, map_inv, hx, hπd₀inv]
          simp only [mul_assoc]
      _ = xh * xh := by rw [e]
  have hy₀K : y₀ ∈ K := by
    show π y₀ ∈ Subgroup.zpowers xh
    rw [hπy₀]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers xh) (Subgroup.mem_zpowers xh)
  have hy₀x' : y₀ ∈ Subgroup.zpowers x' := hinvK y₀ hy₀K (hinv_of x)
  have hy₀O : y₀ ∉ O := by
    intro h1
    rw [← hπO, hπy₀] at h1
    apply hxh1
    calc xh = xh ^ 3 * (xh * xh)⁻¹ := by group
      _ = 1 := by rw [hxh3, h1, inv_one, one_mul]
  have hcomm₀ : ∀ o ∈ O, o * d₀ = d₀ * o := by
    intro o ho
    set c := o * d₀ * o⁻¹ * d₀ with hc
    have hcO : c ∈ O := by
      have h1 : d₀ * o⁻¹ * d₀⁻¹ ∈ O := (inferInstance : O.Normal).conj_mem _ (O.inv_mem ho) d₀
      have e : c = o * (d₀ * o⁻¹ * d₀⁻¹) := by rw [hc, hd₀inv]; group
      rw [e]
      exact O.mul_mem ho h1
    have hcx : c ∈ Subgroup.zpowers x' := hinvK c (hOK hcO) (hinv_of o)
    have hc1 : c = 1 := by
      by_contra hc1
      have hco : orderOf c ∣ 3 :=
        (orderOf_dvd_of_mem_zpowers hcx).trans (orderOf_dvd_of_pow_eq_one hx'3)
      have hc3' : orderOf c = 3 := ((Nat.dvd_prime Nat.prime_three).mp hco).resolve_left
        (fun h1 => hc1 (orderOf_eq_one_iff.mp h1))
      have heq : Subgroup.zpowers c = Subgroup.zpowers x' := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcx)
        rw [Nat.card_zpowers, Nat.card_zpowers, hc3']
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx'3)
      have hy₀c : y₀ ∈ Subgroup.zpowers c := heq ▸ hy₀x'
      exact hy₀O ((Subgroup.zpowers_le.mpr hcO) hy₀c)
    calc o * d₀ = o * d₀ * o⁻¹ * d₀ * (d₀⁻¹ * o) := by group
      _ = d₀⁻¹ * o := by rw [← hc, hc1, one_mul]
      _ = d₀ * o := by rw [hd₀inv]
  have hX₀C : X₀ ≤ Subgroup.centralizer (O : Set X) := by
    apply Subgroup.normalClosure_le_normal
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact hcomm₀
  have hcomm : ∀ a ∈ X₀, ∀ o ∈ O, a * o = o * a := fun a ha o ho =>
    (Subgroup.mem_centralizer_iff.mp (hX₀C ha) o ho).symm
  have hinf : X₀ ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzX₀, hzO⟩
    exact (Subgroup.mem_bot).mpr (eq_one_of_mem_normalClosure_of_commute h.sq_eq_one
      h.injective h.transvection hzX₀ (fun a ha => hcomm a ha z hzO)
      (odd_orderOf_of_mem_pPrimeCore hzO))
  have h01 : (0 : Fin n) ≠ 1 := fin_zero_ne_one_of hn
  have hsup : X₀ ⊔ O = ⊤ := by
    have hmap : X₀.map π = ⊤ := by
      have h1 : (X₀.map π).map φ.toMonoidHom = ⊤ := by
        rw [hX₀, Subgroup.map_normalClosure _ _ hπs,
          Subgroup.map_normalClosure _ _ φ.surjective, Set.image_singleton, Set.image_singleton]
        show Subgroup.normalClosure {φ (π d₀)} = ⊤
        rw [hφd₀]
        exact perm_normalClosure_swap h01
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [h1, Subgroup.map_top_of_surjective _ φ.surjective]
    have := Subgroup.comap_map_eq π X₀
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at this
    exact this.symm
  have hd₁X₀ : d₁ ∈ X₀ := Subgroup.conjugatesOfSet_subset_normalClosure
    (Group.mem_conjugatesOfSet_iff.mpr ⟨d₀, rfl, h.isConj₁⟩)
  refine ⟨φ.surjective.comp hπs, ?_, hφd₀, h₁, hd₁X₀, hinf, hsup, hcomm⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact hπO x

theorem isSymDirect (h : TvHyp ρ D d₀ d₁) (hnc : ¬ HasNormalPComplement 2 X)
    (hHig : HigmanHyp) :
    (∃ φ : X →* Perm (Fin 4), IsSymDirect d₀ d₁ φ) ∨
      (∃ φ : X →* Perm (Fin 5), IsSymDirect d₀ d₁ φ) := by
  obtain ⟨n, hn, ⟨φ⟩⟩ := h.exists_quotient_mulEquiv hnc hHig
  rcases hn with rfl | rfl
  · obtain ⟨φ', h₀, h₁⟩ := h.exists_normalized (Or.inl rfl) φ
    exact Or.inl ⟨_, h.isSymDirect_of_quotient (Or.inl rfl) φ' h₀ h₁⟩
  · obtain ⟨φ', h₀, h₁⟩ := h.exists_normalized (Or.inr rfl) φ
    exact Or.inr ⟨_, h.isSymDirect_of_quotient (Or.inr rfl) φ' h₀ h₁⟩

theorem lemma9 (h : TvHyp ρ D d₀ d₁) (hnc : ¬ HasNormalPComplement 2 X) (hHig : HigmanHyp)
    {P : Subgroup X} (hPodd : Odd (Nat.card P)) (hP₀ : ∀ p ∈ P, p * d₀ = d₀ * p)
    (hP₁ : ∀ p ∈ P, p * d₁ = d₁ * p)
    (hL1 : Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
      Subgroup.centralizer ({d₁} : Set X)) = 1 ∨
      Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
        Subgroup.centralizer ({d₁} : Set X)) = 3) :
    ((∃ φ : X →* Perm (Fin 4), IsSymDirect d₀ d₁ φ) ∨
      (∃ φ : X →* Perm (Fin 5), IsSymDirect d₀ d₁ φ)) ∧
    (Nat.card (pPrimeCore 2 X) = 1 ∨ Nat.card (pPrimeCore 2 X) = 3) ∧
    P ≤ pPrimeCore 2 X ∧ (Nat.card P = 3 → P = pPrimeCore 2 X) := by
  have hS := h.isSymDirect hnc hHig
  have key : (Nat.card (pPrimeCore 2 X) = 1 ∨ Nat.card (pPrimeCore 2 X) = 3) ∧
      P ≤ pPrimeCore 2 X := by
    rcases hS with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
    · exact ⟨hφ.card_pPrimeCore hL1, hφ.le_pPrimeCore_of_commute (Or.inl rfl) hPodd hP₀ hP₁⟩
    · exact ⟨hφ.card_pPrimeCore hL1, hφ.le_pPrimeCore_of_commute (Or.inr rfl) hPodd hP₀ hP₁⟩
  refine ⟨hS, key.1, key.2, fun h3 => ?_⟩
  apply Subgroup.eq_of_le_of_card_ge key.2
  rcases key.1 with h1 | h1 <;> omega

end TvHyp

end CFSG.CGT.Foote81L6.Normalizer
