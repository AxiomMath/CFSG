module

public import CFSG.LargeExtraspecial.S11MaKey

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

omit [Finite G] in
theorem Qa_inf_Qa_inf_Qa_eq_map (u k₁ k₂ : G) :
    S.Qa u ⊓ S.Qa k₁ ⊓ S.Qa k₂ =
      (S.QG ⊓ S.Qa (u⁻¹ * k₁) ⊓ S.Qa (u⁻¹ * k₂)).map (MulAut.conj u).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, ← S.Qa_mul, ← S.Qa_mul,
    mul_inv_cancel_left, mul_inv_cancel_left, ← S.Qa_eq_map]

theorem Hyp.isLagrangian_clSub (hy : Hyp S g) {k : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) :
    (toQuadForm S.q S.q_nondegenerate).IsLagrangian (S.clSub (S.QG ⊓ S.Qa k)) := by
  refine ⟨fun w hw => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hkz hw, ?_⟩
  have h1 := S.finrank_clSub_QG_inf_Qa hkQ hkz (hy.cons_of hkQ hkz).card_QG_inf_Qa
  have h2 := S.finrank_Qt_eq_two_mul_width
  omega

theorem Conf.dual_base_of_mem (K : Conf S g t τ u) {k : G}
    (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    (u⁻¹ * k) * S.z * (u⁻¹ * k)⁻¹ ∈ S.QG ∧ (u⁻¹ * k) * S.z * (u⁻¹ * k)⁻¹ ≠ S.z := by
  refine ⟨by rw [inv_mul_conj_z]; exact (S11.mem_Qa_iff S u _).mp hk.2, ?_⟩
  rw [inv_mul_conj_z]
  intro h
  apply K.not_mem_QG
  rw [K.conj_eq, show u * S.z * u⁻¹ = k * S.z * k⁻¹ by
    calc u * S.z * u⁻¹ = u * (u⁻¹ * (k * S.z * k⁻¹) * u) * u⁻¹ := by rw [h]
      _ = k * S.z * k⁻¹ := by group]
  exact hk.1

theorem Conf.key_relation (hy : Hyp S g) (K : Conf S g t τ u) {k₁ k₂ : G}
    (hk₁ : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u) (hk₂ : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u)
    (hne : k₁ * S.z * k₁⁻¹ ≠ k₂ * S.z * k₂⁻¹) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa k₁) ⊓ S.clSub (S.QG ⊓ S.Qa k₂)) +
        finrank (ZMod 2)
          ↥(S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k₁)) ⊓ S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k₂))) =
      S.width + finrank (ZMod 2) (Vt S g t) - 1 := by
  obtain ⟨hk₁z, -⟩ := K.base_of_mem hk₁
  obtain ⟨hk₂z, -⟩ := K.base_of_mem hk₂
  obtain ⟨hd₁Q, hd₁z⟩ := K.dual_base_of_mem hk₁
  obtain ⟨hd₂Q, hd₂z⟩ := K.dual_base_of_mem hk₂
  have h1 := card_QG_inf_Qa_inf_Qa hk₁.1 hk₁z hk₂.1 hk₂z
  have h2 := card_QG_inf_Qa_inf_Qa hd₁Q hd₁z hd₂Q hd₂z
  have h3 := K.card_mul_card hy hk₁ hk₂ hne
  rw [Qa_inf_Qa_inf_Qa_eq_map u k₁ k₂,
    Subgroup.card_map_of_injective (MulAut.conj u).injective, h1, h2, ← pow_add] at h3
  have h4 := Nat.pow_right_injective le_rfl h3
  omega

theorem odd_of_parity {n m d₁ d₂ d₃ e₁ e₂ e₃ : ℕ} (h₁ : d₁ ≤ n) (h₂ : d₂ ≤ n) (h₃ : d₃ ≤ n)
    (h₁' : e₁ ≤ n) (h₂' : e₂ ≤ n) (h₃' : e₃ ≤ n) (r₁ : d₁ + e₁ = n + m - 1)
    (r₂ : d₂ + e₂ = n + m - 1) (r₃ : d₃ + e₃ = n + m - 1)
    (hd : Even ((n - d₁) + (n - d₂) + (n - d₃))) (he : Even ((n - e₁) + (n - e₂) + (n - e₃)))
    (hm : 2 ≤ m) : Odd (n + m) := by
  rw [Nat.even_iff] at hd he
  rw [Nat.odd_iff]
  omega

theorem Conf.odd_width_add_finrank (hy : Hyp S g) (K : Conf S g t τ u) :
    Odd (S.width + finrank (ZMod 2) (Vt S g t)) := by
  have haE : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa u := ⟨hy.hyp4.conj_mem, K.mem_Qa⟩
  obtain ⟨k, hkE, hks⟩ := K.exists_base_ne hy
  have hab : g * S.z * g⁻¹ ≠ k * S.z * k⁻¹ := fun h => hks (by
    rw [← h]
    exact Submodule.mem_span_singleton_self _)
  have hcE : g * S.z * g⁻¹ * (k * S.z * k⁻¹) ∈ S.QG ⊓ S.Qa u := mul_mem haE hkE
  have hc1 : g * S.z * g⁻¹ * (k * S.z * k⁻¹) ≠ 1 := fun h => hab
    ((inv_eq_of_mul_eq_one_right (conj_z_mul_self S g)).symm.trans
      (inv_eq_of_mul_eq_one_right h))
  obtain ⟨j, hj⟩ := K.exists_conj hy hcE hc1
  have hjE : j * S.z * j⁻¹ ∈ S.QG ⊓ S.Qa u := hj ▸ hcE
  have hbc : k * S.z * k⁻¹ ≠ j * S.z * j⁻¹ := by
    rw [hj]
    intro h
    apply conj_z_ne_one S g
    calc g * S.z * g⁻¹ = g * S.z * g⁻¹ * (k * S.z * k⁻¹) * (k * S.z * k⁻¹)⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel]
  have hac : g * S.z * g⁻¹ ≠ j * S.z * j⁻¹ := by
    rw [hj]
    intro h
    apply conj_z_ne_one S k
    calc k * S.z * k⁻¹ = (g * S.z * g⁻¹)⁻¹ * (g * S.z * g⁻¹ * (k * S.z * k⁻¹)) := by group
      _ = 1 := by rw [← h, inv_mul_cancel]
  have r1 := K.key_relation hy haE hkE hab
  have r2 := K.key_relation hy hkE hjE hbc
  have r3 := K.key_relation hy haE hjE hac
  have La := hy.isLagrangian_clSub haE.1 (K.base_of_mem haE).1
  have Lb := hy.isLagrangian_clSub hkE.1 (K.base_of_mem hkE).1
  have Lc := hy.isLagrangian_clSub hjE.1 (K.base_of_mem hjE).1
  have La' := hy.isLagrangian_clSub (K.dual_base_of_mem haE).1 (K.dual_base_of_mem haE).2
  have Lb' := hy.isLagrangian_clSub (K.dual_base_of_mem hkE).1 (K.dual_base_of_mem hkE).2
  have Lc' := hy.isLagrangian_clSub (K.dual_base_of_mem hjE).1 (K.dual_base_of_mem hjE).2
  have hQt := S.finrank_Qt_eq_two_mul_width
  have e1 := La.even_add_add hQt Lb Lc
  have e2 := La'.even_add_add hQt Lb' Lc'
  have b1 := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa g) ⊓
    S.clSub (S.QG ⊓ S.Qa k) ≤ S.clSub (S.QG ⊓ S.Qa g))
  have b2 := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa k) ⊓
    S.clSub (S.QG ⊓ S.Qa j) ≤ S.clSub (S.QG ⊓ S.Qa k))
  have b3 := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa g) ⊓
    S.clSub (S.QG ⊓ S.Qa j) ≤ S.clSub (S.QG ⊓ S.Qa g))
  have b1' := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa (u⁻¹ * g)) ⊓
    S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k)) ≤ S.clSub (S.QG ⊓ S.Qa (u⁻¹ * g)))
  have b2' := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k)) ⊓
    S.clSub (S.QG ⊓ S.Qa (u⁻¹ * j)) ≤ S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k)))
  have b3' := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa (u⁻¹ * g)) ⊓
    S.clSub (S.QG ⊓ S.Qa (u⁻¹ * j)) ≤ S.clSub (S.QG ⊓ S.Qa (u⁻¹ * g)))
  have da : 2 * finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = 2 * S.width := La.2.trans hQt
  have db : 2 * finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa k)) = 2 * S.width := Lb.2.trans hQt
  have da' : 2 * finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa (u⁻¹ * g))) = 2 * S.width :=
    La'.2.trans hQt
  have db' : 2 * finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa (u⁻¹ * k))) = 2 * S.width :=
    Lb'.2.trans hQt
  have fa := (Nat.eq_of_mul_eq_mul_left two_pos da).le
  have fb := (Nat.eq_of_mul_eq_mul_left two_pos db).le
  have fa' := (Nat.eq_of_mul_eq_mul_left two_pos da').le
  have fb' := (Nat.eq_of_mul_eq_mul_left two_pos db').le
  exact odd_of_parity (b1.trans fa) (b2.trans fb) (b3.trans fa) (b1'.trans fa') (b2'.trans fb')
    (b3'.trans fa') r1 r2 r3 e1 e2 K.lin.two_le_finrank

theorem Conf.finrank_ne_two_of_even_width (hy : Hyp S g) (K : Conf S g t τ u)
    (hn : Even S.width) : finrank (ZMod 2) (Vt S g t) ≠ 2 := by
  intro hm
  have h := K.odd_width_add_finrank hy
  rw [hm] at h
  obtain ⟨r, hr⟩ := hn
  obtain ⟨s, hs⟩ := h
  omega

end CFSG.LargeExtraspecial.S11
