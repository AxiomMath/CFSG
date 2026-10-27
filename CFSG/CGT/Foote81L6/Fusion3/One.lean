module

public import CFSG.CGT.Foote81L6.Fusion3.Odd
public import CFSG.CGT.Foote81L6.Fusion3.Sylow

public section

namespace CFSG.CGT.Foote81L6.Fusion3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {m n : ℕ}
  (D : FooteCore G (T : Subgroup G) m n)

theorem T_le_normalizer_T₁ : (T : Subgroup G) ≤ normalizer (D.T₁ : Set G) := fun _ hu =>
  TStruct.mem_normalizer_of_forall_conj_mem fun _ hx => D.conj_mem_T₁ hu hx

theorem T_le_normalizer_Zab : (T : Subgroup G) ≤ normalizer (D.Zab : Set G) := fun _ hu =>
  TStruct.mem_normalizer_of_forall_conj_mem fun _ hx => conj_mem_Zab_of_mem_T D hu hx

theorem exists_mem_T_conj_eq_of_normalizer {g : G} (hg : g ∈ normalizer (D.T₁ : Set G)) {x : G}
    (hx : x ∈ D.Zab) (hgx : g * x * g⁻¹ ∈ D.Zab) :
    ∃ u ∈ (T : Subgroup G), u * x * u⁻¹ = g * x * g⁻¹ := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · obtain rfl : m = 2 := le_antisymm (by omega) D.two_le_m
    obtain ⟨α, w, hα, hw, rfl⟩ := (mem_Zab_iff D).1 hx
    rcases hα with rfl | rfl
    ·
      obtain ⟨u, hu, huΩ⟩ := exists_conj_eq_of_odd T (T_le_normalizer_T₁ D)
        (Ω := {y | y = 1 ∨ y = D.b₀ ∨ y = D.b₁ ∨ y = D.b})
        (fun h hh _ hω => conj_mem_Bz D hh hω)
        (fun h hh hodd ω hω => by
          obtain ⟨h₀, h₁⟩ := conj_b₀_b₁_of_odd D hh hodd
          rcases hω with rfl | rfl | rfl | rfl
          · group
          · exact h₀
          · exact h₁
          · show h * (D.b₀ * D.b₁) * h⁻¹ = D.b₀ * D.b₁
            calc h * (D.b₀ * D.b₁) * h⁻¹ = (h * D.b₀ * h⁻¹) * (h * D.b₁ * h⁻¹) := by group
              _ = D.b₀ * D.b₁ := by rw [h₀, h₁]) hg
      exact ⟨u, hu, by rw [one_mul]; exact (huΩ w hw).symm⟩
    ·
      have hgw : g * w * g⁻¹ ∈ D.Zab := mem_Zab_of_Bz D (conj_mem_Bz D hg hw)
      have hga : g * D.a * g⁻¹ ∈ D.Zab := by
        have e : g * D.a * g⁻¹ = (g * (D.a * w) * g⁻¹) * (g * w * g⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          calc g * D.a * g⁻¹ = g * (D.a * (w * w)) * g⁻¹ := by rw [mul_self_of_Bz D hw, mul_one]
            _ = g * (D.a * w) * g⁻¹ * (g * w⁻¹ * g⁻¹) := by
                rw [inv_eq_of_mul_eq_one_right (mul_self_of_Bz D hw)]; group
            _ = _ := by group
        rw [e]
        exact mul_mem hgx (inv_mem hgw)
      have hgN : g ∈ normalizer (D.Zab : Set G) :=
        TStruct.mem_normalizer_of_forall_conj_mem fun _ hz => conj_mem_Zab_of_gen D hga
          (mem_Zab_of_Bz D (conj_mem_Bz D hg (Or.inr (Or.inl rfl))))
          (mem_Zab_of_Bz D (conj_mem_Bz D hg (Or.inr (Or.inr (Or.inl rfl))))) hz
      obtain ⟨u, hu, huΩ⟩ := exists_conj_eq_of_odd T
        (H := normalizer (D.T₁ : Set G) ⊓ normalizer (D.Zab : Set G))
        (le_inf (T_le_normalizer_T₁ D) (T_le_normalizer_Zab D)) (Ω := D.Zab)
        (fun h hh ω hω => (mem_normalizer_iff.1 (mem_inf.1 hh).2 ω).1 hω)
        (fun h hh hodd ω hω => by
          obtain ⟨hh₁, hhZ⟩ := mem_inf.1 hh
          obtain ⟨h₀, h₁⟩ := conj_b₀_b₁_of_odd D hh₁ hodd
          have ha := conj_a_of_odd D hh₁ hodd
            ((mem_normalizer_iff.1 hhZ D.a).1 (subset_closure (Set.mem_insert _ _)))
          exact conj_eq_of_fix D ha h₀ h₁ hω)
        (mem_inf.2 ⟨hg, hgN⟩)
      exact ⟨u, hu, (huΩ _ hx).symm⟩
  · obtain ⟨u, hu, huΩ⟩ := exists_conj_eq_of_odd T (T_le_normalizer_T₁ D) (Ω := D.T₁)
      (fun h hh ω hω => (mem_normalizer_iff.1 hh ω).1 hω)
      (fun h hh hodd ω hω => conj_eq_of_odd_of_three_le D hm hh hodd hω) hg
    exact ⟨u, hu, (huΩ x (Zab_le_T₁ D hx)).symm⟩

theorem exists_mem_T_conj_eq {x y g : G} (hx : x ∈ D.Zab) (hy : y ∈ D.Zab)
    (hg : g * x * g⁻¹ = y)
    (hsyl : ∃ SK : Sylow 2 ↥(centralizer ({x} : Set G)),
      (SK : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({x} : Set G))) :
    ∃ u ∈ (T : Subgroup G), u * x * u⁻¹ = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁2 : IsPGroup 2 D.T₁ := T.isPGroup'.to_le D.T₁_le_T
  have hT₁y : D.T₁ ≤ centralizer ({y} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2 (comm_of_mem_Zab D hy hw)
  obtain ⟨h, hhx, hhT⟩ := exists_conj_eq_and_conj_le hg hsyl hT₁2 hT₁y
  have hmap : D.T₁.map (MulAut.conj h⁻¹).toMonoidHom = D.T₁ := by
    refine D.map_T₁_eq (MulAut.conj h⁻¹).injective ?_
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hhT q hq
  have hN : h ∈ normalizer (D.T₁ : Set G) := by
    simpa using inv_mem (TStruct.mem_normalizer_of_map_conj_eq hmap)
  obtain ⟨u, hu, hux⟩ := exists_mem_T_conj_eq_of_normalizer D hN hx (hhx ▸ hy)
  exact ⟨u, hu, hux.trans hhx⟩

theorem sylow_centralizer_of_mem_Zab {x : G} (hx : x ∈ D.Zab) :
    ∃ SK : Sylow 2 ↥(centralizer ({x} : Set G)),
      (SK : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({x} : Set G)) := by
  have hcent : ∀ z : G, (∀ u ∈ (T : Subgroup G), u * z = z * u) →
      ∃ SK : Sylow 2 ↥(centralizer ({z} : Set G)),
        (SK : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) := by
    intro z hc
    have hle : (T : Subgroup G) ≤ centralizer ({z} : Set G) := fun u hu =>
      mem_centralizer_singleton_iff.2 (hc u hu)
    exact ⟨T.subtype hle, T.coe_subtype hle⟩
  by_contra hns
  have hxT : x ∈ (T : Subgroup G) := D.T₁_le_T (Zab_le_T₁ D hx)
  have hcos : ∀ u ∈ (T : Subgroup G), ∀ v ∈ (T : Subgroup G),
      u ∉ (T : Subgroup G) ⊓ centralizer ({x} : Set G) →
      v ∉ (T : Subgroup G) ⊓ centralizer ({x} : Set G) →
      u⁻¹ * v ∈ (T : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    intro u hu v hv hun hvn
    have hsw : ∀ w ∈ (T : Subgroup G), w ∉ (T : Subgroup G) ⊓ centralizer ({x} : Set G) →
        w * x * w⁻¹ = D.s * x * D.s⁻¹ := fun w hw hwn =>
      (conj_Zab_cases D hw hx).resolve_left fun h =>
        hwn (mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 (comm_of_conj_eq h).symm⟩)
    have e : (u⁻¹ * v) * x * (u⁻¹ * v)⁻¹ = x := by
      calc (u⁻¹ * v) * x * (u⁻¹ * v)⁻¹ = u⁻¹ * (v * x * v⁻¹) * u := by group
        _ = u⁻¹ * (u * x * u⁻¹) * u := by rw [hsw v hv hvn, hsw u hu hun]
        _ = x := by group
    exact mem_inf.2 ⟨mul_mem (inv_mem hu) hv,
      mem_centralizer_singleton_iff.2 (comm_of_conj_eq e).symm⟩
  obtain ⟨k, hkT, hkc⟩ := exists_conj_comm_of_not_sylow T hxT hcos hns
  have hkZ : k * x * k⁻¹ ∈ D.Zab := mem_Zab_of_comm_T D hkT hkc
  obtain ⟨u, hu, hux⟩ := exists_mem_T_conj_eq D hkZ hx (g := k⁻¹) (by group) (hcent _ hkc)
  have hxz : x = k * x * k⁻¹ := by
    calc x = u * (k * x * k⁻¹) * u⁻¹ := hux.symm
      _ = k * x * k⁻¹ := by rw [hkc u hu, mul_inv_cancel_right]
  have hxc : ∀ u ∈ (T : Subgroup G), u * x = x * u := by
    intro u hu
    rw [hxz]
    exact hkc u hu
  exact hns (hcent x hxc)

theorem lemma3_one {x y : G} (hx : x ∈ D.Zab) (hy : y ∈ D.Zab) (hxy : IsConj x y) :
    x = y ∨ (x = D.b₀ ∧ y = D.b₁) ∨ (x = D.b₁ ∧ y = D.b₀) ∨
      (x = D.a * D.b₀ ∧ y = D.a * D.b₁) ∨ (x = D.a * D.b₁ ∧ y = D.a * D.b₀) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  obtain ⟨u, hu, hux⟩ := exists_mem_T_conj_eq D hx hy hg (sylow_centralizer_of_mem_Zab D hx)
  subst hux
  rcases conj_Zab_cases D hu hx with h | h
  · exact Or.inl h.symm
  · rw [h]
    obtain ⟨α, w, hα, hw, rfl⟩ := (mem_Zab_iff D).1 hx
    have hsα : D.s * α * D.s⁻¹ = α := by
      rcases hα with rfl | rfl
      · group
      · exact conj_s_a D
    have hsb : D.s * D.b * D.s⁻¹ = D.b := by
      rw [D.b_comm_T (D.B_le_T D.s_mem_B), mul_inv_cancel_right]
    have e : D.s * (α * w) * D.s⁻¹ = α * (D.s * w * D.s⁻¹) := by
      calc D.s * (α * w) * D.s⁻¹ = (D.s * α * D.s⁻¹) * (D.s * w * D.s⁻¹) := by group
        _ = α * (D.s * w * D.s⁻¹) := by rw [hsα]
    rw [e]
    rcases hα with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
    · left; group
    · right; left; exact ⟨one_mul _, by rw [D.conj_s_b₀, one_mul]⟩
    · right; right; left; exact ⟨one_mul _, by rw [D.conj_s_b₁, one_mul]⟩
    · left; rw [hsb]
    · left; group
    · right; right; right; left; exact ⟨rfl, by rw [D.conj_s_b₀]⟩
    · right; right; right; right; exact ⟨rfl, by rw [D.conj_s_b₁]⟩
    · left; rw [hsb]

end CFSG.CGT.Foote81L6.Fusion3
