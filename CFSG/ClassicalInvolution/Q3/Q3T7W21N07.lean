module

public import CFSG.ClassicalInvolution.Q3.Q3T7M01
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson


namespace T7N

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem sup_le_centralizer_of_twin (hz : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z) :
    K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm)
    (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr (hzK'.commute_of_mem hw).symm)

theorem exists_conj_xy_twin (hΩ : Q3T7M.HM Ω) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z) {u : G}
    (hu : u ∈ K ⊔ K') (hu1 : u ≠ 1) (huz : u ≠ z) (hu2 : u * u = 1) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ K ⊔ K', c * u * c⁻¹ = x * y := by
  have hΩg : Q3T8.Asc77.HypOmegaMod Ω := hΩ
  have hLN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hMC : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := sup_le_centralizer_of_twin hz hzK'
  have hQ : IsSylow2In (R₁ ⊔ R₂) (K ⊔ K') :=
    T7A.isSylow2In_sup_of_twin hΩg hK hK'Ω hne hz hzK' hR₁ hR₂ hc
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2 hu1
  obtain ⟨V, hV, huV⟩ := IsSylow2In.exists_ge hu2' (Subgroup.zpowers_le.mpr hu)
  obtain ⟨m, hmM, hmV⟩ := exists_conjSub_eq_of_isSylow2In hV hQ
  have hu'mem : m * u * m⁻¹ ∈ R₁ ⊔ R₂ := by
    rw [← hmV]
    exact conj_mem_conjSub (huV (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc hu'mem
  have hmz : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * z * m⁻¹ = (z * m) * m⁻¹ := by rw [this]
      _ = z := by group
  have hu'2 : (a * b) * (a * b) = 1 := by
    rw [hab]
    calc m * u * m⁻¹ * (m * u * m⁻¹) = m * (u * u) * m⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu'2
  have haL : a ∈ K := hR₁.1 ha
  have hbL' : b ∈ K' := hR₂.1 hb
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hz.unique (a * a) (K.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hz.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzK'.unique b hbL' hbb
      have hu'z : m * u * m⁻¹ = 1 ∨ m * u * m⁻¹ = z := by
        rw [← hab]
        rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
        · left; rw [h1, h2, one_mul]
        · right; rw [h1, h2, one_mul]
        · right; rw [h1, h2, mul_one]
        · left; rw [h1, h2]; exact hz.sq
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m := by group
      rcases hu'z with h' | h'
      · exact hu1 (by rw [hu, h']; group)
      · exact huz (by
          rw [hu, h']
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group)
    · exact h
  have hbb : b * b = z := by
    have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz.sq
  have hx2 : x * x = z := T7B.mul_self_eq_of_orderOf_four hz (hR₁.1 hx) ox
  have hy2 : y * y = z := T7B.mul_self_eq_of_orderOf_four hzK' (hR₂.1 hy) oy
  obtain ⟨k, hkL, hk⟩ := T7B.exists_conj_of_sq_eq hΩ hK hz haL (hR₁.1 hx) haa hx2
  set b₁ := k * b * k⁻¹ with hb₁
  have hb₁L' : b₁ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hLN hkL) b).mp hbL'
  have hb₁2 : b₁ * b₁ = z := by
    have e : b₁ * b₁ = k * (b * b) * k⁻¹ := by rw [hb₁]; group
    rw [e, hbb]
    have := hz.commute_of_mem hkL
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [this]
      _ = z := by group
  have hxb₁ : x * b₁ = b₁ * x := by
    rw [← hk, hb₁]
    calc k * a * k⁻¹ * (k * b * k⁻¹) = k * (a * b) * k⁻¹ := by group
      _ = k * (b * a) * k⁻¹ := by rw [hcab]
      _ = k * b * k⁻¹ * (k * a * k⁻¹) := by group
  have hxy : x * y = y * x := hc x hx y hy
  obtain ⟨ℓ, hℓL', hℓ⟩ := T7B.exists_conj_of_sq_eq hΩ hK'Ω hzK' hb₁L' (hR₂.1 hy) hb₁2 hy2
  obtain ⟨ℓ', hℓ'L', hℓ'b, hℓ'x⟩ := T7B.exists_centralizing_conj hΩg hK hK'Ω hne hz hzK'
    (hR₁.1 hx) (T7B.isPGroup_zpowers_of_orderOf_four ox) hℓL' hxb₁ hxy hℓ
  refine ⟨ℓ' * k * m, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hℓ'L')
    (Subgroup.mem_sup_left hkL)) hmM, ?_⟩
  have hℓ'x' : ℓ' * x * ℓ'⁻¹ = x := by
    rw [hℓ'x]
    group
  calc ℓ' * k * m * u * (ℓ' * k * m)⁻¹ = ℓ' * k * (m * u * m⁻¹) * k⁻¹ * ℓ'⁻¹ := by group
    _ = ℓ' * k * (a * b) * k⁻¹ * ℓ'⁻¹ := by rw [hab]
    _ = ℓ' * ((k * a * k⁻¹) * (k * b * k⁻¹)) * ℓ'⁻¹ := by group
    _ = ℓ' * (x * b₁) * ℓ'⁻¹ := by rw [hk]
    _ = (ℓ' * x * ℓ'⁻¹) * (ℓ' * b₁ * ℓ'⁻¹) := by group
    _ = x * y := by rw [hℓ'x', hℓ'b]

theorem exists_conj_of_involution_twin (hΩ : Q3T7M.HM Ω) (hK : K ∈ Ω)
    (hK'Ω : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) {u₁ u₂ : G} (h₁ : u₁ ∈ K ⊔ K') (h₁1 : u₁ ≠ 1)
    (h₁z : u₁ ≠ z) (h₁2 : u₁ * u₁ = 1) (h₂ : u₂ ∈ K ⊔ K') (h₂1 : u₂ ≠ 1) (h₂z : u₂ ≠ z)
    (h₂2 : u₂ * u₂ = 1) : ∃ c ∈ K ⊔ K', c * u₁ * c⁻¹ = u₂ := by
  obtain ⟨R, R', hR, hR', hc, -⟩ :=
    T7A.exists_sylow_pair_of_mem hΩ hK hK'Ω hne hz hzK' h₁ h₁2 h₁1
  obtain ⟨x, hx, ox⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨y, hy, oy⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet
    (mem_RSet_of_isSylow2In hK'Ω hR')
  obtain ⟨c₁, hc₁, e₁⟩ := exists_conj_xy_twin hΩ hK hK'Ω hne hz hzK' h₁ h₁1 h₁z h₁2 hR hR' hc
    hx hy ox oy
  obtain ⟨c₂, hc₂, e₂⟩ := exists_conj_xy_twin hΩ hK hK'Ω hne hz hzK' h₂ h₂1 h₂z h₂2 hR hR' hc
    hx hy ox oy
  refine ⟨c₂⁻¹ * c₁, (K ⊔ K').mul_mem ((K ⊔ K').inv_mem hc₂) hc₁, ?_⟩
  calc c₂⁻¹ * c₁ * u₁ * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * u₁ * c₁⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₂ * u₂ * c₂⁻¹) * c₂ := by rw [e₁, e₂]
    _ = u₂ := by group

end T7N

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
