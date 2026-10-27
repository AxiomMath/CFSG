module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9c

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

namespace Ph0

theorem K1c (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a) {c : G} (hcP : c ∈ P)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcz : c ≠ z) :
    ∀ g ∈ S, g ∉ T → g * c * g⁻¹ ≠ c ∧ g * c * g⁻¹ ≠ c * z := by
  intro g hg hgT
  have hz2 := H.hz.z_sq
  have hzc : z * c = c * z := H.hz.z_central c (H.base.P_le_T hcP)
  have hV' : IsFour (Subgroup.zpowers c ⊔ Subgroup.zpowers z) :=
    isFour_pair hc2 hz2 hc1 H.hz.z_ne_one hcz hzc.symm
  have hV'P : Subgroup.zpowers c ⊔ Subgroup.zpowers z ≤ P :=
    sup_le ((Subgroup.zpowers_le).2 hcP) ((Subgroup.zpowers_le).2 H.hz.z_mem_P)
  have hnorm : (g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c * z) →
      g ∈ Subgroup.normalizer
        ((((Subgroup.zpowers c ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers x : Subgroup G)) : Set G) := by
    intro hcg
    apply mem_normalizer_of_forward
    intro e he
    have hle : (Subgroup.zpowers c ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers x ≤
        Hconj g ((Subgroup.zpowers c ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers x) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · apply (Subgroup.zpowers_le).2
        rw [mem_Hconj]
        rcases hcg with e1 | e1
        · rw [e1]
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
        · rw [e1]
          exact Subgroup.mul_mem _
            (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
      · apply (Subgroup.zpowers_le).2
        rw [mem_Hconj, Ph0.sz H A g hg]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      · apply (Subgroup.zpowers_le).2
        rw [mem_Hconj, Ph0.sx H A hg hgT]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
    exact mem_Hconj.1 (hle he)
  exact ⟨fun h1 => A.K1 _ hV'P hV' g hg hgT (hnorm (Or.inl h1)),
    fun h1 => A.K1 _ hV'P hV' g hg hgT (hnorm (Or.inr h1))⟩

end Ph0

namespace Ph1

variable (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
  (B : Ph1 G x z T P Rd a V P₁ F')
include H A B

omit A in
theorem dih_data : ∃ ρ s : G, ∃ j : ℕ, DihData P₁ ρ s j ∧ z = ρ ^ DihData.zc j := by
  obtain ⟨ρ, s, j, hD⟩ := dihData_of_dih H.base.T_pgroup (B.P1_le_T H) B.dih B.big
  refine ⟨ρ, s, j, hD, ?_⟩
  exact hD.central_inv_eq (B.P_le H.hz.z_mem_P) H.hz.z_sq H.hz.z_ne_one
    (fun d hd => H.hz.z_central d (B.P1_le_T H hd))

theorem K1pp {c : G} (hc : c ∈ P₁) (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcz : c ≠ z) :
    ∀ g ∈ S, g ∉ T → g * c * g⁻¹ ≠ c ∧ g * c * g⁻¹ ≠ c * z := by
  rcases B.inv_cases H A hc hc2 with hcP | ⟨p₁, hp₁, u, huW, hu2, huR, hcu⟩
  · exact Ph0.K1c H A hcP hc2 hc1 hcz
  · intro g hg hgT
    have hkS : a * p₁ ∈ S := S.mul_mem A.a_mem (H.base.T_le_S (H.base.P_le_T hp₁))
    have hg'S : (a * p₁) * g * (a * p₁)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hkS hg) (S.inv_mem hkS)
    have hg'T : (a * p₁) * g * (a * p₁)⁻¹ ∉ T := by
      intro h
      apply hgT
      have := H.T_normal_S (a * p₁)⁻¹ (S.inv_mem hkS) _ h
      have e : (a * p₁)⁻¹ * ((a * p₁) * g * (a * p₁)⁻¹) * (a * p₁)⁻¹⁻¹ = g := by group
      rwa [e] at this
    have hv' : (a * p₁) * c * (a * p₁)⁻¹ = a * u * a⁻¹ := by rw [hcu]; group
    have hv'V : a * u * a⁻¹ ∈ V := huW
    have hv'P : a * u * a⁻¹ ∈ P := B.V_le hv'V
    have hv'2 : (a * u * a⁻¹) * (a * u * a⁻¹) = 1 := (B.V_four.1 _ hv'V).1
    have hv'1 : a * u * a⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      have : (a * p₁) * c * (a * p₁)⁻¹ = 1 := by rw [hv', h1]
      have h2 : c = (a * p₁)⁻¹ * ((a * p₁) * c * (a * p₁)⁻¹) * (a * p₁) := by group
      rw [h2, this]; group
    have hkz : (a * p₁) * z * (a * p₁)⁻¹ = z := Ph0.sz H A _ hkS
    have hv'z : a * u * a⁻¹ ≠ z := by
      intro h1
      apply hcz
      have h3 : (a * p₁) * c * (a * p₁)⁻¹ = (a * p₁) * z * (a * p₁)⁻¹ := by rw [hv', h1, hkz]
      have h2 := mul_right_cancel h3
      exact mul_left_cancel (a := a * p₁) h2
    obtain ⟨h1, h2⟩ := Ph0.K1c H A hv'P hv'2 hv'1 hv'z _ hg'S hg'T
    constructor
    · intro e
      apply h1
      calc ((a * p₁) * g * (a * p₁)⁻¹) * (a * u * a⁻¹) * ((a * p₁) * g * (a * p₁)⁻¹)⁻¹
          = (a * p₁) * (g * ((a * p₁)⁻¹ * (a * u * a⁻¹) * (a * p₁)) * g⁻¹) * (a * p₁)⁻¹ := by group
        _ = (a * p₁) * (g * c * g⁻¹) * (a * p₁)⁻¹ := by
            congr 3
            rw [← hv']; group
        _ = (a * p₁) * c * (a * p₁)⁻¹ := by rw [e]
        _ = a * u * a⁻¹ := hv'
    · intro e
      apply h2
      calc ((a * p₁) * g * (a * p₁)⁻¹) * (a * u * a⁻¹) * ((a * p₁) * g * (a * p₁)⁻¹)⁻¹
          = (a * p₁) * (g * ((a * p₁)⁻¹ * (a * u * a⁻¹) * (a * p₁)) * g⁻¹) * (a * p₁)⁻¹ := by group
        _ = (a * p₁) * (g * c * g⁻¹) * (a * p₁)⁻¹ := by
            congr 3
            rw [← hv']; group
        _ = (a * p₁) * (c * z) * (a * p₁)⁻¹ := by rw [e]
        _ = ((a * p₁) * c * (a * p₁)⁻¹) * ((a * p₁) * z * (a * p₁)⁻¹) := by group
        _ = (a * u * a⁻¹) * z := by rw [hv', hkz]

theorem x_conj_not_P1 {y : G} (hy : y ∈ P₁) (hconj : ∃ g : G, g⁻¹ * x * g = y) : False := by
  obtain ⟨g, hg⟩ := hconj
  have hy2 : y * y = 1 := by
    rw [← hg]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [H.base.x_sq]; group
  have hy1 : y ≠ 1 := by
    intro h1
    apply H.base.x_ne_one
    have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h2, hg, h1]; group
  obtain ⟨g', hg'⟩ := B.inv_zconj H A hy hy2 hy1
  apply (H.h127.z_not_conj A.card4 (g * g'⁻¹)).1
  have : (g * g'⁻¹)⁻¹ * x * (g * g'⁻¹) = g' * (g⁻¹ * x * g) * g'⁻¹ := by group
  rw [this, hg, ← hg']; group

theorem ext_inv_false {y : G} (hyS : y ∈ S) (hyT : y ∉ T) (hy2 : y * y = 1)
    (hconj : ∃ g : G, g⁻¹ * x * g = y) (hex : IsExtremal S y) : False := by
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨ρ, s, j, hD, hz⟩ := B.dih_data H
  have hrel := relIndex_extremal H.base.T_sylow hg hex H.base.T_le_S
  rw [H.S2] at hrel
  have hyD : ∀ d, d ∈ P₁ ↔ y * d * y⁻¹ ∈ P₁ := by
    intro d
    constructor
    · exact B.P1_normalS H A y hyS d
    · intro h
      have := B.P1_normalS H A y⁻¹ (S.inv_mem hyS) _ h
      have e : y⁻¹ * (y * d * y⁻¹) * y⁻¹⁻¹ = d := by group
      rwa [e] at this
  have hcent : ∀ d ∈ S ⊓ Subgroup.centralizer ({y} : Set G), y * d * y⁻¹ = d := by
    intro d hd
    have h1 : y * d = d * y := Subgroup.mem_centralizer_iff.1 hd.2 y (Set.mem_singleton y)
    rw [h1]; group
  have hpairs : ∀ d₁ ∈ P₁, ∀ d₂ ∈ P₁, y * d₁ * y⁻¹ = d₁ ∨ y * d₂ * y⁻¹ = d₂ ∨
      y * (d₁⁻¹ * d₂) * y⁻¹ = d₁⁻¹ * d₂ := by
    intro d₁ hd₁ d₂ hd₂
    have hS₁ : d₁ ∈ S := H.base.T_le_S (B.P1_le_T H hd₁)
    have hS₂ : d₂ ∈ S := H.base.T_le_S (B.P1_le_T H hd₂)
    rcases pigeon_of_relIndex_two hrel hS₁ hS₂ with h | h | h
    · exact Or.inl (hcent _ h)
    · exact Or.inr (Or.inl (hcent _ h))
    · exact Or.inr (Or.inr (hcent _ h))
  obtain ⟨c, hcP₁, hc2, hc1, hcz, hyc⟩ := hD.exists_normalized_four_of_pairs hy2 hyD hpairs
  rw [← hz] at hcz hyc
  obtain ⟨k1, k2⟩ := B.K1pp H A hcP₁ hc2 hc1 hcz y hyS hyT
  rcases hyc with e | e
  · exact k1 e
  · exact k2 e

theorem x_transfer_false {N : Subgroup G} {g₀ : G} (hNS : N ≤ S)
    (hNn : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N) (hNT : ∀ y ∈ N, y ∈ T → y ∈ P₁)
    (hxN : x ∉ N) (hg₀ : g₀ ∈ S) (hcyc : ∀ t ∈ S, ∃ k : ℤ, (g₀ ^ k)⁻¹ * t ∈ N) : False := by
  have hxS : x ∈ S := H.base.T_le_S H.base.x_mem_T
  have hne : N ≠ S := fun e => hxN (e ▸ hxS)
  have hord : ∀ v ∈ S, v ∉ N → orderOf x ≤ orderOf v := by
    intro v _ hv
    have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact H.base.x_sq)
      H.base.x_ne_one
    rw [hx2]
    have hv1 : v ≠ 1 := fun e => hv (by rw [e]; exact N.one_mem)
    have hpos : 0 < orderOf v := orderOf_pos v
    have hne1 : orderOf v ≠ 1 := fun e => hv1 (orderOf_eq_one_iff.1 e)
    omega
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * x * g = y) → IsExtremal S y → y ∈ N ∨ x⁻¹ * y ∈ N := by
    intro y hyS hconj _
    obtain ⟨g, hg⟩ := hconj
    by_cases hyN : y ∈ N
    · exact Or.inl hyN
    · right
      have hy2 : y * y = 1 := by
        rw [← hg]
        calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
          _ = 1 := by rw [H.base.x_sq]; group
      have h1 := uniq_inv_coset hNn hg₀ hcyc hyS hxS hyN hxN (by rw [hy2]; exact N.one_mem)
        (by rw [H.base.x_sq]; exact N.one_mem)
      have h2 := N.inv_mem h1
      simpa using h2
  obtain ⟨g, hgN, hgext⟩ := transfer_conj H.IG H.base.simple H.base.nonabelian H.base.S_sylow hNS hNn
    hne ⟨g₀, hg₀, hcyc⟩ hxS hxN hord hext
  by_cases hyP : g⁻¹ * x * g ∈ P₁
  · exact B.x_conj_not_P1 H A hyP ⟨g, rfl⟩
  · have hyT : g⁻¹ * x * g ∉ T := fun h => hyP (hNT _ hgN h)
    have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [H.base.x_sq]; group
    exact B.ext_inv_false H A (hNS hgN) hyT hy2 ⟨g, rfl⟩ hgext

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
