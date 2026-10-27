module

public import CFSG.ClassicalInvolution.Q3.Q3T8B17

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Conj

variable {G : Type*} [Group G]

theorem sup_centralizer_eq_top_conj {a b : G}
    (h : Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G) = ⊤) (g : G) :
    Subgroup.centralizer ({g * a * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * b * g⁻¹} : Set G) =
      ⊤ := by
  have key : ∀ c : G, (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({g * c * g⁻¹} : Set G) := by
    intro c y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hy₀' : y₀ ∈ Subgroup.centralizer ({c} : Set G) := hy₀
    rw [Subgroup.mem_centralizer_singleton_iff] at hy₀' ⊢
    show (g * y₀ * g⁻¹) * (g * c * g⁻¹) = (g * c * g⁻¹) * (g * y₀ * g⁻¹)
    calc g * y₀ * g⁻¹ * (g * c * g⁻¹) = g * (y₀ * c) * g⁻¹ := by group
      _ = g * (c * y₀) * g⁻¹ := by rw [hy₀']
      _ = g * c * g⁻¹ * (g * y₀ * g⁻¹) := by group
  rw [eq_top_iff]
  intro x _
  have hx : g⁻¹ * x * g ∈
      Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G) :=
    h ▸ Subgroup.mem_top _
  have hmap : (Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G)).map
      (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ({g * a * g⁻¹} : Set G) ⊔
          Subgroup.centralizer ({g * b * g⁻¹} : Set G) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (key a) (key b)
  refine hmap ⟨g⁻¹ * x * g, hx, ?_⟩
  show g * (g⁻¹ * x * g) * g⁻¹ = x
  group

end Conj

section Cert

private theorem mem_wordA {G : Type*} [Group G] {H : Subgroup G} {h₁ h₂ : G} (a₁ : h₁ ∈ H)
    (a₂ : h₂ ∈ H) : h₁ ^ 2 * h₂ * h₁ ^ 2 * h₂ * h₁⁻¹ ^ 2 * h₂ * h₁ ^ 2 * h₂ ∈ H := by
  repeat' first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | assumption

private theorem mem_wordB {G : Type*} [Group G] {H : Subgroup G} {h₁ h₂ : G} (a₁ : h₁ ∈ H)
    (a₂ : h₂ ∈ H) : h₁ ^ 3 * h₂ * h₁ ^ 2 * h₂ * h₁⁻¹ ^ 2 * h₂ * h₁ ^ 2 ∈ H := by
  repeat' first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | assumption

abbrev m11SdYElt : ↥NativeSporadic.M11 := ⟨m11SdY, m11SdY_mem⟩

abbrev m11SdXElt : ↥NativeSporadic.M11 := ⟨m11SdX, m11SdX_mem⟩

theorem sup_centralizer_m11SdZ_m11SdYElt :
    Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11) ⊔
      Subgroup.centralizer ({m11SdYElt} : Set ↥NativeSporadic.M11) = ⊤ := by
  set W := Subgroup.centralizer ({m11SdZ} : Set ↥NativeSporadic.M11) ⊔
    Subgroup.centralizer ({m11SdYElt} : Set ↥NativeSporadic.M11) with hW
  have h1 : m11Conj [1, 0, 1, 1, 0, 1, 1] ∈ W := by
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    show m11Eval [1, 0, 1, 1, 0, 1, 1] * m11SdX ^ 4 = m11SdX ^ 4 * m11Eval [1, 0, 1, 1, 0, 1, 1]
    decide +kernel
  have h2 : m11Conj [0, 1, 1, 0, 1, 1, 0] ∈ W := by
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    show m11Eval [0, 1, 1, 0, 1, 1, 0] * m11SdY = m11SdY * m11Eval [0, 1, 1, 0, 1, 1, 0]
    decide +kernel
  have hA : m11a ∈ W := by
    have e : m11a = m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        (m11Conj [1, 0, 1, 1, 0, 1, 1])⁻¹ ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] := by
      refine Subtype.ext ?_
      show m11gA = m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        (m11Eval [1, 0, 1, 1, 0, 1, 1])⁻¹ ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0]
      decide +kernel
    rw [e]
    exact mem_wordA h1 h2
  have hB : m11b ∈ W := by
    have e : m11b = m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 3 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        (m11Conj [1, 0, 1, 1, 0, 1, 1])⁻¹ ^ 2 * m11Conj [0, 1, 1, 0, 1, 1, 0] *
        m11Conj [1, 0, 1, 1, 0, 1, 1] ^ 2 := by
      refine Subtype.ext ?_
      show m11gB = m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 3 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        (m11Eval [1, 0, 1, 1, 0, 1, 1])⁻¹ ^ 2 * m11Eval [0, 1, 1, 0, 1, 1, 0] *
        m11Eval [1, 0, 1, 1, 0, 1, 1] ^ 2
      decide +kernel
    rw [e]
    exact mem_wordB h1 h2
  have hcl : Subgroup.closure ({m11a, m11b} : Set ↥NativeSporadic.M11) = ⊤ :=
    closure_pair_eq_top m11_eq _ _
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hA
  · exact hB

end Cert

section Sylow

private theorem m11Sd_pairs : ∀ p q : Fin 8 × Fin 2,
    m11SdMap p * m11SdMap p = 1 → m11SdMap p ≠ 1 → m11SdMap q * m11SdMap q = 1 →
    m11SdMap q ≠ 1 → m11SdMap p ≠ m11SdMap q →
    m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p →
    (∃ k : Fin 8, m11SdMap p = m11SdX ^ k.val * m11SdY * (m11SdX ^ k.val)⁻¹ ∨
        m11SdMap q = m11SdX ^ k.val * m11SdY * (m11SdX ^ k.val)⁻¹ ∨
        m11SdMap p * m11SdMap q = m11SdX ^ k.val * m11SdY * (m11SdX ^ k.val)⁻¹) ∧
      (m11SdX ^ 4 = m11SdMap p ∨ m11SdX ^ 4 = m11SdMap q ∨
        m11SdX ^ 4 = m11SdMap p * m11SdMap q) := by
  decide +kernel

theorem exists_conj_pair_mem_m11SdS {u v : ↥NativeSporadic.M11} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hv2 : v * v = 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : u * v = v * u) :
    ∃ g s t : ↥NativeSporadic.M11, s ∈ m11SdS ∧ t ∈ m11SdS ∧ g * s * g⁻¹ = u ∧
      g * t * g⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 m11SdS := IsPGroup.of_card (n := 4) (by rw [card_m11SdS]; norm_num)
  have hidx : ¬ 2 ∣ m11SdS.index := by
    have h := Subgroup.card_mul_index m11SdS
    rw [card_m11SdS, card_m11_kernel] at h
    have : m11SdS.index = 495 := by omega
    rw [this]
    norm_num
  have hVab := T7A.isElemAbelian2_closure_pair hu2 hv2 hu1 hv1 huv hcomm
  have hV : IsPGroup 2 ↥(Subgroup.closure ({u, v} : Set ↥NativeSporadic.M11)) :=
    isPGroup_two_of_sq_eq_one hVab.2
  obtain ⟨P, hP⟩ := hV.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 (hS.toSylow hidx) P
  have hu : u ∈ ((g • hS.toSylow hidx : Sylow 2 ↥NativeSporadic.M11) : Subgroup _) := by
    rw [hg]
    exact hP (Subgroup.subset_closure (by simp))
  have hv : v ∈ ((g • hS.toSylow hidx : Sylow 2 ↥NativeSporadic.M11) : Subgroup _) := by
    rw [hg]
    exact hP (Subgroup.subset_closure (by simp))
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu hv
  obtain ⟨s, hs, hsu⟩ := hu
  obtain ⟨t, ht, htv⟩ := hv
  exact ⟨g, s, t, hs, ht, by simpa [MulAut.smul_def, MulAut.conj_apply] using hsu,
    by simpa [MulAut.smul_def, MulAut.conj_apply] using htv⟩

end Sylow

section Main

theorem exists_conj_of_involutions_m11 {u v : ↥NativeSporadic.M11} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hv2 : v * v = 1) (hv1 : v ≠ 1) : ∃ g : ↥NativeSporadic.M11, g * u * g⁻¹ = v := by
  have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hv : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  obtain ⟨a, ha⟩ := isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two hu)
  obtain ⟨b, hb⟩ := isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two hv)
  exact ⟨b * a⁻¹, by rw [← ha, ← hb]; group⟩

theorem linkModelFacts_m11 : LinkModelFacts ↥NativeSporadic.M11 := by
  refine ⟨fun u v hu2 hu1 hv2 hv1 => exists_conj_of_involutions_m11 hu2 hu1 hv2 hv1, ?_⟩
  intro u v hu2 hu1 hv2 hv1 huv hcomm
  obtain ⟨g, s, t, hsS, htS, hgs, hgt⟩ := exists_conj_pair_mem_m11SdS hu2 hu1 hv2 hv1 huv hcomm
  have hsu : s = g⁻¹ * u * g := by rw [← hgs]; group
  have htv : t = g⁻¹ * v * g := by rw [← hgt]; group
  have hs2 : s * s = 1 := by
    calc s * s = g⁻¹ * (u * u) * g := by rw [hsu]; group
      _ = 1 := by rw [hu2]; group
  have ht2 : t * t = 1 := by
    calc t * t = g⁻¹ * (v * v) * g := by rw [htv]; group
      _ = 1 := by rw [hv2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hu1 (by rw [← hgs]; group)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hv1 (by rw [← hgt]; group)
  have hst : s ≠ t := by
    rintro rfl
    exact huv (by rw [← hgs, ← hgt])
  have hcst : s * t = t * s := by
    calc s * t = g⁻¹ * (u * v) * g := by rw [hsu, htv]; group
      _ = g⁻¹ * (v * u) * g := by rw [hcomm]
      _ = t * s := by rw [hsu, htv]; group
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem hsS
  obtain ⟨q, hq⟩ := exists_m11SdMap_eq_of_mem htS
  have hp2 : m11SdMap p * m11SdMap p = 1 := by
    rw [hp]; simpa using congrArg Subtype.val hs2
  have hq2 : m11SdMap q * m11SdMap q = 1 := by
    rw [hq]; simpa using congrArg Subtype.val ht2
  have hp1 : m11SdMap p ≠ 1 := by
    rw [hp]; exact fun h => hs1 (Subtype.ext h)
  have hq1 : m11SdMap q ≠ 1 := by
    rw [hq]; exact fun h => ht1 (Subtype.ext h)
  have hpq : m11SdMap p ≠ m11SdMap q := by
    rw [hp, hq]; exact fun h => hst (Subtype.ext h)
  have hpqc : m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p := by
    rw [hp, hq]; simpa using congrArg Subtype.val hcst
  obtain ⟨⟨k, hk⟩, hz⟩ := m11Sd_pairs p q hp2 hp1 hq2 hq1 hpq hpqc
  set ck : ↥NativeSporadic.M11 := m11SdXElt ^ k.val * m11SdYElt * (m11SdXElt ^ k.val)⁻¹ with hck
  have hckc : (ck : Perm (Fin 11)) = m11SdX ^ k.val * m11SdY * (m11SdX ^ k.val)⁻¹ := rfl
  have hk' : s = ck ∨ t = ck ∨ s * t = ck := by
    rcases hk with h | h | h
    · exact Or.inl (Subtype.ext (by rw [← hp, h]; rfl))
    · exact Or.inr (Or.inl (Subtype.ext (by rw [← hq, h]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [Subgroup.coe_mul, ← hp, ← hq, h]; rfl)))
  have hz' : m11SdZ = s ∨ m11SdZ = t ∨ m11SdZ = s * t := by
    rcases hz with h | h | h
    · exact Or.inl (Subtype.ext (by rw [← hp, ← h]; rfl))
    · exact Or.inr (Or.inl (Subtype.ext (by rw [← hq, ← h]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [Subgroup.coe_mul, ← hp, ← hq, ← h]; rfl)))
  set W := Subgroup.centralizer ({u} : Set ↥NativeSporadic.M11) ⊔
    Subgroup.centralizer ({v} : Set ↥NativeSporadic.M11) ⊔
    Subgroup.centralizer ({u * v} : Set ↥NativeSporadic.M11) with hW
  have hle : ∀ c : ↥NativeSporadic.M11, (c = s ∨ c = t ∨ c = s * t) →
      Subgroup.centralizer ({g * c * g⁻¹} : Set ↥NativeSporadic.M11) ≤ W := by
    rintro c (rfl | rfl | rfl)
    · rw [hgs]
      exact le_sup_left.trans le_sup_left
    · rw [hgt]
      exact le_sup_right.trans le_sup_left
    · have : g * (s * t) * g⁻¹ = u * v := by rw [← hgs, ← hgt]; group
      rw [this]
      exact le_sup_right
  have hgood := sup_centralizer_eq_top_conj sup_centralizer_m11SdZ_m11SdYElt (g * m11SdXElt ^ k.val)
  have hZ : m11SdZ = m11SdXElt ^ 4 := Subtype.ext rfl
  have e1 : g * m11SdXElt ^ k.val * m11SdZ * (g * m11SdXElt ^ k.val)⁻¹ = g * m11SdZ * g⁻¹ := by
    have hc : m11SdXElt ^ k.val * m11SdZ = m11SdZ * m11SdXElt ^ k.val := by
      rw [hZ, ← pow_add, ← pow_add, add_comm]
    calc g * m11SdXElt ^ k.val * m11SdZ * (g * m11SdXElt ^ k.val)⁻¹
        = g * (m11SdXElt ^ k.val * m11SdZ) * (m11SdXElt ^ k.val)⁻¹ * g⁻¹ := by group
      _ = g * (m11SdZ * m11SdXElt ^ k.val) * (m11SdXElt ^ k.val)⁻¹ * g⁻¹ := by rw [hc]
      _ = g * m11SdZ * g⁻¹ := by group
  have e2 : g * m11SdXElt ^ k.val * m11SdYElt * (g * m11SdXElt ^ k.val)⁻¹ = g * ck * g⁻¹ := by
    rw [hck]
    group
  rw [e1, e2] at hgood
  rw [eq_top_iff, ← hgood]
  exact sup_le (hle _ hz') (hle _ (hk'.imp Eq.symm (Or.imp Eq.symm Eq.symm)))

end Main

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
