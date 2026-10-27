module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7K1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Count

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup Wreath

section Generic

variable {G : Type} [Group G]

theorem s7td_odd_of_mem_O [Finite G] {H : Subgroup G} {g : G} (hg : g ∈ Open.fusionOddCoreOf H) :
    Odd (orderOf g) := by
  rw [fusionOddCoreOf_eq] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have e : orderOf (H.subtype h) = orderOf h := Subgroup.orderOf_coe h
  rw [e]
  exact Odd.of_dvd_nat (natCard_fusionOddCore_odd' _) (Subgroup.orderOf_dvd_natCard _ hh)

theorem s7td_conj_mem_O {H : Subgroup G} {x o : G} (hx : x ∈ H) (ho : o ∈ Open.fusionOddCoreOf H) :
    x * o * x⁻¹ ∈ Open.fusionOddCoreOf H := by
  rw [fusionOddCoreOf_eq] at ho ⊢
  obtain ⟨h, hh, rfl⟩ := ho
  exact ⟨⟨x, hx⟩ * h * ⟨x, hx⟩⁻¹,
    (inferInstance : (Open.fusionOddCore ↥H).Normal).conj_mem h hh ⟨x, hx⟩, rfl⟩

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.s7td_comm_conj {a : PA5 L t E z} {o : G} (ho : o ∈ Open.fusionOddCoreOf (Cen a.y))
    {c : G} (hc : c ∈ a.K₁) : o * (t * c * t⁻¹) = t * c * t⁻¹ * o := by
  have h1 : t⁻¹ * o * t ∈ Open.fusionOddCoreOf (Cen a.y) := by
    have := s7td_conj_mem_O (inv_mem a.t_cy) ho
    simpa using this
  have h2 : t⁻¹ * o * t * c = c * (t⁻¹ * o * t) := mem_centralizer_iff.1 (a.K₁_O hc) _ h1
  calc o * (t * c * t⁻¹) = t * ((t⁻¹ * o * t) * c) * t⁻¹ := by group
    _ = t * (c * (t⁻¹ * o * t)) * t⁻¹ := by rw [h2]
    _ = t * c * t⁻¹ * o := by group

theorem PA5.s7td_mem_Cen (hb : PAB G L t E W z) (a : PA5 L t E z) (g : ↥a.s7_N₁)
    (hg : g ∈ centralizer ({a.s7_yT hb} : Set ↥a.s7_N₁)) : (g : G) ∈ Cen a.y := by
  rw [mem_centralizer_singleton_iff] at hg
  exact mem_Cen.2 (congrArg (fun x : ↥a.s7_N₁ => (x : G)) hg)

@[expose] noncomputable def PA5.s7td_ρ (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ↥(centralizer ({a.s7_yT hb} : Set ↥a.s7_N₁)) →* Wr2 (Equiv.Perm (Fin 5)) :=
  (S5.phi a.toPA4).comp (MonoidHom.codRestrict
    (a.s7_N₁.subtype.comp (centralizer ({a.s7_yT hb} : Set ↥a.s7_N₁)).subtype) (Cen a.y)
    (fun g => a.s7td_mem_Cen hb g.1 g.2))

theorem PA5.s7td_F₀_cen (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f ∈ a.F₀, f ∈ Cen a.y := by
  intro f hf
  rw [a.s7_mem_F₀_iff hb] at hf
  rcases hf with rfl | rfl | ⟨hd, rfl | rfl⟩
  · exact one_mem _
  · exact a.ub_cy
  · obtain ⟨-, -, hu₁J, -, -, -, -⟩ := a.d8_props hd
    exact S5.cent_J_le_Cen_y a.toPA0 hu₁J
  · obtain ⟨-, -, hu₁J, -, -, -, -⟩ := a.d8_props hd
    exact mul_mem a.ub_cy (S5.cent_J_le_Cen_y a.toPA0 hu₁J)

theorem PA5.s7_hB (hb : PAB G L t E W z) (a : PA5 L t E z) (c k : ↥a.s7_N₁)
    (hc : (c : G) ∈ a.K₁) (hk : (k : G) ∈ a.K₁) :
    ∃ D₁ : Subgroup ((↥a.s7_N₁ ⧸ a.s7_F) ⧸ Open.fusionOddCore (↥a.s7_N₁ ⧸ a.s7_F)),
      D₁ ≤ Subgroup.centralizer ({a.s7_κ (a.s7_yT hb), a.s7_κ c,
          a.s7_κ (a.s7_tT hb) * a.s7_κ c * (a.s7_κ (a.s7_tT hb))⁻¹, a.s7_κ k,
          a.s7_κ (a.s7_tT hb) * a.s7_κ k * (a.s7_κ (a.s7_tT hb))⁻¹} : Set _) ∧
      Nat.card ↥((Subgroup.centralizer ({a.s7_yT hb} : Set ↥a.s7_N₁)).map a.s7_κ) ≤
        Nat.card D₁ * 72 := by
  set B : Subgroup ↥a.s7_N₁ := centralizer ({a.s7_yT hb} : Set ↥a.s7_N₁) with hBdef
  let κ' : ↥B →* _ := a.s7_κ.comp B.subtype
  let ρ := a.s7td_ρ hb
  have hρapply : ∀ (g : ↥B) (hcy : ((g : ↥a.s7_N₁) : G) ∈ Cen a.y),
      ρ g = S5.phi a.toPA4 ⟨((g : ↥a.s7_N₁) : G), hcy⟩ := fun g hcy => rfl
  have hker : ∀ g : ↥B, g ∈ ρ.ker → (((g : ↥a.s7_N₁) : G)) ∈ Open.fusionOddCoreOf (Cen a.y) := by
    intro g hg
    have hcy := a.s7td_mem_Cen hb g.1 g.2
    rw [MonoidHom.mem_ker, hρapply g hcy] at hg
    exact (s7_phi_eq_one_iff a.toPA4 hcy).1 hg
  refine ⟨ρ.ker.map κ', ?_, ?_⟩
  ·
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    have hgO := hker g hg
    have hgy : (g : ↥a.s7_N₁) * a.s7_yT hb = a.s7_yT hb * (g : ↥a.s7_N₁) :=
      mem_centralizer_singleton_iff.1 g.2
    have hκg : κ' g = a.s7_κ (g : ↥a.s7_N₁) := rfl
    rw [hκg]
    have hcomm : ∀ x : ↥a.s7_N₁, (g : ↥a.s7_N₁) * x = x * (g : ↥a.s7_N₁) →
        a.s7_κ x * a.s7_κ (g : ↥a.s7_N₁) = a.s7_κ (g : ↥a.s7_N₁) * a.s7_κ x := by
      intro x h
      rw [← map_mul, ← map_mul, h]
    have hcC : ∀ x : ↥a.s7_N₁, (x : G) ∈ a.K₁ →
        a.s7_κ x * a.s7_κ (g : ↥a.s7_N₁) = a.s7_κ (g : ↥a.s7_N₁) * a.s7_κ x := by
      intro x hx
      refine hcomm x (Subtype.ext ?_)
      exact mem_centralizer_iff.1 (a.K₁_O hx) _ hgO
    have hcT : ∀ x : ↥a.s7_N₁, (x : G) ∈ a.K₁ →
        a.s7_κ (a.s7_tT hb) * a.s7_κ x * (a.s7_κ (a.s7_tT hb))⁻¹ * a.s7_κ (g : ↥a.s7_N₁) =
          a.s7_κ (g : ↥a.s7_N₁) * (a.s7_κ (a.s7_tT hb) * a.s7_κ x * (a.s7_κ (a.s7_tT hb))⁻¹) := by
      intro x hx
      have e : a.s7_κ (a.s7_tT hb) * a.s7_κ x * (a.s7_κ (a.s7_tT hb))⁻¹ =
          a.s7_κ (a.s7_tT hb * x * (a.s7_tT hb)⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [e]
      refine hcomm _ (Subtype.ext ?_)
      exact a.s7td_comm_conj hgO hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hcomm _ hgy
    · exact hcC c hc
    · exact hcT c hc
    · exact hcC k hk
    · exact hcT k hk
  ·
    have hrange : κ'.range = B.map a.s7_κ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hFle : a.s7_F ≤ B := by
      intro f hf
      rw [hBdef, mem_centralizer_singleton_iff]
      refine Subtype.ext ?_
      exact mem_Cen.1 (a.s7td_F₀_cen hb _ hf)
    set FB : Subgroup ↥B := a.s7_F.subgroupOf B with hFB
    have hFBcard : Nat.card FB = Nat.card a.F₀ := by
      have h1 : Nat.card FB = Nat.card a.s7_F :=
        Nat.card_congr (subgroupOfEquivOfLe hFle).toEquiv
      have h2 : Nat.card a.s7_F = Nat.card a.F₀ :=
        Nat.card_congr (subgroupOfEquivOfLe (a.s7_F₀_le_N₁ hb)).toEquiv
      rw [h1, h2]
    have hFκ : ∀ f ∈ FB, κ' f = 1 := by
      intro f hf
      have hfF : (f : ↥a.s7_N₁) ∈ a.s7_F := hf
      exact (MonoidHom.mem_ker).1 (le_ker_xhatMap a.s7_F hfF)
    have hFρ : ∀ f ∈ FB, ρ f = 1 → f = 1 := by
      intro f hf hρf
      have hf0 : ((f : ↥a.s7_N₁) : G) ∈ a.F₀ := hf
      have hO : ((f : ↥a.s7_N₁) : G) ∈ Open.fusionOddCoreOf (Cen a.y) :=
        hker f (MonoidHom.mem_ker.2 hρf)
      have h1 := eq_one_of_pGroup_two_odd (a.s7_F₀_isPGroup hb) hf0 (s7td_odd_of_mem_O hO)
      exact Subtype.ext (Subtype.ext h1)
    have key := card_range_mul_card_le κ' ρ FB hFκ hFρ
    rw [hrange, hFBcard] at key
    obtain ⟨σ, hσ, hι⟩ := a.ub_base
    have hub : S5.phi a.toPA4 ⟨a.ub, a.ub_cy⟩ = base σ σ := hι
    have hρC : ρ.range ≤ centralizer ({base σ σ} : Set (Wr2 (Equiv.Perm (Fin 5)))) := by
      rintro _ ⟨g, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hcy := a.s7td_mem_Cen hb g.1 g.2
      rw [← hub, hρapply g hcy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (((a.s7_mem_N₁).1 (g : ↥a.s7_N₁).2).2)
    by_cases hd : a.dcase = DCase.d8
    · have hF4 : Nat.card a.F₀ = 4 := a.F₀_card hd
      rw [hF4] at key
      have hr : Nat.card ρ.range ≤ 288 := by
        have := Subgroup.card_le_of_le hρC
        rwa [card_centralizer_base_swap σ hσ] at this
      have h2 : Nat.card (B.map a.s7_κ) * 4 ≤ 288 * Nat.card (ρ.ker.map κ') :=
        key.trans (Nat.mul_le_mul_right _ hr)
      omega
    · have he4 : a.dcase = DCase.e4 := by
        cases h : a.dcase
        · exact absurd h hd
        · rfl
      have hF2 : Nat.card a.F₀ = 2 := by
        rw [(a.F₀_e4 he4).1, Nat.card_zpowers, a.ub_ord]
      rw [hF2] at key
      have hne : a.ι.range ≠ ⊤ := fun h => hd (a.dcase_iff.2 h)
      have hDE : a.ι.range = DE4 := (a.ι_range).resolve_left hne
      have hρD : ρ.range ≤ DE4 := by
        rintro _ ⟨g, rfl⟩
        have hcy := a.s7td_mem_Cen hb g.1 g.2
        rw [hρapply g hcy, ← hDE]
        exact ⟨oMk (Cen a.y) ⟨((g : ↥a.s7_N₁) : G), hcy⟩, rfl⟩
      have hr : Nat.card ρ.range ≤ 144 := by
        have := Subgroup.card_le_of_le (le_inf hρC hρD)
        rwa [card_centralizer_base_swap_inf_DE4 σ hσ] at this
      have h2 : Nat.card (B.map a.s7_κ) * 2 ≤ 144 * Nat.card (ρ.ker.map κ') :=
        key.trans (Nat.mul_le_mul_right _ hr)
      omega

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
