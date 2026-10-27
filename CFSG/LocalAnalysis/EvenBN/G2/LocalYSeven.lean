module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYSix
public import CFSG.LocalAnalysis.EvenBN.G2.TorusCentralizers

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem normalizer_yamadaL₂_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
  have h1 := normalizer_le_normalizer_thompsonSubgroup (yamadaL₂ d t)
  rw [h.yamada_5_13_2 d hK hD] at h1
  have h2 := normalizer_le_normalizer_center (yamadaM₂ d t)
  rw [h.yamadaM₂_center d hK hD] at h2
  exact ⟨h1, h1.trans h2⟩

theorem S_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.S ≤ normalizer (yamadaY₂ d t : Set G) :=
  (h.S_le_normalizer_yamadaL₂ d).trans (h.normalizer_yamadaL₂_le d hK hD).2

theorem yamadaS₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₂ d t ⊓ centralizer ({t} : Set G) = d.S := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  apply le_antisymm
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer'
      (h.S_le_normalizer_yamadaY₂ d hK hD) x hx₁
    have hyC : y ∈ centralizer ({t} : Set G) := by
      have := mul_mem (inv_mem (h.S_le_centralizer d hs)) hx₂
      rwa [inv_mul_cancel_left] at this
    have hyY : y ∈ d.Y := by
      rw [← h.yamadaY₂_inf_centralizer d hK hD]
      exact ⟨hy, hyC⟩
    exact mul_mem hs ((hYX.trans (hXF.trans (hFD.trans hDS))) hyY)
  · exact le_inf le_sup_left (h.S_le_centralizer d)

theorem yamada_5_13_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    d.S ≤ normalizer (yamadaY₂ d t : Set G) ∧ yamadaS₂ d t ≤ yamadaR₂ d t ∧
      yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t ∧
      yamadaR₂ d t ≤ normalizer (yamadaS₂ d t : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hSR₂ : d.S ≤ yamadaR₂ d t := le_sup_right
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have hS₂R₂ : yamadaS₂ d t ≤ yamadaR₂ d t :=
    sup_le hSR₂ ((h.yamadaY₂_le_yamadaL₂ d hK hD).trans hL₂R₂)
  have hM₂S₂ : yamadaM₂ d t ≤ yamadaS₂ d t := sup_le_sup_right hMS _
  have hR₂ : yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t := by
    apply le_antisymm
    · have hR₂' : yamadaR₂ d t = yamadaL₂ d t ⊔ d.S := rfl
      rw [hR₂', h.yamadaL₂_eq_sup d hK hD]
      exact sup_le (sup_le (hM₂S₂.trans le_sup_left) le_sup_right)
        ((le_sup_left : d.S ≤ yamadaS₂ d t).trans le_sup_left)
    · exact sup_le hS₂R₂ ((zpowers_le).2 (hL₂R₂ htL₂))
  have ht : t ∉ yamadaS₂ d t := fun ht => by
    refine h.t_not_mem_L (d.image_le (Model.S K) ?_)
    rw [← G2Data.S, ← h.yamadaS₂_inf_centralizer d hK hD]
    exact ⟨ht, h.t_mem_centralizer⟩
  have htN : t ∈ normalizer (yamadaS₂ d t : Set G) := by
    refine mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2
      fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))) ?_
    exact h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  refine ⟨h.S_le_normalizer_yamadaY₂ d hK hD, hS₂R₂, hR₂, ht, ?_⟩
  rw [hR₂]
  exact sup_le le_normalizer ((zpowers_le).2 htN)

theorem mul_self_mem_Y_of_mem_yamadaL₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaL₂ d t) :
    x * x ∈ d.Y := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  have hcY := h.cosetData_tY d hK
  have hV : ∀ {g : G}, g ∈ yamadaL₂ d t → g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.Y : Set G) := fun hg => ⟨yamadaL₂_le d t hg, hL₂Y hg⟩
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : zpowers t ≤ normalizer (yamadaM₂ d t : Set G) :=
    (zpowers_le).2 (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)
  rw [h.yamadaL₂_eq_sup d hK hD] at hx
  obtain ⟨m₂, hm₂, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hx
  obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_M d hK hD) m₂ hm₂
  have hyL₂ := h.yamadaY₂_le_yamadaL₂ d hK hD hy
  have hmm : m * m ∈ d.Y := by
    have h1 : m ^ 2 ∈ closure {z | ∃ g ∈ d.M, z = g ^ 2} := subset_closure ⟨m, hm, rfl⟩
    rwa [(d.yamada_3_12_mho hK4).2.1, sq] at h1
  have hyy : y * y ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    refine ⟨mul_mem hy hy, mem_centralizer_singleton_iff.2 ?_⟩
    have e := hcY.crossed_mul_of_mem (hV hyL₂) (hV hyL₂)
    rw [hcY.mul_self_of_mem (hcY.crossed_mem_of_mem (hV hyL₂))] at e
    calc y * y * t = y * y * ((y * y)⁻¹ * t * (y * y) * t) * t := by rw [e, mul_one]
      _ = t * (y * y) * (t * t) := by group
      _ = t * (y * y) := by rw [h.t_mul_t, mul_one]
  have hym : y * m = m * y := mem_centralizer_iff.1 (h.M_le_centralizer_yamadaY₂ d hK hD hm) y hy
  have htm : t * m = m * t := (mem_centralizer_singleton_iff.1
    (h.L_le_centralizer (d.image_le _ hm))).symm
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
  · rw [mul_one, show m * y * (m * y) = m * (y * m) * y by group, hym,
      show m * (m * y) * y = m * m * (y * y) by group]
    exact mul_mem hmm hyy
  · have e : m * y * t * (m * y * t) = m * m * (y * y) * (y⁻¹ * t * y * t) := by
      calc m * y * t * (m * y * t) = m * y * (t * m) * y * t := by group
        _ = m * y * (m * t) * y * t := by rw [htm]
        _ = m * (y * m) * t * y * t := by group
        _ = m * (m * y) * t * y * t := by rw [hym]
        _ = m * m * (y * y) * (y⁻¹ * t * y * t) := by group
    rw [e]
    exact mul_mem (mul_mem hmm hyy) (hcY.crossed_mem_of_mem (hV hyL₂))

theorem closure_sq_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : closure {z | ∃ g ∈ yamadaL₂ d t, z = g ^ 2} = d.Y := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  refine le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => ?_) ?_
  · rw [e, sq]
    exact h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hg
  · rw [← (d.yamada_3_12_mho hK4).2.1]
    exact closure_mono fun z ⟨g, hg, e⟩ =>
      ⟨g, (le_sup_left.trans (h.tM_le_yamadaL₂ d hK)) hg, e⟩

theorem closure_sq_yamadaY₂_sup (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    closure {z | ∃ g ∈ yamadaY₂ d t ⊔ zpowers t, z = g ^ 2} = d.Y := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have hle : yamadaY₂ d t ⊔ zpowers t ≤ yamadaL₂ d t :=
    sup_le (h.yamadaY₂_le_yamadaL₂ d hK hD) ((zpowers_le).2 htL₂)
  set E := closure {z | ∃ g ∈ yamadaY₂ d t ⊔ zpowers t, z = g ^ 2} with hE
  have hEY : E ≤ d.Y := by
    rw [← h.closure_sq_yamadaL₂ d hK hD]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hle hg, e⟩
  have hN : d.leviB ≤ normalizer (E : Set G) := by
    intro l hl
    have hl' := h.leviB_le_centralizer_inf_normalizer_Y d hl
    have hlL₂ := le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hl')
    refine normalizer_le_normalizer_closure_sq _ (mem_normalizer_sup
      ((h.normalizer_yamadaL₂_le d hK hD).2 hlL₂) (mem_normalizer_zpowers ?_))
    exact mem_centralizer_singleton_iff.1 hl'.1
  rcases (d.yamada_3_16_2_G hN).1 hEY with hE0 | hE1
  · exfalso
    have hU₁U : ¬ yamadaU₁ d t ≤ d.U := by
      intro hle'
      have h1 := Subgroup.card_le_of_le hle'
      rw [(hD.yamada_5_10_1).2.2, d.cards.1] at h1
      have h2 : 1 < Nat.card K := by omega
      nlinarith
    obtain ⟨u, hu, huU⟩ := Set.not_subset.1 hU₁U
    have huY₂ : u ∈ yamadaY₂ d t := yamadaU₁_le_yamadaY₂ d t hu
    have huE : u ^ 2 ∈ E := subset_closure ⟨u, mem_sup_left huY₂, rfl⟩
    have htuE : (t * u) ^ 2 ∈ E :=
      subset_closure ⟨t * u, mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left huY₂), rfl⟩
    rw [hE0, mem_bot, sq] at huE htuE
    refine huU (h.mem_U_of_crossed_eq_one d hK hD hu ?_)
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huE
    calc u⁻¹ * t * u * t = u * t * u * t := by rw [hui]
      _ = t⁻¹ * ((t * u) * (t * u)) * t := by group
      _ = 1 := by rw [htuE, mul_one, inv_mul_cancel]
  · exact hE1

theorem yamada_5_13_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    closure {z | ∃ g ∈ yamadaL₂ d t, z = g ^ 2} = d.Y ∧
      closure {z | ∃ g ∈ yamadaY₂ d t ⊔ zpowers t, z = g ^ 2} = d.Y :=
  ⟨h.closure_sq_yamadaL₂ d hK hD, h.closure_sq_yamadaY₂_sup d hK hD⟩

theorem J_le_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaU₁ d t : Set G) := fun _ hj =>
  hD.inf_normalizer_U_le_normalizer hK (d.J_le_inf_normalizer_U hj)

omit [Finite K] in
theorem J₅_le_centralizer_map_wb (h : Setup G L f t) (d : G2Data L K) (hD : h.DoublingFacts d) :
    d.J₅ ≤ centralizer ((yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) := by
  rw [← (d.Ji_conj_G).1]
  rintro _ ⟨j, hj, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hju : j * u = u * j := mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu) j hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc d.wb * u * d.wb⁻¹ * (d.wb * j * d.wb⁻¹) = d.wb * (u * j) * d.wb⁻¹ := by group
    _ = d.wb * (j * u) * d.wb⁻¹ := by rw [hju]
    _ = d.wb * j * d.wb⁻¹ * (d.wb * u * d.wb⁻¹) := by group

theorem mul_conj_mem_yamadaU₁_of_mem_J₅ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {j y : G} (hj : j ∈ d.J₅)
    (hy : y ∈ yamadaY₂ d t) : y⁻¹ * (j * y * j⁻¹) ∈ yamadaU₁ d t := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.map_wb_yamadaU₁_le_normalizer d hK hD) y hy
  have hjv : j * v * j⁻¹ = v := by
    rw [← mem_centralizer_iff.1 (h.J₅_le_centralizer_map_wb d hD hj) v hv, mul_inv_cancel_right]
  have hju : j * u * j⁻¹ ∈ yamadaU₁ d t :=
    (mem_normalizer_iff.1 (h.J_le_normalizer_yamadaU₁ d hK hD (d.J₅_le_J hj)) u).1 hu
  rw [show (u * v)⁻¹ * (j * (u * v) * j⁻¹) = v⁻¹ * (u⁻¹ * (j * u * j⁻¹)) * (j * v * j⁻¹) by
    group, hjv]
  have := (mem_normalizer_iff.1 (inv_mem (h.map_wb_yamadaU₁_le_normalizer d hK hD hv)) _).1
    (mul_mem (inv_mem hu) hju)
  rwa [inv_inv] at this

theorem yamadaY₂_le_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaY₂ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun _ hy =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hu =>
    h.yamadaY₂_mul_comm d hK hD (yamadaU₁_le_yamadaY₂ d t hu) hy)

theorem elemModulo_S_inf_sup_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4)
    (hXB : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaB d)
    (hP : ∀ P : Subgroup G, P ≤ yamadaB d → IsPGroup 2 P →
      yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ P → ElemModulo (yamadaU₁ d t) P) :
    ElemModulo (yamadaU₁ d t) (d.S ⊓ centralizer (d.J₁ : Set G) ⊔ yamadaY₂ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₁X : yamadaU₁ d t ≤ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) :=
    le_inf hD.le_D₁ hD.le_centralizer_J₁
  have hwbJ : d.wb ∈ normalizer (d.J₁ : Set G) := by
    have e : d.J₁.map (MulAut.conj d.wb).toMonoidHom = d.J₁ := by
      rw [(d.Ji_conj_G).1, ← (d.yamada_3_9_4_four_G hK4).2.1]
    exact mem_normalizer_of_map_conj_eq e
  have hwbL : d.wb ∈ normalizer (L : Set G) :=
    Subgroup.le_normalizer (d.wb_mem_normalizer.1.1)
  have hPB : d.S ⊓ centralizer (d.J₁ : Set G) ⊔ yamadaY₂ d t ≤ yamadaB d := by
    refine sup_le ((inf_le_inf_right _ d.inclusions.2.2.2.2.2.2.2.2.2).trans
      (inf_centralizer_J₁_le_yamadaB d)) (sup_le (hU₁X.trans hXB) ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact conj_mem_yamadaB_of_mem_normalizer d hwbL hwbJ (hXB (hU₁X hu))
  have hSN : d.S ⊓ centralizer (d.J₁ : Set G) ≤ normalizer (yamadaY₂ d t : Set G) :=
    inf_le_left.trans (h.yamada_5_13_3 d hK hD).1
  have hP2 : IsPGroup 2 (d.S ⊓ centralizer (d.J₁ : Set G) ⊔ yamadaY₂ d t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (d.isSylowOf_S.isPGroup.to_le inf_le_left)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (h.yamadaY₂_le_yamadaL₂ d hK hD)) hSN
  refine hP _ hPB hP2 fun x hx => ?_
  obtain ⟨hxD₁, hxJ⟩ := Subgroup.mem_inf.1 hx
  rw [hD.D₁_eq] at hxD₁
  obtain ⟨δ, hδ, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer
    ((hD.le_C₁ hK).trans (h.yamadaC₁_le_normalizer_D d hK)) _ hxD₁
  have hδJ : δ ∈ centralizer (d.J₁ : Set G) := by
    have := mul_mem hxJ (inv_mem (hD.le_centralizer_J₁ hu))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left ⟨d.inclusions.2.2.2.2.2.2.2.1 hδ, hδJ⟩)
    (mem_sup_right (yamadaU₁_le_yamadaY₂ d t hu))

theorem commutator_mem_yamadaU₁_of_mem_S (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {s y : G} (hs : s ∈ d.S)
    (hy : y ∈ yamadaY₂ d t) : s * y * s⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSY₂ := h.S_le_normalizer_yamadaY₂ d hK hD
  have hSU₁ := h.S_le_normalizer_yamadaU₁ d hK hD
  have hK₀ : ∀ g ∈ d.S, ∀ y ∈ yamadaY₂ d t, g * y * g⁻¹ ∈ yamadaY₂ d t := fun g hg y hy =>
    (mem_normalizer_iff.1 (hSY₂ hg) y).1 hy
  have hB : ∀ g ∈ d.S, ∀ b ∈ yamadaU₁ d t, g * b * g⁻¹ ∈ yamadaU₁ d t := fun g hg b hb =>
    (mem_normalizer_iff.1 (hSU₁ hg) b).1 hb
  set N := Common.centralizerMod d.S (yamadaY₂ d t) (yamadaU₁ d t) hK₀ hB with hNdef
  have hJ₅S : d.J₅ ≤ normalizer (d.S : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.S : Set G) := by
      rw [(d.yamada_3_13_1_G).2.2]
      exact mem_sup_left (d.J₅_le_J hj)
    exact this.2
  have hJ₅U₁ : d.J₅ ≤ normalizer (yamadaU₁ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaU₁ d hK hD (d.J₅_le_J hj)
  have hJ₅Y₂ : d.J₅ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJ₅U₁ hj)
      (Subgroup.centralizer_le_normalizer _ (h.J₅_le_centralizer_map_wb d hD hj))
  have h2 : IsPGroup 2 d.S := d.isSylowOf_S.isPGroup
  have hsolv : Group.IsSolvable d.S := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₅).Coprime (Nat.card d.S) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₅, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  have hyN : ∀ {y : G}, y ∈ yamadaY₂ d t → y ∈ normalizer (yamadaU₁ d t : Set G) :=
    fun hy => h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD hy
  have hfix : ∀ j ∈ d.J₅, s⁻¹ * (j * s * j⁻¹) ∈ N := by
    intro j hj
    have hs' : j * s * j⁻¹ ∈ d.S := (mem_normalizer_iff.1 (hJ₅S hj) s).1 hs
    refine ⟨mul_mem (inv_mem hs) hs', fun y hy => ?_⟩
    have ha := h.mul_conj_mem_yamadaU₁_of_mem_J₅ d hK hD (inv_mem hj) hy
    rw [inv_inv] at ha
    have hb := h.mul_conj_mem_yamadaU₁_of_mem_J₅ d hK hD hj (hK₀ s hs y hy)
    have ha' : j * (s * (y⁻¹ * (j⁻¹ * y * j)) * s⁻¹) * j⁻¹ ∈ yamadaU₁ d t :=
      (mem_normalizer_iff.1 (hJ₅U₁ hj) _).1 (hB s hs _ ha)
    have key : s⁻¹ * (j * s * j⁻¹) * y * (s⁻¹ * (j * s * j⁻¹))⁻¹ * y⁻¹ =
        y * (s⁻¹ * (((s * y * s⁻¹)⁻¹ * (j * (s * y * s⁻¹) * j⁻¹)) *
          (j * (s * (y⁻¹ * (j⁻¹ * y * j)) * s⁻¹) * j⁻¹)) * s) * y⁻¹ := by group
    rw [key]
    have h1 := (mem_normalizer_iff.1 (inv_mem (hSU₁ hs)) _).1 (mul_mem hb ha')
    rw [inv_inv] at h1
    exact (mem_normalizer_iff.1 (hyN hy) _).1 h1
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime (N := N)
    (fun x hx => hx.1) (fun x hx => mem_normalizer_of_conj_mem fun z hz =>
      Common.conj_mem_centralizerMod hx hz) hJ₅S (fun j hj => mem_normalizer_of_conj_mem
      fun z hz => ⟨(mem_normalizer_iff.1 (hJ₅S hj) z).1 hz.1, fun y hy => by
        have hy' : j⁻¹ * y * j ∈ yamadaY₂ d t := by
          have := (mem_normalizer_iff.1 (inv_mem (hJ₅Y₂ hj)) y).1 hy
          rwa [inv_inv] at this
        have h1 := (mem_normalizer_iff.1 (hJ₅U₁ hj) _).1 (hz.2 _ hy')
        rwa [show j * (z * (j⁻¹ * y * j) * z⁻¹ * (j⁻¹ * y * j)⁻¹) * j⁻¹ =
          j * z * j⁻¹ * y * (j * z * j⁻¹)⁻¹ * y⁻¹ by group] at h1⟩)
    hsolv hcop hs hfix
  have hcy : c * y * c⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
    rcases hD.branch with h8 | ⟨hK4, -, hXB, hP⟩
    ·
      have hcY : c ∈ d.Y := by
        have := hc
        rw [d.S_inf_centralizer_J₅ h8] at this
        rw [← (d.yamada_defs).1]
        exact mem_sup_left this
      have hcy : c * y = y * c := h.yamadaY₂_mul_comm d hK hD (h.Y_le_yamadaY₂ d hK hD hcY) hy
      rw [hcy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    ·
      have hcJ₁ : c ∈ d.S ⊓ centralizer (d.J₁ : Set G) := by
        rw [(d.yamada_3_9_4_four_G hK4).2.1]
        exact hc
      have := (h.elemModulo_S_inf_sup_yamadaY₂ d hK hD hK4 hXB hP) c (mem_sup_left hcJ₁) y
        (mem_sup_right hy)
      rw [← commutatorElement_def]
      exact this.2
  rw [show c * n * y * (c * n)⁻¹ * y⁻¹ = c * (n * y * n⁻¹ * y⁻¹) * c⁻¹ * (c * y * c⁻¹ * y⁻¹) by
    group]
  exact mul_mem (hB c hc.1 _ (hn.2 y hy)) hcy

theorem yamadaS₂_center (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₂ d t ⊓ centralizer (yamadaS₂ d t : Set G) = yamadaU₁ d t := by
  obtain ⟨-, hS₂R₂, -, -, -⟩ := h.yamada_5_13_3 d hK hD
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hS₁S₂ : yamadaS₁ d t ≤ yamadaS₂ d t := by
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact sup_le le_sup_left hU₁S₂
  apply le_antisymm
  · intro z hz
    obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
    have hzN : z ∈ normalizer (d.S : Set G) := Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (le_sup_left : d.S ≤ yamadaS₂ d t) hz₂)
    have hzR₁ : z ∈ yamadaR₁ d t := by
      rw [← (h.yamada_5_8_6 d hK).1]
      exact ⟨hS₂R₂ hz₁, hzN⟩
    obtain ⟨hR₁, hRN⟩ := h.yamadaR₁_eq_sup d hK hD
    rw [hR₁] at hzR₁
    obtain ⟨r, hr, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN _ hzR₁
    have hrS₂ : r ∈ yamadaS₂ d t := by
      have := mul_mem hz₁ (inv_mem (hU₁S₂ hu))
      rwa [mul_inv_cancel_right] at this
    have hrC : r ∈ centralizer ({t} : Set G) := by
      rw [← h.yamadaR_eq d] at hr
      exact h.yamadaR_le_centralizer d hr
    have hrS : r ∈ d.S := by
      rw [← h.yamadaS₂_inf_centralizer d hK hD]
      exact ⟨hrS₂, hrC⟩
    rw [← h.yamada_5_11_1 d hK hD]
    refine ⟨?_, Subgroup.centralizer_le hS₁S₂ hz₂⟩
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact mul_mem (mem_sup_left hrS) (mem_sup_right hu)
  · refine le_inf hU₁S₂ ?_
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (h.S_le_centralizer_yamadaU₁ d hK hD) fun y hy => mem_centralizer_iff.2
      fun u hu => h.yamadaY₂_mul_comm d hK hD (yamadaU₁_le_yamadaY₂ d t hu) hy

theorem mem_yamadaY₂_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaS₂ d t) :
    x ∈ yamadaY₂ d t ↔ ∀ g ∈ yamadaS₂ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hSY₂ := h.S_le_normalizer_yamadaY₂ d hK hD
  have hSU₁ := h.S_le_normalizer_yamadaU₁ d hK hD
  have fwd : ∀ {x : G}, x ∈ yamadaY₂ d t → ∀ g ∈ yamadaS₂ d t,
      x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
    intro x hxY g hg
    obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hSY₂ g hg
    have hxy : x * y = y * x := h.yamadaY₂_mul_comm d hK hD hxY hy
    have hxy' : y * x⁻¹ = x⁻¹ * y := by
      calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
        _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hxy]
        _ = x⁻¹ * y := by group
    have e : x * (s * y) * x⁻¹ * (s * y)⁻¹ = (s * x * s⁻¹ * x⁻¹)⁻¹ := by
      calc x * (s * y) * x⁻¹ * (s * y)⁻¹ = x * s * (y * x⁻¹) * y⁻¹ * s⁻¹ := by group
        _ = x * s * (x⁻¹ * y) * y⁻¹ * s⁻¹ := by rw [hxy']
        _ = (s * x * s⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (h.commutator_mem_yamadaU₁_of_mem_S d hK hD hs hxY)
  refine ⟨fun hxY => fwd hxY, fun hc => ?_⟩
  obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hSY₂ x hx
  have hsY : s ∈ d.Y := by
    rw [d.mem_Y_iff_commutator hK4 hs]
    intro g hg
    have hgS₂ : g ∈ yamadaS₂ d t := mem_sup_left hg
    have h1 := hc g hgS₂
    have h2 := fwd hy g hgS₂
    have h3 : s * g * s⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
      rw [show s * g * s⁻¹ * g⁻¹ = (s * (y * g * y⁻¹ * g⁻¹) * s⁻¹)⁻¹ *
        (s * y * g * (s * y)⁻¹ * g⁻¹) by group]
      exact mul_mem (inv_mem ((mem_normalizer_iff.1 (hSU₁ hs) _).1 h2)) h1
    rw [commutatorElement_def, ← hD.inf_centralizer]
    exact ⟨h3, h.S_le_centralizer d (mul_mem (mul_mem (mul_mem hs hg) (inv_mem hs))
      (inv_mem hg))⟩
  exact mul_mem (h.Y_le_yamadaY₂ d hK hD hsY) hy

theorem yamada_5_13_5 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₂ d t ⊓ centralizer (yamadaS₂ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype =
        yamadaY₂ d t := by
  have hZ := h.yamadaS₂_center d hK hD
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hY₂S₂ : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right
  have hmem1 : ∀ x : yamadaS₂ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₂ d t) 1 ↔ (x : G) ∈ yamadaU₁ d t := by
    intro x
    rw [Subgroup.upperCentralSeries_one, ← hZ]
    constructor
    · intro hx
      exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)
  have hmem2 : ∀ x : yamadaS₂ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₂ d t) 2 ↔ (x : G) ∈ yamadaY₂ d t := by
    intro x
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      h.mem_yamadaY₂_iff d hK hD x.2]
    constructor
    · intro hx g hg
      have := (hmem1 _).1 (hx ⟨g, hg⟩)
      simpa [commutatorElement_def] using this
    · intro hx y
      rw [hmem1]
      simpa [commutatorElement_def] using hx y y.2
  refine ⟨hZ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem1 y).1 hy
    · intro hx
      exact ⟨⟨x, hU₁S₂ hx⟩, (hmem1 _).2 hx, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem2 y).1 hy
    · intro hx
      exact ⟨⟨x, hY₂S₂ hx⟩, (hmem2 _).2 hx, rfl⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
