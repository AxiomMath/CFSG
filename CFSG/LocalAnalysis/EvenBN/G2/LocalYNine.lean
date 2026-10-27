module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYEight

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

theorem yamadaF₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaF₁ d t = d.F ⊔ yamadaU₁ d t := by
  obtain ⟨-, -, -, -, -, hFD, -⟩ := d.inclusions
  have hD₁ := hD.D₁_eq
  have hFU₁D₁ : d.F ⊔ yamadaU₁ d t ≤ yamadaD₁ d t := by
    rw [hD₁]
    exact sup_le (hFD.trans le_sup_left) le_sup_right
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ hFU₁D₁)
  · obtain ⟨hxE, hxD₁⟩ := Subgroup.mem_inf.1 hx
    rw [h.yamadaE₁_eq_sup d hK hD] at hxE
    have htN : zpowers t ≤ normalizer ((d.F ⊔ yamadaU₁ d t : Subgroup G) : Set G) :=
      (zpowers_le).2 (mem_normalizer_sup (Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun _ hy => mem_centralizer_singleton_iff.1
          (h.L_le_centralizer (d.image_le _ hy))))
        (hD.yamadaC₁_le_normalizer hK (h.t_mem_yamadaC₁ d hK)))
    obtain ⟨a, ha, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hxE
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk, mul_one]
      exact ha
    · exfalso
      rw [hk] at hxD₁
      refine h.t_not_mem_yamadaD₁ d hK ?_
      have := mul_mem (inv_mem (hFU₁D₁ ha)) hxD₁
      rwa [inv_mul_cancel_left] at this
  · rw [h.yamadaE₁_eq_sup d hK hD]
    exact le_sup_left

theorem eq_or_eq_of_le_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {V : Subgroup G} (hUV : d.U ≤ V) (hVU₁ : V ≤ yamadaU₁ d t)
    (hJ : d.J₃ ≤ normalizer (V : Set G)) : V = d.U ∨ V = yamadaU₁ d t := by
  obtain ⟨ν, hνmul, hνinj, -, hνscal, hκU, hκker⟩ := hD.exists_coords hK
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have hV' : ∀ {g : G}, g ∈ yamadaU₁ d t → g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hg =>
    ⟨yamadaC₁_le d t (hU₁C₁ hg), hC₁U (hU₁C₁ hg)⟩
  have hν1 : ν 1 = 0 := by
    have := hνmul (one_mem d.U) (one_mem d.U)
    rwa [mul_one, left_eq_add] at this
  by_cases hV : V ≤ d.U
  · exact Or.inl (le_antisymm hV hUV)
  right
  refine le_antisymm hVU₁ fun u hu => ?_
  obtain ⟨v, hvV, hvU⟩ := Set.not_subset.1 hV
  have hv := hVU₁ hvV
  have hθv : ν (v⁻¹ * t * v * t) ≠ 0 := fun e => hvU ((hκker hv).1 (e.trans hν1.symm))
  by_cases hθu : ν (u⁻¹ * t * u * t) = 0
  · exact hUV ((hκker hu).1 (hθu.trans hν1.symm))
  obtain ⟨j, hj, hju⟩ := hνscal (ν (u⁻¹ * t * u * t) / ν (v⁻¹ * t * v * t))
    (div_ne_zero hθu hθv)
  have hjt : j * t = t * j :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))
  have hjv : j * v * j⁻¹ ∈ V := (mem_normalizer_iff.1 (hJ hj) v).1 hvV
  have hjvU₁ := hD.conj_mem hK hj hv
  have h1 : (j * v * j⁻¹)⁻¹ * t * (j * v * j⁻¹) * t = u⁻¹ * t * u * t := by
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt]
    refine hνinj ?_ (hκU hu) ?_
    · exact (mem_normalizer_iff.1 (d.J₃_le_inf_normalizer_U hj).2 _).1 (hκU hv)
    · rw [hju _ (hκU hv), div_mul_cancel₀ _ hθv]
  have h2 : ((j * v * j⁻¹)⁻¹ * u)⁻¹ * t * ((j * v * j⁻¹)⁻¹ * u) * t = 1 := by
    rw [hc₁.crossed_mul_of_mem (hV' (inv_mem hjvU₁)) (hV' hu), hc₁.crossed_inv_of_mem (hV' hjvU₁),
      h1, inv_mul_cancel]
  have h3 := hUV (h.mem_U_of_crossed_eq_one d hK hD (mul_mem (inv_mem hjvU₁) hu) h2)
  have := mul_mem hjv h3
  rwa [mul_inv_cancel_left] at this

theorem J_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaY₂ d t : Set G) := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hJN, -, -, hwb2, -⟩ := d.yamada_3_7_G hK4
  have hwbJ : d.wb ∈ normalizer (d.J : Set G) := by
    have : d.wb ∈ L ⊓ normalizer (d.J : Set G) := by
      rw [hJN]
      exact mem_sup_right (subset_closure (Or.inr rfl))
    exact this.2
  have hwbi : d.wb⁻¹ = d.wb := inv_eq_of_mul_eq_one_right hwb2
  intro j hj
  refine mem_normalizer_sup (h.J_le_normalizer_yamadaU₁ d hK hD hj) ?_
  have hj' : d.wb⁻¹ * j * d.wb ∈ d.J := by
    have := (mem_normalizer_iff.1 hwbJ j).1 hj
    rw [hwbi] at this ⊢
    exact this
  have h1 := map_conj_le_normalizer_map_conj (P := d.J) (h.J_le_normalizer_yamadaU₁ d hK hD)
    d.wb ⟨_, hj', rfl⟩
  simpa [mul_assoc] using h1

theorem J_le_normalizer_yamadaS₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaS₂ d t : Set G) := fun j hj => by
  have hjS : j ∈ L ⊓ normalizer (d.S : Set G) := by
    rw [(d.yamada_3_13_1_G).2.2]
    exact mem_sup_left hj
  exact mem_normalizer_sup hjS.2 (h.J_le_normalizer_yamadaY₂ d hK hD hj)

theorem mul_self_mem_yamadaF₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₂ d t) : x * x ∈ yamadaF₁ d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, hYX, -, hXF, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  have hR₁ : x * x ∈ yamadaR₁ d t := by
    obtain ⟨_, Ψ, hΨ, -, hker⟩ := h.exists_hom_yamadaR₂ d hK
    have h1 : Ψ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
      obtain ⟨hy, e⟩ := hΨ ⟨x, hx⟩
      rw [map_mul, e, ← QuotientGroup.mk_mul]
      have : (⟨t * x⁻¹ * t * x, hy⟩ : d.Y) * ⟨t * x⁻¹ * t * x, hy⟩ = 1 :=
        Subtype.ext ((h.cosetData_tY d hK).mul_self_of_mem hy)
      rw [this, QuotientGroup.mk_one]
    have h2 : (⟨x, hx⟩ * ⟨x, hx⟩ : yamadaR₂ d t) ∈ Ψ.ker := h1
    rw [hker, mem_subgroupOf] at h2
    exact h2
  have hF₂ : x * x ∈ d.F ⊔ yamadaY₂ d t := by
    obtain ⟨hR₂, hRN⟩ := h.yamadaR₂_eq_sup_yamadaY₂ d hK hD
    rw [hR₂] at hx
    obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN x hx
    have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
      (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
        mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
    obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS r hr
    have hτs : τ * s = s * τ := (commute_of_mem_zpowers hτ (h.S_le_centralizer d hs)).symm
    have hττ : τ * τ = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
      rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
      · rw [mul_one]
      · exact h.t_mul_t
    have hss : s * s ∈ d.F := by
      have h1 : s ^ 2 ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, rfl⟩
      rwa [(d.yamada_3_12_mho hK4).2.2, sq] at h1
    have hy' : (s * τ)⁻¹ * y * (s * τ) ∈ yamadaY₂ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hRN hr)) y).1 hy
      rwa [inv_inv] at this
    have e : s * τ * y * (s * τ * y) = (s * s) * (((s * τ)⁻¹ * y * (s * τ)) * y) := by
      calc s * τ * y * (s * τ * y) = s * τ * (s * τ) * (((s * τ)⁻¹ * y * (s * τ)) * y) := by
            group
        _ = s * (τ * s) * τ * (((s * τ)⁻¹ * y * (s * τ)) * y) := by group
        _ = s * (s * τ) * τ * (((s * τ)⁻¹ * y * (s * τ)) * y) := by rw [hτs]
        _ = s * s * (τ * τ) * (((s * τ)⁻¹ * y * (s * τ)) * y) := by group
        _ = (s * s) * (((s * τ)⁻¹ * y * (s * τ)) * y) := by rw [hττ, mul_one]
    rw [e]
    exact mul_mem (mem_sup_left hss) (mem_sup_right (mul_mem hy' hy))
  have hY₂F : yamadaY₂ d t ≤ normalizer (d.F : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun f hf =>
      (mem_centralizer_iff.1 (h.M_le_centralizer_yamadaY₂ d hK hD (hFM hf)) y hy).symm)
  obtain ⟨f, hf, y, hy, hfy⟩ := Common.exists_mul_of_le_normalizer hY₂F (x * x) hF₂
  have hfR₁ : f ∈ yamadaR₁ d t := (le_sup_right : d.S ≤ yamadaR₁ d t) ((hFD.trans hDS) hf)
  have hyY₁ : y ∈ yamadaY₁ d t := by
    rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
    refine ⟨hy, ?_⟩
    have := mul_mem (inv_mem hfR₁) hR₁
    rwa [hfy, inv_mul_cancel_left] at this
  rw [hfy, h.yamadaF₁_eq_sup d hK hD]
  obtain ⟨y₀, hy₀, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer'
    ((h.Y_le_yamadaY₂ d hK hD).trans (h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD)) y hyY₁
  rw [← mul_assoc]
  exact mul_mem (mem_sup_left (mul_mem hf ((hYX.trans hXF) hy₀))) (mem_sup_right hu)

theorem exists_mem_yamadaY₂_not_mem_yamadaR₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ∃ y ∈ yamadaY₂ d t, y ∉ yamadaR₁ d t := by
  obtain ⟨u, hu, huU⟩ := h.exists_mem_yamadaU₁_not_mem_U d hK hD
  have hv : d.wb * u * d.wb⁻¹ ∈ yamadaY₂ d t := mem_sup_right ⟨u, hu, rfl⟩
  refine ⟨_, hv, fun hvR₁ => huU (h.mem_U_of_crossed_eq_one d hK hD hu ?_)⟩
  have h1 := (h.mem_yamadaR₁_iff d hK (h.yamadaY₂_le_yamadaR₂ d hK hD hv)).1 hvR₁
  obtain ⟨h2, e2⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu
  rw [e2] at h1
  exact d.eq_one_of_wb_conj_mem_U h2 h1

theorem closure_sq_yamadaS₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : closure {z | ∃ g ∈ yamadaS₂ d t, z = g ^ 2} = yamadaF₁ d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  obtain ⟨-, hS₂R₂, -, -, -⟩ := h.yamada_5_13_3 d hK hD
  have hUF : d.U ≤ d.F := hUY.trans (hYX.trans hXF)
  set E := closure {z | ∃ g ∈ yamadaS₂ d t, z = g ^ 2} with hEdef
  have hEF₁ : E ≤ yamadaF₁ d t := (closure_le _).2 fun z ⟨g, hg, e⟩ => by
    rw [e, sq]
    exact h.mul_self_mem_yamadaF₁ d hK hD (hS₂R₂ hg)
  have hFE : d.F ≤ E := by
    rw [hEdef, ← (d.yamada_3_12_mho hK4).2.2]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, (le_sup_left : d.S ≤ yamadaS₂ d t) hg, e⟩
  have hJ : d.J₃ ≤ normalizer ((E ⊓ yamadaU₁ d t : Subgroup G) : Set G) := fun j hj => by
    have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
    exact Common.mem_normalizer_inf (normalizer_le_normalizer_closure_sq _
      (h.J_le_normalizer_yamadaS₂ d hK hD hjJ)) (h.J_le_normalizer_yamadaU₁ d hK hD hjJ)
  rcases h.eq_or_eq_of_le_yamadaU₁ d hK hD (le_inf (hUF.trans hFE) (hD.spec).2.1)
    inf_le_right hJ with hV | hV
  · exfalso
    have hU₁F : yamadaU₁ d t ≤ normalizer (d.F : Set G) := fun u hu =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun f hf =>
        (mem_centralizer_iff.1 (h.S_le_centralizer_yamadaU₁ d hK hD ((hFD.trans hDS) hf)) u
          hu).symm)
    have hEF : E ≤ d.F := by
      intro z hz
      have hz' := hEF₁ hz
      rw [h.yamadaF₁_eq_sup d hK hD] at hz'
      obtain ⟨f, hf, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁F z hz'
      have huE : u ∈ E := by
        have := mul_mem (inv_mem (hFE hf)) hz
        rwa [inv_mul_cancel_left] at this
      have huU : u ∈ d.U := by
        rw [← hV]
        exact ⟨huE, hu⟩
      exact mul_mem hf (hUF huU)
    have hS₂F : yamadaS₂ d t ≤ normalizer (d.F : Set G) :=
      sup_le (d.S_le_normalizers.2.2.2.2.1) fun y hy =>
        Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun f hf =>
          (mem_centralizer_iff.1 (h.M_le_centralizer_yamadaY₂ d hK hD (hFM hf)) y hy).symm)
    have hEl : ElemModulo d.F (yamadaS₂ d t) := elemModulo_of_mul_self_mem hS₂F fun x hx => by
      have : x ^ 2 ∈ E := subset_closure ⟨x, hx, rfl⟩
      rw [sq] at this
      exact hEF this
    obtain ⟨y, hy, hyR₁⟩ := h.exists_mem_yamadaY₂_not_mem_yamadaR₁ d hK hD
    refine hyR₁ ?_
    rw [← (h.yamada_5_8_6 d hK).1]
    refine ⟨h.yamadaY₂_le_yamadaR₂ d hK hD hy, mem_normalizer_of_conj_mem fun s hs => ?_⟩
    have h1 := (hEl y ((le_sup_right : yamadaY₂ d t ≤ yamadaS₂ d t) hy) s
      ((le_sup_left : d.S ≤ yamadaS₂ d t) hs)).2
    have h2 := h.commutator_mem_yamadaU₁_of_mem_S d hK hD hs hy
    have h3 : y * s * y⁻¹ * s⁻¹ ∈ d.U := by
      rw [← hD.inf_centralizer]
      refine Subgroup.mem_inf.2 ⟨?_, h.L_le_centralizer (d.image_le _
        (by rwa [commutatorElement_def] at h1))⟩
      rw [show y * s * y⁻¹ * s⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ by group]
      exact inv_mem h2
    have := mul_mem ((hUY.trans (hYX.trans (hXF.trans (hFD.trans hDS)))) h3) hs
    rwa [inv_mul_cancel_right] at this
  · refine le_antisymm hEF₁ ?_
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact sup_le hFE (hV ▸ inf_le_left)

theorem closure_sq_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : closure {z | ∃ g ∈ yamadaR₂ d t, z = g ^ 2} = yamadaF₁ d t := by
  obtain ⟨-, hS₂R₂, -, -, -⟩ := h.yamada_5_13_3 d hK hD
  refine le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => ?_) ?_
  · rw [e, sq]
    exact h.mul_self_mem_yamadaF₁ d hK hD hg
  · rw [← h.closure_sq_yamadaS₂ d hK hD]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, hS₂R₂ hg, e⟩

theorem yamadaC₂_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaC₂ d t = yamadaC₁ d t ⊔ yamadaY₂ d t ∧
      yamadaC₁ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  have hC₁ : yamadaC₁ d t = d.D ⊔ yamadaU₁ d t ⊔ zpowers t := by
    rw [(h.yamada_5_8_1 d hK).2.1, hD.D₁_eq]
  refine ⟨?_, (h.yamadaC₁_le_yamadaR₂ d hK).trans (h.yamadaR₂_le_normalizer_yamadaY₂ d hK hD)⟩
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  rw [hC₁]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  · exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left) (hU₁Y₂.trans
      (le_sup_right.trans le_sup_left))) le_sup_right) (le_sup_right.trans le_sup_left)

theorem closure_sq_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} = yamadaY₁ d t := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  obtain ⟨hC₂, hC₁N⟩ := h.yamadaC₂_eq_sup d hK hD
  have hEU := h.elemModulo_U_yamadaC₁ d hK
  have hYY₁ : d.Y ≤ yamadaY₁ d t := le_sup_left
  have hC₂R₂ : yamadaC₂ d t ≤ yamadaR₂ d t := by
    rw [hC₂]
    exact sup_le (h.yamadaC₁_le_yamadaR₂ d hK) (h.yamadaY₂_le_yamadaR₂ d hK hD)
  set E := closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} with hEdef
  have hEY₁ : E ≤ yamadaY₁ d t := (closure_le _).2 fun z ⟨g, hg, e⟩ => by
    rw [e, sq]
    rw [hC₂] at hg
    obtain ⟨c, hc, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hC₁N g hg
    have h1 : c * c ∈ d.U := (hEU c hc c hc).1
    have h2 : c⁻¹ * y * c * y⁻¹ ∈ yamadaY₁ d t := by
      have := h.commutator_mem_yamadaY₁ d hK hD
        ((le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t) (inv_mem hc)) hy
      rwa [inv_inv] at this
    have h3 := h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD (h.yamadaY₂_le_yamadaL₂ d hK hD hy)
    rw [show c * y * (c * y) = (c * c) * (c⁻¹ * y * c * y⁻¹) * (y * y) by group]
    exact mul_mem (mul_mem (hYY₁ (hUY h1)) h2) (hYY₁ h3)
  have hYE : d.Y ≤ E := by
    have htC₂ : t ∈ yamadaC₂ d t := mem_sup_right (mem_zpowers t)
    have hY₂C₂ : yamadaY₂ d t ≤ yamadaC₂ d t := le_sup_right.trans le_sup_left
    rw [hEdef, ← h.closure_sq_yamadaY₂_sup d hK hD]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, sup_le hY₂C₂ ((zpowers_le).2 htC₂) hg, e⟩
  have hJC₂ : d.J ≤ normalizer (yamadaC₂ d t : Set G) := fun j hj => by
    have hjD : j ∈ normalizer (d.D : Set G) := by
      have : j ∈ L ⊓ normalizer (d.D : Set G) := by
        rw [(d.yamada_3_13_2_G).2.1, ← (d.yamada_3_13_2_G).1]
        exact d.J_le_inf_normalizer_U hj
      exact this.2
    exact mem_normalizer_sup (mem_normalizer_sup hjD (h.J_le_normalizer_yamadaY₂ d hK hD hj))
      (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1
        (h.L_le_centralizer (d.image_le _ hj))))
  have hJ : d.J₃ ≤ normalizer ((E ⊓ yamadaU₁ d t : Subgroup G) : Set G) := fun j hj => by
    have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
    exact Common.mem_normalizer_inf (normalizer_le_normalizer_closure_sq _ (hJC₂ hjJ))
      (h.J_le_normalizer_yamadaU₁ d hK hD hjJ)
  rcases h.eq_or_eq_of_le_yamadaU₁ d hK hD (le_inf (hUY.trans hYE) (hD.spec).2.1)
    inf_le_right hJ with hV | hV
  · exfalso
    have hEY : E ≤ d.Y := by
      intro z hz
      have hz' := hEY₁ hz
      obtain ⟨y₀, hy₀, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer'
        ((h.Y_le_yamadaY₂ d hK hD).trans (h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD)) z hz'
      have huE : u ∈ E := by
        have := mul_mem (inv_mem (hYE hy₀)) hz
        rwa [inv_mul_cancel_left] at this
      have huU : u ∈ d.U := by
        rw [← hV]
        exact ⟨huE, hu⟩
      exact mul_mem hy₀ (hUY huU)
    have hEl : ElemModulo d.Y (yamadaC₂ d t) :=
      elemModulo_of_mul_self_mem (hC₂R₂.trans (h.yamadaR₂_le_normalizer_Y d hK)) fun x hx => by
        have : x ^ 2 ∈ E := subset_closure ⟨x, hx, rfl⟩
        rw [sq] at this
        exact hEY this
    obtain ⟨y, hy, hyR₁⟩ := h.exists_mem_yamadaY₂_not_mem_yamadaR₁ d hK hD
    refine hyR₁ ?_
    rw [← (h.yamada_5_8_6 d hK).2]
    refine ⟨h.yamadaY₂_le_yamadaR₂ d hK hD hy, mem_normalizer_of_conj_mem fun δ hδ => ?_⟩
    have h1 := (hEl y ((le_sup_right.trans le_sup_left : yamadaY₂ d t ≤ yamadaC₂ d t) hy) δ
      ((le_sup_left.trans le_sup_left : d.D ≤ yamadaC₂ d t) hδ)).2
    rw [commutatorElement_def] at h1
    have := mul_mem ((hYX.trans (hXF.trans hFD)) h1) hδ
    rwa [inv_mul_cancel_right] at this
  · refine le_antisymm hEY₁ ?_
    exact sup_le hYE (hV ▸ inf_le_left)

theorem yamada_5_15_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    closure {z | ∃ g ∈ yamadaR₂ d t, z = g ^ 2} = yamadaF₁ d t ∧
      closure {z | ∃ g ∈ yamadaS₂ d t, z = g ^ 2} = yamadaF₁ d t ∧
      closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} = yamadaY₁ d t :=
  ⟨h.closure_sq_yamadaR₂ d hK hD, h.closure_sq_yamadaS₂ d hK hD, h.closure_sq_yamadaC₂ d hK hD⟩

theorem yamadaE₂_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaF₂ d t ≤ yamadaM₂ d t ∧ yamadaE₂ d t ≤ yamadaL₂ d t := by
  obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
  have hF₂M₂ : yamadaF₂ d t ≤ yamadaM₂ d t := sup_le_sup_right hFM _
  refine ⟨hF₂M₂, ?_⟩
  rw [h.yamadaL₂_eq_sup d hK hD]
  exact sup_le_sup_right hF₂M₂ _

theorem yamadaE₂_inf_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaE₂ d t ⊓ yamadaM₂ d t = yamadaF₂ d t := by
  obtain ⟨hF₂M₂, -⟩ := h.yamadaE₂_le_yamadaL₂ d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : zpowers t ≤ normalizer (yamadaF₂ d t : Set G) := (zpowers_le).2
    (mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hy =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hy))))
      (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂))
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hF₂M₂)
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hx₁
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with hk | hk
  · rw [hk, mul_one]
    exact ha
  · exfalso
    rw [hk] at hx₂
    refine h.t_not_mem_yamadaM₂ d hK hD ?_
    have := mul_mem (inv_mem (hF₂M₂ ha)) hx₂
    rwa [inv_mul_cancel_left] at this

theorem abelian_sup_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {E : Subgroup G} (hEM : E ≤ d.M) (hYE : d.Y ≤ E)
    (hE : CFSG.IsElementaryAbelian 2 E) (hEc : Nat.card E = Nat.card K ^ 3) :
    (∀ x ∈ E ⊔ yamadaY₂ d t, ∀ y ∈ E ⊔ yamadaY₂ d t, x * y = y * x) ∧
      Nat.card (E ⊔ yamadaY₂ d t : Subgroup G) = Nat.card K ^ 5 := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hMY₂ := h.M_le_centralizer_yamadaY₂ d hK hD
  have : IsMulCommutative E := hE.toIsMulCommutative
  have : IsMulCommutative (yamadaY₂ d t) :=
    ⟨⟨fun a b => Subtype.ext (h.yamadaY₂_mul_comm d hK hD a.2 b.2)⟩⟩
  have hc := isMulCommutative_sup (A := E) (B := yamadaY₂ d t) fun a ha b hb =>
    (mem_centralizer_iff.1 (hMY₂ (hEM ha)) b hb).symm
  refine ⟨fun x hx y hy => congrArg Subtype.val
    (mul_comm' (⟨x, hx⟩ : (E ⊔ yamadaY₂ d t : Subgroup G)) ⟨y, hy⟩), ?_⟩
  have hN : yamadaY₂ d t ≤ normalizer (E : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (hMY₂ (hEM hx)) y hy).symm)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have hinf : E ⊓ yamadaY₂ d t = d.Y := le_antisymm
    (by rw [← h.M_inf_yamadaY₂ d hK hD]; exact inf_le_inf_right _ hEM)
    (le_inf hYE (h.Y_le_yamadaY₂ d hK hD))
  rw [hinf, d.cards.2.1, hEc, h.card_yamadaY₂ d hK hD] at h1
  have hpos : 0 < Nat.card K ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))

theorem yamada_5_15_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : CFSG.Open.thompsonSubgroup (yamadaE₂ d t) = yamadaF₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, hYX, hYW, hXF, hWF, -, hFM, -⟩ := d.inclusions
  obtain ⟨hF₂M₂, hE₂L₂⟩ := h.yamadaE₂_le_yamadaL₂ d hK hD
  have hF₂E₂ : yamadaF₂ d t ≤ yamadaE₂ d t := le_sup_left
  have hq : 2 * Nat.card K ^ 3 < Nat.card K ^ 5 := by
    have : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = Nat.card K ^ 5 := by ring
  have hcomm : ∀ {A : Subgroup G}, IsMulCommutative A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun {A} _ x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsmall : ∀ B : Subgroup G, B ≤ yamadaE₂ d t → IsMulCommutative B →
      ¬ B ≤ yamadaF₂ d t → Nat.card B ≤ 2 * Nat.card K ^ 3 := fun B hB hBc hBF => by
    refine h.card_le_of_not_le_yamadaM₂ d hK hD (hB.trans hE₂L₂) (hcomm hBc) fun hBM => hBF ?_
    rw [← h.yamadaE₂_inf_yamadaM₂ d hK hD]
    exact le_inf hB hBM
  have hmax : ∀ B : Subgroup G, B ≤ yamadaE₂ d t → IsMulCommutative B →
      Nat.card B ≤ Nat.card K ^ 5 := fun B hB hBc => by
    by_cases hBF : B ≤ yamadaF₂ d t
    · exact h.card_le_of_le_yamadaM₂ d hK hD (hBF.trans hF₂M₂) (hcomm hBc)
    · exact (hsmall B hB hBc hBF).trans hq.le
  obtain ⟨hW₂c, hW₂card⟩ := h.abelian_sup_yamadaY₂ d hK hD (hWF.trans hFM) hYW
    d.isElementaryAbelian.2.2.2 d.cards.2.2.2.1
  obtain ⟨hX₂c, hX₂card⟩ := h.abelian_sup_yamadaY₂ d hK hD (hXF.trans hFM) hYX
    d.isElementaryAbelian.2.2.1 d.cards.2.2.1
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  have hmem : ∀ {A : Subgroup G}, A ≤ yamadaF₂ d t → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A = Nat.card K ^ 5 →
      A ≤ ⨆ (A' : Subgroup G) (_ : A' ≤ yamadaE₂ d t) (_ : IsMulCommutative A')
        (_ : ∀ B : Subgroup G, B ≤ yamadaE₂ d t → IsMulCommutative B →
          Nat.card B ≤ Nat.card A'), A' := by
    intro A hAF hAc hAcard
    have hAc' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
    have hAm : ∀ B : Subgroup G, B ≤ yamadaE₂ d t → IsMulCommutative B →
        Nat.card B ≤ Nat.card A := fun B hB hBc => (hmax B hB hBc).trans hAcard.ge
    exact le_iSup_of_le A (le_iSup_of_le (hAF.trans hF₂E₂) (le_iSup_of_le hAc'
      (le_iSup_of_le hAm le_rfl)))
  refine le_antisymm (iSup_le fun A => iSup_le fun hAE => iSup_le fun hAc =>
    iSup_le fun hAm => ?_) ?_
  swap
  · have hF₂ : yamadaF₂ d t = (d.W ⊔ yamadaY₂ d t) ⊔ (d.X ⊔ yamadaY₂ d t) := by
      rw [show yamadaF₂ d t = d.F ⊔ yamadaY₂ d t from rfl, ← (d.yamada_defs).2.2.2.1]
      apply le_antisymm
      · exact sup_le (sup_le (le_sup_left.trans le_sup_right) (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left)
      · exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    rw [hF₂]
    have hW₂F₂ : d.W ⊔ yamadaY₂ d t ≤ yamadaF₂ d t := sup_le_sup_right hWF _
    have hX₂F₂ : d.X ⊔ yamadaY₂ d t ≤ yamadaF₂ d t := sup_le_sup_right hXF _
    exact sup_le (hmem hW₂F₂ hW₂c hW₂card) (hmem hX₂F₂ hX₂c hX₂card)
  by_contra hAF
  have h1 := hAm _ ((sup_le_sup_right hWF _).trans hF₂E₂)
    ⟨⟨fun a b => Subtype.ext (hW₂c a a.2 b b.2)⟩⟩
  have h2 := hsmall A hAE hAc hAF
  rw [hW₂card] at h1
  omega

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
