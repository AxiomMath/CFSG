module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YAbel
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckPara

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def Data.NLA₂ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  normalizer (d.A₂ : Set G) ⊓ d.L

@[expose] def Data.D₀ {G : Type} [Group G] (d : Data G) : Subgroup G := ⁅d.C₀, d.NLA₂⁆

@[expose] def Data.Y {G : Type} [Group G] (d : Data G) : Subgroup G :=
  centralizer (d.D₀ : Set G) ⊓ d.D₀

theorem mem_normalizer_sup {G : Type*} [Group G] [Finite G] {H K : Subgroup G} {x : G}
    (hH : x ∈ normalizer (H : Set G)) (hK : x ∈ normalizer (K : Set G)) :
    x ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun h hh => mem_sup_left ((mem_normalizer_iff.1 hH h).1 hh))
      (fun k hk => mem_sup_right ((mem_normalizer_iff.1 hK k).1 hk))
  exact hle hy

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem mem_F_of_central {z : G} (hz : z ∈ d.A₂) (h : ∀ a ∈ d.A₂, a * z = z * a) : z ∈ d.F := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  refine d.ι_mem_pull_iff.2 (mem_Fsub_of_central hζ fun α hα => d.ι_injective ?_)
  rw [map_mul, map_mul]
  exact h _ (d.ι_mem_pull_iff.2 hα)

omit [Finite G] in
theorem exists_eq_mul_of_mem_NLA₂ {n : G} (hn : n ∈ d.NLA₂) :
    ∃ l ∈ d.Lev, ∃ a ∈ d.A₂, n = l * a := by
  obtain ⟨hnN, hnL⟩ := Subgroup.mem_inf.1 hn
  obtain ⟨ν, rfl⟩ : ∃ ν : SU52, d.ι ν = n := ⟨d.η ⟨n, hnL⟩, ι_η' hnL⟩
  have hνA : ∀ α ∈ A₂sub, ν * α * ν⁻¹ ∈ A₂sub := fun α hα => by
    have := (mem_normalizer_iff.1 hnN _).1 (d.ι_mem_pull_iff.2 hα)
    rw [ι_conj] at this
    exact (d.ι_mem_pull_iff (M := A₂sub)).1 this
  have hνA' : ∀ α ∈ A₂sub, ν⁻¹ * α * ν ∈ A₂sub := fun α hα => by
    have := (mem_normalizer_iff.1 (inv_mem hnN) _).1 (d.ι_mem_pull_iff.2 hα)
    rw [← map_inv, ι_conj, inv_inv] at this
    exact (d.ι_mem_pull_iff (M := A₂sub)).1 this
  have hνF : ν ∈ normalizer (Fsub : Set SU52) := by
    refine mem_normalizer_fintype fun z hz => ?_
    refine mem_Fsub_of_central (hνA z (Fsub_le_A₂sub hz)) fun α hα => ?_
    have e := Fsub_comm_A₂ (hνA' α hα) hz
    calc α * (ν * z * ν⁻¹) = ν * ((ν⁻¹ * α * ν) * z) * ν⁻¹ := by group
      _ = ν * (z * (ν⁻¹ * α * ν)) * ν⁻¹ := by rw [e]
      _ = ν * z * ν⁻¹ * α := by group
  obtain ⟨A, hA, α, hα, rfl⟩ := exists_eq_levSU_mul_of_normalizer hνF
  exact ⟨d.ι (levSU A hA), ⟨levSU A hA, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne_zero,
    rfl⟩, rfl⟩, d.ι α, ⟨α, hα, rfl⟩, map_mul _ _ _⟩

theorem A₂_le_normalizer_E₂
    (h : d.Hyp) : d.A₂ ≤ normalizer (d.E₂ : Set G) := by
  intro a ha
  refine mem_normalizer_fintype fun e he => ?_
  have hc := h.conj_mul_inv_mem_F_of_C₀ (U_le_C₀ (h.E₂_le_U he)) ha
  have e1 : a * e * a⁻¹ = (e * a * e⁻¹ * a⁻¹)⁻¹ * e := by group
  rw [e1]
  exact mul_mem (inv_mem (h.F_le_E₂ hc)) he

theorem A₂_le_C₀
    (h : d.Hyp) : d.A₂ ≤ d.C₀ := by
  rw [h.C₀_eq_sup]
  exact le_sup_left

theorem C₀_le_normalizer_A₂
    (h : d.Hyp) : d.C₀ ≤ normalizer (d.A₂ : Set G) :=
  h.C₀_le_normalizer.trans (h.normalizer_withT_F_eq ▸ h.normalizer_withT_F_le)

theorem mem_A₂E₂_iff
    (h : d.Hyp) {y : G} :
    y ∈ d.A₂ ⊔ d.E₂ ↔ ∃ a ∈ d.A₂, ∃ e ∈ d.E₂, y = a * e := by
  have hset := coe_mul_of_left_le_normalizer_right d.A₂ d.E₂ h.A₂_le_normalizer_E₂
  have hiff : y ∈ d.A₂ ⊔ d.E₂ ↔ y ∈ ((d.A₂ ⊔ d.E₂ : Subgroup G) : Set G) := Iff.rfl
  rw [hiff, hset]
  constructor
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩

theorem t_not_mem_A₂E₂
    (h : d.Hyp) : d.t ∉ d.A₂ ⊔ d.E₂ := by
  intro ht
  obtain ⟨a, ha, e, he, hae⟩ := (h.mem_A₂E₂_iff).1 ht
  have haL : a ∈ d.L := d.pull_le_L _ ha
  have heH : e ∈ d.H := by
    have : e = a⁻¹ * d.t := by rw [hae]; group
    rw [this]
    exact mul_mem (inv_mem (h.L_le_H haL)) h.t_mem_H
  have heF : e ∈ d.F := by
    rw [← h.E₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨he, heH⟩
  exact h.t_not_mem_L (hae ▸ mul_mem haL (h.F_le_L heF))

theorem C₀_eq_A₂E₂_sup
    (h : d.Hyp) : d.C₀ = d.A₂ ⊔ d.E₂ ⊔ zpowers d.t := by
  rw [h.C₀_eq_sup, ← h.sup_zpowers_E₂, sup_assoc]

theorem le_normalizer_A₂E₂
    (h : d.Hyp) :
    d.NLA₂ ≤ normalizer ((d.A₂ ⊔ d.E₂ : Subgroup G) : Set G) := by
  intro n hn
  obtain ⟨l, hl, a, ha, rfl⟩ := exists_eq_mul_of_mem_NLA₂ hn
  have hlA : l ∈ normalizer (d.A₂ : Set G) := by
    have := h.Lev_le_normalizer hl
    rw [← h.normalizer_withT_F_eq] at this
    exact h.normalizer_withT_F_le this
  refine mul_mem (mem_normalizer_sup hlA ((h.le_normalizer_E₂).1 hl))
    (mem_normalizer_sup ((d.A₂).le_normalizer ha) (h.A₂_le_normalizer_E₂ ha))

theorem t_mem_normalizer_A₂E₂
    (h : d.Hyp) :
    d.t ∈ normalizer ((d.A₂ ⊔ d.E₂ : Subgroup G) : Set G) :=
  mem_normalizer_sup (h.C₀_le_normalizer_A₂ (U_le_C₀ h.t_mem_U)) ((h.le_normalizer_E₂).2 h.t_mem_U)

theorem D₀_le
    (h : d.Hyp) : d.D₀ ≤ d.A₂ ⊔ d.E₂ := by
  rw [Data.D₀, commutator_le]
  intro c hc n hn
  have hnN := h.le_normalizer_A₂E₂ hn
  have hnt : n * d.t = d.t * n := comm_of_mem_centralizer h.t_mem (Subgroup.mem_inf.1 hn).2
  have htN := h.t_mem_normalizer_A₂E₂
  have hset := coe_mul_of_left_le_normalizer_right (zpowers d.t) (d.A₂ ⊔ d.E₂)
    (zpowers_le.2 htN)
  rw [h.C₀_eq_A₂E₂_sup, sup_comm] at hc
  obtain ⟨k, hk, w, hw, rfl⟩ :
      c ∈ (zpowers d.t : Set G) * ((d.A₂ ⊔ d.E₂ : Subgroup G) : Set G) := by
    rw [← hset]
    exact hc
  have hkn : k * n = n * k := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_left (Commute.symm hnt) m).eq
  have hkN : k ∈ normalizer ((d.A₂ ⊔ d.E₂ : Subgroup G) : Set G) := zpowers_le.2 htN hk
  have hnk : n * k⁻¹ * n⁻¹ = k⁻¹ := by
    calc n * k⁻¹ * n⁻¹ = k⁻¹ * (k * n) * k⁻¹ * n⁻¹ := by group
      _ = k⁻¹ * (n * k) * k⁻¹ * n⁻¹ := by rw [hkn]
      _ = k⁻¹ := by group
  have e : ⁅k * w, n⁆ = k * ⁅w, n⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    calc k * w * n * (k * w)⁻¹ * n⁻¹ = k * (w * n * w⁻¹ * n⁻¹) * (n * k⁻¹ * n⁻¹) := by group
      _ = k * (w * n * w⁻¹ * n⁻¹) * k⁻¹ := by rw [hnk]
  rw [e]
  refine (mem_normalizer_iff.1 hkN _).1 ?_
  rw [commutatorElement_def, show w * n * w⁻¹ * n⁻¹ = w * (n * w⁻¹ * n⁻¹) by group]
  exact mul_mem hw ((mem_normalizer_iff.1 hnN _).1 (inv_mem hw))

theorem e₂_mem_NLA₂
    (h : d.Hyp) : d.e₂ ∈ d.NLA₂ :=
  Subgroup.mem_inf.2 ⟨h.normalizer_withT_F_le h.e₂_mem_normalizer, d.ι_mem _⟩

omit [Finite G] in
theorem A₂_le_NLA₂ : d.A₂ ≤ d.NLA₂ := fun _ ha =>
  Subgroup.mem_inf.2 ⟨(d.A₂).le_normalizer ha, d.pull_le_L _ ha⟩

theorem Lev_le_NLA₂
    (h : d.Hyp) : d.Lev ≤ d.NLA₂ := fun l hl => by
  have := h.Lev_le_normalizer hl
  rw [← h.normalizer_withT_F_eq] at this
  exact Subgroup.mem_inf.2 ⟨h.normalizer_withT_F_le this, Lev_le_L hl⟩

theorem A₂_le_D₀
    (h : d.Hyp) : d.A₂ ≤ d.D₀ := by
  have hcomm : ∀ α ∈ A₂sub, ∀ β ∈ A₂sub, d.ι ⁅α, β⁆ ∈ d.D₀ := fun α hα β hβ => by
    rw [map_commutatorElement]
    exact commutator_mem_commutator (h.A₂_le_C₀ ⟨α, hα, rfl⟩) (A₂_le_NLA₂ ⟨β, hβ, rfl⟩)
  have he : ∀ x ∈ A₂sub, d.ι ⁅e₂SU, x⁆ ∈ d.D₀ := fun x hx => by
    rw [map_commutatorElement, Data.D₀, commutator_comm]
    exact commutator_mem_commutator h.e₂_mem_NLA₂ (h.A₂_le_C₀ ⟨x, hx, rfl⟩)
  have hF : Fsub ≤ d.D₀.comap d.ι := by
    rw [← closure_genFSU, closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha, b, hb, e⟩ := exists_genFSU_eq_commutator j
    show d.ι (genFSU j) ∈ d.D₀
    rw [e]
    exact hcomm a ha b hb
  have hX₁ : X₁sub ≤ d.D₀.comap d.ι := fun g hg => by
    obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₁ hg
    have e : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
    rw [mem_comap, e, map_mul]
    exact mul_mem (he x (X₁sub_le_A₂sub hx)) (hF hz)
  have hX₄ : X₄sub ≤ d.D₀.comap d.ι := fun g hg => by
    obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₄ hg
    have e : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
    rw [mem_comap, e, map_mul]
    exact mul_mem (he x (X₄sub_le_A₂sub hx)) (hF hz)
  have hX₃ : X₃sub ≤ d.D₀.comap d.ι := fun g hg => hF (mem_sup_left (mem_sup_right hg))
  have hA : A₂sub ≤ d.D₀.comap d.ι := sup_le (sup_le hX₁ hX₃) hX₄
  rintro _ ⟨α, hα, rfl⟩
  exact hA hα

theorem E₂_le_D₀
    (h : d.Hyp) : d.E₂ ≤ d.D₀ := by
  rw [Data.E₂, Data.D₀, commutator_comm d.C₀]
  exact commutator_mono h.Lev_le_NLA₂ U_le_C₀

theorem D₀_eq
    (h : d.Hyp) : d.D₀ = d.A₂ ⊔ d.E₂ :=
  le_antisymm h.D₀_le (sup_le h.A₂_le_D₀ h.E₂_le_D₀)

theorem Y_eq_E₂
    (h : d.Hyp) :
    d.Y = d.E₂ := by
  have hE₂N : d.D₀ ≤ normalizer (d.E₂ : Set G) := by
    rw [h.D₀_eq]
    exact sup_le h.A₂_le_normalizer_E₂ (d.E₂).le_normalizer
  have hcE : ⁅d.E₂, d.D₀⁆ ≤ d.E₂ := by
    rw [commutator_le]
    intro e he x hx
    rw [commutatorElement_def]
    have := (mem_normalizer_iff.1 (inv_mem (hE₂N hx)) e).1 he
    rw [inv_inv] at this
    have e1 : e * x * e⁻¹ * x⁻¹ = e * (x * e⁻¹ * x⁻¹) := by group
    rw [e1]
    exact mul_mem he ((mem_normalizer_iff.1 (hE₂N hx) _).1 (inv_mem he))
  have he₂E : ⁅zpowers d.e₂, d.E₂⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, zpowers_le]
    exact mem_centralizer_iff.2 fun e he =>
      (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (h.E₂_le_U he)).2)
  have h3 : ⁅⁅d.D₀, zpowers d.e₂⁆, d.E₂⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [he₂E, commutator_bot_left]
    · rw [eq_bot_iff, ← he₂E, commutator_comm (zpowers d.e₂)]
      exact commutator_mono hcE le_rfl
  have hdec : d.D₀ ≤ ⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂ := by
    have hA : d.A₂ ≤ ⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂ := by
      have hFE : Fsub ≤ (⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂).comap d.ι := fun z hz =>
        mem_sup_right (h.F_le_E₂ ⟨z, hz, rfl⟩)
      have hcm : ∀ x ∈ A₂sub, d.ι ⁅e₂SU, x⁆ ∈ ⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂ := fun x hx => by
        refine mem_sup_left ?_
        rw [map_commutatorElement, commutator_comm]
        exact commutator_mem_commutator (mem_zpowers _) (h.A₂_le_D₀ ⟨x, hx, rfl⟩)
      have hX₁ : X₁sub ≤ (⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂).comap d.ι := fun g hg => by
        obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₁ hg
        have e : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
        rw [mem_comap, e, map_mul]
        exact mul_mem (hcm x (X₁sub_le_A₂sub hx)) (hFE hz)
      have hX₄ : X₄sub ≤ (⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂).comap d.ι := fun g hg => by
        obtain ⟨x, hx, hz⟩ := exists_commutator_e₂_x₄ hg
        have e : g = ⁅e₂SU, x⁆ * (⁅e₂SU, x⁆⁻¹ * g) := by group
        rw [mem_comap, e, map_mul]
        exact mul_mem (hcm x (X₄sub_le_A₂sub hx)) (hFE hz)
      have hX₃ : X₃sub ≤ (⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂).comap d.ι := fun g hg =>
        hFE (mem_sup_left (mem_sup_right hg))
      have hle : A₂sub ≤ (⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂).comap d.ι := sup_le (sup_le hX₁ hX₃) hX₄
      rintro _ ⟨α, hα, rfl⟩
      exact hle hα
    calc d.D₀ = d.A₂ ⊔ d.E₂ := h.D₀_eq
      _ ≤ _ := sup_le hA le_sup_right
  have hEZ : d.E₂ ≤ d.Y := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_, h.E₂_le_D₀ he⟩
    have hC : ⁅d.D₀, zpowers d.e₂⁆ ⊔ d.E₂ ≤ centralizer ({e} : Set G) := by
      refine sup_le (fun y hy => ?_) fun y hy => ?_
      · have := (commutator_eq_bot_iff_le_centralizer.1 h3) hy
        exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 this) e he).symm
      · exact mem_centralizer_singleton_iff.2 (h.E₂_comm hy he)
    exact mem_centralizer_singleton_iff.1 (hC (hdec hx))
  refine le_antisymm (fun y hy => ?_) hEZ
  obtain ⟨hyC, hyD⟩ := Subgroup.mem_inf.1 hy
  rw [h.D₀_eq] at hyD
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hyD
  have heC : e ∈ centralizer (d.D₀ : Set G) := (Subgroup.mem_inf.1 (hEZ he)).1
  have haF : a ∈ d.F := by
    refine mem_F_of_central ha fun b hb => ?_
    have hbD : b ∈ d.D₀ := h.A₂_le_D₀ hb
    have h1 := mem_centralizer_iff.1 hyC b hbD
    have h2 := mem_centralizer_iff.1 heC b hbD
    calc b * a = b * (a * e) * e⁻¹ := by group
      _ = a * e * b * e⁻¹ := by rw [h1]
      _ = a * (e * b) * e⁻¹ := by group
      _ = a * (b * e) * e⁻¹ := by rw [h2]
      _ = a * b := by group
  exact mul_mem (h.F_le_E₂ haF) he

theorem sec4_6
    (h : d.Hyp) :
    d.C₀ = d.D₀ ⊔ zpowers d.t ∧ d.t ∉ d.D₀ ∧ d.D₀ = d.A₂ ⊔ d.Y ∧
      d.Y ⊓ centralizer ({d.t} : Set G) = d.F ∧ Nat.card d.Y = 2 ^ 8 ∧
      (∀ x ∈ d.Y, ∀ y ∈ d.Y, x * y = y * x) ∧ d.Y = d.E₂ := by
  have hY := h.Y_eq_E₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hY⟩
  · rw [h.D₀_eq, h.C₀_eq_A₂E₂_sup]
  · rw [h.D₀_eq]
    exact h.t_not_mem_A₂E₂
  · rw [hY, h.D₀_eq]
  · rw [hY]
    exact h.E₂_inf_H
  · rw [hY]
    exact h.card_E₂
  · intro x hx y hy
    rw [hY] at hx hy
    exact h.E₂_comm hx hy

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
