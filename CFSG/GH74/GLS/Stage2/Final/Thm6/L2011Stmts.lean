module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S5Stmt
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Psp
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)

@[expose] def Pkg2010 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail20 G z k S M → M = Cen z →
    TypeCl z k S → ∀ g : G, Case20A z S g →
      ∃ g' : G, Case20A z S g' ∧ orderOf (zc z g') = 2 ∧ zc z g' ∈ S1 S z ∧
        (∀ a ∈ A20 z, a * zc z g' = zc z g' * a) ∧ S ≤ H0 z g' ∧
        IsSimpleGroup ↥(barIn (H0 z g') (J0 z g'))

section Basic

variable {G : Type} [Group G]

theorem oddCore_conj_mem (z : G) {c : G} (hc : c ∈ Cen z) {b : G} (hb : b ∈ OddCore z) :
    c * b * c⁻¹ ∈ OddCore z := by
  obtain ⟨y', hy', rfl⟩ := hb
  exact ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y' hy' ⟨c, hc⟩, rfl⟩

theorem oddCore_le_Cen (z : G) : OddCore z ≤ Cen z := Subgroup.map_subtype_le _

theorem stab_F0 (z g : G) {c : G} (hc : c ∈ Cen z) (hct : c * zc z g = zc z g * c) {x : G}
    (hx : x ∈ F0 z g) : c * x * c⁻¹ ∈ F0 z g := by
  refine ⟨F20_conj_mem z hc hx.1, ?_⟩
  have hx2 : g * x * g⁻¹ ∈ OddCore z := bar_mem_conjugate_iff.1 hx.2
  have hgc : g * c * g⁻¹ ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c := hct
    calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [h1]
      _ = z * (g * c * g⁻¹) := by group
  have := oddCore_conj_mem z hgc hx2
  refine bar_mem_conjugate_iff.2 ?_
  have e : g * (c * x * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
  rw [e]; exact this

theorem mem_H0_of_cen_comm (z g : G) {c : G} (hc : c ∈ Cen z) (hct : c * zc z g = zc z g * c) :
    c ∈ H0 z g := by
  unfold H0
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => stab_F0 z g hc hct hx
  · intro hx
    have hc' : c⁻¹ ∈ Cen z := (Cen z).inv_mem hc
    have hct' : c⁻¹ * zc z g = zc z g * c⁻¹ := by
      calc c⁻¹ * zc z g = c⁻¹ * (zc z g * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * zc z g) * c⁻¹ := by rw [hct]
        _ = zc z g * c⁻¹ := by group
    have := stab_F0 z g hc' hct' hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem two_lt_card_of_sl2 {Y : Type} [Group Y] {q : ℕ} (h : HasSL2Model Y (fun r => r = q)) (hq : 3 < q) :
    2 < Nat.card Y := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := h
  have h2 : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv]
  rw [h2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]
  have : 4 ≤ q := hq
  nlinarith [Nat.sub_add_cancel (show 1 ≤ q ^ 2 from Nat.one_le_pow _ _ (by omega))]

theorem barOf_mono' {z : G} {X Y : Subgroup G} (h : X ≤ Y) : barOf z X ≤ barOf z Y :=
  Subgroup.map_mono (fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)))

section Pair

variable [Finite G] {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem LC_decomp (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) {l : G} (hl : l ∈ LC z) :
    ∃ a ∈ OddCore z, ∃ k ∈ Em (Cen z), l = a * k := by
  have hlC : l ∈ Cen z := LC_le_Cen z hl
  have hb : toBar z ⟨l, hlC⟩ ∈ LBar z := ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hK₁ : K₁ ≤ Em (Cen z) := hK.layer ▸ le_sup_left
  have hK₂ : K₂ ≤ Em (Cen z) := hK.layer ▸ le_sup_right
  have hL₁ : L₁ ≤ barOf z (Em (Cen z)) := hK.bar₁ ▸ barOf_mono' hK₁
  have hL₂ : L₂ ≤ barOf z (Em (Cen z)) := hK.bar₂ ▸ barOf_mono' hK₂
  rw [← hP.prod.1] at hb
  have hb' := sup_le hL₁ hL₂ hb
  obtain ⟨k, hkC, hkE, hk⟩ := bar_mem_barOf_iff.1 hb'
  refine ⟨l * k⁻¹, ?_, k, hkE, by group⟩
  have h1 : toBar z ⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ = 1 := by
    have : (⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ : ↥(Cen z)) =
        ⟨l, hlC⟩ * ⟨k, hkC⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hk]
    group
  have h2 : (⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

theorem not_simple_barIn_Cen (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂)
    (h4a : pLayerOf 2 (Cen z) = Em (Cen z))
    (hsimp : IsSimpleGroup ↥(barIn (Cen z) (pLayerOf 2 (Cen z)))) : False := by
  have hB : barIn (Cen z) (pLayerOf 2 (Cen z)) = L₁ ⊔ L₂ := by
    rw [h4a, hK.layer]
    change barOf z (K₁ ⊔ K₂) = L₁ ⊔ L₂
    unfold barOf
    rw [Subgroup.subgroupOf_sup hK.le₁ hK.le₂, Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) hK.bar₁ hK.bar₂
  rw [hB] at hsimp
  have hle : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
  have hcomm : ∀ b ∈ L₂, ∀ a ∈ L₁, b * a * b⁻¹ = a := fun b hb a ha => by
    have := hP.prod.2.1 a ha b hb
    calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [this]
      _ = a := by group
  have hnorm : (L₁.subgroupOf (L₁ ⊔ L₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    refine sup_le Subgroup.le_normalizer ?_
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; rw [hcomm b hb a ha]; exact ha
    · intro ha
      have hxb : (b * a * b⁻¹) * b = b * (b * a * b⁻¹) := by
        have := hP.prod.2.1 (b * a * b⁻¹) ha b hb
        exact this
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b⁻¹ * ((b * a * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [hxb]
          _ = b * a * b⁻¹ := by group
      rw [e]; exact ha
  have := hnorm
  have hcard1 : 2 < Nat.card ↥L₁ := two_lt_card_of_sl2 hP.sl₁ hP.gt3
  have hcard2 : 2 < Nat.card ↥L₂ := two_lt_card_of_sl2 hP.sl₂ hP.gt3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L₁.subgroupOf (L₁ ⊔ L₂)) with h | h
  · have h1 : Disjoint L₁ (L₁ ⊔ L₂) := Subgroup.subgroupOf_eq_bot.1 h
    have h2 : L₁ = ⊥ := disjoint_self.1 (h1.mono_right hle)
    rw [h2, Subgroup.card_bot] at hcard1
    omega
  · have h1 : L₁ ⊔ L₂ ≤ L₁ := Subgroup.subgroupOf_eq_top.1 h
    have h2 : L₂ ≤ L₁ ⊓ L₂ := le_inf (le_sup_right.trans h1) le_rfl
    have h3 := Subgroup.card_le_of_le h2
    have h4 := hP.prod.2.2
    omega

end Pair

end Basic

theorem lemma20_11_of_parts (hP : Pkg2010) (h5 : L2011S5) : Lemma20_11 := by
  intro G _ _ z k S M hF hMC hT g hSg hnz
  by_contra hne
  subst hMC
  have hctx : Stage2Ctx G z k S := hF.ctx.ctx17.ctx
  obtain ⟨g', hcase, ht2, hS1, hcenA, hSH, hsimp⟩ :=
    hP G z k S (Cen z) hF rfl hT g ⟨hSg, hnz, hne⟩
  have hfac := h5 G z k S hctx hT (zc z g') hS1 ht2
  obtain ⟨q, L₁, L₂, hpair⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ := by
    rcases hT with ⟨ε, q, hk, L₁, L₂, h⟩ | ⟨q, hk, L₁, L₂, h⟩
    · exact ⟨q, L₁, L₂, h.pair⟩
    · exact ⟨q, L₁, L₂, h.pair⟩
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := hF.ctx.thm4.1
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  have hAH : ∀ a ∈ OddCore z, a ∈ H0 z g' := fun a ha =>
    mem_H0_of_cen_comm z g' (oddCore_le_Cen z ha) (hcenA a ha)
  have hEH : ∀ e ∈ Em (Cen z), e ∈ H0 z g' := by
    intro e he
    have hcommE : ∀ e' ∈ Em (Cen z), ∀ x ∈ F0 z g', e' * x * e'⁻¹ = x := fun e' he' x hx => by
      have := hK.oddcomm x (F20_le_OddCore z hx.1) e' he'
      calc e' * x * e'⁻¹ = (x * e') * e'⁻¹ := by rw [← this]
        _ = x := by group
    unfold H0
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hcommE e he x hx]; exact hx
    · intro hx
      have h2 := hcommE e⁻¹ ((Em (Cen z)).inv_mem he) _ hx
      have e1 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
      rw [e1] at h2
      rw [h2]; exact hx
  have hCH : Cen z ≤ H0 z g' := by
    intro c hc
    obtain ⟨a, ha, l, hl, σ, hσ, d, hd, rfl⟩ := hfac c hc
    refine (H0 z g').mul_mem ((H0 z g').mul_mem ((H0 z g').mul_mem (hAH a ha) ?_) (hSH hσ)) ?_
    · obtain ⟨a', ha', k', hk', rfl⟩ := LC_decomp hpair hK hl
      exact (H0 z g').mul_mem (hAH a' ha') (hEH k' hk')
    · exact mem_H0_of_cen_comm z g' hd.1 (Subgroup.mem_centralizer_singleton_iff.1 hd.2)
  have hmax := hF.ctx.ctx17.mem
  have hHne : H0 z g' ≠ ⊤ := by
    intro htop
    have hnormal : (F0 z g').Normal := Subgroup.normalizer_eq_top_iff.1 htop
    have := hctx.std.kps.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F0 z g') with h0 | h1
    · exact hcase.inter h0
    · apply hmax.1.1
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ F0 z g' := by rw [h1]; trivial
      exact oddCore_le_Cen z (F20_le_OddCore z hx.1)
  have hEq : H0 z g' = Cen z := by
    rcases hmax.1.le_iff.1 hCH with h | h
    · exact absurd h hHne
    · exact h
  have key : ∀ H : Subgroup G, H = Cen z → IsSimpleGroup ↥(barIn H (pLayerOf 2 H)) → False := by
    intro H hH
    subst hH
    exact fun h => not_simple_barIn_Cen hpair hK h4a h
  exact key (H0 z g') hEq hsimp

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
