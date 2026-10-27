module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalLemmas1

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

@[expose] def Kp (σ : Setting G) (r : ℕ) : Subgroup G := Subgroup.normalizer (σ.Ps r 0 : Set G)

theorem lt_inf_normalizer {p : ℕ} [Fact p.Prime] {Y V : Subgroup G}
    (hV : IsPGroup p V) (hYV : Y < V) : Y < V ⊓ Subgroup.normalizer (Y : Set G) := by
  have hnil : Group.IsNilpotent V := hV.isNilpotent
  have hlt : Y.subgroupOf V < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hYV.ne
    apply le_antisymm hYV.le
    intro x hx
    have : (⟨x, hx⟩ : V) ∈ Y.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hYV.le] at hnorm
  obtain ⟨⟨n, hnV⟩, hnN, hnY⟩ := IsConcreteLE.exists_of_lt hnorm
  refine lt_of_le_of_ne (le_inf hYV.le Subgroup.le_normalizer) fun h => hnY ?_
  have : n ∈ V ⊓ Subgroup.normalizer (Y : Set G) := ⟨hnV, hnN⟩
  rw [← h] at this
  exact this

section K

omit [Finite G] in
theorem N_le_Kp : σ.N ≤ Kp σ r := le_normalizer_pCoreIn r σ.N

omit [Finite G] in
theorem C_le_Kp : σ.C ≤ Kp σ r := σ.C_le_N.trans (N_le_Kp (σ := σ))

theorem Ps_le_oddCore_Kp (Δ : Data σ r) : σ.Ps r 0 ≤ oddCoreIn (Kp σ r) :=
  le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Ps 0))

theorem oddCore_Kp_ne_bot (Δ : Data σ r) : oddCoreIn (Kp σ r) ≠ ⊥ := fun h =>
  Ps_zero_ne_bot Δ (eq_bot_iff.mpr (h ▸ Ps_le_oddCore_Kp Δ))

theorem Kp_cover (Δ : Data σ r) (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) :
    oddCoreIn (Kp σ r) ⊔ (Kp σ r ⊓ σ.N) = Kp σ r :=
  (hF.cover_qgroup (Kp σ r) ((σ.T_le_C hσ).trans C_le_Kp) (oddCore_Kp_ne_bot Δ)
    (fun l hl => ⟨l, N_le_Kp (hσ.L₀_le_N hl), 1, σ.ON.one_mem, mul_one l⟩)).2

theorem mem_oddCore_Kp_of_inverted (Δ : Data σ r) (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) {u : G}
    (hu : u ∈ Kp σ r) (huo : Odd (orderOf u)) (hinv : σ.x * u * σ.x⁻¹ = u⁻¹) :
    u ∈ oddCoreIn (Kp σ r) :=
  mem_oddCoreIn_of_inverted (N_le_Kp σ.x_mem_N) (Kp_cover Δ hσ hF) hu huo hinv

theorem not_isSylowOf_Ps (Δ : Data σ r) (hσ : σ.IsValid) :
    ¬ IsSylowOf r (σ.Ps r 0) (oddCoreIn (Kp σ r)) := by
  intro h
  apply Δ.exceptional
  refine ⟨⟨σ.Ps r 0, Δ.P_sylow, h⟩, Or.inr ⟨σ.Ps r 0, Δ.P_sylow,
    (σ.T_le_C hσ).trans (C_le_normalizer_Ps r 0), fun y hy => ?_⟩⟩
  exact Δ.P_inverted 0 1 (by decide) y hy

theorem oddCore_Kp_inf_N_le_ON : oddCoreIn (Kp σ r) ⊓ σ.N ≤ σ.ON :=
  le_oddCoreIn inf_le_right
    (fun _ hn => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_oddCoreIn (Kp σ r) (N_le_Kp hn), Subgroup.le_normalizer hn⟩)
    ((odd_card_oddCoreIn (Kp σ r)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

theorem le_Ps_of_le_ON (Δ : Data σ r) {X : Subgroup G} (hXO : X ≤ σ.ON) (hX : IsPGroup r X) :
    X ≤ σ.Ps r 0 := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hXN : X ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
    (hXO.trans σ.ON_le_N).trans (le_normalizer_pCoreIn r σ.N)
  have hsup : IsPGroup r (X ⊔ σ.Ps r 0 : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hX (isPGroup_Ps 0) hXN
  have heq := Δ.P_sylow.eq_of_le le_sup_right (sup_le hXO (Ps_zero_le_ON Δ)) hsup
  rw [← heq]
  exact le_sup_left

theorem Ps_inf_C (Δ : Data σ r) (hσ : σ.IsValid) (i : Fin 3) : σ.Ps r i ⊓ σ.C = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right _ (Ps_le_R Δ i)).trans (R_inf_C Δ hσ i).le)

end K

section Lemma3

variable {V : Subgroup G}

omit [Finite G] in
theorem isPGroup_V (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) : IsPGroup r V :=
  hV.1.1.2.1

theorem odd_card_V (Δ : Data σ r) (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    Odd (Nat.card V) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_V hV)

omit [Finite G] in
theorem T_le_normalizer_V (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    σ.T ≤ Subgroup.normalizer (V : Set G) := hV.1.1.2.2.1

omit [Finite G] in
theorem V_le_Kp (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) : V ≤ Kp σ r :=
  hV.1.1.1

theorem omnibusAt_V (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) : OmnibusAt Δ (Kp σ r) V :=
  homni (Kp σ r) C_le_Kp V hV

theorem isSylowOf_V_inf_C (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    IsSylowOf r (V ⊓ σ.C) σ.C := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨R₀, hR₀, hR₀V⟩ := (omnibusAt_V Δ homni hV).part_ii_a
  rw [hR₀.eq_of_le (le_inf hR₀V hR₀.le) inf_le_right ((isPGroup_V hV).to_le inf_le_left)]
  exact hR₀

theorem isSylowOf_V_inf_oddCore (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    IsSylowOf r (V ⊓ oddCoreIn (Kp σ r)) (oddCoreIn (Kp σ r)) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨R₀, hR₀, hR₀V⟩ := (omnibusAt_V Δ homni hV).part_ii_b
  rw [hR₀.eq_of_le (le_inf hR₀V hR₀.le) inf_le_right ((isPGroup_V hV).to_le inf_le_left)]
  exact hR₀

theorem V_inf_C_inf_oddCore (hσ : σ.IsValid) (Δ : Data σ r)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    V ⊓ σ.C ⊓ oddCoreIn (Kp σ r) = ⊥ := by
  have hle : V ⊓ σ.C ⊓ oddCoreIn (Kp σ r) ≤ σ.Ps r 0 := by
    apply le_Ps_of_le_ON Δ _ ((isPGroup_V hV).to_le (inf_le_left.trans inf_le_left))
    exact fun g hg => oddCore_Kp_inf_N_le_ON ⟨hg.2, σ.C_le_N hg.1.2⟩
  rw [eq_bot_iff, ← Ps_inf_C Δ hσ 0]
  exact le_inf hle (inf_le_left.trans inf_le_right)

theorem V_inf_N_inf_oddCore_le (Δ : Data σ r)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    V ⊓ σ.N ⊓ oddCoreIn (Kp σ r) ≤ σ.Ps r 0 :=
  le_Ps_of_le_ON Δ (fun _ hg => oddCore_Kp_inf_N_le_ON ⟨hg.2, hg.1.2⟩)
    ((isPGroup_V hV).to_le (inf_le_left.trans inf_le_left))

theorem comp_zero_eq_R (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) (hRV : R Δ 0 ≤ V) :
    comp σ V 0 = (R Δ 0 : Set G) := by
  obtain ⟨W, hW, hCW, -⟩ := (omnibusAt_V Δ homni hV).part_i_b 0
  have hWmem : W ∈ signalizers σ.N σ.C r := by
    refine ⟨fun u hu => ?_, (isPGroup_V hV).to_le (fun u hu => ?_), hCW, ?_⟩
    · rw [← SetLike.mem_coe, hW] at hu
      exact (Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm)
    · rw [← SetLike.mem_coe, hW] at hu
      exact hu.1
    · rw [eq_bot_iff]
      intro u hu
      have hu1 : u ∈ comp σ V 0 := by rw [← hW]; exact hu.1
      exact eq_one_of_conj_eq_inv_of_commute
        (odd_orderOf_of_mem (odd_card_V Δ hV) hu1.1) hu1.2.2
        (Subgroup.mem_centralizer_iff.mp hu.2 _ (xs_mem_T 1))
  have hRW : R Δ 0 ≤ W := fun u hu => by
    rw [← SetLike.mem_coe, hW]
    exact R_subset_comp Δ hσ hRV hu
  rw [← hW, (R_mem_maximals Δ 0).2 W hWmem hRW]

theorem comp_one_subset_oddCore (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    comp σ V 1 ⊆ oddCoreIn (Kp σ r) := fun _ hu =>
  mem_oddCore_Kp_of_inverted Δ hσ hF (V_le_Kp hV hu.1)
    (odd_orderOf_of_mem (odd_card_V Δ hV) hu.1) ((mem_comp_iff' hσ).mp hu).2.2

theorem comp_two_subset_oddCore (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    comp σ V 2 ⊆ oddCoreIn (Kp σ r) := fun _ hu =>
  mem_oddCore_Kp_of_inverted Δ hσ hF (V_le_Kp hV hu.1)
    (odd_orderOf_of_mem (odd_card_V Δ hV) hu.1) hu.2.2

theorem T_le_normalizer_V_inf_oddCore (hσ : σ.IsValid)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) :
    σ.T ≤ Subgroup.normalizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨T_le_normalizer_V hV ht,
    le_normalizer_oddCoreIn (Kp σ r) (C_le_Kp (σ.T_le_C hσ ht))⟩

theorem C_le_normalizer_V_inf_oddCore (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) (hRV : R Δ 0 ≤ V) :
    σ.C ≤ Subgroup.normalizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) := by
  obtain ⟨W₁, hW₁, hCW₁, -⟩ := (omnibusAt_V Δ homni hV).part_i_b 1
  obtain ⟨W₂, hW₂, hCW₂, -⟩ := (omnibusAt_V Δ homni hV).part_i_b 2
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  have hYodd : Odd (Nat.card Y) :=
    (odd_card_V Δ hV).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  intro c hc
  apply mem_normalizer_of_conj_mem
  intro y hy
  obtain ⟨y₀, h₀, y₁, h₁, y₂, h₂, y₃, h₃, rfl⟩ :=
    exists_mul_comp hσ hYodd (T_le_normalizer_V_inf_oddCore hσ hV) hy
  have hy₀ : y₀ = 1 := by
    have : y₀ ∈ V ⊓ σ.C ⊓ oddCoreIn (Kp σ r) := ⟨⟨h₀.1.1, h₀.2⟩, h₀.1.2⟩
    rw [V_inf_C_inf_oddCore hσ Δ hV] at this
    exact this
  have hy₁ : y₁ ∈ σ.Ps r 0 :=
    V_inf_N_inf_oddCore_le Δ hV ⟨⟨h₁.1.1, Subgroup.mem_centralizer_singleton_iff.mpr
      h₁.2.1.symm⟩, h₁.1.2⟩
  have hy₂ : y₂ ∈ W₁ := by rw [← SetLike.mem_coe, hW₁]; exact ⟨h₂.1.1, h₂.2⟩
  have hy₃ : y₃ ∈ W₂ := by rw [← SetLike.mem_coe, hW₂]; exact ⟨h₃.1.1, h₃.2⟩
  have hcP := (Subgroup.mem_normalizer_iff.mp (C_le_normalizer_Ps r 0 hc) _).mp hy₁
  have hc₂ := (Subgroup.mem_normalizer_iff.mp (hCW₁ hc) _).mp hy₂
  have hc₃ := (Subgroup.mem_normalizer_iff.mp (hCW₂ hc) _).mp hy₃
  have hW₁Y : ∀ {w : G}, w ∈ W₁ → w ∈ Y := fun hw => by
    rw [← SetLike.mem_coe, hW₁] at hw
    exact ⟨hw.1, comp_one_subset_oddCore hσ hF Δ hV hw⟩
  have hW₂Y : ∀ {w : G}, w ∈ W₂ → w ∈ Y := fun hw => by
    rw [← SetLike.mem_coe, hW₂] at hw
    exact ⟨hw.1, comp_two_subset_oddCore hσ hF Δ hV hw⟩
  have hPY : ∀ {w : G}, w ∈ σ.Ps r 0 → w ∈ Y := fun hw =>
    ⟨hRV (Ps_le_R Δ 0 hw), Ps_le_oddCore_Kp Δ hw⟩
  rw [hy₀, one_mul]
  have e : c * (y₁ * y₂ * y₃) * c⁻¹ = (c * y₁ * c⁻¹) * (c * y₂ * c⁻¹) * (c * y₃ * c⁻¹) := by
    group
  rw [e]
  exact Y.mul_mem (Y.mul_mem (hPY hcP) (hW₁Y hc₂)) (hW₂Y hc₃)

theorem lemma11_3_iv (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)) (hRV : R Δ 0 ≤ V) :
    (∃ u ∈ comp σ V 1, u ≠ 1 ∧ u ∈ Subgroup.centralizer (R Δ 0 : Set G)) ∨
      (∃ u ∈ comp σ V 2, u ≠ 1 ∧ u ∈ Subgroup.centralizer (R Δ 0 : Set G)) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set O := oddCoreIn (Kp σ r) with hO
  set Y : Subgroup G := V ⊓ O with hY
  have hYs := isSylowOf_V_inf_oddCore Δ homni hV
  have hPY : σ.Ps r 0 ≤ Y := le_inf ((Ps_le_R Δ 0).trans hRV) (Ps_le_oddCore_Kp Δ)
  have hPne : σ.Ps r 0 ≠ Y := fun h => not_isSylowOf_Ps Δ hσ (h ▸ hYs)
  have hRY : R Δ 0 ⊓ O ≤ σ.Ps r 0 := fun g hg =>
    V_inf_N_inf_oddCore_le Δ hV ⟨⟨hRV hg.1, R_le_Ns Δ hσ 0 hg.1⟩, hg.2⟩
  have hRnY : R Δ 0 ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hRV hg),
      le_normalizer_oddCoreIn _ (V_le_Kp hV (hRV hg))⟩
  have hsupp : IsPGroup r (R Δ 0 ⊔ Y : Subgroup G) :=
    (isPGroup_V hV).to_le (sup_le hRV inf_le_left)
  have hlt : R Δ 0 < R Δ 0 ⊔ Y := by
    refine lt_of_le_of_ne le_sup_left (fun h => hPne ?_)
    apply le_antisymm hPY
    intro y hy
    have hyR : y ∈ R Δ 0 := by
      rw [h]
      exact (le_sup_right : Y ≤ R Δ 0 ⊔ Y) hy
    exact hRY ⟨hyR, hy.2⟩
  obtain ⟨g, hg, hgR⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hsupp hlt)
  obtain ⟨ρ, hρ, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hRnY).mp hg.1
  have hyN : y ∈ Subgroup.normalizer (R Δ 0 : Set G) := by
    have := (Subgroup.normalizer _).mul_mem
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hρ)) hg.2
    rwa [inv_mul_cancel_left] at this
  have hyR : y ∉ R Δ 0 := fun h => hgR ((R Δ 0).mul_mem hρ h)
  set Y' : Subgroup G := Y ⊓ Subgroup.normalizer (R Δ 0 : Set G) with hY'
  have hY'odd : Odd (Nat.card Y') :=
    (odd_card_V Δ hV).of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
  have hTN : σ.T ≤ Subgroup.normalizer
      ((Subgroup.normalizer (R Δ 0 : Set G) : Subgroup G) : Set G) := fun t ht => by
    rw [← conjSub_eq_self_iff, ← normalizer_conjSub,
      conjSub_eq_self_iff.mpr (C_le_normalizer_R Δ 0 (σ.T_le_C hσ ht))]
  have hTY' : σ.T ≤ Subgroup.normalizer (Y' : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨T_le_normalizer_V_inf_oddCore hσ hV ht, hTN ht⟩
  obtain ⟨y₀, h₀, y₁, h₁, y₂, h₂, y₃, h₃, hye⟩ := exists_mul_comp hσ hY'odd hTY' ⟨hy, hyN⟩
  have hy₀ : y₀ = 1 := by
    have : y₀ ∈ V ⊓ σ.C ⊓ O := ⟨⟨h₀.1.1.1, h₀.2⟩, h₀.1.1.2⟩
    rw [V_inf_C_inf_oddCore hσ Δ hV] at this
    exact this
  have hy₁ : y₁ ∈ σ.Ps r 0 :=
    V_inf_N_inf_oddCore_le Δ hV ⟨⟨h₁.1.1.1,
      Subgroup.mem_centralizer_singleton_iff.mpr h₁.2.1.symm⟩, h₁.1.1.2⟩
  have hcent : ∀ {u : G}, u ∈ Y' → σ.x * u * σ.x⁻¹ = u⁻¹ →
      u ∈ Subgroup.centralizer (R Δ 0 : Set G) := fun hu hinv =>
    mem_centralizer_of_inverted (odd_orderOf_of_mem hY'odd hu) hinv
      (fun _ ha => R_centralized Δ hσ 0 ha) hu.2
  by_contra hcon
  rw [not_or] at hcon
  have hy₂ : y₂ = 1 := by
    by_contra hne
    exact hcon.1 ⟨y₂, ⟨h₂.1.1.1, h₂.2⟩, hne, hcent h₂.1 ((mem_comp_iff' hσ).mp h₂).2.2⟩
  have hy₃ : y₃ = 1 := by
    by_contra hne
    exact hcon.2 ⟨y₃, ⟨h₃.1.1.1, h₃.2⟩, hne, hcent h₃.1 h₃.2.2⟩
  apply hyR
  rw [hye, hy₀, hy₂, hy₃, one_mul, mul_one, mul_one]
  exact Ps_le_R Δ 0 hy₁

theorem lemma11_4 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (hI : Inputs Δ) (hV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r))
    (hX : ∃ u ∈ comp σ V 1, u ≠ 1 ∧ u ∈ Subgroup.centralizer (R Δ 0 : Set G)) :
    PGroupR Δ ∨ (σ.DeltaEpsMinus ∧ r ∣ σ.q ∧
      (Δ.Qs 1 : Set G) = comp σ V 1 ∩ Subgroup.centralizer (R Δ 0 : Set G) ∧
      IsPGroup r (R Δ 0 ⊔ Rs Δ 1 : Subgroup G)) := by
  obtain ⟨W, hW, hCW, hWcases⟩ := (omnibusAt_V Δ homni hV).part_i_b 1
  set X : Subgroup G := W ⊓ Subgroup.centralizer (R Δ 0 : Set G) with hXdef
  have hCX : σ.C ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hCW hc, normalizer_le_normalizer_centralizer (R Δ 0) (C_le_normalizer_R Δ 0 hc)⟩
  have hXset : (X : Set G) = comp σ V 1 ∩ Subgroup.centralizer (R Δ 0 : Set G) := by
    rw [hXdef, Subgroup.coe_inf, hW]
  have hX1 : X ≠ ⊥ := by
    obtain ⟨u, hu, hu1, huc⟩ := hX
    intro h
    have : u ∈ (X : Set G) := by rw [hXset]; exact ⟨hu, huc⟩
    rw [h] at this
    exact hu1 this
  have hXcent : X ≤ Subgroup.centralizer (R Δ 0 : Set G) := inf_le_right
  by_cases hXP : X ⊓ σ.Ps r 1 = ⊥
  · have hXnotP : ¬ W ≤ σ.Ps r 1 := fun hWP =>
      hX1 (by rw [eq_bot_iff, ← hXP]; exact le_inf le_rfl (inf_le_left.trans hWP))
    by_cases hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q
    · rcases hWcases with hWP | hWR | hWRs
      · exact absurd hWP hXnotP
      · left
        have hXQ := eq_Q_of_le_R Δ hδq hI.ii_4_10_iii 1 (inf_le_left.trans hWR) hCX hXP hX1
        apply pGroupR_of_R01
        have hRQ : R Δ 0 ≤ Subgroup.centralizer (Δ.Q 1 : Set G) :=
          Subgroup.le_centralizer_iff.mp (hXQ ▸ hXcent)
        exact lemma11_1 hσ Δ homni (C_le_normalizer_Q Δ 1)
          (hRQ.trans (centralizer_le_normalizer _))
          (R_le_oddCore_normalizer_Q Δ hδq hσ hI.ii_4_4 1) (isPGroup_R Δ hσ 0)
          (isPGroup_R Δ hσ 1) (C_le_normalizer_R Δ 0) (C_le_normalizer_R Δ 1)
      · right
        have hXQ := eq_Qs_of_le_Rs Δ hδq hI.ii_4_10_iii 1 (inf_le_left.trans hWRs) hCX hXP hX1
        have hRQ : R Δ 0 ≤ Subgroup.centralizer (Δ.Qs 1 : Set G) :=
          Subgroup.le_centralizer_iff.mp (hXQ ▸ hXcent)
        refine ⟨hδq.1, hδq.2, by rw [← hXQ, hXset], ?_⟩
        exact lemma11_1 hσ Δ homni (C_le_normalizer_Qs Δ 1)
          (hRQ.trans (centralizer_le_normalizer _))
          (Rs_le_oddCore_normalizer_Qs Δ hδq hσ hI.ii_4_4 1) (isPGroup_R Δ hσ 0)
          (isPGroup_Rs Δ hσ 1) (C_le_normalizer_R Δ 0) (C_le_normalizer_Rs Δ 1)
    · exfalso
      have hR : R Δ 1 = σ.Ps r 1 := by rw [R, (Δ.Q_trivial hδq 1).1, bot_sup_eq]
      have hRs : Rs Δ 1 = σ.Ps r 1 := by rw [Rs, (Δ.Q_trivial hδq 1).2, bot_sup_eq]
      rcases hWcases with hWP | hWR | hWRs
      · exact hXnotP hWP
      · exact hXnotP (hR ▸ hWR)
      · exact hXnotP (hRs ▸ hWRs)
  · left
    apply pGroupR_of_centralizer_Ps1_R0 hσ hF Δ homni
    intro h
    apply hXP
    rw [eq_bot_iff, ← h]
    exact fun g hg => ⟨hg.2, hXcent hg.1⟩

end Lemma3

end CFSG.ABGTheoremB.TotallyInverted.Sec11
