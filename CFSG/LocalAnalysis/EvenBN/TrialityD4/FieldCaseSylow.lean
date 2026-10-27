module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoMain

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

abbrev ncs (d : TrialityD4Data L (2 ^ f)) (t : G) : Subgroup G :=
  centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)

theorem yamadaP_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ⊓ centralizer ({t} : Set G) = d.S.map L.subtype := by
  obtain ⟨-, -, htP, -, hSP, -, hker, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  refine le_antisymm (fun x hx => ?_) (le_inf (h.S_map_le_yamadaP d hlay) (h.S_le_centralizer d))
  obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
  have hxF : x ∈ normalizer (yamadaF₄ d t : Set G) :=
    h.yamadaP_le_normalizer_yamadaF₄_PA d hlay hxP
  have hxt : x * t * x⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.1 hxC]
    group
  have hxN : x ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay) hxF
      (by rw [hxt]; exact mem_sup_right (mem_zpowers t))
  have hxR₄ : x ∈ yamadaR₄ d t := by
    rw [← hker]
    exact mem_inf.2 ⟨mem_sup_left hxP, hxN⟩
  have hxS : x ∈ d.S.map L.subtype ⊔ zpowers t :=
    h.yamadaR₄_inf_centralizer_le d hlay ⟨hxR₄, hxC⟩
  rcases (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_map d.S)).1 hxS with h1 | h1
  · exact h1
  · exfalso
    apply htP
    have := mul_mem (hSP h1) (inv_mem hxP)
    rwa [mul_inv_cancel_right] at this

theorem ncs_le_normalizer_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ncs d t ≤ normalizer ((yamadaP d t : Subgroup G) : Set G) := by
  intro c hc
  have hE' := h.commutator_yamadaP_sup_zpowers d hlay
  have hcQ : c ∈ normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [h.yamadaP_sup_zpowers d hlay]
    exact Common.mem_normalizer_sup (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hc)
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ d hlay hc)
  have hcS₄ : c ∈ normalizer (yamadaS₄ d t : Set G) := by
    have := Setup.normalizer_le_normalizer_commutator_C8 (yamadaP d t ⊔ zpowers t) hcQ
    rwa [hE'] at this
  have hcN := h.normalizer_yamadaS₄_le d hlay (h.commutator_mem_yamadaY₂_of_mem_yamadaM₄ d hlay)
    (fun _ hx _ hy => h.commutator_mem_yamadaW₃_of_mem_yamadaF₄ d hlay hx hy)
    (h.yamadaS₄_eq_yamadaF₄_sup_S d hlay) hcS₄
  obtain ⟨⟨⟨hcV₁, -⟩, -⟩, -⟩ := hcN
  rw [h.yamadaP_eq_inf_centralizer_LS d hlay]
  exact Common.mem_normalizer_inf hcQ (Setup.mem_normalizer_centralizer_C8 hcV₁)

theorem yamadaP_le_closure_involutions (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ closure {x : G | x ∈ yamadaP d t ∧ x * x = 1} := by
  obtain ⟨hD₅, -, hD₅N, -⟩ := (h.yamada_5_25 d (h.normalizerHyp_of_layerHyp d hlay)
    (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay)
    (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay)
    (h.yamada_5_10_2 d hlay) (h.yamadaY₂_eq d hlay) (h.yamada_5_20 d hlay)
    (h.yamada_5_22_1 d hlay) (h.yamada_5_21 d hlay)).2.2.2
  set I := closure {x : G | x ∈ yamadaP d t ∧ x * x = 1} with hI
  have hinv : ∀ x, x ∈ yamadaP d t → x * x = 1 → x ∈ I := fun x hx hx2 =>
    subset_closure ⟨hx, hx2⟩
  set u : G := ((d.u : L) : G) with hu
  set v : G := ((d.v : L) : G) with hv
  have hW₃P : yamadaW₃ d t ≤ yamadaP d t :=
    (h.yamadaW₃_le_yamadaD₅_PA d hlay).trans (yamadaD₅_le_yamadaP d t)
  have hW₃I : ∀ w ∈ yamadaW₃ d t, w ∈ I := fun w hw =>
    hinv w (hW₃P hw) (h.mul_self_eq_one_of_mem_yamadaW₃ d hlay hw)
  have hWu : (yamadaW₃ d t).map (MulAut.conj u).toMonoidHom ≤ yamadaD₅ d t := by
    rw [hD₅]
    exact le_sup_right
  have hWuP : ∀ y ∈ (yamadaW₃ d t).map (MulAut.conj u).toMonoidHom, y ∈ yamadaP d t := fun y hy =>
    yamadaD₅_le_yamadaP d t (hWu hy)
  have hWu2 : ∀ y ∈ (yamadaW₃ d t).map (MulAut.conj u).toMonoidHom, y * y = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have hw2 := h.mul_self_eq_one_of_mem_yamadaW₃ d hlay hw
    change u * w * u⁻¹ * (u * w * u⁻¹) = 1
    calc u * w * u⁻¹ * (u * w * u⁻¹) = u * (w * w) * u⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hWuI : ∀ y ∈ (yamadaW₃ d t).map (MulAut.conj u).toMonoidHom, y ∈ I := fun y hy =>
    hinv y (hWuP y hy) (hWu2 y hy)
  have hD₅I : yamadaD₅ d t ≤ I := by
    rw [hD₅]
    exact sup_le hW₃I hWuI
  have hdec : ∀ z ∈ yamadaF₄ d t, ∃ w ∈ yamadaW₃ d t,
      ∃ y ∈ (yamadaW₃ d t).map (MulAut.conj u).toMonoidHom, y ∈ yamadaF₄ d t ∧ z = w * y := by
    intro z hz
    have hzD₅ : z ∈ yamadaD₅ d t := Setup.yamadaF₄_le_yamadaD₅_PA d hz
    rw [hD₅, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
      (fun y hy => hD₅N (hWu hy)), Set.mem_mul] at hzD₅
    obtain ⟨w, hw, y, hy, rfl⟩ := hzD₅
    refine ⟨w, hw, y, hy, ?_, rfl⟩
    have hwF : w ∈ yamadaF₄ d t := h.yamadaW₃_le_yamadaF₄_R5 d hlay hw
    have := mul_mem (inv_mem hwF) hz
    simpa using this
  have hF₄I : yamadaF₄ d t ≤ I := fun z hz => by
    obtain ⟨w, hw, y, hy, -, rfl⟩ := hdec z hz
    exact mul_mem (hW₃I w hw) (hWuI y hy)
  have hv2 : v * v = 1 := Setup.coe_v_mul_self d
  have hF₄vI : (yamadaF₄ d t).map (MulAut.conj v).toMonoidHom ≤ I := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, y, hy, hyF, rfl⟩ := hdec z hz
    have hvw : v * w * v⁻¹ ∈ yamadaW₃ d t :=
      (mem_normalizer_iff.1 (h.v_mem_normalizer_yamadaW₃ d) w).1 hw
    have hvy : v * y * v⁻¹ ∈ yamadaM₆ d t :=
      (mem_normalizer_iff.1 (h.v_mem_normalizer_yamadaM₆_PA d hlay) y).1
        (h.yamadaF₄_le_yamadaM₆_PA d hlay hyF)
    have hvy2 : v * y * v⁻¹ * (v * y * v⁻¹) = 1 := by
      calc v * y * v⁻¹ * (v * y * v⁻¹) = v * (y * y) * v⁻¹ := by group
        _ = 1 := by rw [hWu2 y hy]; group
    have : (MulAut.conj v).toMonoidHom (w * y) = (v * w * v⁻¹) * (v * y * v⁻¹) := by
      change v * (w * y) * v⁻¹ = _
      group
    rw [this]
    exact mul_mem (hW₃I _ hvw) (hinv _ (yamadaM₆_le_yamadaP d t hvy) hvy2)
  have hM₆I : yamadaM₆ d t ≤ I :=
    (h.yamadaM₆_le_sup_map_conj_yamadaF₄_PA d hlay).trans (sup_le hF₄I hF₄vI)
  exact sup_le hD₅I hM₆I

theorem fieldTwo_abelian_cyclic (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {X : Subgroup G}
    (hXC : X ≤ centralizer ({t} : Set G)) (htX : t ∈ X)
    (hXL : X ⊓ (L ⊔ zpowers t) = zpowers t) :
    IsMulCommutative X ∧ ∃ x ∈ X, X = zpowers t ⊔ zpowers x := by
  classical
  haveI := mulAutConj_range_normal (G := L)
  haveI : IsCyclic (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) :=
    d.isCyclic_quotient_range_conj
  set ε : X →* MulAut L ⧸ (MulAut.conj : L →* MulAut L).range :=
    (QuotientGroup.mk' (MulAut.conj : L →* MulAut L).range).comp
      (h.act.comp (inclusion hXC)) with hε
  have hker : ∀ x : X, ε x = 1 ↔ (x : G) ∈ zpowers t := by
    intro x
    have hε' : ε x = 1 ↔ h.act (inclusion hXC x) ∈ (MulAut.conj : L →* MulAut L).range := by
      simp only [hε, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hε', h.act_mem_range_conj_iff, h.centralizer_L_inf_of_data d]
    constructor
    · intro hx
      have : (x : G) ∈ X ⊓ (L ⊔ zpowers t) := ⟨x.2, hx⟩
      rwa [hXL] at this
    · intro hx
      exact mem_sup_right hx
  have hkerc : ε.ker ≤ center X := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hx' : (x : G) ∈ zpowers t := (hker x).1 (MonoidHom.mem_ker.1 hx)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx'
    apply Subtype.ext
    change (y : G) * x = x * y
    rw [← hk]
    exact ((show Commute (y : G) t from mem_centralizer_singleton_iff.1 (hXC y.2)).zpow_right k).eq
  refine ⟨ε.isMulCommutative_of_isCyclic_of_ker_le_center hkerc, ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ε.range)
  obtain ⟨x₀, hx₀⟩ := g.2
  refine ⟨x₀, x₀.2, le_antisymm (fun z hz => ?_) (sup_le ((zpowers_le).2 htX)
    ((zpowers_le).2 x₀.2))⟩
  obtain ⟨k, hk⟩ := hg ⟨ε ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  have hk' : ε x₀ ^ k = ε ⟨z, hz⟩ := by
    have := congrArg Subtype.val hk
    simpa [hx₀] using this
  have hz1 : ε (x₀ ^ (-k) * ⟨z, hz⟩) = 1 := by
    rw [map_mul, map_zpow, zpow_neg, hk', inv_mul_cancel]
  have hz2 : ((x₀ ^ (-k) * ⟨z, hz⟩ : X) : G) ∈ zpowers t := (hker _).1 hz1
  have e : z = (x₀ : G) ^ k * ((x₀ ^ (-k) * ⟨z, hz⟩ : X) : G) := by
    simp [zpow_neg]
  rw [e]
  exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers _) k)) (mem_sup_left hz2)

theorem exists_fieldTwoSubgroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∃ X : Subgroup G,
      X ≤ ncs d t ⊓ normalizer ((d.torus.range.map L.subtype : Subgroup G) : Set G) ∧
      t ∈ X ∧ X ⊓ (L ⊔ zpowers t) = zpowers t ∧ IsPGroup 2 X ∧
      IsSylowOf 2 (X ⊔ d.S.map L.subtype) (centralizer ({t} : Set G)) ∧
      ∀ x : centralizer ({t} : Set G), (x : G) ∈ X → ∃ k : ℕ, h.act x = d.φ ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin := d.finite
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set Nφ : Subgroup G := ((zpowers d.φ).comap h.act).map C.subtype with hNφ
  have hmem : ∀ x : C, (x : G) ∈ Nφ ↔ h.act x ∈ zpowers d.φ := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hNC : Nφ ≤ C := Subgroup.map_subtype_le _
  have hpow : ∀ x : C, (x : G) ∈ Nφ → ∃ k : ℕ, h.act x = d.φ ^ k := by
    intro x hx
    have h1 := (hmem x).1 hx
    rw [← mem_powers_iff_mem_zpowers] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, hk.symm⟩
  have htN : t ∈ Nφ := (hmem ⟨t, h.t_mem_centralizer⟩).2 (by
    rw [(h.act_eq_one_iff ⟨t, h.t_mem_centralizer⟩).2 h.htL]
    exact one_mem _)
  have hNS : Nφ ≤ ncs d t ⊓ normalizer ((d.torus.range.map L.subtype : Subgroup G) : Set G) := by
    intro c hc
    have hcC : c ∈ C := hNC hc
    obtain ⟨k, hk⟩ := hpow ⟨c, hcC⟩ hc
    refine ⟨⟨hcC, ?_⟩, ?_⟩
    · refine mem_normalizer_fintype fun z hz => ?_
      obtain ⟨s, hs, rfl⟩ := hz
      rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hcC, hk]
      exact d.φ_pow_mem_S k hs
    · refine mem_normalizer_fintype fun z hz => ?_
      obtain ⟨j, hj, rfl⟩ := hz
      rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hcC, hk]
      obtain ⟨η, rfl⟩ := hj
      rw [d.φ_pow_torus]
      exact ⟨_, rfl⟩
  have hLN : L ⊓ Nφ = ⊥ := by
    refine le_bot_iff.1 fun l hl => ?_
    have hlC : l ∈ C := h.L_le_centralizer hl.1
    have h1 : h.act ⟨l, hlC⟩ ∈ zpowers d.φ := (hmem ⟨l, hlC⟩).1 hl.2
    have h2 : h.act ⟨l, hlC⟩ = MulAut.conj (⟨l, hl.1⟩ : L) := h.act_of_mem_L hl.1
    have h3 : h.act ⟨l, hlC⟩ ∈ zpowers d.φ ⊓ (MulAut.conj : L →* MulAut L).range :=
      ⟨h1, ⟨_, h2.symm⟩⟩
    rw [d.zpowers_φ_inf_range_conj] at h3
    have h4 : MulAut.conj (⟨l, hl.1⟩ : L) = 1 := by rw [← h2]; exact mem_bot.1 h3
    have h5 : (⟨l, hl.1⟩ : L) = 1 := d.mulAutConj_injective (by rw [h4, map_one])
    exact mem_bot.2 (congrArg Subtype.val h5)
  have hCLN : C ≤ L ⊔ Nφ := by
    intro c hc
    obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨c, hc⟩)
    have hgC : (g : G) ∈ C := h.L_le_centralizer g.2
    have hc' : (g : G)⁻¹ * c ∈ C := mul_mem (inv_mem hgC) hc
    have hact : h.act ⟨(g : G)⁻¹ * c, hc'⟩ = d.φ ^ k := by
      have e : (⟨(g : G)⁻¹ * c, hc'⟩ : C) = (⟨(g : G), hgC⟩ : C)⁻¹ * ⟨c, hc⟩ := rfl
      rw [e, map_mul, map_inv, hgk, show (⟨(g : G), hgC⟩ : C) =
        ⟨g, h.L_le_centralizer g.2⟩ from rfl, h.act_of_mem_L g.2, Subtype.coe_eta]
      group
    have hn : (g : G)⁻¹ * c ∈ Nφ := (hmem ⟨_, hc'⟩).2 (by rw [hact]; exact npow_mem_zpowers _ k)
    have : c = (g : G) * ((g : G)⁻¹ * c) := by group
    rw [this]
    exact mul_mem (mem_sup_left g.2) (mem_sup_right hn)
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one])
  obtain ⟨B₀, hB₀⟩ := (hz2.comap_subtype (K := Nφ)).exists_le_sylow
  have hX : IsSylowOf 2 (B₀.map Nφ.subtype) Nφ := ⟨B₀, rfl⟩
  set X : Subgroup G := (B₀ : Subgroup Nφ).map Nφ.subtype with hXdef
  have hXN : X ≤ Nφ := hX.le
  have htX : zpowers t ≤ X := fun x hx =>
    ⟨⟨x, (zpowers_le).2 htN hx⟩, hB₀ (mem_subgroupOf.2 hx), rfl⟩
  have hXt : t ∈ X := htX (mem_zpowers t)
  have hLnorm : Nφ ≤ normalizer (L : Set G) := hNC.trans h.centralizer_le_normalizer
  have hcardC : Nat.card C = Nat.card L * Nat.card Nφ := by
    have h1 := card_sup_mul_card_inf_eq_D4 hLnorm
    rw [hLN, Subgroup.card_bot, mul_one, le_antisymm (sup_le h.L_le_centralizer hNC) hCLN] at h1
    exact h1
  set S' : Subgroup G := d.S.map L.subtype with hS'
  have hXnorm : X ≤ normalizer (S' : Set G) := fun x hx => (hNS (hXN hx)).1.2
  have hXS' : X ⊓ S' = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have : x ∈ L ⊓ Nφ := ⟨map_subtype_le _ hx.2, hXN hx.1⟩
    rwa [hLN] at this
  have hcardXS : Nat.card (S' ⊔ X : Subgroup G) = Nat.card S' * Nat.card X := by
    have h1 := card_sup_mul_card_inf_eq_D4 hXnorm
    rw [inf_comm, hXS', Subgroup.card_bot, mul_one] at h1
    exact h1
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hS : Nat.card d.S = 2 ^ (Nat.card L).factorization 2 := by
    rw [← hP, Sylow.card_eq_multiplicity]
  have hS'card : Nat.card S' = 2 ^ (Nat.card L).factorization 2 := by
    rw [hS', Subgroup.card_map_of_injective L.subtype_injective, hS]
  have hSyl : IsSylowOf 2 (X ⊔ S') C := by
    refine isSylowOf_of_card (sup_le (hXN.trans hNC) (h.S_le_centralizer d)) ?_
    rw [sup_comm, hcardXS, hS'card, hX.card_eq, hcardC,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add,
      mul_comm]
  refine ⟨X, hXN.trans hNS, hXt, ?_, hX.isPGroup, hSyl, fun x hx => hpow x (hXN hx)⟩
  refine le_antisymm (fun x hx => ?_) (le_inf htX (zpowers_le.2 (mem_sup_right (mem_zpowers t))))
  obtain ⟨hxX, hxLt⟩ := hx
  have hxC : x ∈ C := hNC (hXN hxX)
  have h1 : h.act ⟨x, hxC⟩ ∈ (MulAut.conj : L →* MulAut L).range := by
    rw [h.act_mem_range_conj_iff, h.centralizer_L_inf_of_data d]
    exact hxLt
  have h2 : h.act ⟨x, hxC⟩ ∈ zpowers d.φ ⊓ (MulAut.conj : L →* MulAut L).range :=
    ⟨(hmem ⟨x, hxC⟩).1 (hXN hxX), h1⟩
  rw [d.zpowers_φ_inf_range_conj] at h2
  have h3 : x ∈ centralizer (L : Set G) := (h.act_eq_one_iff ⟨x, hxC⟩).1 (mem_bot.1 h2)
  rw [← h.centralizer_L_inf_of_data d]
  exact ⟨h3, hxC⟩

theorem exists_complement_of_sylow (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (X B : Subgroup G) (hXC : X ≤ ncs d t) (hXL : X ⊓ L = ⊥)
    (hXS : IsSylowOf 2 (X ⊔ d.S.map L.subtype) (centralizer ({t} : Set G)))
    (hB : IsSylowOf 2 B (normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G)))
    (hQB : yamadaP d t ⊔ zpowers t ≤ B) :
    ∃ X' : Subgroup G, X' ≤ B ∧ X' ⊓ yamadaP d t = ⊥ ∧ B = yamadaP d t ⊔ X' ∧
      Nonempty (X' ≃* X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNQ : normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) =
      ncs d t ⊔ yamadaP d t :=
    h.normalizer_yamadaP_sup_zpowers d hlay (h.commutator_yamadaP_sup_zpowers d hlay)
      (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx)
  have hAP : ncs d t ≤ normalizer (yamadaP d t : Set G) := ncs_le_normalizer_yamadaP h d hlay
  have hPB : yamadaP d t ≤ B := le_sup_left.trans hQB
  have hSP : d.S.map L.subtype ≤ yamadaP d t := h.S_map_le_yamadaP d hlay
  have hS'A : d.S.map L.subtype ≤ ncs d t := le_inf (h.S_le_centralizer d) le_normalizer
  have hXS_A : IsSylowOf 2 (X ⊔ d.S.map L.subtype) (ncs d t) :=
    hXS.of_le (sup_le hXC hS'A) inf_le_left
  have hX2 : IsPGroup 2 X := hXS.isPGroup.to_le le_sup_left
  have hXP : X ⊓ yamadaP d t = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have hxS : x ∈ d.S.map L.subtype := by
      have : x ∈ yamadaP d t ⊓ centralizer ({t} : Set G) := ⟨hx.2, (hXC hx.1).1⟩
      rwa [yamadaP_inf_centralizer h d hlay] at this
    have : x ∈ X ⊓ L := ⟨hx.1, map_subtype_le _ hxS⟩
    rwa [hXL] at this
  have hD2 : IsPGroup 2 (B ⊓ ncs d t : Subgroup G) := hB.isPGroup.to_inf_left
  obtain ⟨a, haA, ha⟩ := exists_conj_le_of_isSylowOf_D4 hXS_A inf_le_right hD2
  have haP : a ∈ normalizer (yamadaP d t : Set G) := hAP haA
  set X' : Subgroup G := X.map (MulAut.conj a).toMonoidHom with hX'
  have hX'A : X' ≤ ncs d t := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem haA (hXC hx)) (inv_mem haA)
  have hBle : B ≤ yamadaP d t ⊔ X' := by
    intro b hb
    have hbN : b ∈ ncs d t ⊔ yamadaP d t := hNQ ▸ hB.le hb
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hAP, Set.mem_mul] at hbN
    obtain ⟨a₀, ha₀, p₀, hp₀, rfl⟩ := hbN
    have ha₀B : a₀ ∈ B := by
      have := mul_mem hb (inv_mem (hPB hp₀))
      rwa [mul_inv_cancel_right] at this
    have h1 := ha a₀ ⟨ha₀B, ha₀⟩
    have h2 : a₀ ∈ (X ⊔ yamadaP d t).map (MulAut.conj a).toMonoidHom := by
      rw [mem_map_conj_iff_D4]
      exact sup_le_sup_left hSP X h1
    rw [Subgroup.map_sup, Setup.map_conj_eq_self_D4 haP] at h2
    exact mul_mem (sup_comm X' (yamadaP d t) ▸ h2) (mem_sup_left hp₀)
  have hX'2 : IsPGroup 2 X' :=
    hX2.of_equiv (X.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
  obtain ⟨-, hP2, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have hPX'2 : IsPGroup 2 (yamadaP d t ⊔ X' : Subgroup G) :=
    hP2.to_sup_of_normal_left' hX'2 (hX'A.trans hAP)
  have hPX'N : yamadaP d t ⊔ X' ≤
      normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [hNQ]
    exact sup_le le_sup_right (hX'A.trans le_sup_left)
  have hBeq : yamadaP d t ⊔ X' = B := hB.eq_of_le hBle hPX'N hPX'2
  refine ⟨X', hBeq ▸ le_sup_right, ?_, hBeq.symm,
    ⟨(X.equivMapOfInjective _ (MulAut.conj a).injective).symm⟩⟩
  refine le_bot_iff.1 fun y hy => ?_
  obtain ⟨⟨x, hx, rfl⟩, hyP⟩ := hy
  have hxP : x ∈ yamadaP d t := by
    have := (mem_normalizer_iff.1 (inv_mem haP) _).1 hyP
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hx1 : x ∈ X ⊓ yamadaP d t := ⟨hx, hxP⟩
  rw [hXP, mem_bot] at hx1
  rw [hx1]
  simp

end CFSG.LocalAnalysis.EvenBN.TrialityD4
