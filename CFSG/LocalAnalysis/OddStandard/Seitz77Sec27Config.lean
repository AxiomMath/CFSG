module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Shape

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

section Hdef

variable {G : Type} [Group G] [Finite G]

abbrev KW27 (W : Subgroup G) : Subgroup ↥(normalizer (W : Set G)) :=
  (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))

instance (W : Subgroup G) : (KW27 W).Normal :=
  Subgroup.normal_subgroupOf_centralizer_normalizer _

abbrev Hh27 (W : Subgroup G) : Type := ↥(normalizer (W : Set G)) ⧸ KW27 W

@[expose] noncomputable def alpha27 (W : Subgroup G) : Hh27 W →* MulAut ↥W :=
  QuotientGroup.lift (KW27 W) W.normalizerMonoidHom (by
    rw [Subgroup.normalizerMonoidHom_ker])

omit [Finite G] in
theorem alpha27_mk (W : Subgroup G) (n : ↥(normalizer (W : Set G))) :
    alpha27 W (QuotientGroup.mk n) = W.normalizerMonoidHom n := rfl

omit [Finite G] in
theorem alpha27_injective (W : Subgroup G) : Function.Injective (alpha27 W) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  rw [alpha27_mk, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker] at hx
  exact (QuotientGroup.eq_one_iff n).mpr hx

end Hdef

theorem exists_subgroup_of_submodule {W : Type*} [Group W]
    (κ : W ≃* Multiplicative (Fin 8 → ZMod 2)) (U : Submodule (ZMod 2) (Fin 8 → ZMod 2)) :
    ∃ U₀ : Subgroup W, (∀ w : W, w ∈ U₀ ↔ Multiplicative.toAdd (κ w) ∈ U) ∧
      Nat.card U₀ = Nat.card U := by
  let U₀ : Subgroup W :=
    { carrier := {w | Multiplicative.toAdd (κ w) ∈ U}
      one_mem' := by
        show Multiplicative.toAdd (κ 1) ∈ U
        rw [map_one, toAdd_one]
        exact U.zero_mem
      mul_mem' := by
        intro a b ha hb
        show Multiplicative.toAdd (κ (a * b)) ∈ U
        rw [map_mul, toAdd_mul]
        exact U.add_mem ha hb
      inv_mem' := by
        intro a ha
        show Multiplicative.toAdd (κ a⁻¹) ∈ U
        rw [map_inv, toAdd_inv]
        exact U.neg_mem ha }
  refine ⟨U₀, fun w => Iff.rfl, ?_⟩
  apply Nat.card_congr
  exact
    { toFun := fun w => ⟨Multiplicative.toAdd (κ w.1), w.2⟩
      invFun := fun u => ⟨κ.symm (Multiplicative.ofAdd u.1), by
        show Multiplicative.toAdd (κ (κ.symm (Multiplicative.ofAdd u.1))) ∈ U
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact u.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }

namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H

@[expose] noncomputable def piH27 : Hh27 (Sy ⊓ Wt) →* Ntil27 (Sy ⊓ Wt) :=
  QuotientGroup.lift (KW27 (Sy ⊓ Wt)) (pi27 (Sy ⊓ Wt))
    (fun _ hx => H.pi_eq_one_of_mem_centralizer_W (mem_subgroupOf.mp hx))

theorem piH27_surjective : Function.Surjective H.piH27 := by
  intro y
  obtain ⟨n, rfl⟩ := pi27_surjective (Sy ⊓ Wt) y
  exact ⟨QuotientGroup.mk n, rfl⟩

theorem odd_card_ker_piH27 : Odd (Nat.card H.piH27.ker) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  set K : Subgroup ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) :=
    (Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) with hK
  have hKL : K ≤ KW27 (Sy ⊓ Wt) := fun y hy =>
    mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun z hz =>
      L34.comm_of_isElemAbelian (hS.elem_inf_Wt hSy hWt) hz (mem_subgroupOf.mp hy))
  have h1 : Nat.card (pi27 (Sy ⊓ Wt)).ker = Nat.card K *
      Nat.card (CFSG.oddCore (Nbar27 (Sy ⊓ Wt))) := card_ker_qPi K
  have h2 : (pi27 (Sy ⊓ Wt)).ker = H.piH27.ker.comap (QuotientGroup.mk' (KW27 (Sy ⊓ Wt))) := by
    ext x
    rfl
  have h3 : Nat.card (pi27 (Sy ⊓ Wt)).ker = Nat.card (KW27 (Sy ⊓ Wt)) * Nat.card H.piH27.ker := by
    rw [h2, card_comap_of_surjective_s27 (QuotientGroup.mk'_surjective _), QuotientGroup.ker_mk']
  have h4 := Subgroup.relIndex_mul_card K (KW27 (Sy ⊓ Wt))
  rw [inf_eq_left.mpr hKL] at h4
  have hr : K.relIndex (KW27 (Sy ⊓ Wt)) = (Sy ⊓ Wt).relIndex
      (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) :=
    Subgroup.relIndex_subgroupOf (Subgroup.centralizer_le_normalizer _)
  have hodd_r : Odd ((Sy ⊓ Wt).relIndex (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G))) :=
    Nat.odd_iff.mpr (by
      have := hS.not_two_dvd_relIndex_centralizer_W hSy hWt
      omega)
  rw [hr] at h4
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have h5 : Nat.card (CFSG.oddCore (Nbar27 (Sy ⊓ Wt))) =
      (Sy ⊓ Wt).relIndex (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) *
        Nat.card H.piH27.ker := by
    apply Nat.eq_of_mul_eq_mul_left hKpos
    calc Nat.card K * Nat.card (CFSG.oddCore (Nbar27 (Sy ⊓ Wt))) =
          Nat.card (pi27 (Sy ⊓ Wt)).ker := h1.symm
      _ = Nat.card (KW27 (Sy ⊓ Wt)) * Nat.card H.piH27.ker := h3
      _ = Nat.card K * ((Sy ⊓ Wt).relIndex (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) *
          Nat.card H.piH27.ker) := by
        rw [← h4]
        ring
  exact (odd_card_oddCore_s27 (G := Nbar27 (Sy ⊓ Wt))).of_dvd_nat
    ⟨(Sy ⊓ Wt).relIndex (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)), by rw [h5]; ring⟩

theorem ker_piH27 : H.piH27.ker = CFSG.oddCore (Hh27 (Sy ⊓ Wt)) := by
  refine le_antisymm (le_oddCore_of_normal_odd inferInstance H.odd_card_ker_piH27) ?_
  have hQn : ((CFSG.oddCore (Hh27 (Sy ⊓ Wt))).map H.piH27).Normal :=
    Subgroup.Normal.map inferInstance _ H.piH27_surjective
  have hQodd : Odd (Nat.card ((CFSG.oddCore (Hh27 (Sy ⊓ Wt))).map H.piH27)) :=
    (odd_card_oddCore_s27 (G := Hh27 (Sy ⊓ Wt))).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hle := le_oddCore_of_normal_odd hQn hQodd
  rw [oddCore_qPi_bot _] at hle
  intro x hx
  have : H.piH27 x ∈ (CFSG.oddCore (Hh27 (Sy ⊓ Wt))).map H.piH27 := ⟨x, hx, rfl⟩
  have h1 := hle this
  rw [Subgroup.mem_bot] at h1
  exact h1

@[expose] noncomputable def piHP : ↥P →* Hh27 (Sy ⊓ Wt) :=
  (QuotientGroup.mk' (KW27 (Sy ⊓ Wt))).comp (Subgroup.inclusion H.le_normalizer_W)

theorem ker_piHP_eq : H.piHP.ker = (conjAct27 R P H.hP.le_norm).ker := by
  have hRW : R ≤ Sy ⊓ Wt := H.sit.S.W_le_inf_Wt H.sit.hSy H.sit.hWt
  have hker : ∀ q : ↥P, conjAct27 R P H.hP.le_norm q = 1 ↔ (q : G) ∈ centralizer (R : Set G) := by
    intro q
    have : conjAct27 R P H.hP.le_norm q = R.normalizerMonoidHom ⟨q, H.hP.le_norm q.2⟩ := rfl
    rw [this, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  ext q
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
  constructor
  · intro h
    have h' : (⟨q, H.le_normalizer_W q.2⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) ∈
        KW27 (Sy ⊓ Wt) := (QuotientGroup.eq_one_iff _).mp h
    exact Subgroup.centralizer_le hRW (mem_subgroupOf.mp h')
  · intro h
    exact (QuotientGroup.eq_one_iff _).mpr
      (mem_subgroupOf.mpr (H.centralizer_R_le_centralizer_W q.2 h))

theorem Xh_equiv :
    Nonempty (↥H.piHP.range ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := rangeEquiv_of_ker_eq H.piHP (conjAct27 R P H.hP.le_norm) H.ker_piHP_eq
  have := H.hP.simple
  obtain ⟨e₂⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five H.hP.card
  exact ⟨e₁.trans e₂⟩

theorem disjoint_Xh_ker : Disjoint H.piHP.range H.piH27.ker := by
  obtain ⟨e⟩ := H.Xh_equiv
  have hsimple : IsSimpleGroup ↥H.piHP.range := e.isSimpleGroup
  rw [Subgroup.disjoint_def]
  intro x hxX hxk
  have hnorm : (H.piH27.ker.subgroupOf H.piHP.range).Normal := Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.piH27.ker.subgroupOf H.piHP.range) with
    h0 | h1
  · have hx : (⟨x, hxX⟩ : ↥H.piHP.range) ∈ H.piH27.ker.subgroupOf H.piHP.range :=
      mem_subgroupOf.mpr hxk
    rw [h0, Subgroup.mem_bot] at hx
    exact congrArg Subtype.val hx
  · exfalso
    have hle : H.piHP.range ≤ H.piH27.ker := by
      intro y hy
      have : (⟨y, hy⟩ : ↥H.piHP.range) ∈ H.piH27.ker.subgroupOf H.piHP.range := by
        rw [h1]
        trivial
      exact mem_subgroupOf.mp this
    have hcard : Nat.card ↥H.piHP.range = 60 := (Nat.card_congr e.toEquiv).trans s27_nat_card_alt5
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    have hodd := H.odd_card_ker_piH27
    have h2 : 2 ∣ Nat.card H.piH27.ker := (show 2 ∣ 60 by norm_num).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem mod27 : Mod27 (Ntil27 (Sy ⊓ Wt)) H.X27 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hWab := hS.elem_inf_Wt hSy hWt
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  have hWc : Nat.card ↥(Sy ⊓ Wt) = 2 ^ 8 := hS.card_inf_Wt hSy hWt
  obtain ⟨κ, ρ, hρinj, hρ⟩ := exists_gl_rep (W := ↥(Sy ⊓ Wt))
    (fun a b => Subtype.ext (L34.comm_of_isElemAbelian hWab a.2 b.2))
    (fun a => Subtype.ext (by
      have := hWab.2 a.1 a.2
      rwa [sq] at this)) hWc (alpha27 (Sy ⊓ Wt)) (alpha27_injective _)
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥P →* MulAut ↥R, σ = conjAct27 R P H.hP.le_norm := ⟨_, rfl⟩
  have hker : H.piHP.ker = σ.ker := hσ ▸ H.ker_piHP_eq
  have hcard60 : Nat.card ↥σ.range = 60 := hσ ▸ H.hP.card
  have htrans' : ∀ r s : ↥R, r ≠ 1 → s ≠ 1 → ∃ g ∈ σ.range, g r = s := by
    intro r s hr hs
    obtain ⟨p, hp, hps⟩ := H.hP.trans r.1 r.2 s.1 s.2 (fun h => hr (Subtype.ext h))
      (fun h => hs (Subtype.ext h))
    refine ⟨σ ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, Subtype.ext ?_⟩
    rw [hσ]
    exact hps
  have hRc : Nat.card ↥R = 16 := hS.W_card
  refine ⟨⟨Hh27 (Sy ⊓ Wt), inferInstance, inferInstance, ρ, H.piH27, hρinj, H.piH27_surjective,
    H.ker_piH27, H.piHP.range, ?_, H.disjoint_Xh_ker, ?_, ?_⟩⟩
  · rw [X27, ← MonoidHom.range_comp]
    rfl
  ·
    intro Usub hinv
    obtain ⟨U₀, hU₀mem, hU₀card⟩ := exists_subgroup_of_submodule κ Usub
    obtain ⟨Ug, hUg⟩ : ∃ Ug : Subgroup G, Ug = U₀.map (Sy ⊓ Wt).subtype := ⟨_, rfl⟩
    have hUgW : Ug ≤ Sy ⊓ Wt := hUg ▸ Subgroup.map_subtype_le _
    have hUginv : ∀ p ∈ P, ∀ u ∈ Ug, p * u * p⁻¹ ∈ Ug := by
      intro p hp u hu
      rw [hUg] at hu ⊢
      obtain ⟨w₀, hw₀, rfl⟩ := hu
      have hx : H.piHP ⟨p, hp⟩ ∈ H.piHP.range := ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ↥(Sy ⊓ Wt), w₁ = alpha27 (Sy ⊓ Wt) (H.piHP ⟨p, hp⟩) w₀ :=
        ⟨_, rfl⟩
      have hw₁G : (w₁ : G) = p * (w₀ : G) * p⁻¹ := by rw [hw₁]; rfl
      have h1 := hρ (H.piHP ⟨p, hp⟩) w₀
      rw [← hw₁] at h1
      have h2 : Multiplicative.toAdd (κ w₁) ∈ Usub := by
        rw [h1, toAdd_ofAdd]
        exact hinv _ hx _ ((hU₀mem w₀).mp hw₀)
      exact ⟨w₁, (hU₀mem w₁).mpr h2, hw₁G⟩
    have hcardU := invariant_card_of_trans (W := Sy ⊓ Wt) (R := R) (P := P) (U := Ug) (t := t)
      hRW (fun a ha b hb => L34.comm_of_isElemAbelian hWab ha hb) hWc hRc
      (fun w hw => hS.t_conj_mem_inf_Wt hSy hWt hw)
      (fun w hw hwt => by
        rw [← hS.inf_Wt_inf_centralizer_t hSy hWt]
        exact mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr hwt⟩)
      (fun r hr => (hS.t_comm_W hr).symm)
      (fun v hv => hS.exists_commutator_eq hSy hWt hv)
      (fun p hp => H.P_comm_t hp)
      (fun p hp r hr => (mem_normalizer_iff.mp (H.hP.le_norm hp) r).mp hr)
      H.hP.trans hUgW hUginv
    have hcardUg : Nat.card Ug = 2 ^ Module.finrank (ZMod 2) Usub := by
      rw [hUg, Subgroup.card_map_of_injective (Sy ⊓ Wt).subtype_injective, hU₀card,
        card_submodule_eq_two_pow]
    rw [hcardUg] at hcardU
    rcases hcardU with h | h | h
    · left
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ _ = 2 ^ 0 by simpa using h)
    · right
      left
      exact Nat.pow_right_injective (le_refl 2) (show 2 ^ _ = 2 ^ 4 by rw [h])
    · right
      right
      exact Nat.pow_right_injective (le_refl 2) h
  ·
    intro x hx hx3 w hw
    obtain ⟨q, rfl⟩ := hx
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(Sy ⊓ Wt), w₀ = κ.symm (Multiplicative.ofAdd w) := ⟨_, rfl⟩
    have hκw : κ w₀ = Multiplicative.ofAdd w := by rw [hw₀]; exact MulEquiv.apply_symm_apply _ _
    have hfix : alpha27 (Sy ⊓ Wt) (H.piHP q) w₀ = w₀ := by
      apply κ.injective
      rw [hρ, hκw, toAdd_ofAdd, hw]
    have hpw : (q : G) * (w₀ : G) * (q : G)⁻¹ = (w₀ : G) := congrArg Subtype.val hfix
    have hq3 : (σ q) ^ 3 = 1 := by
      have h1 : (H.piHP q) ^ 3 = 1 := by
        rw [← hx3]
        exact pow_orderOf_eq_one _
      have h2 : q ^ 3 ∈ H.piHP.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact h1
      rw [hker, MonoidHom.mem_ker, map_pow] at h2
      exact h2
    have hkey : ∀ r : ↥R, r ≠ 1 → σ q r = r → False := by
      intro r hr1 hfixr
      have h1 : σ q = 1 := stab_of_trans_sixty hRc σ.range hcard60 htrans' (σ q) ⟨q, rfl⟩ hq3 r
        hr1 hfixr
      have h2 : q ∈ H.piHP.ker := by
        rw [hker]
        exact h1
      rw [MonoidHom.mem_ker] at h2
      rw [h2, orderOf_one] at hx3
      exact absurd hx3 (by norm_num)
    have hσapply : ∀ r : ↥R, ((σ q r : ↥R) : G) = (q : G) * (r : G) * (q : G)⁻¹ := by
      intro r
      rw [hσ]
      rfl
    have hcR : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ ∈ R :=
      hS.commutator_t_mem_W (hSy.le (mem_inf.mp w₀.2).1)
    have hqt : (q : G) * t = t * (q : G) := H.P_comm_t q.2
    have hrfix : σ q ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ =
        ⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ := by
      apply Subtype.ext
      rw [hσapply]
      show (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹ = _
      have e1 : (q : G) * t * (q : G)⁻¹ = t := by rw [hqt]; group
      calc (q : G) * (t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹) * (q : G)⁻¹
          = ((q : G) * t * (q : G)⁻¹) * ((q : G) * (w₀ : G) * (q : G)⁻¹) *
            ((q : G) * t * (q : G)⁻¹)⁻¹ * ((q : G) * (w₀ : G) * (q : G)⁻¹)⁻¹ := by group
        _ = t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ := by rw [e1, hpw]
    have hr1 : (⟨t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹, hcR⟩ : ↥R) = 1 := by
      by_contra hne
      exact hkey _ hne hrfix
    have hw₀R : (w₀ : G) ∈ R := by
      have h1 : t * (w₀ : G) * t⁻¹ * (w₀ : G)⁻¹ = 1 := congrArg Subtype.val hr1
      have h2 : (w₀ : G) * t = t * (w₀ : G) := by
        have := mul_inv_eq_one.mp h1
        calc (w₀ : G) * t = (t * (w₀ : G) * t⁻¹) * t := by rw [this]
          _ = t * (w₀ : G) := by group
      rw [← hS.inf_Wt_inf_centralizer_t hSy hWt]
      exact mem_inf.mpr ⟨w₀.2, mem_centralizer_singleton_iff.mpr h2⟩
    have hw₀1 : w₀ = 1 := by
      by_contra hne
      apply hkey ⟨(w₀ : G), hw₀R⟩ (fun h => hne (Subtype.ext (by
        have h' : (w₀ : G) = 1 := congrArg Subtype.val h
        exact h')))
      apply Subtype.ext
      rw [hσapply]
      exact hpw
    rw [hw₀1, map_one] at hκw
    have h0 := congrArg Multiplicative.toAdd hκw
    simpa using h0.symm

end Setup27

end CFSG.OddStandard.Seitz77
