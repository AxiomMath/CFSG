module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwo
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviJZeroSLThreeIso
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Neighbour

variable {q : ℕ}

omit [Finite G] in
theorem leviJ₀_map_le_centralizer_J₀ (d : TrialityD4Data L q) :
    d.leviJ₀.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  exact coe_mem_centralizer_of_mem (d.leviJ₀_le_centralizer_J₀ hk)

omit [Finite G] in
noncomputable def leviJ₀MapEquiv (d : TrialityD4Data L q) :
    d.leviJ₀ ≃* (d.leviJ₀.map L.subtype : Subgroup G) :=
  d.leviJ₀.equivMapOfInjective L.subtype L.subtype_injective

omit [Finite G] in
theorem isQuasisimple_leviJ₀_map (d : TrialityD4Data L q) :
    CFSG.IsQuasisimple (d.leviJ₀.map L.subtype : Subgroup G) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (leviJ₀MapEquiv d) d.isQuasisimple_leviJ₀

omit [Finite G] in
theorem isQuasisimple_open_leviJ₀_map (d : TrialityD4Data L q) :
    CFSG.Open.IsQuasisimple (d.leviJ₀.map L.subtype : Subgroup G) :=
  CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
    (isQuasisimple_leviJ₀_map d)

omit [Finite G] in
theorem lieModel_leviJ₀_map (d : TrialityD4Data L (2 ^ f)) (hf : 1 ≤ f) :
    LieModel ((d.leviJ₀.map L.subtype : Subgroup G) ⧸
      center (d.leviJ₀.map L.subtype : Subgroup G)) .PSL 3 2 f := by
  let e₁ : (d.leviJ₀.map L.subtype : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 3) d.Γ₀ :=
    (leviJ₀MapEquiv d).symm.trans d.leviJ₀EquivSL3
  let e₂ := QuotientGroup.congr (center (d.leviJ₀.map L.subtype : Subgroup G))
    (center (Matrix.SpecialLinearGroup (Fin 3) d.Γ₀)) e₁ (map_center_eq e₁)
  let e₃ := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 d.Γ₀).symm
  exact SeitzReduction.LinearPilot.lieModel_of_mulEquiv_projectiveSL le_rfl hf d.card_Γ₀
    (e₂.trans e₃)

omit [Finite G] in
theorem leviJ₀_map_eq_layer (d : TrialityD4Data L q) :
    d.leviJ₀.map L.subtype = CFSG.inSubgroup CFSG.layer
      (L ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := by
  refine (SeitzReduction.LinearPilot.inSubgroup_layer_eq_of_commutator_mem
    (le_inf (map_subtype_le _) (leviJ₀_map_le_centralizer_J₀ d)) (fun g hg k hk => ?_)
    (isQuasisimple_leviJ₀_map d)).symm
  have hg' : (⟨g, hg.1⟩ : L) ∈ centralizer (d.J₀ : Set L) := mem_centralizer_of_coe_mem hg.2
  have hk' : (⟨k, hk.1⟩ : L) ∈ centralizer (d.J₀ : Set L) := mem_centralizer_of_coe_mem hk.2
  have hc : (⟨g, hg.1⟩ : L) * ⟨k, hk.1⟩ * (⟨g, hg.1⟩ : L)⁻¹ * (⟨k, hk.1⟩ : L)⁻¹ ∈ d.leviJ₀ := by
    rw [← d.commutator_centralizer_J₀, ← commutatorElement_def]
    exact commutator_mem_commutator hg' hk'
  exact ⟨_, hc, rfl⟩

end Neighbour

theorem eq_one_of_fix_J₀_leviJ₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (β : MulAut L) (hJ : ∀ a : L, (a : G) ∈ d.J₀.map L.subtype → β a = a)
    (hK : ∀ a : L, (a : G) ∈ d.leviJ₀.map L.subtype → β a = a) (n : ℕ) (hn : β ^ 2 ^ n = 1) :
    β = 1 := by
  have hJ' : ∀ j ∈ d.J₀, β j = j := fun j hj => hJ j ⟨j, hj, rfl⟩
  obtain ⟨g, hg, rfl⟩ := d.exists_conj_of_centralizes_J₀ rfl hJ'
  have hgK : g ∈ centralizer (d.leviJ₀ : Set L) := by
    rw [mem_centralizer_iff]
    intro k hk
    have e := hK k ⟨k, hk, rfl⟩
    rw [MulAut.conj_apply] at e
    calc k * g = g * k * g⁻¹ * g := by rw [e]
      _ = g * k := by group
  have hgn : g ^ 2 ^ n = 1 := by
    have hc : g ^ 2 ^ n ∈ center L := by
      rw [mem_center_iff]
      intro y
      have e := congrArg (fun γ : MulAut L => γ y) hn
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at e
      calc y * g ^ 2 ^ n = g ^ 2 ^ n * y * (g ^ 2 ^ n)⁻¹ * g ^ 2 ^ n := by rw [e]
        _ = g ^ 2 ^ n * y := by group
    rw [h.center_eq, mem_bot] at hc
    exact hc
  rw [d.eq_one_of_mem_centralizer_leviJ₀ hg hgK hgn, map_one]

omit [Finite G] in
theorem J₀_map_ne_bot {q : ℕ} (d : TrialityD4Data L q) : d.J₀.map L.subtype ≠ ⊥ := by
  intro hb
  have hc := d.yamada_three_five_four.2
  have hq := d.two_le_q
  have h1 : Nat.card (d.J₀.map L.subtype : Subgroup G) = 1 := by rw [hb, card_bot]
  rw [card_map_of_injective L.subtype_injective, hc] at h1
  nlinarith

theorem centralizer_J₀_ne_top (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≠ ⊤ := by
  intro htop
  have := h.simple
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := h.nonab
      exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
  apply J₀_map_ne_bot (G := G) d
  rw [eq_bot_iff]
  intro j hj
  have hjZ : j ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := htop ▸ mem_top g
    exact (mem_centralizer_iff.1 hg j hj).symm
  rw [hZ] at hjZ
  exact hjZ

theorem yamada_5_4_hr7 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    CFSG.Open.IsComponentOf
        (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))))
        (centralizer {(QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)}) ∧
      (∀ U : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
          CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) :
          Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
            CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) :=
  SeitzReduction.F4Pilot.standard_inheritance_of_forall_fix_eq_one h.std h.htL h.ht
    (h.centralizer_L_inf_of_data d) (h.t_mem_centralizer_J₀ d) (leviJ₀_map_eq_layer d)
    (isQuasisimple_open_leviJ₀_map d) (h.eq_one_of_fix_J₀_leviJ₀ d)

theorem not_normal_leviJ₀_bar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ¬ (((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))).Normal := by
  intro hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  set Kb := ((d.leviJ₀.map L.subtype).subgroupOf H).map π with hKb
  have htH : t ∈ H := h.t_mem_centralizer_J₀ d
  set tb : H ⧸ CFSG.oddCore H := π ⟨t, htH⟩ with htb
  obtain ⟨-, hsyl, -⟩ := h.yamada_5_4_hr7 d
  have htp : IsPGroup 2 (zpowers (⟨t, htH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, h.ht, pow_one])
  obtain ⟨T, hT⟩ := htp.exists_le_sylow
  have htT : (⟨t, htH⟩ : H) ∈ (T : Subgroup H) := hT (mem_zpowers _)
  have hO : Odd (Nat.card (CFSG.oddCore H)) :=
    CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore H
  have hTO : ∀ y ∈ (T : Subgroup H), y ∈ CFSG.oddCore H → y = 1 := by
    intro y hyT hyO
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨y, hyT⟩
    have hyk : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
    have h2 : orderOf y ∣ Nat.card (CFSG.oddCore H) := by
      have := orderOf_dvd_natCard (⟨y, hyO⟩ : CFSG.oddCore H)
      rwa [orderOf_mk] at this
    have h3 : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore H)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
    exact orderOf_eq_one_iff.1 ((h3.coprime_dvd_left h1).eq_one_of_dvd h2)
  have htb1 : tb ≠ 1 := by
    intro h1
    have h2 : (⟨t, htH⟩ : H) ∈ CFSG.oddCore H := (QuotientGroup.eq_one_iff _).1 h1
    have := hTO _ htT h2
    exact h.t_ne_one (congrArg Subtype.val this)
  have htbK : tb ∈ centralizer (Kb : Set (H ⧸ CFSG.oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [htb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.1 (h.t_mem_centralizer_leviJ₀ d) _ (mem_subgroupOf.1 hk)
  set U := (T : Subgroup H).map π ⊓ centralizer (Kb : Set (H ⧸ CFSG.oddCore H)) with hU
  have hUp : IsPGroup 2 U := (T.isPGroup'.map π).to_le inf_le_left
  have hU2 := hsyl U hUp inf_le_right
  have htbU : tb ∈ U := ⟨⟨_, htT, rfl⟩, htbK⟩
  apply h.not_le_centralizer_of_isSylowOf_centralizer_J₀ d (T := (T : Subgroup H).map H.subtype)
    ⟨T, rfl⟩
  rintro _ ⟨x, hxT, rfl⟩
  have hxT' : π x ∈ (T : Subgroup H).map π := ⟨x, hxT, rfl⟩
  have hxb : π x * tb * (π x)⁻¹ ∈ U := by
    refine Subgroup.mem_inf.2 ⟨((T : Subgroup H).map π).mul_mem
      (((T : Subgroup H).map π).mul_mem hxT' (Subgroup.mem_inf.1 htbU).1)
      (((T : Subgroup H).map π).inv_mem hxT'), ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : (π x)⁻¹ * k * π x ∈ Kb := by
      have := hN.conj_mem k hk (π x)⁻¹
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 htbK _ hk'
    calc k * (π x * tb * (π x)⁻¹) = π x * ((π x)⁻¹ * k * π x * tb) * (π x)⁻¹ := by group
      _ = π x * (tb * ((π x)⁻¹ * k * π x)) * (π x)⁻¹ := by rw [hc]
      _ = π x * tb * (π x)⁻¹ * k := by group
  have heq : π x * tb * (π x)⁻¹ = tb := by
    by_contra hne
    have hne1 : π x * tb * (π x)⁻¹ ≠ 1 := fun h1 => htb1 (by
      have := congrArg (fun z => (π x)⁻¹ * z * π x) h1
      simpa [mul_assoc] using this)
    let e : Fin 3 → U := ![1, ⟨tb, htbU⟩, ⟨π x * tb * (π x)⁻¹, hxb⟩]
    have he : Function.Injective e := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp only [e, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue] at hab ⊢
      all_goals first
        | rfl
        | exact absurd (congrArg Subtype.val hab) (by
            simp only [OneMemClass.coe_one]
            first
              | exact fun e => htb1 e.symm
              | exact fun e => hne1 e.symm
              | exact fun e => htb1 e
              | exact fun e => hne1 e
              | exact fun e => hne e.symm
              | exact fun e => hne e)
    have h3 := Nat.card_le_card_of_injective e he
    rw [Nat.card_fin] at h3
    have h4 := h3.trans hU2
    norm_num at h4
  have hcomm : x * ⟨t, htH⟩ * x⁻¹ * (⟨t, htH⟩ : H)⁻¹ ∈ CFSG.oddCore H := by
    have hπ1 : π (x * ⟨t, htH⟩ * x⁻¹ * (⟨t, htH⟩ : H)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← htb, heq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 hπ1
  have h1 := hTO _ (mul_mem (mul_mem (mul_mem hxT htT) (inv_mem hxT)) (inv_mem htT)) hcomm
  have h2 : x * ⟨t, htH⟩ = ⟨t, htH⟩ * x := by
    have := congrArg (fun z => z * ⟨t, htH⟩ * x) h1
    simpa [mul_assoc] using this
  exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h2)

theorem yamada_5_4_of_cat (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f)
    (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧
      ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
          ((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) < Kc ∧
          QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉ Kc ∧
          (∃ hsN : QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
                ⟨t, h.t_mem_centralizer_J₀ d⟩ ∈ normalizer (Kc : Set _),
            Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* (((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) : Subgroup _)))) := by
  obtain ⟨hcomp, hsyl, hstd⟩ := h.yamada_5_4_hr7 d
  have hov := SeitzReduction.LinearPilot.neighbour_overgroup_slm_center le_rfl (Or.inr hf) hcat
    h.kproper (h.centralizer_J₀_ne_top d) (h.t_mem_centralizer_J₀ d) h.ht
    (leviJ₀_map_le_centralizer_J₀ d) (isQuasisimple_leviJ₀_map d)
    (lieModel_leviJ₀_map d (by omega)) hcomp hsyl hstd (h.not_normal_leviJ₀_bar d)
  exact SeitzReduction.LinearPilot.NeighbourOvergroupSLm.exact
    (SeitzReduction.F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (Or.inr hf) hov

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
