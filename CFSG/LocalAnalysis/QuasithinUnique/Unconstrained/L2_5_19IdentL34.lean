module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL34

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

open scoped commutatorElement in
theorem commutatorElement_mul_central {H : Type*} [Group H] {k₁ k₂ z₁ z₂ : H}
    (h₁ : z₁ ∈ Subgroup.center H) (h₂ : z₂ ∈ Subgroup.center H) :
    ⁅k₁ * z₁, k₂ * z₂⁆ = ⁅k₁, k₂⁆ := by
  have c₁ : ∀ g : H, g * z₁ = z₁ * g := Subgroup.mem_center_iff.mp h₁
  have c₂ : ∀ g : H, g * z₂ = z₂ * g := Subgroup.mem_center_iff.mp h₂
  have s1 : z₁ * k₂ = k₂ * z₁ := (c₁ k₂).symm
  have s2 : z₁ * z₂ * z₁⁻¹ = z₂ := by rw [c₂ z₁]; group
  have s3 : z₂ * k₁⁻¹ * z₂⁻¹ = k₁⁻¹ := by rw [← c₂ k₁⁻¹]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc k₁ * z₁ * (k₂ * z₂) * (k₁ * z₁)⁻¹ * (k₂ * z₂)⁻¹
      = k₁ * (z₁ * k₂) * z₂ * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by group
    _ = k₁ * (k₂ * z₁) * z₂ * z₁⁻¹ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by rw [s1]
    _ = k₁ * k₂ * (z₁ * z₂ * z₁⁻¹) * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by group
    _ = k₁ * k₂ * z₂ * k₁⁻¹ * z₂⁻¹ * k₂⁻¹ := by rw [s2]
    _ = k₁ * k₂ * (z₂ * k₁⁻¹ * z₂⁻¹) * k₂⁻¹ := by group
    _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by rw [s3]

section L34

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

theorem IdentSetting.l34_core
    (hs : IdentSetting X K t)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2) :
    IsL32 K ∧ InducesOuter t X ∧
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨e0⟩ := nonempty_equiv_of_stated (↥X ⧸ Subgroup.center ↥X) hmodel
  have hπ := Tab.quotProj_surjective e0
  have hker := Tab.quotProj_ker e0
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hs.comp.1
  have hKX : K ≤ X := hs.K_le
  have hα2 := Tab.quotAct_mul_self (Tab.quotProj e0) hπ hker hs.tN hs.sq
  have hα1 := Tab.quotAct_ne_one (Tab.quotProj e0) hπ hker hs.tN hs.quasi hs.comm
  obtain ⟨e, he, hein⟩ := full_automorphism_action
  obtain ⟨τ, hτe⟩ : ∃ τ : R, e τ = Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN :=
    ⟨e.symm _, e.apply_symm_apply _⟩
  obtain ⟨τp, hτp⟩ : ∃ τp : Equiv.Perm (Fin 42), τp = (τ : Equiv.Perm (Fin 42)) := ⟨_, rfl⟩
  have hτs : ∀ s : S, ((Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN s : S) : Equiv.Perm (Fin 42)) =
      τp * s * τp⁻¹ := by
    intro s
    rw [hτp, ← hτe]
    exact he τ s
  have hτ2 : τ * τ = 1 := by
    apply e.injective
    rw [map_mul, hτe, hα2, map_one]
  have hτ2' : τp * τp = 1 := by
    rw [hτp]
    exact congrArg Subtype.val hτ2
  have hτi : τp⁻¹ = τp := inv_eq_of_mul_eq_one_right hτ2'
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hα1
    rw [← hτe, h, map_one]
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  let ρ : ↥K →* ↥S := (Tab.quotProj e0).comp (Subgroup.inclusion hKX)
  obtain ⟨hKsimple, a, b, hab⟩ := isKType_simple hs.ktype
  have hKcenter : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonab ⟨a, b, hab⟩
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hz : Subgroup.inclusion hKX k ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hk
    have hzk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k'
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hKX k'))
    rw [hKcenter] at hzk
    exact Subgroup.mem_bot.mp hzk
  have hKbcard0 : Nat.card ρ.range = Nat.card ↥K := by
    have h := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    exact h.symm
  have hρfix : ∀ k : ↥K, Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN (ρ k) = ρ k := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact Tab.quotAct_apply (Tab.quotProj e0) hπ hker hs.tN _ _ hy
  have hKbcard : Nat.card (ρ.range.map S.subtype) = Nat.card ↥K := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hKbcard0
  have hKbC' : ρ.range.map S.subtype ≤ Subgroup.centralizer {τp} ⊓ S := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, (ρ k).2⟩
    have h := hτs (ρ k)
    rw [hρfix k] at h
    calc ((ρ k : S) : Equiv.Perm (Fin 42)) * τp =
        (τp * ((ρ k : S) : Equiv.Perm (Fin 42)) * τp⁻¹) * τp := by rw [← h]
      _ = τp * ((ρ k : S) : Equiv.Perm (Fin 42)) := by group
  have hKbC : ρ.range.map S.subtype ≤
      Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S := by
    rw [← hτp]
    exact hKbC'
  have hKge := isKType_card_ge hs.ktype
  have hconj : IsConj τ r₂R :=
    Tab.L34.isConj_r₂_of_card hord hKbC (by rw [hKbcard]; exact hKge)
  have hC168 := Tab.L34.card_cent_of_isConj hconj
  have hKle : Nat.card ↥K ≤ 168 := by
    have := Subgroup.card_le_of_le hKbC
    rw [hKbcard, hC168] at this
    exact this
  have hK168 : Nat.card ↥K = 168 := le_antisymm hKle hKge
  have hL32 : IsL32 K := by
    rcases hs.ktype with h | h | h
    · have := h.card_ge
      omega
    · exact h
    · have := h.card_eq
      omega
  obtain ⟨c, hcR, hτc⟩ := eq_conj_of_isConj hconj
  have hτc' : τp = c * r₂ * c⁻¹ := by
    rw [hτp]
    exact hτc
  have hKbeq : ρ.range.map S.subtype = Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S :=
    Subgroup.eq_of_le_of_card_ge hKbC (by rw [hC168, hKbcard, hK168])
  refine ⟨hL32, ?_, ?_⟩
  ·
    refine ⟨hs.tN, ?_⟩
    rintro ⟨l, hl, hlt⟩
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.sq
    have hconjl : Tab.conjAut X t hs.tN = MulAut.conj (⟨l, hl⟩ : ↥X)⁻¹ := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [Tab.coe_conjAut]
      have h1 := hlt x x.2
      rw [hinv] at h1
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hinv]
      exact h1
    have hαinner : Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S := by
      refine ⟨Tab.quotProj e0 (⟨l, hl⟩ : ↥X)⁻¹, ?_⟩
      show MulAut.conj (Tab.quotProj e0 (⟨l, hl⟩ : ↥X)⁻¹) =
        Tab.quotActHom (Tab.quotProj e0) hπ hker (Tab.conjAut X t hs.tN)
      rw [hconjl, Tab.quotActHom_conj]
    have hmem : Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN ∈
        (S.subgroupOf R).map e.toMonoidHom := by
      rw [hein]
      exact hαinner
    obtain ⟨r, hrS, hr⟩ := Subgroup.mem_map.mp hmem
    have hrτ : r = τ := e.injective (hr.trans hτe.symm)
    have hτS : (τ : Equiv.Perm (Fin 42)) ∈ S := by
      rw [← hrτ]
      exact hrS
    exact not_mem_S_of_isConj hconj not_mem_S_r₂ hτS
  ·
    set C := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
    set Rr := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C with hRdef
    have hKR : K ≤ Rr := le_perfectResidualOf hs.perfect_K hKXt
    have hRC : Rr ≤ C := perfectResidualOf_le C
    have hRperf : ⁅Rr, Rr⁆ = Rr := perfectResidualOf_perfect C
    have hCKZ : ∀ x : ↥X, (x : G) ∈ C →
        ∃ k : ↥K, ∃ z ∈ Subgroup.center ↥X, x = Subgroup.inclusion hKX k * z := by
      intro x hx
      have hxt : (x : G) * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hy : (x : G) = t * (x : G) * t⁻¹ := by
        calc (x : G) = ((x : G) * t) * t⁻¹ := by group
          _ = (t * x) * t⁻¹ := by rw [hxt]
      have hfix := Tab.quotAct_apply (Tab.quotProj e0) hπ hker hs.tN x x hy
      have hs1 := hτs (Tab.quotProj e0 x)
      rw [hfix] at hs1
      have hxC : ((Tab.quotProj e0 x : S) : Equiv.Perm (Fin 42)) ∈
          Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S := by
        refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, (Tab.quotProj e0 x).2⟩
        rw [← hτp]
        calc ((Tab.quotProj e0 x : S) : Equiv.Perm (Fin 42)) * τp =
            (τp * ((Tab.quotProj e0 x : S) : Equiv.Perm (Fin 42)) * τp⁻¹) * τp := by rw [← hs1]
          _ = τp * ((Tab.quotProj e0 x : S) : Equiv.Perm (Fin 42)) := by group
      rw [← hKbeq] at hxC
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Subgroup.mem_map.mp hxC
      have hρk : ρ k = Tab.quotProj e0 x := Subtype.ext hk
      refine ⟨k, (Subgroup.inclusion hKX k)⁻¹ * x, ?_, by group⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
      have : (Tab.quotProj e0 (Subgroup.inclusion hKX k)) = Tab.quotProj e0 x := hρk
      rw [this, inv_mul_cancel]
    have hRK : Rr ≤ K := by
      have hcomm : ⁅Rr, Rr⁆ ≤ K := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        have haC : a ∈ C := hRC ha
        have hbC : b ∈ C := hRC hb
        obtain ⟨k₁, z₁, hz₁, h₁⟩ := hCKZ ⟨a, haC.1⟩ haC
        obtain ⟨k₂, z₂, hz₂, h₂⟩ := hCKZ ⟨b, hbC.1⟩ hbC
        have h3 : ⁅(⟨a, haC.1⟩ : ↥X), ⟨b, hbC.1⟩⁆ =
            ⁅Subgroup.inclusion hKX k₁, Subgroup.inclusion hKX k₂⁆ := by
          rw [h₁, h₂]
          exact commutatorElement_mul_central hz₁ hz₂
        have h4 := congrArg (Subtype.val : ↥X → G) h3
        have h5 : ⁅a, b⁆ = ⁅(k₁ : G), (k₂ : G)⁆ := by
          simpa [commutatorElement_def] using h4
        rw [h5]
        exact K.mul_mem (K.mul_mem (K.mul_mem k₁.2 k₂.2) (K.inv_mem k₁.2)) (K.inv_mem k₂.2)
      rw [← hRperf]
      exact hcomm
    exact le_antisymm hKR hRK

theorem tabIdentFor_l3Four
    : TabIdentFor @Ident.FamL3Four := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, hmodel⟩ := hX
  have hc : Subgroup.center ↥X = ⊥ := hs.center_eq_bot_of_simple hsimple
  have hmodel' :
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm hmodel
  obtain ⟨hL32, hout, hK⟩ := hs.l34_core hmodel'
  refine ⟨?_, hK, fun hbig => ?_, fun _ => Or.inl ⟨hL32, hmodel', hout⟩, fun hA6 => ?_⟩
  · rw [hc]
    exact (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup ↥X))
  · have h1 := hbig.card_ge
    have h2 := hL32.card_eq
    omega
  · exfalso
    have h1 := hA6.card_eq
    have h2 := hL32.card_eq
    omega

theorem tabIdentFor_coverL34
    : TabIdentFor @Ident.FamCoverL34 := by
  intro G _ _ X K t hs hX
  obtain ⟨-, hZc, hmodel⟩ := hX
  have hmodel' :
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZc).symm hmodel
  obtain ⟨hL32, hout, hK⟩ := hs.l34_core hmodel'
  refine ⟨?_, hK, fun hbig => ?_, fun _ => Or.inl ⟨hL32, hmodel', hout⟩, fun hA6 => ?_⟩
  · rw [hZc]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  · have h1 := hbig.card_ge
    have h2 := hL32.card_eq
    omega
  · exfalso
    have h1 := hA6.card_eq
    have h2 := hL32.card_eq
    omega

end L34

end CFSG.QuasithinUnique.Id2519
