module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentQuot

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Quot

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

theorem IdentSetting.exists_normalized_quot
    (hs : IdentSetting X K t) (hK : IsKType K)
    {Q : Type*} [Group Q] (π : ↥X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center ↥X) :
    ∃ N L₀ : Subgroup Q, L₀ ≤ N ∧ (∀ n ∈ N, Tab.quotAct π hπ hker hs.tN n = n) ∧
      (∀ n : Q, Tab.quotAct π hπ hker hs.tN n = n → ∀ c ∈ N, n * c * n⁻¹ ∈ N) ∧
      CFSG.IsComponent (L₀.subgroupOf N) ∧ Nonempty (↥L₀ ≃* ↥K) := by
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hCX : C ≤ X := inf_le_left
  have hKC : K ≤ C := hs.comp.1
  have hKX : K ≤ X := hs.K_le
  set a : MulAut Q := Tab.quotAct π hπ hker hs.tN with ha
  let ρ : ↥C →* Q := π.comp (Subgroup.inclusion hCX)
  let κ : ↥K →* Q := π.comp (Subgroup.inclusion hKX)
  have hκ : Function.Injective κ := hs.injective_proj hK π hker
  set N : Subgroup Q := ρ.range with hN
  set L₀ : Subgroup Q := κ.range with hL₀
  have hL₀N : L₀ ≤ N := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, hKC k.2⟩, rfl⟩
  have hfixC : ∀ c : ↥C, a (ρ c) = ρ c := by
    intro c
    have hct : (c : G) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    have hy : ((Subgroup.inclusion hCX c : ↥X) : G) =
        t * ((Subgroup.inclusion hCX c : ↥X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (c : G) = ((c : G) * t) * t⁻¹ := by group
        _ = (t * c) * t⁻¹ := by rw [hct]
    exact Tab.quotAct_apply π hπ hker hs.tN _ _ hy
  have hfix : ∀ n ∈ N, a n = n := by
    rintro _ ⟨c, rfl⟩
    exact hfixC c
  have hnorm : ∀ n : Q, a n = n → ∀ c ∈ N, n * c * n⁻¹ ∈ N := by
    intro n hn c hc
    obtain ⟨x, rfl⟩ := hπ n
    obtain ⟨w, rfl⟩ := hc
    obtain ⟨y, hy⟩ : ∃ y : ↥X, (y : G) = t * (x : G) * t⁻¹ :=
      ⟨Tab.conjAut X t hs.tN x, Tab.coe_conjAut X hs.tN x⟩
    have hπy : π y = π x := by
      rw [← Tab.quotAct_apply π hπ hker hs.tN x y hy]
      exact hn
    have hz : x⁻¹ * y ∈ Subgroup.center ↥X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπy, inv_mul_cancel]
    set w' : ↥X := Subgroup.inclusion hCX w with hw'
    have hwt : (w' : G) = t * (w' : G) * t⁻¹ := by
      have hct : (w : G) * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp w.2.2
      rw [hw', Subgroup.coe_inclusion]
      calc (w : G) = ((w : G) * t) * t⁻¹ := by group
        _ = (t * w) * t⁻¹ := by rw [hct]
    have hX1 : y * w' * y⁻¹ = x * w' * x⁻¹ := by
      have hz' : w' * (x⁻¹ * y) = (x⁻¹ * y) * w' := (Subgroup.mem_center_iff.mp hz w')
      calc y * w' * y⁻¹ = x * ((x⁻¹ * y) * w' * (x⁻¹ * y)⁻¹) * x⁻¹ := by group
        _ = x * (w' * (x⁻¹ * y) * (x⁻¹ * y)⁻¹) * x⁻¹ := by rw [hz']
        _ = x * w' * x⁻¹ := by group
    have hxw : ((x * w' * x⁻¹ : ↥X) : G) ∈ C := by
      refine ⟨(x * w' * x⁻¹).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : t * ((x * w' * x⁻¹ : ↥X) : G) * t⁻¹ = ((x * w' * x⁻¹ : ↥X) : G) := by
        have h2 : ((y * w' * y⁻¹ : ↥X) : G) = t * ((x * w' * x⁻¹ : ↥X) : G) * t⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hy]
          conv_lhs => rw [hwt]
          group
        rw [← h2, hX1]
      calc ((x * w' * x⁻¹ : ↥X) : G) * t
          = (t * ((x * w' * x⁻¹ : ↥X) : G) * t⁻¹) * t := by rw [h1]
        _ = t * ((x * w' * x⁻¹ : ↥X) : G) := by group
    refine ⟨⟨_, hxw⟩, ?_⟩
    show π (x * w' * x⁻¹) = π x * π w' * (π x)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hcomp : CFSG.IsComponent (L₀.subgroupOf N) := by
    have hsurj : Function.Surjective ρ.rangeRestrict := MonoidHom.rangeRestrict_surjective ρ
    have hq := hs.comp.2
    have hKne : ¬ (K.subgroupOf C) ≤ ρ.rangeRestrict.ker := by
      intro hle
      have hnt : Nontrivial ↥(K.subgroupOf C) := CFSG.LocalCores.isQuasisimple_nontrivial hq.1
      obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(K.subgroupOf C))
      apply hc1
      have h1 : ρ.rangeRestrict (c : ↥C) = 1 := MonoidHom.mem_ker.mp (hle c.2)
      have h2 : ρ (c : ↥C) = 1 := congrArg Subtype.val h1
      have h3 : κ ⟨(c : ↥C), c.2⟩ = 1 := h2
      have h4 := hκ (h3.trans (map_one κ).symm)
      have h5 : ((c : ↥C) : G) = (1 : G) := congrArg Subtype.val h4
      exact Subtype.ext (Subtype.ext h5)
    have himg : CFSG.IsComponent ((K.subgroupOf C).map ρ.rangeRestrict) :=
      ⟨CFSG.LocalCores.isQuasisimple_map hq.1 ρ.rangeRestrict hKne, hq.2.map hsurj⟩
    have heq : L₀.subgroupOf N = (K.subgroupOf C).map ρ.rangeRestrict := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨⟨k, hKC k.2⟩, k.2, rfl⟩
      · rintro ⟨c, hc, hcy⟩
        have hcy' : ρ c = y := congrArg Subtype.val hcy
        exact ⟨⟨(c : G), hc⟩, hcy'⟩
    rw [heq]
    exact himg
  exact ⟨N, L₀, hL₀N, hfix, hnorm, hcomp, ⟨(MonoidHom.ofInjective hκ).symm⟩⟩

theorem isComponent_subgroupOf_of_normal {Q : Type*} [Group Q] {F N L₀ : Subgroup Q} (hNF : N ≤ F)
    (hn : (N.subgroupOf F).Normal) (hL₀N : L₀ ≤ N) (hcomp : CFSG.IsComponent (L₀.subgroupOf N)) :
    CFSG.IsComponent (L₀.subgroupOf F) := by
  have hL₀F : L₀ ≤ F := hL₀N.trans hNF
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hL₀N).trans (Subgroup.subgroupOfEquivOfLe hL₀F).symm)
    hcomp.1, ?_⟩
  have hHK : L₀.subgroupOf F ≤ N.subgroupOf F := fun x hx => hL₀N hx
  refine Subgroup.IsSubnormal.trans hHK ?_ hn.isSubnormal
  let f : ↥N →* ↥(N.subgroupOf F) := (Subgroup.subgroupOfEquivOfLe hNF).symm.toMonoidHom
  have hf : Function.Surjective f := (Subgroup.subgroupOfEquivOfLe hNF).symm.surjective
  have hmap := hcomp.2.map hf
  convert hmap using 1
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hy
    exact ⟨⟨((y : ↥F) : Q), y.2⟩, hy, Subtype.ext (Subtype.ext rfl)⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

theorem IdentSetting.hasKComponent_fix_quot
    (hs : IdentSetting X K t) (hK : IsKType K)
    {Q : Type*} [Group Q] (π : ↥X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center ↥X) :
    HasKComponent ↥(fixSubgroup (Tab.quotAct π hπ hker hs.tN)) := by
  obtain ⟨N, L₀, hL₀N, hfix, hnorm, hcomp, ⟨e⟩⟩ := hs.exists_normalized_quot hK π hπ hker
  have hNF : N ≤ fixSubgroup (Tab.quotAct π hπ hker hs.tN) := fun n hn => hfix n hn
  have hn : (N.subgroupOf (fixSubgroup (Tab.quotAct π hπ hker hs.tN))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNF]
    intro c n hc hn'
    exact hnorm n hn' c hc
  have hL₀F : L₀ ≤ fixSubgroup (Tab.quotAct π hπ hker hs.tN) := hL₀N.trans hNF
  refine ⟨L₀.subgroupOf (fixSubgroup (Tab.quotAct π hπ hker hs.tN)),
    isComponent_subgroupOf_of_normal hNF hn hL₀N hcomp, ?_⟩
  have hcard : Nat.card ↥(L₀.subgroupOf (fixSubgroup (Tab.quotAct π hπ hker hs.tN))) =
      Nat.card ↥K :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀F).toEquiv).trans (Nat.card_congr e.toEquiv)
  rw [hcard]
  exact hK.kOrder

end Quot

end CFSG.QuasithinUnique.Id2519
