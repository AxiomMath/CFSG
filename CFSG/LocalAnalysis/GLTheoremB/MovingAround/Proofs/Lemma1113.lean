module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.GH74.Constrained

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Lemma1113

section Transfer

variable {G T : Type} [Group G] [Group T] [Finite G] [Finite T]

theorem layer_transfer (X : Subgroup G) (f : X →* T)
    (hT : GLAPPrimeCoreOf 3 f.range = ⊥) (hL : GLAPLayer 3 f.range = ⊥)
    (hcop : Nat.Coprime 3 (Nat.card f.ker)) :
    GLAPPrimeCore 3 ↥X = f.ker ∧ GLAPLayer 3 X = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup T := f.range with hCdef
  have hOC : GLAPPrimeCore 3 ↥C = ⊥ := by
    apply Subgroup.map_injective (f := C.subtype) Subtype.val_injective
    rw [Subgroup.map_bot]
    exact hT
  have hA : GLAPPrimeCore 3 ↥X ≤ f.ker := by
    set O : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hOdef
    set Cn : Subgroup T := O.map f with hCn
    have hCn_le : Cn ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    have hnorm : (Cn.subgroupOf C).Normal := by
      constructor
      intro n hn g
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 g.2
      obtain ⟨o, ho, hon⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
      rw [Subgroup.mem_subgroupOf]
      have hval : ((g * n * g⁻¹ : C) : T) = f (y * o * y⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hy, hon]
      rw [hval]
      exact Subgroup.mem_map.2 ⟨y * o * y⁻¹, (GLAPPrimeCore.normal 3 ↥X).conj_mem o ho y, rfl⟩
    have hcopCn : Nat.Coprime 3 (Nat.card (Cn.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCn_le).toEquiv]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd O f) pPrimeCore_coprime_card
    have hle : Cn.subgroupOf C ≤ GLAPPrimeCore 3 ↥C :=
      le_sSup (s := {K : Subgroup ↥C | K.Normal ∧ Nat.Coprime 3 (Nat.card K)}) ⟨hnorm, hcopCn⟩
    rw [hOC] at hle
    have hsub : Cn.subgroupOf C = ⊥ := le_bot_iff.1 hle
    have hCn_bot : Cn = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hCn_le, hsub, Subgroup.map_bot]
    intro x hx
    have hfx : f x ∈ Cn := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    rw [hCn_bot, Subgroup.mem_bot] at hfx
    exact MonoidHom.mem_ker.2 hfx
  have hB : f.ker ≤ GLAPPrimeCore 3 ↥X :=
    le_sSup (s := {K : Subgroup ↥X | K.Normal ∧ Nat.Coprime 3 (Nat.card K)})
      ⟨MonoidHom.normal_ker f, hcop⟩
  have hEq : GLAPPrimeCore 3 ↥X = f.ker := le_antisymm hA hB
  refine ⟨hEq, ?_⟩
  let fC : ↥X →* ↥C := f.codRestrict C (fun x => MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hfC : ∀ x : ↥X, ((fC x : ↥C) : T) = f x := fun x => rfl
  let Θ : ↥X ⧸ GLAPPrimeCore 3 ↥X →* ↥C :=
    QuotientGroup.lift (GLAPPrimeCore 3 ↥X) fC (fun x hx => by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfC]
      exact MonoidHom.mem_ker.1 (hA hx))
  have hΘ : ∀ x : ↥X, Θ (QuotientGroup.mk x) = fC x := fun x => rfl
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hΘ] at hq
    have hx : x ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have h1 := congrArg Subtype.val hq
      rw [hfC] at h1
      exact h1
    rw [← hEq] at hx
    exact (QuotientGroup.eq_one_iff x).2 hx
  have hΘsurj : Function.Surjective Θ := by
    intro c
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 c.2
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [hΘ]
    apply Subtype.ext
    rw [hfC]
    exact hx
  let Θe : ↥X ⧸ GLAPPrimeCore 3 ↥X ≃* ↥C := MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩
  let Ω : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)
  have hΩinj : Function.Injective Ω := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hc' : c ∈ GLAPPrimeCore 3 ↥C := (QuotientGroup.eq_one_iff c).1 hc
    rw [hOC, Subgroup.mem_bot] at hc'
    exact hc'
  have hΩsurj : Function.Surjective Ω := QuotientGroup.mk_surjective
  let Ωe : ↥C ≃* ↥C ⧸ GLAPPrimeCore 3 ↥C := MulEquiv.ofBijective Ω ⟨hΩinj, hΩsurj⟩
  unfold GLAPLayer
  show sSup {L : Subgroup G | GLAPComponent 3 X L} = ⊥
  rw [sSup_eq_bot]
  intro L hL0
  exfalso
  have hLc : GLAPComponent 3 X L := hL0
  unfold GLAPComponent at hLc
  obtain ⟨hLX, hsubLX, hcompLX, -⟩ := hLc
  set Lx : Subgroup ↥X := L.subgroupOf X with hLxdef
  have hsubLx : IsSubnormal Lx ⊤ :=
    (IsSubnormal.top_iff).2 ((IsSubnormal.iff_subgroupOf hLX).1 hsubLX)
  set J : Subgroup T := Lx.map f with hJdef
  have hJC : J ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  have hsubJ : IsSubnormal J C := by
    have h1 := hsubLx.map f
    have h2 : (⊤ : Subgroup ↥X).map f = C := (MonoidHom.range_eq_map f).symm
    rw [h2] at h1
    exact h1
  have hJsub : J.subgroupOf C = Lx.map fC := by
    ext y
    simp only [Subgroup.mem_subgroupOf, hJdef, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  have hbarΘ : ((L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map
      (Θe : ↥X ⧸ GLAPPrimeCore 3 ↥X →* ↥C) = Lx.map fC := by
    rw [Subgroup.map_map]
    have hcomp : (Θe : ↥X ⧸ GLAPPrimeCore 3 ↥X →* ↥C).comp
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = fC := MonoidHom.ext (fun x => rfl)
    rw [hcomp]
  have hcompJC : IsComponentOf (J.subgroupOf C) ⊤ := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Θe hcompLX
    rw [hbarΘ, Subgroup.map_top_of_surjective (Θe : ↥X ⧸ GLAPPrimeCore 3 ↥X →* ↥C) Θe.surjective]
      at h1
    rw [hJsub]
    exact h1
  have hcompJ : IsComponentOf ((J.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C))) ⊤ := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Ωe hcompJC
    rw [Subgroup.map_top_of_surjective (Ωe : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C) Ωe.surjective] at h1
    exact h1
  have hmin : ∀ J' : Subgroup T, J' < J → IsSubnormal J' C →
      (J'.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) ≠
        (J.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) := by
    intro J' hlt _ heq
    have h1 : J'.subgroupOf C = J.subgroupOf C := Subgroup.map_injective hΩinj heq
    have h2 : J' = J := by
      have e1 : J' ≤ C := hlt.le.trans hJC
      rw [← Subgroup.map_subgroupOf_eq_of_le e1, h1, Subgroup.map_subgroupOf_eq_of_le hJC]
    exact hlt.ne h2
  have hJcomp : GLAPComponent 3 C J := by
    unfold GLAPComponent
    exact ⟨hJC, hsubJ, hcompJ, hmin⟩
  have hJle : J ≤ GLAPLayer 3 C := le_sSup (s := {K : Subgroup T | GLAPComponent 3 C K}) hJcomp
  have hJbot : J = ⊥ := by
    rw [hL] at hJle
    exact le_bot_iff.1 hJle
  have hbar_bot : (L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = ⊥ := by
    apply Subgroup.map_injective (f := (Θe : ↥X ⧸ GLAPPrimeCore 3 ↥X →* ↥C)) Θe.injective
    rw [Subgroup.map_bot, hbarΘ, ← hJsub, hJbot]
    ext y
    simp [Subgroup.mem_subgroupOf]
  rw [hbar_bot] at hcompLX
  obtain ⟨-, hs⟩ := hcompLX.2.2
  exact not_nontrivial _ hs.toNontrivial

end Transfer

@[expose] def TildeCore : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m p B M E A a K) (_ : p = 3) (e : G) (he : e ∈ M) (_ : e ∈ E ⊓ A) (_ : e ≠ 1),
    GLAPLayer 3 (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨e, he⟩ : ↥M)} :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) = ⊥ ∧
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨e, he⟩ : ↥M)} :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) = ⊥

end Lemma1113

theorem lemma1113_of_inputs (h11 : Lemma1111Statement) (hcore : Lemma1113.TildeCore) :
    Lemma1113Statement := by
  intro G _ _ m p B M E A a K h e heEA he1
  obtain ⟨rfl, -⟩ := h11 h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEM : E ≤ M := h.pair.1.1.1.1.1
  have hE3 : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 heEA).1
  have hem : e ∈ M := hEM heE
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have ht3 : (⟨e, hem⟩ : ↥M) ^ 3 = 1 := Subtype.ext he3
  have ht1 : (⟨e, hem⟩ : ↥M) ≠ 1 := fun h1 => he1 (congrArg Subtype.val h1)
  have hord : ∃ k : ℕ, orderOf (⟨e, hem⟩ : ↥M) = 3 ^ k :=
    ⟨1, by rw [orderOf_eq_prime ht3 ht1, pow_one]⟩
  have hcent : Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨e, hem⟩ : ↥M)} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) =
      (Subgroup.centralizer ({(⟨e, hem⟩ : ↥M)} : Set ↥M)).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)) :=
    CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map 3 hord
  have hC := hcore h rfl e hem heEA he1
  let X : Subgroup G := M ⊓ Subgroup.centralizer ({e} : Set G)
  have hXM : X ≤ M := inf_le_left
  let incl : ↥X →* ↥M := Subgroup.inclusion hXM
  let f : ↥X →* (↥M ⧸ GLAPPrimeCore 3 ↥M) := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp incl
  have hinclr : incl.range = Subgroup.centralizer ({(⟨e, hem⟩ : ↥M)} : Set ↥M) := by
    ext m
    rw [MonoidHom.mem_range, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hxe : (x : G) * e = e * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, incl, Subgroup.coe_inclusion]
      exact hxe
    · intro hm
      have hme : (m : G) * e = e * (m : G) := congrArg Subtype.val hm
      refine ⟨⟨m.1, Subgroup.mem_inf.2 ⟨m.2, Subgroup.mem_centralizer_singleton_iff.2 hme⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hrange : f.range = Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨e, hem⟩ : ↥M)} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rw [hcent, MonoidHom.range_comp, hinclr]
  have hT : GLAPPrimeCoreOf 3 f.range = ⊥ := by rw [hrange]; exact hC.2
  have hL : GLAPLayer 3 f.range = ⊥ := by rw [hrange]; exact hC.1
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    have hmap : f.ker.map incl ≤ GLAPPrimeCore 3 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff (incl x)).1 (MonoidHom.mem_ker.1 hx)
    have hc : Nat.card (f.ker.map incl) = Nat.card f.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXM)
    rw [← hc]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hmap) pPrimeCore_coprime_card
  obtain ⟨hEq, hlayer⟩ := Lemma1113.layer_transfer X f hT hL hcop
  refine ⟨hlayer, ?_⟩
  intro x hx
  have hx' : x ∈ (GLAPPrimeCore 3 ↥X).map X.subtype := hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx'
  have hy' : y ∈ f.ker := by rw [← hEq]; exact hy
  have hyN : incl y ∈ GLAPPrimeCore 3 ↥M := (QuotientGroup.eq_one_iff (incl y)).1 (MonoidHom.mem_ker.1 hy')
  exact Subgroup.mem_map.2 ⟨incl y, hyN, rfl⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
