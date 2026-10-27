module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbRes
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NatSL2Mat

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V]

section Module

variable {X : Subgroup (MulAut V)} {n : ℕ}

theorem slLift_eq_one_of_fixed (m : Multiplicative (Fin 2 → Fq n))
    (h : ∀ s : SLq n, slAct n s m = m) : m = 1 := by
  have h1 := congrArg Multiplicative.toAdd (h (TwoThree.lowerUni 1))
  have h2 := congrArg Multiplicative.toAdd (h (CFSG.SL2MinimalFaithful.unipotent 1))
  simp only [slAct, toAdd_ofAdd, TwoThree.lowerUni_mulVec, TwoThree.unipotent_mulVec] at h1 h2
  have e1 := congrFun h1 1
  have e2 := congrFun h2 0
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul] at e1 e2
  have e3 : Multiplicative.toAdd m 0 = 0 := by simpa using e1
  have e4 : Multiplicative.toAdd m 1 = 0 := by simpa using e2
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact e3
  · exact e4

theorem slLift_commV_inf_fixV {θ : X ≃* SLq n} (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) :
    commV X ⊓ fixV X = ⊥ := by
  obtain ⟨hinv, β, -, hβk, hβe⟩ := hnat
  rw [eq_bot_iff]
  rintro u ⟨hu, hfix⟩
  have hall : ∀ s : SLq n, slAct n s (β ⟨u, hu⟩) = β ⟨u, hu⟩ := by
    intro s
    have h1 := hβe (θ.symm s) ⟨u, hu⟩ (hinv _ (θ.symm s).2 u hu)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    congr 1
    exact Subtype.ext ((mem_fixV.mp hfix) _ (θ.symm s).2)
  have h0 : (⟨u, hu⟩ : ↥(commV X)) ∈ β.ker := slLift_eq_one_of_fixed _ hall
  rw [hβk, Subgroup.mem_subgroupOf] at h0
  exact h0

theorem slLift_eq_commV_of_ne_bot {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) {A : Subgroup V} (hAU : A ≤ commV X)
    (hA : ∀ g ∈ X, ∀ a ∈ A, g a ∈ A) (hne : A ≠ ⊥) : A = commV X := by
  obtain ⟨hinv, β, hβs, hβk, hβe⟩ := hnat
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha₀U : ((a₀ : ↥A) : V) ∈ commV X := hAU a₀.2
  have hv₀ : Multiplicative.toAdd (β ⟨(a₀ : V), ha₀U⟩) ≠ 0 := by
    intro h0
    apply ha₀
    have h1 : β ⟨(a₀ : V), ha₀U⟩ = 1 := by
      rw [← ofAdd_toAdd (β _), h0, ofAdd_zero]
    have h2 : (⟨(a₀ : V), ha₀U⟩ : ↥(commV X)) = 1 := hβi (h1.trans (map_one β).symm)
    exact Subtype.ext (congrArg (fun y : ↥(commV X) => (y : V)) h2)
  refine le_antisymm hAU fun u hu => ?_
  by_cases hv : Multiplicative.toAdd (β ⟨u, hu⟩) = 0
  · have h1 : β ⟨u, hu⟩ = 1 := by rw [← ofAdd_toAdd (β _), hv, ofAdd_zero]
    have h2 : (⟨u, hu⟩ : ↥(commV X)) = 1 := hβi (h1.trans (map_one β).symm)
    have h3 : u = 1 := congrArg (fun y : ↥(commV X) => (y : V)) h2
    rw [h3]
    exact A.one_mem
  · obtain ⟨g, hg⟩ := Glue.exists_sl2_mulVec_eq_of_ne_zero hv₀ hv
    have hxU : ((θ.symm g : ↥X) : MulAut V) (a₀ : V) ∈ commV X :=
      hinv _ (θ.symm g).2 _ ha₀U
    have h1 : β ⟨((θ.symm g : ↥X) : MulAut V) (a₀ : V), hxU⟩ = β ⟨u, hu⟩ := by
      refine (hβe (θ.symm g) ⟨(a₀ : V), ha₀U⟩ hxU).trans ?_
      rw [MulEquiv.apply_symm_apply, ← ofAdd_toAdd (β ⟨u, hu⟩)]
      exact congrArg Multiplicative.ofAdd hg
    have h2 := hβi h1
    have h3 : ((θ.symm g : ↥X) : MulAut V) (a₀ : V) = u :=
      congrArg (fun y : ↥(commV X) => (y : V)) h2
    rw [← h3]
    exact hA _ (θ.symm g).2 _ a₀.2

theorem slLift_exists_moved {θ : X ≃* SLq n} (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) :
    ∃ g ∈ X, ∃ u ∈ commV X, (g : MulAut V) u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hle : commV X ≤ fixV X := fun u hu => mem_fixV.mpr fun g hg => hcon g hg u hu
  have h1 := slLift_commV_inf_fixV hnat
  rw [inf_eq_left.mpr hle] at h1
  obtain ⟨-, β, hβs, -, -⟩ := hnat
  obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hp1 : p = 1 := Subtype.ext (by simpa using (h1 ▸ p.2 : (p : V) ∈ (⊥ : Subgroup V)))
  rw [hp1, map_one] at hp
  have := congrArg (fun m : Multiplicative (Fin 2 → Fq n) => Multiplicative.toAdd m 0) hp
  simp at this

end Module

section Lift

variable {X : Subgroup (MulAut V)} {n : ℕ}

theorem slLift_pCore_bot (hn : 2 ≤ n) (θ : X ≃* SLq n) : pCore 2 ↥X = ⊥ :=
  pCore_eq_bot_of_equiv θ (pCore_sl2_eq_bot hn)

theorem slLift_pCore_yuHol (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) (θ : X ≃* SLq n) :
    pCore 2 ↥(yuHol X) = (yuInc X).range := by
  rw [pCore_yuHol X hV, slLift_pCore_bot hn θ, MonoidHom.comap_bot, ker_yuProj]

theorem slLift_irreducible {θ : X ≃* SLq n} (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥)
    (N : Subgroup ↥(yuHol X)) [hNn : N.Normal] (hN : N ≤ (yuInc X).range) :
    N = ⊥ ∨ N = (yuInc X).range := by
  let A : Subgroup V := (N.comap (yuInc X)).map (commV X).subtype
  have hA : ∀ x ∈ X, ∀ v ∈ A, (x : MulAut V) v ∈ A := by
    rintro x hx v ⟨u, hu, rfl⟩
    refine ⟨⟨(x : MulAut V) (u : V), apply_mem_commV_self X hx u.2⟩, ?_, rfl⟩
    have h1 := conj_yuInc X (yuSec X ⟨x, hx⟩) u
    have h2 : yuSec X ⟨x, hx⟩ * yuInc X u * (yuSec X ⟨x, hx⟩)⁻¹ ∈ N :=
      hNn.conj_mem _ hu _
    rw [h1] at h2
    exact h2
  have hle : A ≤ commV X := by
    rintro v ⟨u, -, rfl⟩
    exact u.2
  by_cases hbot : A = ⊥
  · left
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨u, rfl⟩ := (MonoidHom.mem_range).mp (hN hn)
    have hu : (u : V) ∈ A := ⟨u, hn, rfl⟩
    rw [hbot] at hu
    have : u = 1 := Subtype.ext (by simpa using hu)
    rw [this, map_one]
    exact Subgroup.one_mem _
  · right
    have h := slLift_eq_commV_of_ne_bot hnat hle hA hbot
    refine le_antisymm hN (fun n hn => ?_)
    obtain ⟨u, rfl⟩ := hn
    have hu : (u : V) ∈ A := by rw [h]; exact u.2
    obtain ⟨u', hu', hu'e⟩ := hu
    have : u' = u := Subtype.ext hu'e
    rw [← this]
    exact hu'

theorem slLift_fixed {θ : X ≃* SLq n} (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) :
    (yuInc X).range ⊓ Subgroup.center ↥(yuHol X) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨u, rfl⟩, hx⟩
  have hfix : (u : V) ∈ commV X ⊓ fixV X := by
    refine ⟨u.2, mem_fixV.mpr fun g hg => ?_⟩
    have h1 := conj_yuInc X (yuSec X ⟨g, hg⟩) u
    have h2 : yuSec X ⟨g, hg⟩ * yuInc X u * (yuSec X ⟨g, hg⟩)⁻¹ = yuInc X u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.mp hx _
    rw [h2] at h1
    exact (congrArg (fun y : ↥(commV X) => (y : V)) (yuInc_injective X h1)).symm
  rw [slLift_commV_inf_fixV hnat] at hfix
  have : u = 1 := Subtype.ext (by simpa using hfix)
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem slLift_shortU (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) :
    shortU ↥(yuHol X) = (yuInc X).range := by
  have hP := slLift_pCore_yuHol hV hn θ
  have hle : shortU ↥(yuHol X) ≤ (yuInc X).range := by
    rw [shortU, ← hP]
    exact Subgroup.commutator_le_left _ _
  have hnorm : (shortU ↥(yuHol X)).Normal := by
    rw [shortU]
    infer_instance
  rcases slLift_irreducible hnat (shortU ↥(yuHol X)) hle with h | h
  · exfalso
    obtain ⟨g, hg, u, hu, hne⟩ := slLift_exists_moved hnat
    have hmem : ⁅yuInc X ⟨u, hu⟩, yuSec X ⟨g, hg⟩⁆ ∈ shortU ↥(yuHol X) := by
      rw [shortU]
      refine Subgroup.commutator_mem_commutator ?_ (Subgroup.mem_top _)
      rw [hP]
      exact ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, comm_yuInc_yuSec] at hmem
    have h1 := yuInc_injective X (hmem.trans (map_one (yuInc X)).symm)
    have h2 : u * (g : MulAut V) u⁻¹ = 1 := congrArg (fun y : ↥(commV X) => (y : V)) h1
    apply hne
    rw [map_inv] at h2
    exact (mul_inv_eq_one.mp (by simpa using h2)).symm
  · exact h

theorem slLift_perfect (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) : Group.IsPerfect ↥(yuHol X) := by
  have hXp : Group.IsPerfect ↥X := by
    have := isPerfect_sl2 hn
    exact Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
  refine ⟨?_⟩
  rw [eq_top_iff]
  intro x _
  rw [yu_eq_inc_mul_sec X x]
  refine Subgroup.mul_mem _ ?_ ?_
  · have h1 : yuInc X ⟨x.1.left, x.2.1⟩ ∈ shortU ↥(yuHol X) := by
      rw [slLift_shortU hV hn hnat]
      exact ⟨_, rfl⟩
    have h2 : shortU ↥(yuHol X) ≤ commutator ↥(yuHol X) := by
      rw [shortU, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  · have hg : (⟨x.1.right, x.2.2⟩ : ↥X) ∈ commutator ↥X := by
      rw [hXp.commutator_eq_top]
      exact Subgroup.mem_top _
    have h1 : yuSec X ⟨x.1.right, x.2.2⟩ ∈ (commutator ↥X).map (yuSec X) := ⟨_, hg, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1

theorem slLift_faithful (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) (g : ↥X)
    (hg : ∀ u ∈ commV X, (g : MulAut V) u = u) : g = 1 := by
  have : IsSimpleGroup (SLq n) := isSimpleGroup_sl2_gf hn
  let K : Subgroup ↥X :=
    { carrier := {g | ∀ u ∈ commV X, (g : MulAut V) u = u}
      one_mem' := fun u _ => rfl
      mul_mem' := fun {a b} ha hb u hu => by
        show (a : MulAut V) ((b : MulAut V) u) = u
        rw [hb u hu, ha u hu]
      inv_mem' := fun {a} ha u hu => by
        have h1 : (a : MulAut V) u = u := ha u hu
        show ((a : MulAut V)⁻¹) u = u
        exact (a : MulAut V).injective (by rw [MulAut.apply_inv_self, h1]) }
  have hKn : K.Normal :=
    { conj_mem := fun n hn h u hu => by
        show (h : MulAut V) ((n : MulAut V) ((h : MulAut V)⁻¹ u)) = u
        have h1 : ((h : MulAut V)⁻¹) u ∈ commV X := by
          have := apply_mem_commV_self X (X.inv_mem h.2) hu
          exact this
        rw [hn _ h1, MulAut.apply_inv_self] }
  have hKm : (K.map θ.toMonoidHom).Normal :=
    Subgroup.Normal.map hKn θ.toMonoidHom θ.surjective
  have := hKm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map θ.toMonoidHom) with h | h
  · have h2 := Subgroup.mem_map_of_mem θ.toMonoidHom (show g ∈ K from hg)
    rw [h] at h2
    exact θ.injective ((Subgroup.mem_bot.mp h2).trans (map_one θ).symm)
  · exfalso
    obtain ⟨g', hg', u, hu, hne⟩ := slLift_exists_moved hnat
    have h3 : θ ⟨g', hg'⟩ ∈ K.map θ.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hke⟩ := h3
    have h4 : k = ⟨g', hg'⟩ := θ.injective hke
    exact hne ((h4 ▸ hk) u hu)

theorem slLift_isCharP (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) : IsCharacteristicP 2 ↥(yuHol X) := by
  intro c hc
  rw [slLift_pCore_yuHol hV hn θ, ← ker_yuProj, mem_ker_yuProj]
  have hfix : ∀ u ∈ commV X, (c.1.right : MulAut V) u = u := by
    intro u hu
    have h1 := conj_yuInc X c ⟨u, hu⟩
    have h2 : c * yuInc X ⟨u, hu⟩ * c⁻¹ = yuInc X ⟨u, hu⟩ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hc (yuInc X ⟨u, hu⟩)
        (by rw [SetLike.mem_coe, slLift_pCore_yuHol hV hn θ]; exact ⟨_, rfl⟩)
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    rw [h2] at h1
    exact (congrArg (fun y : ↥(commV X) => (y : V)) (yuInc_injective X h1)).symm
  have := slLift_faithful hn hnat ⟨c.1.right, c.2.2⟩ hfix
  exact congrArg Subtype.val this

theorem slLift_residual [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) : oResidualTwo ↥(yuHol X) = ⊤ := by
  refine CGT.PushingUpLit.oResidualTwo_eq_top_iff.2 fun N hN hpow => ?_
  have hp : IsPGroup 2 (↥(yuHol X) ⧸ N) :=
    (CGT.PushingUpLit.isPGroup_two_quotient_iff N).2 hpow
  have := slLift_perfect hV hn hnat
  have : Group.IsPerfect (↥(yuHol X) ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hss : Subsingleton (↥(yuHol X) ⧸ N) := by
    by_contra hns
    have : Nontrivial (↥(yuHol X) ⧸ N) := not_subsingleton_iff_nontrivial.mp hns
    have := hp.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (↥(yuHol X) ⧸ N) inferInstance
  rw [eq_top_iff]
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim (QuotientGroup.mk x) 1)

theorem slLift_naturalSL (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) : IsNaturalSLTwoModule ↥(yuHol X) n := by
  have hpX := slLift_pCore_bot hn θ
  have hS := slLift_shortU hV hn hnat
  have hF := slLift_fixed hnat
  obtain ⟨-, β₀, hβs, hβk, hβe⟩ := hnat
  have hβi : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let eqv : ↥(yuInc X).range ≃* ↥(commV X) := (MonoidHom.ofInjective (yuInc_injective X)).symm
  have heqv : ∀ w : ↥(commV X), ∀ h : yuInc X w ∈ (yuInc X).range, eqv ⟨yuInc X w, h⟩ = w := by
    intro w h
    rw [MulEquiv.symm_apply_eq]
    rfl
  let incl : ↥(shortU ↥(yuHol X)) →* ↥(yuInc X).range := Subgroup.inclusion hS.le
  let ψ : ↥(shortU ↥(yuHol X)) →* Multiplicative (Fin 2 → Fq n) :=
    β₀.comp (eqv.toMonoidHom.comp incl)
  have hψ : ∀ (w : ↥(commV X)) (h : yuInc X w ∈ shortU ↥(yuHol X)),
      ψ ⟨yuInc X w, h⟩ = β₀ w := by
    intro w h
    show β₀ (eqv (incl ⟨yuInc X w, h⟩)) = _
    rw [show incl ⟨yuInc X w, h⟩ = ⟨yuInc X w, hS ▸ h⟩ from rfl, heqv]
  refine ⟨(yuTop' X hV hpX).trans θ, ψ, fun m => ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hβs m
    have hmem : yuInc X w ∈ shortU ↥(yuHol X) := by rw [hS]; exact ⟨_, rfl⟩
    exact ⟨⟨yuInc X w, hmem⟩, by rw [hψ, hw]⟩
  · have hC : shortC ↥(yuHol X) = ⊥ := by rw [shortC, hS, hF]
    have hψi : Function.Injective ψ :=
      hβi.comp (eqv.injective.comp (Subgroup.inclusion_injective _))
    rw [hC, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff ψ).mpr hψi
  · intro l u hu hu'
    obtain ⟨w, rfl⟩ : u ∈ (yuInc X).range := hS ▸ hu
    have hc := conj_yuInc X l w
    have hmem3 : yuInc X ⟨(l.1.right : MulAut V) w, apply_mem_commV_self X l.2.2 w.2⟩ ∈
        shortU ↥(yuHol X) := by
      rw [hS]
      exact ⟨_, rfl⟩
    have e : (⟨l * yuInc X w * l⁻¹, hu'⟩ : ↥(shortU ↥(yuHol X))) =
        ⟨yuInc X ⟨(l.1.right : MulAut V) w, apply_mem_commV_self X l.2.2 w.2⟩, hmem3⟩ :=
      Subtype.ext hc
    rw [e, hψ, hψ w hu, hβe ⟨l.1.right, l.2.2⟩ w _]
    rfl

theorem slLift_isShortGroup [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hn : 2 ≤ n) {θ : X ≃* SLq n}
    (hnat : IsNatSectionWith (slAct n) θ (commV X) ⊥) : IsShortGroup ↥(yuHol X) :=
  Glue.isShortGroup_of_natural (slLift_isCharP hV hn hnat) (slLift_residual hV hn hnat)
    (fun x hx y hy => by
      rw [slLift_pCore_yuHol hV hn θ] at hx hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact yuInc_comm X u w)
    (Or.inl ⟨n, hn, slLift_naturalSL hV hn hnat⟩)

end Lift

theorem inClassX_yuHol_of_natSL [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {X : Subgroup (MulAut V)} (hnat : IsNatSectionBy (slAct n) X (commV X) ⊥) :
    InClassX ↥(yuHol X) := by
  obtain ⟨hinv, θ, hrest⟩ := hnat
  have hW : IsNatSectionWith (slAct n) θ (commV X) ⊥ := ⟨hinv, hrest⟩
  exact ⟨slLift_isShortGroup hV hn hW, Or.inr ⟨n, by omega, slLift_naturalSL hV hn hW⟩⟩

theorem isNatSectionBy_barW {G K : Subgroup (MulAut V)} {W E : Subgroup V} (h : GInv G W)
    (hKG : K ≤ G) (hinj : K ⊓ fixW W = ⊥) (hEW : E ≤ W) {S M : Type*} [Group S] [Group M]
    {act : S → M → M} (hnat : IsNatSectionBy act K E ⊥) :
    IsNatSectionBy act (barW h K) (E.subgroupOf W) ⊥ := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  let e : ↥(E.subgroupOf W) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEW
  refine ⟨?_, (barWEquiv h hKG hinj).symm.trans θ, β.comp e.toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx p hp
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hx
    exact hinv _ hg _ hp
  · exact hβs.comp e.surjective
  · ext p
    have h1 : p ∈ (β.comp e.toMonoidHom).ker ↔ e p ∈ β.ker := Iff.rfl
    rw [h1, hβk]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hp
      exact Subtype.ext (by simpa using hp)
    · intro hp
      simpa using congrArg (fun w : ↥W => (w : V)) hp
  · intro x p hp
    set k : ↥K := (barWEquiv h hKG hinj).symm x with hk
    have hxk : (x : MulAut ↥W) = resG G W h ⟨k, hKG k.2⟩ := by
      rw [← coe_barWEquiv h hKG hinj k, hk, MulEquiv.apply_symm_apply]
    have hval : (((x : MulAut ↥W) p : ↥W) : V) = (k : MulAut V) ((p : ↥W) : V) := by
      rw [hxk]
      rfl
    have hp' : (k : MulAut V) ((p : ↥W) : V) ∈ E := by
      have h2 : (((x : MulAut ↥W) p : ↥W) : V) ∈ E := hp
      rwa [hval] at h2
    have key := hβe k ⟨((p : ↥W) : V), p.2⟩ hp'
    show β (e ⟨(x : MulAut ↥W) p, hp⟩) = act (θ k) (β (e p))
    have e1 : e ⟨(x : MulAut ↥W) p, hp⟩ = ⟨(k : MulAut V) ((p : ↥W) : V), hp'⟩ := Subtype.ext hval
    have e2 : e p = ⟨((p : ↥W) : V), p.2⟩ := rfl
    rw [e1, e2]
    exact key

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
