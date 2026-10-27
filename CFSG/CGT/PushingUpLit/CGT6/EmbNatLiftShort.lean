module

public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltModFix
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V] {X : Subgroup (MulAut V)} {a : ℕ}

theorem pCore_alt_eq_bot (ha : 2 ≤ a) : pCore 2 (alternatingGroup (Fin (2 * a + 1))) = ⊥ := by
  have h5 : 5 ≤ Nat.card (Fin (2 * a + 1)) := by simp; omega
  have : IsSimpleGroup (alternatingGroup (Fin (2 * a + 1))) := alternatingGroup.isSimpleGroup h5
  refine pCore_eq_bot_of_simple fun hp => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  have : Nontrivial (Fin (2 * a + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hn
  have h3 : 3 ∣ (2 * a + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h2 : 2 ∣ (2 * a + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : (2 * a + 1).factorial = 2 * ((2 * a + 1).factorial / 2) := (Nat.mul_div_cancel' h2).symm
  have h5' : 3 ∣ (2 * a + 1).factorial / 2 := by
    rw [h4] at h3
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  rw [hn] at h5'
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h5')
  omega

theorem natLift_pCore_bot (ha : 2 ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1))) :
    pCore 2 ↥X = ⊥ :=
  pCore_eq_bot_of_equiv θ (pCore_alt_eq_bot ha)

theorem natLift_pCore_yuHol (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1))) :
    pCore 2 ↥(yuHol X) = (yuInc X).range := by
  rw [pCore_yuHol X hV, natLift_pCore_bot ha θ, MonoidHom.comap_bot, ker_yuProj]

theorem natLift_irreducible (ha : 2 ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥)
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
  rcases commV_subgroup_eq_bot_or_top_of_natural ⟨a, rfl⟩ (by omega) θ hnat hA hle with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨u, rfl⟩ := (MonoidHom.mem_range).mp (hN hn)
    have hu : (u : V) ∈ A := ⟨u, hn, rfl⟩
    rw [h] at hu
    have : u = 1 := Subtype.ext (by simpa using hu)
    rw [this, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hN (fun n hn => ?_)
    obtain ⟨u, rfl⟩ := hn
    have hu : (u : V) ∈ A := by rw [h]; exact u.2
    obtain ⟨u', hu', hu'e⟩ := hu
    have : u' = u := Subtype.ext hu'e
    rw [← this]
    exact hu'

theorem natLift_exists_moved (ha : 2 ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    ∃ g ∈ X, ∃ u ∈ commV X, (g : MulAut V) u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hle : commV X ≤ fixV X := fun u hu => mem_fixV.mpr fun g hg => hcon g hg u hu
  have h1 := commV_inf_fixV_of_natural (⟨a, rfl⟩ : Odd (2 * a + 1)) (by omega) θ hnat
  rw [inf_eq_left.mpr hle] at h1
  have h2 := card_commV_of_natural (by omega) θ hnat
  rw [h1, Subgroup.card_bot] at h2
  have h3 : 2 ≤ 2 ^ (2 * a + 1 - 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem natLift_fixed (ha : 2 ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
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
  rw [commV_inf_fixV_of_natural (⟨a, rfl⟩ : Odd (2 * a + 1)) (by omega) θ hnat] at hfix
  have : u = 1 := Subtype.ext (by simpa using hfix)
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem natLift_shortU (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    shortU ↥(yuHol X) = (yuInc X).range := by
  have hP := natLift_pCore_yuHol hV ha θ
  have hle : shortU ↥(yuHol X) ≤ (yuInc X).range := by
    rw [shortU, ← hP]
    exact Subgroup.commutator_le_left _ _
  have hn : (shortU ↥(yuHol X)).Normal := by
    rw [shortU]
    infer_instance
  rcases natLift_irreducible ha θ hnat (shortU ↥(yuHol X)) hle with h | h
  · exfalso
    obtain ⟨g, hg, u, hu, hne⟩ := natLift_exists_moved ha θ hnat
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

theorem natLift_perfect (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    Group.IsPerfect ↥(yuHol X) := by
  have hXq : CFSG.IsQuasisimple ↥X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv θ.symm
      (Glue.isQuasisimple_alternating (k := 2 * a + 1) (by omega))
  have hXp : Group.IsPerfect ↥X := hXq.1
  refine ⟨?_⟩
  rw [eq_top_iff]
  intro x _
  rw [yu_eq_inc_mul_sec X x]
  refine Subgroup.mul_mem _ ?_ ?_
  · have h1 : yuInc X ⟨x.1.left, x.2.1⟩ ∈ shortU ↥(yuHol X) := by
      rw [natLift_shortU hV ha θ hnat]
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

theorem natLift_faithful (ha : 2 ≤ a) (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) (g : ↥X)
    (hg : ∀ u ∈ commV X, (g : MulAut V) u = u) : g = 1 := by
  have : IsSimpleGroup (alternatingGroup (Fin (2 * a + 1))) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
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
    obtain ⟨g', hg', u, hu, hne⟩ := natLift_exists_moved ha θ hnat
    have h3 : θ ⟨g', hg'⟩ ∈ K.map θ.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hke⟩ := h3
    have h4 : k = ⟨g', hg'⟩ := θ.injective hke
    exact hne ((h4 ▸ hk) u hu)

theorem natLift_isCharP (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    IsCharacteristicP 2 ↥(yuHol X) := by
  intro c hc
  rw [natLift_pCore_yuHol hV ha θ, ← ker_yuProj, mem_ker_yuProj]
  have hfix : ∀ u ∈ commV X, (c.1.right : MulAut V) u = u := by
    intro u hu
    have h1 := conj_yuInc X c ⟨u, hu⟩
    have h2 : c * yuInc X ⟨u, hu⟩ * c⁻¹ = yuInc X ⟨u, hu⟩ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hc (yuInc X ⟨u, hu⟩)
        (by rw [SetLike.mem_coe, natLift_pCore_yuHol hV ha θ]; exact ⟨_, rfl⟩)
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    rw [h2] at h1
    exact (congrArg (fun y : ↥(commV X) => (y : V)) (yuInc_injective X h1)).symm
  have := natLift_faithful ha θ hnat ⟨c.1.right, c.2.2⟩ hfix
  exact congrArg Subtype.val this

theorem natLift_residual [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    oResidualTwo ↥(yuHol X) = ⊤ := by
  refine CGT.PushingUpLit.oResidualTwo_eq_top_iff.2 fun N hN hpow => ?_
  have hp : IsPGroup 2 (↥(yuHol X) ⧸ N) :=
    (CGT.PushingUpLit.isPGroup_two_quotient_iff N).2 hpow
  have := natLift_perfect hV ha θ hnat
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

theorem natLift_naturalAltWith (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    IsNaturalAltModuleWith ↥(yuHol X) a ((yuTop' X hV (natLift_pCore_bot ha θ)).trans θ) := by
  have hpX := natLift_pCore_bot ha θ
  have hS := natLift_shortU hV ha θ hnat
  have hF := natLift_fixed ha θ hnat
  obtain ⟨-, β₀, hβs, hβk, hβe⟩ := hnat
  have hβi : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let eqv : ↥(yuInc X).range ≃* ↥(commV X) := (MonoidHom.ofInjective (yuInc_injective X)).symm
  have heqv : ∀ w : ↥(commV X), ∀ h : yuInc X w ∈ (yuInc X).range, eqv ⟨yuInc X w, h⟩ = w := by
    intro w h
    rw [MulEquiv.symm_apply_eq]
    rfl
  let incl : ↥(shortU ↥(yuHol X)) →* ↥(yuInc X).range := Subgroup.inclusion hS.le
  let ψ : ↥(shortU ↥(yuHol X)) →* Multiplicative (Fin (2 * a + 1) → ZMod 2) :=
    (G6.coreMod (2 * a + 1)).subtype.comp (β₀.comp (eqv.toMonoidHom.comp incl))
  have hψ : ∀ (w : ↥(commV X)) (h : yuInc X w ∈ shortU ↥(yuHol X)),
      ψ ⟨yuInc X w, h⟩ = ((β₀ w : ↥(G6.coreMod (2 * a + 1))) : G6.PermMod (2 * a + 1)) := by
    intro w h
    show ((β₀ (eqv (incl ⟨yuInc X w, h⟩)) : ↥(G6.coreMod (2 * a + 1))) : G6.PermMod (2 * a + 1)) = _
    rw [show incl ⟨yuInc X w, h⟩ = ⟨yuInc X w, hS ▸ h⟩ from rfl, heqv]
  refine ⟨ψ, fun u => ?_, fun v hv => ?_, ?_, ?_⟩
  · exact G6.mem_coreMod.mp (β₀ (eqv (incl u))).2
  · obtain ⟨w, hw⟩ := hβs ⟨Multiplicative.ofAdd v, G6.mem_coreMod.mpr hv⟩
    have hmem : yuInc X w ∈ shortU ↥(yuHol X) := by rw [hS]; exact ⟨_, rfl⟩
    refine ⟨⟨yuInc X w, hmem⟩, ?_⟩
    rw [hψ, hw]
  · have hC : shortC ↥(yuHol X) = ⊥ := by rw [shortC, hS, hF]
    have hψi : Function.Injective ψ :=
      Subtype.val_injective.comp (hβi.comp (eqv.injective.comp (Subgroup.inclusion_injective _)))
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
    apply Multiplicative.toAdd.injective
    funext i
    rfl

theorem natLift_naturalAlt (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    IsNaturalAltModule ↥(yuHol X) a :=
  ⟨_, natLift_naturalAltWith hV ha θ hnat⟩

theorem isShortGroup_yuHol_of_natSection [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) :
    IsShortGroup ↥(yuHol X) :=
  Glue.isShortGroup_of_natural (natLift_isCharP hV ha θ hnat) (natLift_residual hV ha θ hnat)
    (fun x hx y hy => by
      rw [natLift_pCore_yuHol hV ha θ] at hx hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact yuInc_comm X u w)
    (Or.inr ⟨a, by omega, natLift_naturalAlt hV ha θ hnat⟩)

theorem inClassX_yuHol_of_natSection [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ha : 2 ≤ a)
    (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥) : InClassX ↥(yuHol X) :=
  ⟨isShortGroup_yuHol_of_natSection hV ha θ hnat,
    Or.inl ⟨a, by omega, natLift_naturalAlt hV ha θ hnat⟩⟩

end CFSG.CGT.PushingUpLit.CGT6
