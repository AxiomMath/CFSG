module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Prop
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoThree
public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6 CFSG.SL2MinimalFaithful
open scoped commutatorElement

section Bridge

variable {V : Type} [CommGroup V] [Finite V]

theorem isSLNatSection_of_inClassX {Y : Subgroup (MulAut V)} [Group.IsPerfect ↥Y]
    (hV : ∀ v : V, v ^ 2 = 1) (hX : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (hnat : IsNaturalSLTwoModule ↥(yuHol Y) n) (hZ : Subgroup.center ↥Y = ⊥) :
    IsSLNatSection Y (commV Y) (commV Y ⊓ fixV Y) n := by
  rw [isSLNatSection_iff]
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hθk : (yuTheta Y φ).ker = ⊥ :=
    le_bot_iff.mp (hZ ▸ yuTheta_ker_le_center Y φ hV hX)
  have hθinj : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hθk
  have hU : shortU ↥(yuHol Y) = (yuInc Y).range := shortU_eq_range Y φ hV hX
  let ι : ↥(commV Y) →* ↥(shortU ↥(yuHol Y)) :=
    (yuInc Y).codRestrict (shortU ↥(yuHol Y)) fun u => yuInc_mem_shortU Y hV u
  refine ⟨fun x hx p hp => apply_mem_commV_self Y hx hp,
    MulEquiv.ofBijective (yuTheta Y φ) ⟨hθinj, hθs⟩, ψ.comp ι, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨s, hs⟩ := hψs m
    obtain ⟨u, hu⟩ : (s : ↥(yuHol Y)) ∈ (yuInc Y).range := hU ▸ s.2
    exact ⟨u, by rw [MonoidHom.comp_apply, show ι u = s from Subtype.ext hu, hs]⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ (ι u) = 1 ↔ (u : V) ∈ commV Y ⊓ fixV Y
    rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨u.2, fun g hg => apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h.2⟩
    · rintro ⟨-, hfix⟩
      refine ⟨yuInc_mem_shortU Y hV u, ?_⟩
      show yuInc Y u ∈ Subgroup.center ↥(yuHol Y)
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := conj_yuInc Y x u
      have h2 : (⟨(x.1.right : MulAut V) (u : V), apply_mem_commV_self Y x.2.2 u.2⟩ :
          ↥(commV Y)) = u := Subtype.ext (hfix _ x.2.2)
      rw [h2] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
  · intro g p hp
    have hu : yuInc Y p ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV p
    have hc := conj_yuInc Y (yuSec Y g) p
    have hu' : yuSec Y g * yuInc Y p * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y) := by
      rw [hc]; exact yuInc_mem_shortU Y hV _
    have key := hψe (yuSec Y g) (yuInc Y p) hu hu'
    have hL : (⟨yuSec Y g * yuInc Y p * (yuSec Y g)⁻¹, hu'⟩ : ↥(shortU ↥(yuHol Y))) =
        ι ⟨(g : MulAut V) p, hp⟩ := Subtype.ext hc
    show ψ (ι ⟨(g : MulAut V) p, hp⟩) = _
    rw [← hL, key]
    rfl

end Bridge

section Two

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem two_le_of_isNaturalSLTwoModule {Y : Subgroup (MulAut V)} [Group.IsPerfect ↥Y]
    (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn1 : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥(yuHol Y) n) :
    2 ≤ n := by
  by_contra h
  have hn : n = 1 := by omega
  subst hn
  obtain ⟨φ, -⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 1 (by norm_num)]
    norm_num
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact false_of_perfect_small (Γ := ↥Y) (by omega) (yuTheta Y φ) hθs

end Two

section SL

variable {V : Type} [CommGroup V] [Finite V]

theorem sl_oddInvariant_le_centralizer (hM4 : SchurMultL2Two) (hV : ∀ v : V, v ^ 2 = 1)
    {Y : Subgroup (MulAut V)} (hperf : ⁅Y, Y⁆ = Y) (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (hn : 3 ≤ n) (hnat : IsNaturalSLTwoModule ↥(yuHol Y) n)
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ Nat.card X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hZ : Subgroup.center ↥Y = ⊥ := by
    rcases center_cases_of_sl Y hM4 hV hshort (by omega) hnat with h | ⟨h2, -⟩
    · exact h
    · omega
  have hSL := isSLNatSection_of_inClassX hV hshort hnat hZ
  have hSL' := isSLNatSection_iff.mp hSL
  obtain ⟨-, θ, -⟩ := id hSL'
  let ιh : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* MulAut V :=
    Y.subtype.comp θ.symm.toMonoidHom
  have hι_inj : Function.Injective ιh := fun A B h =>
    θ.symm.injective (Subtype.ext h)
  obtain ⟨T, hT⟩ : ∃ T : Subgroup (MulAut V),
      T = (unipotentHom (F := GaloisField 2 n)).range.map ιh := ⟨_, rfl⟩
  have hTY : T ≤ Y := by
    intro e he
    rw [hT] at he
    obtain ⟨A, -, rfl⟩ := he
    exact (θ.symm A).2
  have hTcard : Nat.card T = 2 ^ n := by
    rw [hT, Subgroup.card_map_of_injective hι_inj, ← GaloisField.card 2 n (by omega)]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (unipotentHom_injective (F := GaloisField 2 n))).toEquiv).symm
  have h2 := emb_two_three_sylow hV Y (by omega) hSL' hTY hTcard
  obtain ⟨hTab, hTfix, -, -⟩ := h2
  have : Nontrivial ↥T := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hTcard]
    exact Nat.one_lt_two_pow (by omega))
  have hTc : X ≤ Subgroup.centralizer (T : Set (MulAut V)) :=
    le_centralizer_of_commonImage_hyperplane (W := commV T) hV hTab
      (fun e he v => Subgroup.subset_closure ⟨e, he, v, rfl⟩)
      (fun e he w hw => hTfix hw e he)
      (fun B hB w hw => emb_two_three_hyperplane hV Y hn hSL' hTY hTcard B hB hw)
      hX (hTY.trans hYX)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimple : IsSimpleGroup ↥Y := by
    have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := GaloisField 2 n) h4
    exact θ.isSimpleGroup
  have h10 : ιh (unipotent (1 : GaloisField 2 n)) ≠ 1 := fun h => by
    have := hι_inj (h.trans (map_one ιh).symm)
    exact one_ne_zero (unipotent_injective (this.trans unipotent_zero.symm))
  have hmemT : ιh (unipotent (1 : GaloisField 2 n)) ∈ T := by
    rw [hT]
    exact ⟨unipotent 1, ⟨Multiplicative.ofAdd 1, rfl⟩, rfl⟩
  exact le_centralizer_of_centKer_eq_top (centKer_eq_top_of_simple hYX (hTY hmemT) h10
    (hTc.trans (Subgroup.centralizer_le (by simpa using hmemT))))

end SL

end CFSG.CGT.PushingUpLit.CGT6
