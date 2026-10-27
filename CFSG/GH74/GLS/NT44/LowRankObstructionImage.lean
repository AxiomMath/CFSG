module

public import CFSG.GH74.GLS.NT44.InvolutionCore
public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZFStar
import CFSG.RankThree.OddKernel.OddLift
public import CFSG.GH74.Uniqueness.Section4Struct

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

theorem original_low_rank_obstruction_faithful_image
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {T W : Subgroup G} {x u : G}
    (hnonab : ∃ b c : G, b * c ≠ c * b)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ z).ncard ≤
        (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x).ncard)
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W
      (CFSG.GH74.GLS.zStar (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x))) :
    let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
    let A : Subgroup G := Z ⊔ Subgroup.zpowers u
    ∀ (_hZ4 : Nat.card ↥Z = 4) (_hZW : Z ≤ W)
      (_hA : CFSG.IsElementaryAbelian 2 ↥A)
      (_hACW : A ≤ Subgroup.centralizer (W : Set G))
      (a : G) (haA : a ∈ A) (_ha2 : orderOf a = 2)
      (hAH : A ≤ Subgroup.centralizer ({a} : Set G))
      (L : Subgroup (CFSG.GH74.CentralizerBar a))
      (_hL : CFSG.IsComponent L)
      (_hcent :
        ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
            (CFSG.GH74.GLS.Th2.Bal.piBar a)) ⊓
          Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
        Subgroup.zpowers (CFSG.GH74.GLS.Th2.Bal.piBar a ⟨a, hAH haA⟩)),
      a ∉ W ∧
        ∃ hWH : W ≤ Subgroup.centralizer ({a} : Set G),
          let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
          let π := CFSG.GH74.GLS.Th2.Bal.piBar a
          let j : ↥W →* CFSG.GH74.CentralizerBar a :=
            π.comp (Subgroup.inclusion hWH)
          let V : Subgroup (CFSG.GH74.CentralizerBar a) :=
            (Z.subgroupOf H).map π
          Function.Injective j ∧
            j.range = (W.subgroupOf H).map π ∧
            Nat.card ↥V = 4 ∧
            CFSG.IsElementaryAbelian 2 ↥V ∧
            V ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ ∧
            (∀ v ∈ V, v ≠ 1 → ¬ ∀ l ∈ L, v * l = l * v) := by
  classical
  intro Z A hZ4 hZW hA hACW a haA ha2 hAH L hL hcent
  have hZA : Z ≤ Z ⊔ Subgroup.zpowers u := le_sup_left
  have haZ_sq : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    exact (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hA).2 z (hZA hz)
  have hA_sq : ∀ x ∈ A, x * x = 1 :=
    (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hA).2
  have ha_sq : a * a = 1 := hA_sq a haA
  have hWH : W ≤ Subgroup.centralizer ({a} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hACW haA) w hw
  have hZ_H : Z ≤ Subgroup.centralizer ({a} : Set G) := hZA.trans hAH
  let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let π : ↥H →* CFSG.GH74.CentralizerBar a := CFSG.GH74.GLS.Th2.Bal.piBar a
  let E : Subgroup (CFSG.GH74.CentralizerBar a) := (A.subgroupOf H).map π
  let V : Subgroup (CFSG.GH74.CentralizerBar a) := (Z.subgroupOf H).map π
  have hVleE : V ≤ E := by
    refine Subgroup.map_mono (f := π) ?_
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hZA (Subgroup.mem_subgroupOf.mp hz))
  have hVcard : Nat.card ↥V = 4 := by
    have hZ_H' : Z ≤ H := hZ_H
    calc
      Nat.card ↥V = Nat.card ↥((Z.subgroupOf H).map π) := rfl
      _ = Nat.card ↥Z := CFSG.GH74.GLS.Th2.Bal.card_map_piBar haZ_sq hZ_H'
      _ = 4 := hZ4
  have hV_el : CFSG.IsElementaryAbelian 2 ↥V := by
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ : CFSG.IsElementaryAbelian 2 ↥A := hA
    let _ : CFSG.IsElementaryAbelian 2 ↥Z :=
      CFSG.isElementaryAbelian_of_le hZA
    let _ : CFSG.IsElementaryAbelian 2 ↥(Z.subgroupOf H) :=
      CFSG.IsElementaryAbelian.subgroupOf hZ_H
    exact CFSG.IsElementaryAbelian.map π
  have hgen2 : (π ⟨a, hAH haA⟩) * (π ⟨a, hAH haA⟩) = 1 := by
    rw [← map_mul]
    have h2 : (⟨a, hAH haA⟩ : ↥H) * ⟨a, hAH haA⟩ = 1 := by
      apply Subtype.ext
      simpa using ha_sq
    rw [h2, map_one]
  have he_ne : π ⟨a, hAH haA⟩ ≠ 1 := by
    intro h
    have hmem : ⟨a, hAH haA⟩ ∈ CFSG.pPrimeCore 2 ↥H :=
      (CFSG.GH74.GLS.Th2.Bal.piBar_eq_one_iff).mp h
    have ha1 : (⟨a, hAH haA⟩ : ↥H) = 1 := by
      exact CFSG.GH74.GLS.Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore (X := ↥H)
        (h := ⟨a, hAH haA⟩) (by
          apply Subtype.ext
          simpa using ha_sq) hmem
    have ha_one : a = 1 := congrArg Subtype.val ha1
    have horder : orderOf a = 2 := ha2
    rw [ha_one, orderOf_one] at horder
    omega
  have he_order : orderOf (π ⟨a, hAH haA⟩) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two]
      exact hgen2
    · exact he_ne
  have hcent' :
      E ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
        Subgroup.zpowers (π ⟨a, hAH haA⟩) := by
    simpa [E, π, H] using hcent
  have ha_not_mem : a ∉ W := by
    intro haW
    have hWcore : W ≤ (CFSG.Op_p'p 2 ↥H).map H.subtype :=
      CFSG.GH74.GLS.NT44.le_core_centralizer_of_mem_rigid_center_sylow
        (G := G) (fullQ := fullQ) (x := x) (W := W) (a := a)
        hnonab hx2 hmax hW haW ha2
    have hZcore : Z ≤ (CFSG.Op_p'p 2 ↥H).map H.subtype := hZW.trans hWcore
    have hVp : V ≤ CFSG.pCore 2 (CFSG.GH74.CentralizerBar a) := by
      rintro v ⟨z, hz, rfl⟩
      have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have hzmap : (z : G) ∈ (CFSG.Op_p'p 2 ↥H).map H.subtype := hZcore hzZ
      obtain ⟨o, hoOp, hoval⟩ := hzmap
      have hoeq : o = z := Subtype.ext hoval
      rw [← hoeq]
      change CFSG.GH74.GLS.TwoThin.barMk ↥H o ∈
        CFSG.pCore 2 (CFSG.GH74.GLS.TwoThin.barQ ↥H)
      simpa [CFSG.Op_p'p, CFSG.GH74.GLS.TwoThin.barMk,
        CFSG.GH74.GLS.TwoThin.barQ] using hoOp
    have hLcent : CFSG.pCore 2 (CFSG.GH74.CentralizerBar a) ≤
        Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) :=
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.pCore_le_centralizer_of_isComponent
        (p := 2) hL
    have hVcent : V ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) :=
      hVp.trans hLcent
    have hVle : V ≤ Subgroup.zpowers (π ⟨a, hAH haA⟩) := by
      rw [← hcent']
      exact le_inf hVleE hVcent
    have hcard_le : Nat.card ↥V ≤ Nat.card ↥(Subgroup.zpowers (π ⟨a, hAH haA⟩)) :=
      Subgroup.card_le_of_le hVle
    have hzp : Nat.card ↥(Subgroup.zpowers (π ⟨a, hAH haA⟩)) =
        orderOf (π ⟨a, hAH haA⟩) := Nat.card_zpowers _
    rw [hzp, he_order, hVcard] at hcard_le
    omega
  have hV_bot : V ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    intro v hv
    rw [Subgroup.mem_inf] at hv
    have hvE : v ∈ E := hVleE hv.1
    have hvC : v ∈ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := hv.2
    have hvzp : v ∈ Subgroup.zpowers (π ⟨a, hAH haA⟩) := by
      rw [← hcent']
      exact ⟨hvE, hvC⟩
    obtain ⟨z, hz, rfl⟩ := hv.1
    have hzA : (z : ↥H) ∈ A.subgroupOf H := by
      exact Subgroup.mem_subgroupOf.mpr (hZA (Subgroup.mem_subgroupOf.mp hz))
    have haH_A : (⟨a, hAH haA⟩ : ↥H) ∈ A.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr haA
    have hA_inj : Set.InjOn (π) ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      CFSG.GH74.GLS.Th2.Bal.piBar_injOn (a := a) (D := A) hA_sq
    rcases CFSG.GH74.Uniqueness.mem_zpowers_involution_cases
        hgen2 hvzp with hπz_one | hπz_eq
    · exact hπz_one
    · have hz_eq : (z : ↥H) = ⟨a, hAH haA⟩ :=
        hA_inj hzA haH_A hπz_eq
      have haZ : a ∈ Z := by
        have hza : (z : G) = a := congrArg Subtype.val hz_eq
        rw [← hza]
        exact Subgroup.mem_subgroupOf.mp hz
      exact absurd (hZW haZ) ha_not_mem
  let j : ↥W →* CFSG.GH74.CentralizerBar a := π.comp (Subgroup.inclusion hWH)
  have hker_odd : Odd (Nat.card ↥(MonoidHom.ker π)) := by
    simpa [π, H, CFSG.GH74.GLS.Th2.Bal.piBar] using
      (CFSG.GH74.GLS.TwoThin.odd_card_ker_barMk (Y := ↥H))
  have hW_p : IsPGroup 2 ↥W := CFSG.ABGLocalTools.IsSylowOf.isPGroup hW
  have hW_sub_p : IsPGroup 2 ↥(W.subgroupOf H) :=
    hW_p.of_equiv (Subgroup.subgroupOfEquivOfLe hWH).symm
  have hinj_sub : Function.Injective (π.comp (Subgroup.subtype (W.subgroupOf H))) :=
    CFSG.RankThree.OddKernel.injective_restrict_of_odd (G := ↥H)
      (H := CFSG.GH74.CentralizerBar a) π hker_odd (A := W.subgroupOf H) hW_sub_p
  have h_eq :
      j = (π.comp (Subgroup.subtype (W.subgroupOf H))).comp
        (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom := by
    ext x
    rfl
  have hinj_j : Function.Injective j := by
    rw [h_eq]
    exact hinj_sub.comp (Subgroup.subgroupOfEquivOfLe hWH).symm.injective
  have hrange : j.range = (W.subgroupOf H).map π := by
    rw [MonoidHom.range_comp]
    have h_incl : (Subgroup.inclusion hWH).range = W.subgroupOf H := by
      ext w
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr x.2
      · intro hw
        exact ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext rfl⟩
    rw [h_incl]
  refine ⟨ha_not_mem, ⟨hWH, ?_⟩⟩
  refine ⟨hinj_j, hrange, hVcard, hV_el, hV_bot, ?_⟩
  intro v hv hv1 hcent_all
  have hmemC : v ∈ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcent_all l hl).symm
  have : v ∈ V ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := ⟨hv, hmemC⟩
  rw [hV_bot, Subgroup.mem_bot] at this
  exact hv1 this

end CFSG.GH74.GLS.NT44

end
