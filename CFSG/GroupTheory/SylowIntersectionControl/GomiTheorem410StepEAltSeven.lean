module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepERegular
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEHyp21
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEAltSevenBlock
import CFSG.GroupTheory.SylowIntersectionControl.GomiAltSevenModule
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

omit [Finite Ω] in
private theorem autOn_zpowers_eq_zpowers_gomiBar_ea7 (G : Subgroup Ω) {d : Ω} (hd : d ∈ G) :
    autOn (Subgroup.zpowers d) (gomiV G) =
      Subgroup.zpowers ((gomiBar G ⟨d, hd⟩ : ↥(autOn G (gomiV G))) : MulAut ↥(gomiV G)) := by
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    (Subgroup.zpowers_le.mpr hd).trans (gomiV_moduleSetting G).2
  rw [autOn]
  have hsub : (Subgroup.zpowers d).subgroupOf (Subgroup.normalizer (gomiV G : Set Ω)) =
      Subgroup.zpowers (⟨d, hN (Subgroup.mem_zpowers d)⟩ :
        Subgroup.normalizer (gomiV G : Set Ω)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  rw [hsub, MonoidHom.map_zpowers]
  congr 1

omit [Finite Ω] in
private theorem card_commV_zpowers_gomiBar_ea7 (G : Subgroup Ω) {d : Ω} (hd : d ∈ G) :
    Nat.card (commV (Subgroup.zpowers
      ((gomiBar G ⟨d, hd⟩ : ↥(autOn G (gomiV G))) : MulAut ↥(gomiV G)))) =
      Nat.card ↥⁅gomiV G, Subgroup.zpowers d⁆ := by
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    (Subgroup.zpowers_le.mpr hd).trans (gomiV_moduleSetting G).2
  rw [← autOn_zpowers_eq_zpowers_gomiBar_ea7 G hd,
    ← CFSG.Quasithin.AutOn.map_commV_autOn_eq (V := gomiV G) (X := Subgroup.zpowers d) hN]
  exact (Subgroup.card_map_of_injective (K := commV (autOn (Subgroup.zpowers d) (gomiV G)))
    (f := (gomiV G).subtype) (gomiV G).subtype_injective).symm

private theorem commute_conj_range_ea7 {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    ∀ K ∈ Set.range (fun g : ↥(autOn G (gomiV G)) =>
        (gomiBarOf G B).map (MulAut.conj g).toMonoidHom),
      ∀ K' ∈ Set.range (fun g : ↥(autOn G (gomiV G)) =>
        (gomiBarOf G B).map (MulAut.conj g).toMonoidHom),
      K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  have hc21 := (gomiHyp21_gomiBarOf hB hBt hGB hCQ).commute
  rintro K ⟨g, rfl⟩ K' ⟨g', rfl⟩ hne k hk k' hk'
  have hug : ((gomiBarOf G B).map (MulAut.conj (g⁻¹ * g')).toMonoidHom).map
      (MulAut.conj g).toMonoidHom =
      (gomiBarOf G B).map (MulAut.conj g').toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hu : (gomiBarOf G B).map (MulAut.conj (g⁻¹ * g')).toMonoidHom ≠ gomiBarOf G B := by
    intro h0
    apply hne
    show (gomiBarOf G B).map (MulAut.conj g).toMonoidHom =
      (gomiBarOf G B).map (MulAut.conj g').toMonoidHom
    rw [← hug, h0]
  have hc := hc21 (g⁻¹ * g') hu
  have hc' : ⁅(gomiBarOf G B).map (MulAut.conj g).toMonoidHom,
      (gomiBarOf G B).map (MulAut.conj g').toMonoidHom⁆ = ⊥ := by
    have hmap := Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom)
      (H₁ := gomiBarOf G B)
      (H₂ := (gomiBarOf G B).map (MulAut.conj (g⁻¹ * g')).toMonoidHom)
    rw [hc, Subgroup.map_bot] at hmap
    rw [hug] at hmap
    exact hmap.symm
  have hcomm := (Subgroup.commutator_le.mp (le_of_eq hc')) k hk k' hk'
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  exact hcomm

omit [Finite Ω] in
private theorem card_commV_conj_range_ea7 {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hB7 : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)
    (g : ↥(autOn G (gomiV G))) :
    Nat.card (commV (((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
      (autOn G (gomiV G)).subtype)) = 16 := by
  have hBbar : (gomiBarOf G B).map (autOn G (gomiV G)).subtype = autOn B (gomiV G) := by
    rw [gomiBarOf]
    exact Subgroup.map_subgroupOf_eq_of_le
      (CFSG.Quasithin.AutOn.autOn_mono hB.le)
  have hconj : ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
      (autOn G (gomiV G)).subtype =
      ((gomiBarOf G B).map (autOn G (gomiV G)).subtype).map
        (MulAut.conj (g : MulAut ↥(gomiV G))).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hconj, CFSG.Quasithin.commV_map_conj_eq,
    Subgroup.card_map_of_injective
      (K := commV ((gomiBarOf G B).map (autOn G (gomiV G)).subtype))
      (f := (g : MulAut ↥(gomiV G)).toMonoidHom) (g : MulAut ↥(gomiV G)).injective, hBbar]
  have hmap := CFSG.Quasithin.AutOn.map_commV_autOn_eq (V := gomiV G) (X := B)
    (hB.le.trans (gomiV_moduleSetting G).2)
  have hcard := Subgroup.card_map_of_injective (K := commV (autOn B (gomiV G)))
    (f := (gomiV G).subtype) (gomiV G).subtype_injective
  rw [hmap, hB7.2] at hcard
  exact hcard.symm

omit [Finite Ω] in
private theorem isGomiThreeCycle_conj_range_ea7 {B : Subgroup Ω}
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) :
    ∀ K ∈ Set.range (fun g : ↥(autOn G (gomiV G)) =>
        ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
          (autOn G (gomiV G)).subtype),
      IsGomiThreeCycle 7 K
        ((x (K.subgroupOf (autOn G (gomiV G))) : ↥(autOn G (gomiV G))) :
          MulAut ↥(gomiV G)) := by
  rintro K ⟨g, rfl⟩
  have hsub : (((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
      (autOn G (gomiV G)).subtype).subgroupOf (autOn G (gomiV G)) =
      (gomiBarOf G B).map (MulAut.conj g).toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (autOn G (gomiV G)).subtype_injective _
  rw [hsub]
  exact IsGomiThreeCycle.map_subtype (hx g)

private theorem commute_conj_range_map_ea7 {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    ∀ K ∈ Set.range (fun g : ↥(autOn G (gomiV G)) =>
        ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
          (autOn G (gomiV G)).subtype),
      ∀ K' ∈ Set.range (fun g : ↥(autOn G (gomiV G)) =>
        ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
          (autOn G (gomiV G)).subtype),
      K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  have hcomm := commute_conj_range_ea7 hB hBt hGB hCQ
  rintro K ⟨g, rfl⟩ K' ⟨g', rfl⟩ hne k hk k' hk'
  rw [Subgroup.mem_map] at hk hk'
  obtain ⟨b, hb, rfl⟩ := hk
  obtain ⟨b', hb', rfl⟩ := hk'
  have hne' : (gomiBarOf G B).map (MulAut.conj g).toMonoidHom ≠
      (gomiBarOf G B).map (MulAut.conj g').toMonoidHom := by
    intro h0
    apply hne
    show ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
        (autOn G (gomiV G)).subtype =
      ((gomiBarOf G B).map (MulAut.conj g').toMonoidHom).map
        (autOn G (gomiV G)).subtype
    rw [h0]
  exact congrArg Subtype.val (hcomm ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
    ⟨g, rfl⟩ ((gomiBarOf G B).map (MulAut.conj g').toMonoidHom) ⟨g', rfl⟩ hne' b hb b' hb')

omit [Finite Ω] in
private theorem image_x'_eq_range_ea7 {B : Subgroup Ω}
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G))) :
    (fun K : Subgroup (MulAut ↥(gomiV G)) =>
        (x (K.subgroupOf (autOn G (gomiV G))) : MulAut ↥(gomiV G))) ''
      Set.range (fun g : ↥(autOn G (gomiV G)) =>
        ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
          (autOn G (gomiV G)).subtype) =
    Set.range (fun g : ↥(autOn G (gomiV G)) =>
      (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom) : MulAut ↥(gomiV G))) := by
  rw [← Set.range_comp']
  congr 1
  funext g
  have hsubK : (((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map
      (autOn G (gomiV G)).subtype).subgroupOf (autOn G (gomiV G)) =
      (gomiBarOf G B).map (MulAut.conj g).toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (autOn G (gomiV G)).subtype_injective _
  rw [hsubK]

omit [Finite Ω] in
private theorem map_closure_range_eq_closure_ea7 {B : Subgroup Ω}
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G))) :
    (Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
      x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))).map
      (autOn G (gomiV G)).subtype =
    Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
      (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom) : MulAut ↥(gomiV G))) := by
  rw [MonoidHom.map_closure]
  congr 1
  rw [← Set.range_comp']
  rfl

private theorem le_card_commV_zpowers_of_le_closure_ea7 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (hB7 : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {S : Subgroup ↥(autOn G (gomiV G))}
    (hS : S ≤ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {d : MulAut ↥(gomiV G)} (hd : d ∈ S.map (autOn G (gomiV G)).subtype) (hd1 : d ≠ 1) :
    16 ≤ Nat.card (commV (Subgroup.zpowers d)) := by
  let Kc : ↥(autOn G (gomiV G)) → Subgroup (MulAut ↥(gomiV G)) := fun g =>
    ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom).map (autOn G (gomiV G)).subtype
  let 𝓚 : Set (Subgroup (MulAut ↥(gomiV G))) := Set.range Kc
  let x' : Subgroup (MulAut ↥(gomiV G)) → MulAut ↥(gomiV G) :=
    fun K => (x (K.subgroupOf (autOn G (gomiV G))) : MulAut ↥(gomiV G))
  have hx' : ∀ K ∈ 𝓚, IsGomiThreeCycle 7 K (x' K) :=
    isGomiThreeCycle_conj_range_ea7 x hx
  have hcard : ∀ K ∈ 𝓚, Nat.card (commV K) = 16 := by
    rintro K ⟨g, rfl⟩
    exact card_commV_conj_range_ea7 hB hB7 g
  have hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k :=
    commute_conj_range_map_ea7 hB hBt hGB hCQ
  have hW : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hx'range : x' '' 𝓚 = Set.range (fun g : ↥(autOn G (gomiV G)) =>
      (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom) : MulAut ↥(gomiV G))) :=
    image_x'_eq_range_ea7 x
  have hXeq : (Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
      x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))).map
      (autOn G (gomiV G)).subtype = Subgroup.closure (x' '' 𝓚) := by
    rw [map_closure_range_eq_closure_ea7 x, ← hx'range]
  have hmem : d ∈ Subgroup.closure (x' '' 𝓚) := by
    rw [← hXeq]
    exact (Subgroup.map_mono hS) hd
  exact le_card_commV_zpowers_of_mem_closure hW x' hx' hcard hcomm hmem hd1

private theorem pow_two_pow_ne_one_of_odd_order_ea7 {H : Type*} [Group H] {z : H}
    (hodd : Odd (orderOf z)) (hz1 : z ≠ 1) (k : ℕ) : z ^ 2 ^ k ≠ 1 := by
  intro h
  have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hjne
    exact hodd.not_two_dvd_nat (dvd_pow_self 2 hjne)
  rw [hj0, pow_zero] at hj
  exact hz1 (orderOf_eq_one_iff.mp hj)

private theorem exists_odd_pow_ne_one_ea7 {D : Subgroup Ω} (hDG : D ≤ G) {y : Ω} (hyD : y ∈ D)
    (hφy : gomiBar G ⟨y, hDG hyD⟩ ≠ 1)
    (hodd : Odd (orderOf (gomiBar G ⟨y, hDG hyD⟩))) :
    ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) ∧
      gomiBar G ⟨y ^ 2 ^ k, hDG (D.pow_mem hyD _)⟩ ≠ 1 := by
  obtain ⟨k, m, hm_odd, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_, ?_⟩
  · have h1 : orderOf (y ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero)
        (by rw [hm]; exact dvd_mul_right _ _), hm]
      exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)
    rw [h1]
    exact hm_odd
  · have h1 : (⟨y, hDG hyD⟩ : ↥G) ^ 2 ^ k =
        ⟨y ^ 2 ^ k, hDG (D.pow_mem hyD _)⟩ := Subtype.ext rfl
    rw [← h1, map_pow]
    exact pow_two_pow_ne_one_of_odd_order_ea7 hodd hφy k

private theorem oResidualTwo_eq_bot_of_isPGroup_ea7 {X : Type*} [Group X] (hX : IsPGroup 2 X) :
    oResidualTwo X = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [oResidualTwo]
  exact sInf_le ⟨inferInstance, hX.of_equiv QuotientGroup.quotientBot.symm⟩

private theorem gomiBarOf_map_ne_bot_ea7 {H : Subgroup Ω} (hHG : H ≤ G)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {D₀ : Subgroup ↥H} (hD₀ : IsAschbacherBlockGomi D₀) :
    gomiBarOf G (D₀.map H.subtype) ≠ ⊥ := by
  intro hbot
  have hDG : D₀.map H.subtype ≤ G := (Subgroup.map_subtype_le D₀).trans hHG
  have hautOn : autOn (D₀.map H.subtype) (gomiV G) = ⊥ := by
    have h1 : ((autOn (D₀.map H.subtype) (gomiV G)).subgroupOf
        (autOn G (gomiV G))).map (autOn G (gomiV G)).subtype =
        autOn (D₀.map H.subtype) (gomiV G) :=
      Subgroup.map_subgroupOf_eq_of_le (CFSG.Quasithin.AutOn.autOn_mono hDG)
    rw [← h1]
    change (gomiBarOf G (D₀.map H.subtype)).map (autOn G (gomiV G)).subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  have hDC : D₀.map H.subtype ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro d hd
    have hN : d ∈ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2 (hDG hd)
    have hmem : conjAct (gomiV G) ⟨d, hN⟩ ∈ autOn (D₀.map H.subtype) (gomiV G) :=
      CFSG.Quasithin.AutOn.conjAct_mem_autOn_of_mem hN hd
    rw [hautOn, Subgroup.mem_bot] at hmem
    exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff ⟨d, hN⟩).1 hmem
  have hDle : D₀.map H.subtype ≤ pCoreOf 2 G := by
    rw [← hCQ]
    exact le_inf hDG hDC
  have hD2 : IsPGroup 2 (D₀.map H.subtype) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_le hDle
  have hD02 : IsPGroup 2 ↥D₀ :=
    hD2.of_equiv (Subgroup.equivMapOfInjective D₀ H.subtype H.subtype_injective).symm
  have hbot' : (⊤ : Subgroup ↥D₀) = ⊥ := by
    rw [← hD₀.residual]
    exact oResidualTwo_eq_bot_of_isPGroup_ea7 hD02
  obtain ⟨X, Y₀, -, -, hYX, -, -, -, -, -, -⟩ := hD₀.chief
  have hXne : X ≠ ⊥ := by
    intro hX
    have hYbot : Y₀ = ⊥ := le_bot_iff.mp (hX ▸ hYX.le)
    exact hYX.ne (by rw [hYbot, hX])
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hxbot : X.subtype x ∈ (⊥ : Subgroup ↥D₀) := by
    rw [← hbot']
    exact Subgroup.mem_top _
  exact hx1 (X.subtype_injective (by rw [Subgroup.mem_bot.mp hxbot, map_one]))

omit [Finite Ω] in
private theorem orderOf_eq_three_of_isGomiThreeCycle_ea7 {K : Subgroup ↥(autOn G (gomiV G))}
    {z : ↥(autOn G (gomiV G))} (h : IsGomiThreeCycle 7 K z) : orderOf z = 3 := by
  obtain ⟨hz, φ, h3⟩ := h
  have h1 : orderOf (φ ⟨z, hz⟩ : alternatingGroup (Fin 7)) = 3 :=
    (Subgroup.orderOf_coe (φ ⟨z, hz⟩)).symm.trans (Equiv.Perm.IsThreeCycle.orderOf h3)
  calc orderOf z = orderOf (⟨z, hz⟩ : ↥K) := (Subgroup.orderOf_mk z hz).symm
    _ = orderOf (φ ⟨z, hz⟩) := (φ.orderOf_eq ⟨z, hz⟩).symm
    _ = 3 := h1

private theorem commute_mem_closure_range_ea7 {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) :
    ∀ a ∈ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)),
      ∀ b ∈ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)), a * b = b * a := by
  have hcomm := commute_conj_range_ea7 hB hBt hGB hCQ
  have hp : (Set.range fun g : ↥(autOn G (gomiV G)) =>
      x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)).Pairwise Commute := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ hne
    have hne' : (gomiBarOf G B).map (MulAut.conj g).toMonoidHom ≠
        (gomiBarOf G B).map (MulAut.conj g').toMonoidHom := by
      intro h0
      apply hne
      show x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom) =
        x ((gomiBarOf G B).map (MulAut.conj g').toMonoidHom)
      rw [h0]
    exact hcomm _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ hne'
      (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)) (hx g).choose
      (x ((gomiBarOf G B).map (MulAut.conj g').toMonoidHom)) (hx g').choose
  intro a ha b hb
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp (Subgroup.isMulCommutative_closure hp) ⟨a, ha⟩ ⟨b, hb⟩)

private theorem pow_three_eq_one_of_mem_closure_range_ea7 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {a : ↥(autOn G (gomiV G))}
    (ha : a ∈ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) : a ^ 3 = 1 := by
  have hcomm := commute_mem_closure_range_ea7 hB hBt hGB hCQ x hx
  induction ha using Subgroup.closure_induction with
  | mem s hs =>
      obtain ⟨g, rfl⟩ := hs
      rw [← orderOf_eq_three_of_isGomiThreeCycle_ea7 (hx g)]
      exact pow_orderOf_eq_one _
  | one => simp
  | mul a b ha hb iha ihb =>
      have hc : Commute a b := hcomm a ha b hb
      rw [hc.mul_pow 3, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

private theorem odd_orderOf_of_mem_closure_range_ea7 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {a : ↥(autOn G (gomiV G))}
    (ha : a ∈ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) : Odd (orderOf a) := by
  have h3 := pow_three_eq_one_of_mem_closure_range_ea7 hB hBt hGB hCQ x hx ha
  have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · rw [h]
    exact odd_one
  · rw [h]
    exact ⟨1, rfl⟩

omit [Finite Ω] in
private theorem exists_gomiBar_ne_one_of_gomiBarOf_ne_bot_ea7 {D : Subgroup Ω} (hDG : D ≤ G)
    (h : gomiBarOf G D ≠ ⊥) :
    ∃ y : Ω, ∃ hy : y ∈ D, gomiBar G ⟨y, hDG hy⟩ ≠ 1 := by
  have haut : autOn D (gomiV G) ≠ ⊥ := by
    intro h0
    exact h (by rw [gomiBarOf, h0, Subgroup.bot_subgroupOf])
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp haut
  obtain ⟨n, hnD, hna⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp a.2
  have hgb : conjAct (gomiV G) n = ↑(gomiBar G ⟨(n : Ω), hDG hnD⟩) :=
    congrArg (conjAct (gomiV G)) (Subtype.ext rfl)
  refine ⟨(n : Ω), hnD, fun hg => ha1 (Subtype.ext ?_)⟩
  rw [← hna, hgb]
  simpa using congrArg Subtype.val hg

private theorem commutator_le_pCoreOf_of_le_closure_ea7 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {D : Subgroup Ω} (hDG : D ≤ G)
    (hDbar_le : gomiBarOf G D ≤ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) :
    ⁅D, D⁆ ≤ pCoreOf 2 G := by
  have hcommD : ⁅gomiBarOf G D, gomiBarOf G D⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (commute_mem_closure_range_ea7 hB hBt hGB hCQ x hx a (hDbar_le ha) b
      (hDbar_le hb)).symm
  exact commutator_le_pCoreOf_of_gomiBarOf hCQ hDG hDG hcommD

private theorem le_card_commV_zpowers_gomiBar_of_mem_ea7 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (hB7 : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {S : Subgroup ↥(autOn G (gomiV G))}
    (hS : S ≤ Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    {d : Ω} (hdG : d ∈ G) (hdS : gomiBar G ⟨d, hdG⟩ ∈ S) (hd1 : gomiBar G ⟨d, hdG⟩ ≠ 1) :
    16 ≤ Nat.card (commV (Subgroup.zpowers
      ((gomiBar G ⟨d, hdG⟩ : ↥(autOn G (gomiV G))) : MulAut ↥(gomiV G)))) := by
  refine le_card_commV_zpowers_of_le_closure_ea7 hB hBt hGB hCQ hB7 x hx hS ?_ ?_
  · exact Subgroup.mem_map_of_mem _ hdS
  · intro h
    exact hd1 (Subtype.ext (by rw [h]; rfl))

theorem Gomi410Cex.isRegular_gomiBarPre_of_le_threeCycles (h : Gomi410Cex f hyp G)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hB7 : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} (hM : M ≠ ⊤)
    (x : Subgroup ↥(autOn G (gomiV G)) → ↥(autOn G (gomiV G)))
    (hx : ∀ g : ↥(autOn G (gomiV G)),
      IsGomiThreeCycle 7 ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)
        (x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)))
    (hle : twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G)))) ≤
      Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom))) :
    f.IsRegular (gomiBarPre G M) := by
  by_contra hreg
  obtain ⟨D₀, hD₀, hD₀le⟩ := exists_block_of_not_isRegular h hchar hmono hCQ hM hreg
  have hHG : gomiBarPre G M ≤ G := gomiBarPre_le G M
  have hDG : D₀.map (gomiBarPre G M).subtype ≤ G := (Subgroup.map_subtype_le D₀).trans hHG
  have hDbar_le : gomiBarOf G (D₀.map (gomiBarPre G M).subtype) ≤
      Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)) := hD₀le.trans hle
  have hab : ⁅D₀.map (gomiBarPre G M).subtype, D₀.map (gomiBarPre G M).subtype⁆ ≤
      pCoreOf 2 G :=
    commutator_le_pCoreOf_of_le_closure_ea7 hB hBt hGB hCQ x hx hDG hDbar_le
  have hDbar_ne : gomiBarOf G (D₀.map (gomiBarPre G M).subtype) ≠ ⊥ :=
    gomiBarOf_map_ne_bot_ea7 hHG hCQ hD₀
  obtain ⟨y, hyD, hyφ⟩ := exists_gomiBar_ne_one_of_gomiBarOf_ne_bot_ea7 hDG hDbar_ne
  have hyφ_mem : gomiBar G ⟨y, hDG hyD⟩ ∈
      Subgroup.closure (Set.range fun g : ↥(autOn G (gomiV G)) =>
        x ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom)) :=
    hDbar_le (by
      rw [gomiBarOf_eq_map hDG]
      exact Subgroup.mem_map_of_mem (gomiBar G) (Subgroup.mem_subgroupOf.mpr hyD))
  have hodd := odd_orderOf_of_mem_closure_range_ea7 hB hBt hGB hCQ x hx hyφ_mem
  obtain ⟨k, hkodd, hkφ⟩ := exists_odd_pow_ne_one_ea7 hDG hyD hyφ hodd
  have hdD : y ^ 2 ^ k ∈ D₀.map (gomiBarPre G M).subtype :=
    (D₀.map (gomiBarPre G M).subtype).pow_mem hyD (2 ^ k)
  have hdG : y ^ 2 ^ k ∈ G := hDG hdD
  have h16 := le_card_commV_zpowers_gomiBar_of_mem_ea7 hB hBt hGB hCQ hB7 x hx hDbar_le hdG
    (by rw [gomiBarOf_eq_map hDG]
        exact Subgroup.mem_map_of_mem (gomiBar G) (Subgroup.mem_subgroupOf.mpr hdD)) hkφ
  have h4 : Nat.card ↥⁅gomiV G, Subgroup.zpowers (y ^ 2 ^ k)⁆ ≤ 4 :=
    card_commutator_gomiV_zpowers_le_four (G := G) (M := gomiBarPre G M)
      hHG (pCoreOf_le_gomiBarPre G M) hD₀ hab hdD hkodd
  have h16' : 16 ≤ Nat.card ↥⁅gomiV G, Subgroup.zpowers (y ^ 2 ^ k)⁆ := by
    rw [← card_commV_zpowers_gomiBar_ea7 G hdG]
    exact h16
  omega

theorem Gomi410Cex.controls_gomiRegFamily_altSeven (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H) (h23 : GomiFact23)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hB7 : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    ControlsSylowIntersections 2 (gomiRegFamily f G) ⊤ := by
  have h21 : GomiHyp21 (gomiBarOf G B) := gomiHyp21_gomiBarOf hB hBt hGB hCQ
  have he7 : Nonempty (↥(gomiBarOf G B) ≃* alternatingGroup (Fin 7)) :=
    ⟨(nonempty_mulEquiv_gomiBarOf hB hCQ).some.symm.trans hB7.1.some⟩
  refine controlsSylowIntersections_of_isPIsolatedOver ?_
  intro H hHne hH2 hIso
  obtain ⟨M, hMne, hModd, ⟨K, hHK, hKN, hKsub, hKdiv, hKM⟩, x, hx, hxle⟩ :=
    (h23 ↥(autOn G (gomiV G)) (gomiBarOf G B) 7 h21 le_rfl he7 H hHne hH2 hIso).2.2
      (by norm_num : 7 % 4 = 3)
  exact ⟨K, hHK, hKN, hKsub, hKdiv, M,
    ⟨hMne, hModd,
      Gomi410Cex.isRegular_gomiBarPre_of_le_threeCycles h hchar hmono hB hBt hB7 hGB hCQ
        hMne x hx hxle⟩,
    hKM⟩

end CFSG.GroupTheory
