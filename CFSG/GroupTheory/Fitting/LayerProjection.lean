module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GH74.GLS.Stage2.Local.P34NS12Grp
public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.LocalCores
open scoped Pointwise commutatorElement

variable {H : Type*} [Group H] [Finite H]

noncomputable def componentProjection {C : Subgroup H} (hC : CFSG.IsComponent C)
    {Y : Subgroup H} (hY : Y ≤ CFSG.layer H) (hZ : Subgroup.center C = ⊥) :
    ↥Y →* ↥C where
  toFun y := Classical.choose (exists_layerMul_eq (hY y.2)) ⟨C, hC⟩
  map_one' := by
    let x := Classical.choose (exists_layerMul_eq (hY (one_mem Y)))
    have hx : layerMul H x = (1 : H) :=
      Classical.choose_spec (exists_layerMul_eq (hY (one_mem Y)))
    have hker : x⁻¹ * (1 : ∀ K : ComponentIndex H, K.1) ∈ (layerMul H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx]
      simp
    have hcoord := layerMul_ker_le hker ⟨C, hC⟩ (Set.mem_univ _)
    change (x⁻¹ * 1) ⟨C, hC⟩ ∈ Subgroup.center C at hcoord
    rw [Subgroup.mem_center_iff] at hcoord
    have hz : (x ⟨C, hC⟩)⁻¹ ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro g
      simpa using hcoord g
    exact inv_eq_one.mp (Subgroup.mem_bot.mp (hZ ▸ hz))
  map_mul' y y' := by
    let x := Classical.choose (exists_layerMul_eq (hY y.2))
    let x' := Classical.choose (exists_layerMul_eq (hY y'.2))
    let x'' := Classical.choose (exists_layerMul_eq (hY (mul_mem y.2 y'.2)))
    have hx : layerMul H x = (y : H) := Classical.choose_spec (exists_layerMul_eq (hY y.2))
    have hx' : layerMul H x' = (y' : H) := Classical.choose_spec (exists_layerMul_eq (hY y'.2))
    have hx'' : layerMul H x'' = ((y * y' : ↥Y) : H) :=
      Classical.choose_spec (exists_layerMul_eq (hY (mul_mem y.2 y'.2)))
    have hker : x''⁻¹ * (x * x') ∈ (layerMul H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx'', map_mul, hx, hx']
      simp
    have hcoord := layerMul_ker_le hker ⟨C, hC⟩ (Set.mem_univ _)
    change (x''⁻¹ * (x * x')) ⟨C, hC⟩ ∈ Subgroup.center C at hcoord
    rw [Subgroup.mem_center_iff] at hcoord
    have hz : (x'' ⟨C, hC⟩)⁻¹ * (x ⟨C, hC⟩ * x' ⟨C, hC⟩) = 1 := by
      have hmem : (x'' ⟨C, hC⟩)⁻¹ * (x ⟨C, hC⟩ * x' ⟨C, hC⟩) ∈ Subgroup.center C := by
        rw [Subgroup.mem_center_iff]
        intro g
        simpa using hcoord g
      exact Subgroup.mem_bot.mp (hZ ▸ hmem)
    exact inv_mul_eq_one.mp hz

theorem componentProjection_conj {C : Subgroup H} (hC : CFSG.IsComponent C)
    {Y : Subgroup H} (hY : Y ≤ CFSG.layer H) (hZ : Subgroup.center C = ⊥)
    (y : ↥Y) {m : H} (hm : m ∈ C) :
    (y : H) * m * (y : H)⁻¹ =
      (((componentProjection hC hY hZ y : ↥C) : H)) * m *
        ((((componentProjection hC hY hZ y : ↥C)) : H))⁻¹ := by
  let x := Classical.choose (exists_layerMul_eq (hY y.2))
  let b := layerMul H (Function.update x ⟨C, hC⟩ 1)
  have hx : layerMul H x = (y : H) :=
    Classical.choose_spec (exists_layerMul_eq (hY y.2))
  have hdec : (y : H) = (x ⟨C, hC⟩ : H) * b := by
    rw [← hx]
    exact layerMul_eq_mul_update x ⟨C, hC⟩
  have hbm : b * m = m * b := (commute_layerMul_update x ⟨C, hC⟩ hm).eq.symm
  change (y : H) * m * (y : H)⁻¹ =
    (x ⟨C, hC⟩ : H) * m * (x ⟨C, hC⟩ : H)⁻¹
  rw [hdec]
  calc
    ((x ⟨C, hC⟩ : ↥C) : H) * b * m * (((x ⟨C, hC⟩ : ↥C) : H) * b)⁻¹
        = ((x ⟨C, hC⟩ : ↥C) : H) * (b * m * b⁻¹) *
            ((((x ⟨C, hC⟩ : ↥C)) : H))⁻¹ := by group
    _ = ((x ⟨C, hC⟩ : ↥C) : H) * (m * b * b⁻¹) *
            ((((x ⟨C, hC⟩ : ↥C)) : H))⁻¹ := by rw [hbm]
    _ = ((x ⟨C, hC⟩ : ↥C) : H) * m * ((((x ⟨C, hC⟩ : ↥C)) : H))⁻¹ := by
      simp

theorem componentProjection_eq_of_conj_eq {C : Subgroup H} (hC : CFSG.IsComponent C)
    {Y : Subgroup H} (hY : Y ≤ CFSG.layer H) (hZ : Subgroup.center C = ⊥)
    {y : ↥Y} {c : ↥C}
    (h : ∀ m ∈ C, (y : H) * m * (y : H)⁻¹ = (c : H) * m * (c : H)⁻¹) :
    componentProjection hC hY hZ y = c := by
  have hinj : Function.Injective (MulAut.conj : ↥C →* MulAut ↥C) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  apply_fun (fun z : ↥C => MulAut.conj z) using hinj
  ext m
  exact (componentProjection_conj hC hY hZ y m.2).symm.trans (h m m.2)

theorem componentProjection_apply_self {C : Subgroup H} (hC : CFSG.IsComponent C)
    {Y : Subgroup H} (hY : Y ≤ CFSG.layer H) (hZ : Subgroup.center C = ⊥)
    {y : ↥Y} (hyC : (y : H) ∈ C) :
    (((componentProjection hC hY hZ y : ↥C)) : H) = (y : H) :=
  congrArg Subtype.val
    (componentProjection_eq_of_conj_eq hC hY hZ (c := ⟨(y : H), hyC⟩)
      (fun _ _ => rfl))

theorem componentProjection_eq_one_of_le_centralizer {C : Subgroup H}
    (hC : CFSG.IsComponent C) {Y : Subgroup H} (hY : Y ≤ CFSG.layer H)
    (hZ : Subgroup.center C = ⊥) {R : Subgroup H} (hRY : R ≤ Y)
    (hRcent : R ≤ Subgroup.centralizer (C : Set H)) {y : ↥Y} (hy : (y : H) ∈ R) :
    componentProjection hC hY hZ y = 1 := by
  apply componentProjection_eq_of_conj_eq hC hY hZ (c := 1)
  intro m hm
  have hc : m * (y : H) = (y : H) * m :=
    Subgroup.mem_centralizer_iff.mp (hRcent hy) m hm
  calc
    (y : H) * m * (y : H)⁻¹ = m := by rw [hc.symm]; group
    _ = ((1 : ↥C) : H) * m * (((1 : ↥C) : H))⁻¹ := by simp

theorem eq_bot_of_commutator_eq_self_of_le_centralizer {P : Subgroup H}
    (hP : ⁅P, P⁆ = P) (h : P ≤ Subgroup.centralizer (P : Set H)) : P = ⊥ := by
  have hbot : ⁅P, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  rw [← hP]
  exact hbot

theorem eq_bot_of_perfect_le_layer_of_centralizes_components {Y : Subgroup H}
    (hY : Y ≤ layer H) (hYp : ⁅Y, Y⁆ = Y)
    (hcent : ∀ C : Subgroup H, CFSG.IsComponent C →
      Y ≤ Subgroup.centralizer (C : Set H)) : Y = ⊥ := by
  have hYcenter : Y ≤ (Subgroup.center (layer H)).map (layer H).subtype := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_layerMul_eq (hY hy)
    have hxc : layerMul H x ∈ Subgroup.centralizer (layer H : Set H) := by
      rw [layerMul_mem_centralizer_iff]
      intro K
      rw [Subgroup.mem_center_iff]
      intro k
      have hcomm : Commute (k : H) (layerMul H x) := by
        rw [hx]
        exact Subgroup.mem_centralizer_iff.mp (hcent K.1 K.2 hy) (k : H) k.2
      exact Subtype.ext ((commute_layerMul_iff x K k.2).mp hcomm).eq
    rw [hx] at hxc
    exact (mem_map_center_iff (layer H)).mpr ⟨hY hy, hxc⟩
  have hYab : ⁅Y, Y⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hyc : (y : H) ∈ Subgroup.centralizer (layer H : Set H) :=
      ((mem_map_center_iff (layer H)).mp (hYcenter hy)).2
    exact Subgroup.mem_centralizer_iff.mp hyc z (hY hz)
  rw [← hYp]
  exact hYab

theorem le_component_of_perfect_le_layer_of_centralizes_components_ne {Y C₀ : Subgroup H}
    (hC₀ : CFSG.IsComponent C₀) (hY : Y ≤ layer H)
    (hcent : ∀ C : Subgroup H, CFSG.IsComponent C → C ≠ C₀ →
      Y ≤ Subgroup.centralizer (C : Set H))
    (hZ : ∀ C : Subgroup H, CFSG.IsComponent C → Subgroup.center C = ⊥) :
    Y ≤ C₀ := by
  intro y hy
  obtain ⟨x, hx⟩ := exists_layerMul_eq (hY hy)
  have hx0 : ∀ K : ComponentIndex H, K.1 ≠ C₀ → x K = 1 := by
    intro K hne
    have hcentK : Y ≤ Subgroup.centralizer (K.1 : Set H) := hcent K.1 K.2 hne
    have hxcent : x K ∈ Subgroup.center K.1 := by
      rw [Subgroup.mem_center_iff]
      intro k
      have hcomm : Commute (k : H) (layerMul H x) := by
        rw [hx]
        exact Subgroup.mem_centralizer_iff.mp (hcentK hy) k k.2
      exact Subtype.ext ((commute_layerMul_iff x K k.2).mp hcomm).eq
    exact Subgroup.mem_bot.mp ((hZ K.1 K.2) ▸ hxcent)
  have hxeq : x = Pi.mulSingle ⟨C₀, hC₀⟩ (x ⟨C₀, hC₀⟩) := by
    funext K
    by_cases h : K = ⟨C₀, hC₀⟩
    · subst h
      simp
    · have hne : K.1 ≠ C₀ := fun heq => h (Subtype.ext heq)
      simp [Pi.mulSingle_eq_of_ne h, hx0 K hne]
  rw [← hx, hxeq, layerMul_mulSingle]
  exact (x ⟨C₀, hC₀⟩).2

theorem eq_bot_of_perfect_of_centralizes_sylow_two {C : Subgroup H}
    (hC : CFSG.IsComponent C) {T : Sylow 2 ↥C} {P : Subgroup ↥C}
    (hPp : ⁅P, P⁆ = P)
    (hcent : ∀ p ∈ P, ∀ t : T, p * (t : ↥C) = (t : ↥C) * p) : P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Tsub : Subgroup ↥C := (T : Subgroup ↥C)
  let N : Subgroup ↥C := P ⊔ Tsub
  let Tn : Subgroup ↥N := Tsub.subgroupOf N
  let Pn : Subgroup ↥N := P.subgroupOf N
  have hPnorm : P ≤ Subgroup.normalizer (Tsub : Set ↥C) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have h := hcent p hp ⟨t, ht⟩
      rw [show p * t * p⁻¹ = t by rw [h]; group]
      exact ht
    · intro ht
      have h := hcent p hp ⟨p * t * p⁻¹, ht⟩
      have ht' : t = p⁻¹ * (p * t * p⁻¹) * p := by group
      rw [ht']
      have hs : p⁻¹ * (p * t * p⁻¹) * p = p * t * p⁻¹ := by
        calc
          p⁻¹ * (p * t * p⁻¹) * p = p⁻¹ * ((p * t * p⁻¹) * p) := by group
          _ = p⁻¹ * (p * (p * t * p⁻¹)) := by rw [h.symm]
          _ = p * t * p⁻¹ := by group
      rw [hs]
      exact ht
  haveI hTn : Tn.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPnorm
  have hTsubOdd : Odd Tsub.index :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using T.not_dvd_index)
  have hrelOdd : Odd (Tsub.relIndex N) :=
    Odd.of_dvd_nat hTsubOdd (Subgroup.relIndex_dvd_index_of_le (show Tsub ≤ N from le_sup_right))
  have hodd : Odd (Nat.card (↥N ⧸ Tn)) := by
    rw [← Subgroup.index_eq_card]
    change Odd (Tsub.relIndex N)
    exact hrelOdd
  have hPnperf : ⁅Pn, Pn⁆ = Pn := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq (show P ≤ N from le_sup_left)
      (show P ≤ N from le_sup_left), hPp]
  have hPnle : Pn ≤ Tn :=
    CFSG.GH74.GLS.Stage2.Local.P34NS.perfect_le_of_odd_quot hodd hPnperf
  have hPleT : P ≤ Tsub := by
    intro p hp
    exact hPnle (show (⟨p, Subgroup.mem_sup_left hp⟩ : ↥N) ∈ Pn from
      Subgroup.mem_subgroupOf.mpr hp)
  have hPcent : P ≤ Subgroup.centralizer (P : Set ↥C) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqT : q ∈ Tsub := hPleT hq
    exact (hcent p hp ⟨q, hqT⟩).symm
  exact eq_bot_of_commutator_eq_self_of_le_centralizer hPp hPcent

theorem commutator_eq_self_of_isPerfect_subgroup {X : Type*} [Group X] {P : Subgroup X}
    [Group.IsPerfect ↥P] : ⁅P, P⁆ = P := by
  rw [← Subgroup.map_subtype_commutator P, Group.IsPerfect.commutator_eq_top]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem componentProjection_conj_normalizer {C : Subgroup H} (hC : CFSG.IsComponent C)
    {Y : Subgroup H} (hY : Y ≤ CFSG.layer H) (hZ : Subgroup.center C = ⊥)
    (y : ↥Y) (t : ↥C) (ht : (t : H) ∈ Subgroup.normalizer (Y : Set H)) :
    componentProjection hC hY hZ
        ⟨(t : H) * (y : H) * (t : H)⁻¹,
          (Subgroup.mem_normalizer_iff.mp ht (y : H)).mp y.2⟩ =
      t * componentProjection hC hY hZ y * t⁻¹ := by
  apply componentProjection_eq_of_conj_eq hC hY hZ
  intro m hm
  have hmt : (t : H)⁻¹ * m * (t : H) ∈ C :=
    C.mul_mem (C.mul_mem (C.inv_mem t.2) hm) t.2
  have hconj := componentProjection_conj hC hY hZ y hmt
  calc
    ((t : H) * (y : H) * (t : H)⁻¹) * m * ((t : H) * (y : H) * (t : H)⁻¹)⁻¹
        = (t : H) * ((y : H) * ((t : H)⁻¹ * m * (t : H)) * (y : H)⁻¹) *
            (t : H)⁻¹ := by group
    _ = (t : H) * (((componentProjection hC hY hZ y : ↥C) : H) *
          ((t : H)⁻¹ * m * (t : H)) *
          (((componentProjection hC hY hZ y : ↥C) : H))⁻¹) * (t : H)⁻¹ := by rw [hconj]
    _ = ((t * componentProjection hC hY hZ y * t⁻¹ : ↥C) : H) * m *
          (((t * componentProjection hC hY hZ y * t⁻¹ : ↥C) : H))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

private theorem projection_ker_eq_of_maximal {Y R : Subgroup H} (hY : Y ≤ layer H)
    (hRY : R ≤ Y)
    (hRmax : ∀ N : Subgroup ↥Y, R.subgroupOf Y ≤ N → N.Normal →
      N = R.subgroupOf Y ∨ N = ⊤)
    (hRcent : ∀ C : Subgroup H, CFSG.IsComponent C →
      R ≤ Subgroup.centralizer (C : Set H))
    (hZ : ∀ C : Subgroup H, CFSG.IsComponent C → Subgroup.center C = ⊥)
    {C : Subgroup H} (hC : CFSG.IsComponent C)
    (hnot : ¬ Y ≤ Subgroup.centralizer (C : Set H)) :
    (componentProjection hC hY (hZ C hC)).ker = R.subgroupOf Y := by
  have hle : R.subgroupOf Y ≤ (componentProjection hC hY (hZ C hC)).ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    exact componentProjection_eq_one_of_le_centralizer hC hY (hZ C hC) hRY
      (hRcent C hC) (Subgroup.mem_subgroupOf.mp hr)
  rcases hRmax _ hle (inferInstance : (componentProjection hC hY (hZ C hC)).ker.Normal)
    with heq | htop
  · exact heq
  · exfalso
    apply hnot
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 : componentProjection hC hY (hZ C hC) ⟨y, hy⟩ = 1 := by
      rw [← MonoidHom.mem_ker, htop]
      exact Subgroup.mem_top _
    have h2 := componentProjection_conj hC hY (hZ C hC) (⟨y, hy⟩ : ↥Y) hm
    rw [h1] at h2
    have h2' : (y : H) * m = m * (y : H) := by
      calc
        (y : H) * m = ((y : H) * m * (y : H)⁻¹) * (y : H) := by group
        _ = m * (y : H) := by rw [h2]; simp
    exact h2'.symm

private theorem inf_component_eq_bot_of_two {Y R : Subgroup H} (hY : Y ≤ layer H)
    (hRY : R ≤ Y)
    (hRmax : ∀ N : Subgroup ↥Y, R.subgroupOf Y ≤ N → N.Normal →
      N = R.subgroupOf Y ∨ N = ⊤)
    (hRcent : ∀ C : Subgroup H, CFSG.IsComponent C →
      R ≤ Subgroup.centralizer (C : Set H))
    (hZ : ∀ C : Subgroup H, CFSG.IsComponent C → Subgroup.center C = ⊥)
    {C₀ C₁ : Subgroup H} (hC₀ : CFSG.IsComponent C₀) (hC₁ : CFSG.IsComponent C₁)
    (hne : C₀ ≠ C₁) (hnot₀ : ¬ Y ≤ Subgroup.centralizer (C₀ : Set H))
    (hnot₁ : ¬ Y ≤ Subgroup.centralizer (C₁ : Set H)) :
    Y ⊓ C₀ = ⊥ := by
  refine le_bot_iff.mp ?_
  intro z hz
  have hzY : z ∈ Y := hz.1
  have hzC₀ : z ∈ C₀ := hz.2
  have hker₀ := projection_ker_eq_of_maximal hY hRY hRmax hRcent hZ hC₀ hnot₀
  have hker₁ := projection_ker_eq_of_maximal hY hRY hRmax hRcent hZ hC₁ hnot₁
  have hcomm : ⁅C₀, C₁⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hC₀ hC₁ with heq | h
    · exact absurd heq hne
    · exact h
  have hle : C₀ ≤ Subgroup.centralizer (C₁ : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hzk₁ : (⟨z, hzY⟩ : ↥Y) ∈ (componentProjection hC₁ hY (hZ C₁ hC₁)).ker := by
    rw [MonoidHom.mem_ker]
    apply componentProjection_eq_of_conj_eq hC₁ hY (hZ C₁ hC₁) (c := 1)
    intro m hm
    have hc : m * z = z * m := Subgroup.mem_centralizer_iff.mp (hle hzC₀) m hm
    calc
      z * m * z⁻¹ = m := by rw [hc.symm]; group
      _ = ((1 : ↥C₁) : H) * m * (((1 : ↥C₁) : H))⁻¹ := by simp
  have hzR : (⟨z, hzY⟩ : ↥Y) ∈ R.subgroupOf Y := by
    rw [← hker₁]
    exact hzk₁
  have hzR' : z ∈ R := Subgroup.mem_subgroupOf.mp hzR
  have hzk₀ : componentProjection hC₀ hY (hZ C₀ hC₀) ⟨z, hzY⟩ = 1 :=
    componentProjection_eq_one_of_le_centralizer hC₀ hY (hZ C₀ hC₀) hRY
      (hRcent C₀ hC₀) hzR'
  have hzid := componentProjection_apply_self hC₀ hY (hZ C₀ hC₀)
    (y := ⟨z, hzY⟩) hzC₀
  rw [hzk₀] at hzid
  simpa using hzid.symm

private theorem false_of_two_components {Y R : Subgroup H} (hY : Y ≤ layer H)
    (hYp : ⁅Y, Y⁆ = Y) (hRY : R ≤ Y)
    (hRmax : ∀ N : Subgroup ↥Y, R.subgroupOf Y ≤ N → N.Normal →
      N = R.subgroupOf Y ∨ N = ⊤)
    (hRcent : ∀ C : Subgroup H, CFSG.IsComponent C →
      R ≤ Subgroup.centralizer (C : Set H))
    (hZ : ∀ C : Subgroup H, CFSG.IsComponent C → Subgroup.center C = ⊥)
    {C₀ C₁ : Subgroup H} (hC₀ : CFSG.IsComponent C₀) (hC₁ : CFSG.IsComponent C₁)
    (hne : C₀ ≠ C₁) (hnot₀ : ¬ Y ≤ Subgroup.centralizer (C₀ : Set H))
    (hnot₁ : ¬ Y ≤ Subgroup.centralizer (C₁ : Set H))
    (hT : ∀ C : Subgroup H, CFSG.IsComponent C → ∃ T : Sylow 2 ↥C,
      ∀ t : T, (t : H) ∈ Subgroup.normalizer (Y : Set H)) : False := by
  have hbot : Y ⊓ C₀ = ⊥ :=
    inf_component_eq_bot_of_two hY hRY hRmax hRcent hZ hC₀ hC₁ hne hnot₀ hnot₁
  obtain ⟨T₀, hT₀⟩ := hT C₀ hC₀
  let T₀H : Subgroup H := (T₀ : Subgroup ↥C₀).map C₀.subtype
  have hT₀H_norm : T₀H ≤ Subgroup.normalizer (Y : Set H) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    exact hT₀ ⟨t', ht'⟩
  have hcommY : ⁅T₀H, Y⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hT₀H_norm
  have hT₀H_le : T₀H ≤ C₀ := Subgroup.map_subtype_le (T₀ : Subgroup ↥C₀)
  have hYnormC : Y ≤ Subgroup.normalizer (C₀ : Set H) :=
    hY.trans (CFSG.LocalCores.layer_le_normalizer hC₀)
  have hYC : ⁅C₀, Y⁆ ≤ C₀ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hYnormC
  have hcommC : ⁅T₀H, Y⁆ ≤ C₀ :=
    (Subgroup.commutator_mono hT₀H_le le_rfl).trans hYC
  have hcommbot : ⁅T₀H, Y⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf hcommY hcommC).trans_eq hbot
  have hcentT : T₀H ≤ Subgroup.centralizer (Y : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
  let P : Subgroup ↥C₀ := (componentProjection hC₀ hY (hZ C₀ hC₀)).range
  haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYp
  haveI : Group.IsPerfect ↥P := Group.IsPerfect.range _
  have hPperf : ⁅P, P⁆ = P := commutator_eq_self_of_isPerfect_subgroup
  have hPcent : ∀ p ∈ P, ∀ t : T₀, p * (t : ↥C₀) = (t : ↥C₀) * p := by
    intro p hp t
    obtain ⟨y, rfl⟩ := hp
    have htY : (t : H) ∈ Subgroup.normalizer (Y : Set H) := hT₀ t
    have hconj := componentProjection_conj_normalizer hC₀ hY (hZ C₀ hC₀) y t htY
    have hty : (⟨(t : H) * (y : H) * (t : H)⁻¹,
        (Subgroup.mem_normalizer_iff.mp htY (y : H)).mp y.2⟩ : ↥Y) = y := by
      apply Subtype.ext
      show (t : H) * (y : H) * (t : H)⁻¹ = (y : H)
      have hcomm : (t : H) * (y : H) = (y : H) * (t : H) :=
        (Subgroup.mem_centralizer_iff.mp
          (hcentT (Subgroup.mem_map_of_mem C₀.subtype t.2)) (y : H) y.2).symm
      calc
        (t : H) * (y : H) * (t : H)⁻¹ = (y : H) * (t : H) * (t : H)⁻¹ := by rw [hcomm]
        _ = (y : H) := by group
    rw [hty] at hconj
    have hmul : componentProjection hC₀ hY (hZ C₀ hC₀) y * t =
        t * componentProjection hC₀ hY (hZ C₀ hC₀) y := by
      have := congrArg (fun z : ↥C₀ => z * t) hconj
      simpa [mul_assoc] using this
    exact hmul
  have hPbot : P = ⊥ := eq_bot_of_perfect_of_centralizes_sylow_two hC₀ hPperf hPcent
  apply hnot₀
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hmem : componentProjection hC₀ hY (hZ C₀ hC₀) ⟨y, hy⟩ ∈ P := by
    change componentProjection hC₀ hY (hZ C₀ hC₀) ⟨y, hy⟩ ∈
      (componentProjection hC₀ hY (hZ C₀ hC₀)).range
    exact ⟨⟨y, hy⟩, rfl⟩
  rw [hPbot] at hmem
  have h1 : componentProjection hC₀ hY (hZ C₀ hC₀) ⟨y, hy⟩ = 1 :=
    Subgroup.mem_bot.mp hmem
  have h2 := componentProjection_conj hC₀ hY (hZ C₀ hC₀) (⟨y, hy⟩ : ↥Y) hm
  rw [h1] at h2
  have h2' : (y : H) * m = m * (y : H) := by
    calc
      (y : H) * m = ((y : H) * m * (y : H)⁻¹) * (y : H) := by group
      _ = m * (y : H) := by rw [h2]; simp
  exact h2'.symm

theorem eq_bot_or_le_component_of_perfect_le_layer {Y : Subgroup H}
    (hY : Y ≤ layer H) (hYp : ⁅Y, Y⁆ = Y) {R : Subgroup H} (hRY : R ≤ Y)
    (hRmax : ∀ N : Subgroup ↥Y, R.subgroupOf Y ≤ N → N.Normal →
      N = R.subgroupOf Y ∨ N = ⊤)
    (hRcent : ∀ C : Subgroup H, CFSG.IsComponent C →
      R ≤ Subgroup.centralizer (C : Set H))
    (hZ : ∀ C : Subgroup H, CFSG.IsComponent C → Subgroup.center C = ⊥)
    (hT : ∀ C : Subgroup H, CFSG.IsComponent C → ∃ T : Sylow 2 ↥C,
      ∀ t : T, (t : H) ∈ Subgroup.normalizer (Y : Set H)) :
    Y = ⊥ ∨ ∃ C₀ : Subgroup H, CFSG.IsComponent C₀ ∧ Y ≤ C₀ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ C : Subgroup H, CFSG.IsComponent C ∧
        ¬ Y ≤ Subgroup.centralizer (C : Set H) := by
      by_contra h
      refine hbot (eq_bot_of_perfect_le_layer_of_centralizes_components hY hYp ?_)
      intro C hC
      by_contra hnc
      exact h ⟨C, hC, hnc⟩
    obtain ⟨C₀, hC₀, hnot₀⟩ := hex
    refine ⟨C₀, hC₀, ?_⟩
    refine le_component_of_perfect_le_layer_of_centralizes_components_ne hC₀ hY ?_ hZ
    intro C hC hne
    by_contra hnot
    exact false_of_two_components hY hYp hRY hRmax hRcent hZ hC₀ hC hne.symm hnot₀ hnot hT
