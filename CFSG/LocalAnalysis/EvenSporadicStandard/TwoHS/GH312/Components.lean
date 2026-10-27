module

public import CFSG.GH74.GLS.TwoThin.Count
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.Quasithin.Background.D2Z9
public import CFSG.Walter.Bender1970.S2.Components
public import CFSG.Adapters.GeneralizedFitting

public section

open Subgroup
open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

variable {X : Type*} [Group X] [Finite X]

private theorem center_layer_le_fitting' :
    (Subgroup.center ↥(CFSG.layer X)).map (CFSG.layer X).subtype ≤ CFSG.fittingSubgroup X := by
  set Z := (Subgroup.center ↥(CFSG.layer X)).map (CFSG.layer X).subtype with hZ
  have hchar : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer X).Characteristic := hchar
  have hn : (CFSG.layer X).Normal := inferInstance
  have hZmem : ∀ g ∈ Z, g ∈ CFSG.layer X ∧ ∀ l ∈ CFSG.layer X, l * g = g * l := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c.2, fun l hl => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hZn : Z.Normal := ⟨fun n hn' g => by
    obtain ⟨hnL, hnc⟩ := hZmem n hn'
    refine ⟨⟨g * n * g⁻¹, hn.conj_mem n hnL g⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center ↥(CFSG.layer X)
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl' : g⁻¹ * (l : X) * g ∈ CFSG.layer X := by
      simpa using hn.conj_mem (l : X) l.2 g⁻¹
    have := hnc _ hl'
    calc (l : X) * (g * n * g⁻¹) = g * ((g⁻¹ * (l : X) * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * (l : X) * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * (l : X) := by group⟩
  have hcomm : IsMulCommutative ↥Z :=
    ⟨⟨fun a b => Subtype.ext ((hZmem b b.2).2 a (hZmem a a.2).1)⟩⟩
  have hnil : Group.IsNilpotent ↥Z := inferInstance
  exact le_sSup ⟨hZn, hnil⟩

private theorem center_component_eq_bot' (hF : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : Subgroup.center ↥K = ⊥ := by
  have h1 := (CFSG.LocalCores.center_component_le_center_layer hK).trans
    center_layer_le_fitting'
  rw [hF, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  rw [Subgroup.ker_subtype] at h1
  exact le_bot_iff.1 h1

private theorem component_isSimple' (hF : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X}
    (hK : CFSG.IsComponent K) :
    IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  have hc := center_component_eq_bot' hF hK
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨(e.isSimpleGroup_congr).1 hs, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

private theorem components_commute_inf' (hF : CFSG.fittingSubgroup X = ⊥) {K L : Subgroup X}
    (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L) (hne : K ≠ L) :
    (∀ a ∈ K, ∀ b ∈ L, a * b = b * a) ∧ K ⊓ L = ⊥ := by
  have hcomm : ⁅K, L⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hne
  have h1 : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  refine ⟨h1, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 g g.2 x hx.2)
  rw [center_component_eq_bot' hF hK, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxZ)

private theorem ncard_conjSet_eq_relIndex {G : Type*} [Group G] (V N : Subgroup G) :
    ({W : Subgroup G | ∃ g ∈ N, W = CFSG.conjugate V g} : Set (Subgroup G)).ncard =
      (Subgroup.normalizer (V : Set G)).relIndex N := by
  rw [← Nat.card_coe_set_eq]
  classical
  let _ : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)
  let _ : MulAction ↥N (Subgroup G) := MulAction.compHom (Subgroup G) N.subtype
  have hsmul : ∀ p : ↥N, p • V = CFSG.conjugate V (p : G)⁻¹ := fun p => by
    rw [CFSG.conjugate, inv_inv]
    rfl
  have horbit : MulAction.orbit ↥N V = {W : Subgroup G | ∃ g ∈ N, W = CFSG.conjugate V g} := by
    ext W
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : G)⁻¹, N.inv_mem p.2, hsmul p⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q⁻¹, N.inv_mem hq⟩, ?_⟩
      rw [hsmul]
      simp
  have hstab : MulAction.stabilizer ↥N V = (Subgroup.normalizer (V : Set G)).subgroupOf N := by
    ext p
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul, CFSG.conjugate, inv_inv]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := V) (g := (p : G))).symm
  rw [← horbit, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥N V),
    ← (MulAction.stabilizer ↥N V).index_eq_card, hstab]
  rfl

private theorem central_involution_mem_orbitJoin (hF : CFSG.fittingSubgroup X = ⊥) (P : Sylow 2 X)
    (hZ : ∀ a ∈ Subgroup.center ↥(P : Subgroup X), ∀ b ∈ Subgroup.center ↥(P : Subgroup X),
      orderOf a = 2 → orderOf b = 2 → a = b)
    (zP : ↥(P : Subgroup X)) (hzP_center : zP ∈ Subgroup.center ↥(P : Subgroup X))
    (hzP2 : orderOf zP = 2)
    {M : Subgroup X} (hM : CFSG.IsComponent M) :
    (zP : X) ∈ sSup (Set.range fun g : ↥(P : Subgroup X) => CFSG.conjugate M (g : X)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(P : Subgroup X) := P.isPGroup'
  set S : Set (Subgroup X) :=
    Set.range fun g : ↥(P : Subgroup X) => CFSG.conjugate M (g : X) with hSdef
  set E : Subgroup X := sSup S with hEdef
  have hScomp : ∀ N ∈ S, CFSG.IsComponent N := by
    rintro N ⟨g, rfl⟩
    exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hM (g : X)
  have hEsubX : E.IsSubnormal := by
    rw [hEdef]
    exact CFSG.ComponentClassification.UnbalancedLayer.sSup_isSubnormal hScomp
  have hEnorm : (P : Subgroup X) ≤ Subgroup.normalizer (E : Set X) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have ha' : a ∈ sSup S := by rwa [hEdef] at ha
      have hcl : ∀ N ∈ S, CFSG.conjugate N p⁻¹ ∈ S := by
        rintro N ⟨g, rfl⟩
        exact ⟨⟨(g : X) * p⁻¹, P.mul_mem g.2 (P.inv_mem hp)⟩,
          (CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate M (g : X) p⁻¹).symm⟩
      have h2 := CFSG.ComponentClassification.UnbalancedLayer.conj_mem_sSup hcl ha'
      rw [hEdef]
      simpa using h2
    · intro ha
      have ha' : p * a * p⁻¹ ∈ sSup S := by rwa [hEdef] at ha
      have hcl : ∀ N ∈ S, CFSG.conjugate N p ∈ S := by
        rintro N ⟨g, rfl⟩
        exact ⟨⟨(g : X) * p, P.mul_mem g.2 hp⟩,
          (CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate M (g : X) p).symm⟩
      have h2 := CFSG.ComponentClassification.UnbalancedLayer.conj_mem_sSup hcl ha'
      have h3 : p⁻¹ * (p * a * p⁻¹) * p = a := by group
      rw [hEdef, ← h3]
      simpa using h2
  have hMleE : M ≤ E := by
    rw [hEdef]
    refine le_sSup ?_
    rw [hSdef]
    have hmem := Set.mem_range_self
      (f := fun g : ↥(P : Subgroup X) => CFSG.conjugate M (g : X))
      (⟨1, P.one_mem⟩ : ↥(P : Subgroup X))
    simpa [CFSG.ComponentClassification.UnbalancedLayer.conjugate_one] using hmem
  have hM4 : 4 ∣ Nat.card ↥M := by
    obtain ⟨hsimple, hna⟩ := component_isSimple' hF hM
    haveI : IsSimpleGroup ↥M := hsimple
    exact CFSG.GH74.GLS.TwoThin.four_dvd_card_of_simple_nonabelian hna
  have hPinfE_ne : (P : Subgroup X) ⊓ E ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hEsubX
    intro hbot
    have hQbot : (Q : Subgroup E) = ⊥ :=
      Subgroup.map_injective E.subtype_injective (by rw [hQ, hbot, Subgroup.map_bot])
    exact Sylow.ne_bot_of_dvd_card Q
      ((by norm_num : 2 ∣ 4).trans (hM4.trans (Subgroup.card_dvd_of_le hMleE))) hQbot
  set A : Subgroup X := (P : Subgroup X) ⊓ E with hAdef
  have hAnorm : (A.subgroupOf (P : Subgroup X)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    have h1 : (P : Subgroup X) ≤
        Subgroup.normalizer (P : Set X) ⊓ Subgroup.normalizer (E : Set X) :=
      le_inf Subgroup.le_normalizer hEnorm
    have h2 := h1.trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := (P : Subgroup X)) (K := E))
    simpa [hAdef] using h2
  have hAne : A ≠ ⊥ := by simpa [hAdef] using hPinfE_ne
  have hHne : (A.subgroupOf (P : Subgroup X)) ≠ ⊥ := by
    intro h
    apply hAne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥(P : Subgroup X)) ∈ A.subgroupOf (P : Subgroup X) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subtype.ext_iff.mp hx'
  haveI : Group.IsNilpotent ↥(P : Subgroup X) := hP2.isNilpotent
  haveI : (A.subgroupOf (P : Subgroup X)).Normal := hAnorm
  have hZne : (A.subgroupOf (P : Subgroup X)) ⊓ Subgroup.center ↥(P : Subgroup X) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set Z : Subgroup ↥(P : Subgroup X) :=
    (A.subgroupOf (P : Subgroup X)) ⊓ Subgroup.center ↥(P : Subgroup X) with hZdef
  have hZ2 : IsPGroup 2 ↥Z := hP2.to_subgroup Z
  haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr (by simpa [hZdef] using hZne)
  have hZ2dvd : 2 ∣ Nat.card ↥Z := hZ2.card_eq_or_dvd.resolve_left (by
    have := Finite.one_lt_card (α := ↥Z)
    omega)
  obtain ⟨w, hw2⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2 hZ2dvd
  let wP : ↥(P : Subgroup X) := (w : ↥(P : Subgroup X))
  have hwP2 : orderOf wP = 2 := by
    have h := orderOf_injective (Subgroup.subtype Z) (fun _ _ h => Subtype.ext h) w
    simpa [wP] using h.trans hw2
  have hwP_center : wP ∈ Subgroup.center ↥(P : Subgroup X) := w.2.2
  have hwP_A : wP ∈ A.subgroupOf (P : Subgroup X) := w.2.1
  have hwP_E : (wP : X) ∈ E := by
    have h1 : (wP : X) ∈ (P : Subgroup X) ⊓ E := by
      simpa [hAdef] using Subgroup.mem_subgroupOf.mp hwP_A
    exact h1.2
  have hzw : zP = wP := hZ zP hzP_center wP hwP_center hzP2 hwP2
  rw [hzw]
  exact hwP_E

theorem exists_mem_sylow_conjugate_eq_of_isComponent (hF : CFSG.fittingSubgroup X = ⊥)
    (P : Sylow 2 X)
    (hZ : ∀ a ∈ Subgroup.center ↥(P : Subgroup X), ∀ b ∈ Subgroup.center ↥(P : Subgroup X),
      orderOf a = 2 → orderOf b = 2 → a = b)
    {K L : Subgroup X} (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L) :
    ∃ g ∈ (P : Subgroup X), CFSG.conjugate K g = L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hconj
  obtain ⟨hKsimple, hna⟩ := component_isSimple' hF hK
  haveI : IsSimpleGroup ↥K := hKsimple
  have hK4 : 4 ∣ Nat.card ↥K := CFSG.GH74.GLS.TwoThin.four_dvd_card_of_simple_nonabelian hna
  have hXeven : 2 ∣ Nat.card X :=
    (dvd_trans (by norm_num : 2 ∣ 4) hK4).trans (Subgroup.card_subgroup_dvd_card K)
  have hPne : (P : Subgroup X) ≠ ⊥ := P.ne_bot_of_dvd_card hXeven
  have hP2 : IsPGroup 2 ↥(P : Subgroup X) := P.isPGroup'
  haveI : Nontrivial ↥(P : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot (P : Subgroup X)).mpr hPne
  haveI hcenter_nt : Nontrivial ↥(Subgroup.center ↥(P : Subgroup X)) := hP2.center_nontrivial
  have hcenter2 : IsPGroup 2 ↥(Subgroup.center ↥(P : Subgroup X)) := hP2.to_subgroup _
  have hcenter2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(P : Subgroup X)) :=
    hcenter2.card_eq_or_dvd.resolve_left (by
      have := Finite.one_lt_card (α := ↥(Subgroup.center ↥(P : Subgroup X)))
      omega)
  obtain ⟨z, hz2⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(P : Subgroup X))) 2 hcenter2dvd
  let zP : ↥(P : Subgroup X) := (z : ↥(P : Subgroup X))
  have hzP_center : zP ∈ Subgroup.center ↥(P : Subgroup X) := z.2
  have hzP2 : orderOf zP = 2 := by
    have h := orderOf_injective (Subgroup.subtype (Subgroup.center ↥(P : Subgroup X)))
      (fun _ _ h => Subtype.ext h) z
    simpa [zP] using h.trans hz2
  set orbK : Set (Subgroup X) :=
    Set.range fun g : ↥(P : Subgroup X) => CFSG.conjugate K (g : X) with horbK
  set orbL : Set (Subgroup X) :=
    Set.range fun g : ↥(P : Subgroup X) => CFSG.conjugate L (g : X) with horbL
  have hKorb : ∀ N ∈ orbK, CFSG.IsComponent N := by
    intro N hN
    rw [horbK] at hN
    rcases hN with ⟨g, rfl⟩
    exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hK (g : X)
  have hLorb : ∀ N ∈ orbL, CFSG.IsComponent N := by
    intro N hN
    rw [horbL] at hN
    rcases hN with ⟨g, rfl⟩
    exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hL (g : X)
  have hLnotK : L ∉ orbK := by
    intro hL
    rw [horbK] at hL
    rcases hL with ⟨g, hg⟩
    exact hconj ⟨g, g.2, hg⟩
  have hz_cent : ∀ M : Subgroup X, CFSG.IsComponent M →
      (zP : X) ∈ Subgroup.centralizer (M : Set X) := by
    intro M hM
    by_cases hMK : M ∈ orbK
    · have hML : M ∉ orbL := by
        intro hML
        rw [horbL] at hML
        rcases hML with ⟨h, hh⟩
        beta_reduce at hh
        rw [horbK] at hMK
        rcases hMK with ⟨g, hg⟩
        beta_reduce at hg
        apply hLnotK
        rw [horbK]
        refine ⟨⟨g * h⁻¹, P.mul_mem g.2 (P.inv_mem h.2)⟩, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate, hg, ← hh,
          CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate_inv]
      have hEL_le : sSup orbL ≤ Subgroup.centralizer (M : Set X) := by
        have h := CFSG.ComponentClassification.UnbalancedLayer.sSup_le_centralizer_sSup
          hLorb (by intro N hN; rw [Set.mem_singleton_iff] at hN; rw [hN]; exact hM)
          (by
            intro N hN hNM
            rw [Set.mem_singleton_iff] at hNM
            exact hML (hNM ▸ hN))
        rwa [sSup_singleton] at h
      refine hEL_le ?_
      simpa [horbL] using
        central_involution_mem_orbitJoin hF P hZ zP hzP_center hzP2 hL
    · have hEK_le : sSup orbK ≤ Subgroup.centralizer (M : Set X) := by
        have h := CFSG.ComponentClassification.UnbalancedLayer.sSup_le_centralizer_sSup
          hKorb (by intro N hN; rw [Set.mem_singleton_iff] at hN; rw [hN]; exact hM)
          (by
            intro N hN hNM
            rw [Set.mem_singleton_iff] at hNM
            exact hMK (hNM ▸ hN))
        rwa [sSup_singleton] at h
      refine hEK_le ?_
      simpa [horbK] using
        central_involution_mem_orbitJoin hF P hZ zP hzP_center hzP2 hK
  have hz_layer : (zP : X) ∈ CFSG.layer X := by
    refine CFSG.ComponentClassification.UnbalancedLayer.sSup_le_layer hKorb ?_
    simpa [horbK] using central_involution_mem_orbitJoin hF P hZ zP hzP_center hzP2 hK
  have hz_center_layer : (zP : X) ∈ Subgroup.centralizer (CFSG.layer X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : CFSG.layer X ≤ Subgroup.centralizer ({(zP : X)} : Set X) := by
      rw [CFSG.layer.eq_sSup]
      refine sSup_le fun M hM => ?_
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hz_cent M hM) m hm
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) (zP : X)
      (Set.mem_singleton (zP : X))).symm
  have hz_center : (zP : X) ∈ (Subgroup.center ↥(CFSG.layer X)).map (CFSG.layer X).subtype := by
    rw [CFSG.LocalCores.mem_map_center_iff]
    exact ⟨hz_layer, hz_center_layer⟩
  have hz_fitting : (zP : X) ∈ CFSG.fittingSubgroup X :=
    center_layer_le_fitting' hz_center
  rw [hF, Subgroup.mem_bot] at hz_fitting
  have hzP1 : zP = 1 := Subtype.ext hz_fitting
  rw [hzP1, orderOf_one] at hzP2
  exact absurd hzP2 (by norm_num)

theorem ncard_setOf_isComponent_le_two (hF : CFSG.fittingSubgroup X = ⊥) (P : Sylow 2 X)
    (hZ : ∀ a ∈ Subgroup.center ↥(P : Subgroup X), ∀ b ∈ Subgroup.center ↥(P : Subgroup X),
      orderOf a = 2 → orderOf b = 2 → a = b)
    (hP : Nat.card (P : Subgroup X) ≤ 2 ^ 7) :
    {K : Subgroup X | CFSG.IsComponent K}.ncard ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let 𝒞 : Set (Subgroup X) := {K : Subgroup X | CFSG.IsComponent K}
  change 𝒞.ncard ≤ 2
  by_contra hle
  push_neg at hle
  have hne : 𝒞.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hle
    simp at hle
  obtain ⟨K, hK⟩ := hne
  have horbK : ({W : Subgroup X | ∃ g ∈ (P : Subgroup X), W = CFSG.conjugate K g} :
      Set (Subgroup X)) = 𝒞 := by
    ext W
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hK g
    · intro hW
      obtain ⟨g, hg, hg'⟩ := exists_mem_sylow_conjugate_eq_of_isComponent hF P hZ hK hW
      exact ⟨g, hg, hg'.symm⟩
  have hdvd : 𝒞.ncard ∣ Nat.card (P : Subgroup X) := by
    have h1 : ({W : Subgroup X | ∃ g ∈ (P : Subgroup X), W = CFSG.conjugate K g} :
        Set (Subgroup X)).ncard = (Subgroup.normalizer (K : Set X)).relIndex (P : Subgroup X) :=
      ncard_conjSet_eq_relIndex K (P : Subgroup X)
    rw [horbK] at h1
    rw [h1]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(P : Subgroup X))).mp P.isPGroup'
  have hdvd' : 𝒞.ncard ∣ 2 ^ m := by rwa [hm] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have h4 : 4 ≤ 𝒞.ncard := by
    have hle' : 2 < 2 ^ k := by rwa [hk] at hle
    have hk2 : 2 ≤ k := by
      by_contra h
      push_neg at h
      interval_cases k <;> norm_num at hle'
    rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hker : (CFSG.LocalCores.layerMul X).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    funext K'
    have h1 : x K' ∈ Subgroup.center ↥(K'.1) :=
      (Subgroup.mem_pi Set.univ).mp (CFSG.LocalCores.layerMul_ker_le (G := X) hx)
        K' (Set.mem_univ K')
    have h2 : Subgroup.center ↥(K'.1) = ⊥ := center_component_eq_bot' hF K'.2
    rw [h2, Subgroup.mem_bot] at h1
    exact h1
  have hinj : Function.Injective (CFSG.LocalCores.layerMul X) :=
    (MonoidHom.ker_eq_bot_iff (CFSG.LocalCores.layerMul X)).mp hker
  have hequiv : (∀ K' : CFSG.LocalCores.ComponentIndex X, ↥(K'.1)) ≃* ↥(CFSG.layer X) :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (CFSG.LocalCores.layerMul_range (G := X)))
  have hcard_layer : Nat.card ↥(CFSG.layer X) =
      ∏ K' : CFSG.LocalCores.ComponentIndex X, Nat.card ↥(K'.1) := by
    rw [← Nat.card_congr hequiv.toEquiv, Nat.card_pi]
  have hcardidx : Fintype.card (CFSG.LocalCores.ComponentIndex X) = 𝒞.ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  have h4comp : ∀ K' : CFSG.LocalCores.ComponentIndex X, 4 ∣ Nat.card ↥(K'.1) := by
    intro K'
    obtain ⟨hsimple, hna⟩ := component_isSimple' hF K'.2
    haveI : IsSimpleGroup ↥(K'.1) := hsimple
    exact CFSG.GH74.GLS.TwoThin.four_dvd_card_of_simple_nonabelian hna
  have h4prod : 4 ^ Fintype.card (CFSG.LocalCores.ComponentIndex X) ∣
      ∏ K' : CFSG.LocalCores.ComponentIndex X, Nat.card ↥(K'.1) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun K' _ => h4comp K')
  have h2layer : 2 ^ 8 ∣ Nat.card ↥(CFSG.layer X) := by
    rw [hcard_layer]
    refine dvd_trans ?_ h4prod
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_dvd_pow 2 (by rw [hcardidx]; omega)
  have h8X : 2 ^ 8 ∣ Nat.card X :=
    h2layer.trans (Subgroup.card_subgroup_dvd_card (CFSG.layer X))
  have h8P : 2 ^ 8 ∣ Nat.card (P : Subgroup X) := P.pow_dvd_card_of_pow_dvd_card h8X
  have hPpos : 0 < Nat.card (P : Subgroup X) := Nat.card_pos
  have h256 : 2 ^ 8 ≤ Nat.card (P : Subgroup X) := Nat.le_of_dvd hPpos h8P
  omega

theorem nonempty_mulEquiv_prod_of_components_eq_pair (hF : CFSG.fittingSubgroup X = ⊥)
    {K L : Subgroup X} (hKL : K ≠ L) (hall : {M : Subgroup X | CFSG.IsComponent M} = {K, L}) :
    Nonempty (↥(CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X)) ≃* ↥K × ↥L) := by
  have hK : CFSG.IsComponent K := by
    have : K ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
      rw [hall]; simp
    simpa using this
  have hL : CFSG.IsComponent L := by
    have : L ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
      rw [hall]; simp
    simpa using this
  have hE : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X) = K ⊔ L := by
    rw [CFSG.Walter.componentLayerOf_top_eq_layer X, CFSG.layer.eq_sSup, hall, sSup_pair]
  rw [hE]
  obtain ⟨hcomm, hinf⟩ := components_commute_inf' hF hK hL hKL
  exact CFSG.Quasithin.sup_mulEquiv_prod hcomm hinf

theorem componentLayerOf_top_eq_of_components_eq_singleton
    (hF : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X}
    (hall : {M : Subgroup X | CFSG.IsComponent M} = {K}) :
    CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X) = K ∧ K.Normal ∧
      Subgroup.centralizer (K : Set X) = ⊥ := by
  have hK : CFSG.IsComponent K := by
    have : K ∈ ({M : Subgroup X | CFSG.IsComponent M} : Set (Subgroup X)) := by
      rw [hall]; simp
    simpa using this
  have hlayer : CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X) = K := by
    rw [CFSG.Walter.componentLayerOf_top_eq_layer X, CFSG.layer.eq_sSup, hall, sSup_singleton]
  have hKnorm : K.Normal := by
    rw [← hlayer, CFSG.Walter.componentLayerOf_top_eq_layer X]
    haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hFstar : CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup X) = K := by
    rw [CFSG.GorensteinWalter.generalizedFittingSubgroupOf,
      show CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup X) = CFSG.fittingSubgroupOf ⊤
        from rfl,
      CFSG.Adapters.fittingSubgroupOf_top_eq_foundations, hF, bot_sup_eq, hlayer]
  have hBender : Subgroup.centralizer (K : Set X) ≤ K := by
    rw [← hFstar]
    exact CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (G := X)
  have hcent : Subgroup.centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hBender hx
    have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [center_component_eq_bot' hF hK, Subgroup.mem_bot] at hxZ
    simpa using Subtype.ext_iff.mp hxZ
  exact ⟨hlayer, hKnorm, hcent⟩

end CFSG.EvenSporadicStandard.TwoHS.GH312
