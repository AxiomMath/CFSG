module

public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor
public import CFSG.LocalAnalysis.ComponentInitial.ComponentTypeLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentInitial.BlockTransporter

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Bridges

variable {X : Type*} [Group X]

theorem assembly_isSubnormal_iff_subgroupOf {K H : Subgroup X} (hKH : K ≤ H) :
    CFSG.Assembly.IsSubnormal K H ↔ (K.subgroupOf H).IsSubnormal :=
  CFSG.Assembly.IsSubnormal.iff_subgroupOf hKH

theorem isTwoPComponent_iff_isPComponent (L : Subgroup X) :
    CFSG.Assembly.ComponentType.IsTwoPComponent L ↔ CFSG.IsPComponent 2 L := by
  have key : ∀ (N : Subgroup X) [N.Normal], N = pPrimeCore 2 X →
      ((∃ K : Subgroup (X ⧸ N), CFSG.Assembly.IsComponentOf K ⊤ ∧
        CFSG.Assembly.IsSubnormal L ⊤ ∧ L.map (QuotientGroup.mk' N) = K ∧
        ∀ J : Subgroup X, J < L → CFSG.Assembly.IsSubnormal J ⊤ →
          J.map (QuotientGroup.mk' N) ≠ K) ↔ CFSG.IsPComponent 2 L) := by
    rintro N _ rfl
    unfold CFSG.IsPComponent
    simp only [AssemblyBPredicates.isComponentOf_top_iff_native,
      AssemblyBPredicates.isSubnormal_top_iff_mathlib]
  exact key _ assembly_oddCore_eq_pPrimeCore

theorem layer_eq_bot_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (hX : layer X = ⊥) :
    layer Y = ⊥ := by
  refine sSup_eq_bot.2 fun K hK => ?_
  have hK' : CFSG.IsComponent K := hK
  have hK'' : CFSG.IsComponent (K.map e.symm.toMonoidHom) := (isComponent_map_iff e.symm K).2 hK'
  have hle : K.map e.symm.toMonoidHom ≤ layer X := le_sSup hK''
  rw [hX, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at hle
  exact hle

theorem layer_eq_bot_iff_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) :
    layer X = ⊥ ↔ layer Y = ⊥ :=
  ⟨layer_eq_bot_of_mulEquiv e, layer_eq_bot_of_mulEquiv e.symm⟩

theorem two_components_ordinary_of_localB {G : Type*} [Group G] [Finite G]
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {S0 F : Subgroup G} (hS0 : S0 ≠ ⊥)
    (hS02 : IsPGroup 2 S0) (hFN : F ≤ normalizer (S0 : Set G))
    (hsub : CFSG.Assembly.IsSubnormal F (normalizer (S0 : Set G))) :
    ∀ L : Subgroup F, CFSG.IsPComponent 2 L → CFSG.IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF'sub : (F.subgroupOf (normalizer (S0 : Set G))).IsSubnormal :=
    (assembly_isSubnormal_iff_subgroupOf hFN).1 hsub
  let e : F ≃* F.subgroupOf (normalizer (S0 : Set G)) := (Subgroup.subgroupOfEquivOfLe hFN).symm
  intro L hL
  have hL' : CFSG.IsPComponent 2 (L.map e.toMonoidHom) := isPComponent_map_of_isPComponent 2 e hL
  have hL'' := CatalogueBPrimeJoin.pComponent_extend_subnormal 2 _ hF'sub _ hL'
  have hcomp := hB S0 hS0 hS02 _ ((isTwoPComponent_iff_isPComponent _).2 hL'')
  have hle : (L.map e.toMonoidHom).map (F.subgroupOf (normalizer (S0 : Set G))).subtype ≤
      F.subgroupOf (normalizer (S0 : Set G)) := map_subtype_le _
  have hcompF := isComponentOf_of_le hcomp hle le_top
  rw [isComponentOf_iff_isComponent_subgroupOf hle] at hcompF
  have hsub_eq : ((L.map e.toMonoidHom).map
      (F.subgroupOf (normalizer (S0 : Set G))).subtype).subgroupOf
        (F.subgroupOf (normalizer (S0 : Set G))) = L.map e.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [hsub_eq] at hcompF
  exact (isComponent_map_iff e L).1 hcompF

end Bridges

section Normalizers

variable {G : Type*} [Group G]

theorem mem_normalizer_iSup {ι : Type*} {K : ι → Subgroup G} {g : G}
    (h : ∀ j, g ∈ normalizer (K j : Set G)) : g ∈ normalizer ((⨆ j, K j : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conjSub_le ?_ ?_
  · rw [conjSub, Subgroup.map_iSup]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_of_mem_normalizer (h j))
  · rw [conjSub, Subgroup.map_iSup]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_of_mem_normalizer (inv_mem (h j)))

theorem mem_normalizer_inf {X Y : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hY : g ∈ normalizer (Y : Set G)) : g ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hX hY ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hX, hY]

theorem normal_centralizer_subgroupOf_normalizer (S : Subgroup G) :
    ((centralizer (S : Set G)).subgroupOf (normalizer (S : Set G))).Normal := by
  rw [normal_subgroupOf_iff (centralizer_le_normalizer _)]
  intro h k hh hk
  have hS : conjSub k S = S := conjSub_eq_of_mem_normalizer hk
  have := conj_mem_centralizer_conjSub hh k
  rwa [hS] at this

end Normalizers

theorem original_three_factor_empty_fixed_layer_core_configuration {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (_hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J)
    (A : Fin 3 → Subgroup G) (hAinj : Function.Injective A) (hΔ : block J = Set.range A)
    (hC0 : 2 ≤ CFSG.pRank 2 ↥(⨅ i, A i)) {u v : G} (hu : orderOf u = 2) (_hv : orderOf v = 2)
    (_huH : u ∈ normalizer (blockGroup J : Set G)) (_hvH : v ∉ normalizer (blockGroup J : Set G))
    (_huv : u * v = v * u) (hunorm : ∀ i, u ∈ normalizer (A i : Set G))
    (hucent : ∀ i, u ∉ centralizer (A i : Set G))
    (hE : ∀ i, layer ↥(A i ⊓ centralizer ({u} : Set G)) = ⊥) :
    (∀ i, FixedFactorConclusions (A i) (hunorm i)) ∧
      ∃ E0 : Subgroup G, (E0 : Set G) = {z | z ∈ ⨅ i, A i ∧ z ^ 2 = 1 ∧ z * u = u * z} ∧
        E0 ≠ ⊥ ∧ IsElementaryAbelian 2 E0 ∧
        ∀ i, let B := fixedSubgroup (conjAut (A i) (hunorm i))
          let R := pPrimeCore 2 B
          let P := pCore 2 (B ⧸ R)
          let E0i := E0.comap ((A i).subtype.comp B.subtype)
          E0 ≤ B.map (A i).subtype ∧ Function.Injective ((QuotientGroup.mk' R).comp E0i.subtype) ∧
            E0i.map (QuotientGroup.mk' R) ≤ (center P).map P.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C0 := ⨅ i, A i with hC0def
  have hAblock : ∀ i, A i ∈ block J := fun i => hΔ ▸ Set.mem_range_self i
  have hAq : ∀ i, CFSG.Assembly.IsQuasisimple (A i) := fun i =>
    isQuasisimple_of_isConjOf hq (hAblock i).1
  have hcommA : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥ := by
    intro i j hij
    rcases commRel_of_mem_block hJ heven (hAblock i) (hAblock j) with h | h
    · exact absurd (hAinj h) hij
    · exact h
  have hother : ∀ i : Fin 3, ∃ j, j ≠ i := fun i => ⟨i + 1, by fin_cases i <;> decide⟩
  have hC0cent : ∀ i, C0 ≤ centralizer (A i : Set G) := by
    intro i x hx
    obtain ⟨j, hj⟩ := hother i
    have hxj : x ∈ A j := Subgroup.mem_iInf.1 hx j
    rw [mem_centralizer_iff]
    intro y hy
    exact (commute_of_commutator_eq_bot (hcommA j i hj) hxj hy).symm
  have hC0comm : ∀ x ∈ C0, ∀ y ∈ C0, Commute x y := fun x hx y hy =>
    (mem_centralizer_iff.1 (hC0cent 0 hx) y (Subgroup.mem_iInf.1 hy 0)).symm
  have hu' : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
  have huC0 : ∀ z ∈ C0, u * z * u⁻¹ ∈ C0 := fun z hz => Subgroup.mem_iInf.2 fun i =>
    (mem_normalizer_iff.1 (hunorm i) z).1 (Subgroup.mem_iInf.1 hz i)
  let E : Subgroup G :=
    { carrier := {z | z ∈ C0 ∧ z ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(hC0comm x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hmemE : ∀ z, z ∈ E ↔ z ∈ C0 ∧ z ^ 2 = 1 := fun z => Iff.rfl
  have hEu : E.map (MulAut.conj u).toMonoidHom = E := by
    have hle : ∀ z ∈ E, u * z * u⁻¹ ∈ E := fun z hz => (hmemE _).2
      ⟨huC0 z ((hmemE z).1 hz).1, by
        rw [show u * z * u⁻¹ = (MulAut.conj u) z by simp, ← map_pow, ((hmemE z).1 hz).2,
          map_one]⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simpa using hle z hz
    · intro z hz
      refine ⟨u * z * u⁻¹, hle z hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hu']
      have h1 : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
      calc u * (u * z * u) * u = (u * u) * z * (u * u) := by group
        _ = z := by rw [h1, one_mul, mul_one]
  let eu : MulAut E := restrictAut (MulAut.conj u) E hEu
  have heu : ∀ x, eu (eu x) = x := by
    intro x
    apply Subtype.ext
    change u * (u * x * u⁻¹) * u⁻¹ = x
    rw [hu']
    have h1 : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [h1, one_mul, mul_one]
  set E0 := E ⊓ centralizer ({u} : Set G) with hE0def
  have hmemE0 : ∀ z, z ∈ E0 ↔ z ∈ C0 ∧ z ^ 2 = 1 ∧ z * u = u * z := by
    intro z
    rw [Subgroup.mem_inf, hmemE, mem_centralizer_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, (h3 u rfl).symm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact h3.symm
  have hEeven : Even (Nat.card E) := by
    obtain ⟨r, hr, V, hVel, hVcard⟩ : ∃ r, 2 ≤ r ∧ ∃ V : Subgroup C0,
        IsElementaryAbelian 2 V ∧ Nat.card V = 2 ^ r := by
      set S := {r : ℕ | ∃ V : Subgroup C0, IsElementaryAbelian 2 V ∧ Nat.card V = 2 ^ r}
      have hS0 : (0 : ℕ) ∈ S := by
        refine ⟨⊥, ?_, by simp⟩
        exact { toIsMulCommutative := ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
                exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
                  Subsingleton.elim _ _ }
      have hSbdd : BddAbove S := by
        refine ⟨Nat.card C0, fun r hr => ?_⟩
        obtain ⟨V, _, hV⟩ := hr
        have h1 : 2 ^ r ≤ Nat.card C0 := hV ▸ Subgroup.card_le_card_group V
        exact (Nat.lt_two_pow_self).le.trans h1
      have hmem := Nat.sSup_mem ⟨0, hS0⟩ hSbdd
      exact ⟨_, hC0, hmem⟩
    have hVE : V.map C0.subtype ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      refine (hmemE _).2 ⟨x.2, ?_⟩
      have := hVel
      have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
      exact congrArg Subtype.val hx2
    have h2V : 2 ∣ Nat.card ↥(V.map C0.subtype) := by
      rw [Subgroup.card_map_of_injective C0.subtype_injective, hVcard]
      exact dvd_pow_self 2 (by omega)
    exact even_iff_two_dvd.2 (h2V.trans (Subgroup.card_dvd_of_le hVE))
  have hfixE : (fixedSubgroup eu).map E.subtype = E0 := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      have h := congrArg Subtype.val (show eu y = y from hy)
      change u * y * u⁻¹ = y at h
      calc u * (y : G) = u * y * u⁻¹ * u := by group
        _ = y * u := by rw [h]
    · intro hz
      obtain ⟨hzE, hzu⟩ := Subgroup.mem_inf.1 hz
      refine ⟨⟨z, hzE⟩, ?_, rfl⟩
      change eu ⟨z, hzE⟩ = ⟨z, hzE⟩
      apply Subtype.ext
      change u * z * u⁻¹ = z
      rw [mem_centralizer_iff.1 hzu u rfl, mul_inv_cancel_right]
  have hE0card : Nat.card E0 = Nat.card (fixedSubgroup eu) := by
    rw [← hfixE, Subgroup.card_map_of_injective E.subtype_injective]
  have hE0even : Even (Nat.card E0) := by
    have hmod := card_modEq_card_fixedSubgroup eu heu
    rw [hE0card, Nat.even_iff]
    rw [Nat.even_iff] at hEeven
    rw [Nat.ModEq] at hmod
    omega
  have hE0ne : E0 ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE0even
    exact Nat.not_even_one hE0even
  have hE0el : IsElementaryAbelian 2 E0 :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext ((hC0comm x ((hmemE0 x).1 x.2).1 y
        ((hmemE0 y).1 y.2).1).eq)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z =>
        Subtype.ext (by simpa using ((hmemE0 z).1 z.2).2.1) }
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE0ne
  obtain ⟨hcC0, hc2, hcu⟩ := (hmemE0 c).1 c.2
  have hc1' : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcord : orderOf (c : G) = 2 := orderOf_eq_prime hc2 hc1'
  have hcA : ∀ i, (c : G) ∈ centralizer (A i : Set G) := fun i => hC0cent i hcC0
  have hcAi : ∀ i, (c : G) ∈ A i := fun i => Subgroup.mem_iInf.1 hcC0 i
  have hcu_ne : (c : G) ≠ u := fun h => hucent 0 (h ▸ hcA 0)
  set S0 := Subgroup.closure ({u, (c : G)} : Set G) with hS0def
  have hmemW : ∀ g, g ∈ centralizer (S0 : Set G) ↔ g * u = u * g ∧ g * c = c * g := by
    intro g
    rw [hS0def, Subgroup.centralizer_closure, mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨(h u (by simp)).symm, (h c (by simp)).symm⟩
    · rintro ⟨h1, h2⟩ w hw
      rcases hw with rfl | rfl
      · exact h1.symm
      · exact h2.symm
  have hS0comm : S0 ≤ centralizer (S0 : Set G) := by
    rw [hS0def, Subgroup.closure_le]
    rintro w hw
    rw [SetLike.mem_coe, hmemW]
    rcases hw with rfl | rfl
    · exact ⟨rfl, hcu.symm⟩
    · exact ⟨hcu, rfl⟩
  have hS0sq : ∀ g ∈ S0, g ^ 2 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [← hu, pow_orderOf_eq_one]
      · exact hc2
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := (mem_centralizer_iff.1 (hS0comm hy) x hx)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hS02 : IsPGroup 2 S0 := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hS0sq g g.2, OneMemClass.coe_one])⟩
  have hS0ne : S0 ≠ ⊥ := by
    intro h
    have hu0 : u ∈ S0 := Subgroup.subset_closure (by simp)
    rw [h, mem_bot] at hu0
    rw [hu0, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hAM : ∀ j, A j ≤ blockGroup J := fun j => le_blockGroup (hAblock j)
  have hMnormA : ∀ j, blockGroup J ≤ normalizer (A j : Set G) := fun j =>
    (normal_subgroupOf_iff_le_normalizer (hAM j)).1 (normal_of_mem_block hJ heven (hAblock j))
  have hMc : blockGroup J ≤ centralizer ({(c : G)} : Set G) := by
    refine iSup₂_le fun K hK => ?_
    rw [hΔ] at hK
    obtain ⟨j, rfl⟩ := hK
    intro x hx
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact (mem_centralizer_iff.1 (hcA j) x hx).symm
  have hCcH : centralizer ({(c : G)} : Set G) ≤ normalizer (blockGroup J : Set G) :=
    centralizer_le_normalizer_blockGroup hJ heven (hAblock 0) (hcA 0) hcord
  have hchain : ∀ i, CFSG.Assembly.IsSubnormal (A i ⊓ centralizer ({u} : Set G))
      (normalizer (S0 : Set G)) ∧ A i ⊓ centralizer ({u} : Set G) ≤ normalizer (S0 : Set G) := by
    intro i
    set F := ⨆ j, (A j ⊓ centralizer ({u} : Set G)) with hF
    set N := blockGroup J ⊓ centralizer ({u} : Set G) with hN
    have h1 : A i ⊓ centralizer ({u} : Set G) ≤ F :=
      le_iSup (fun j => A j ⊓ centralizer ({u} : Set G)) i
    have h1n : ((A i ⊓ centralizer ({u} : Set G)).subgroupOf F).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer h1]
      refine iSup_le fun j => ?_
      rcases eq_or_ne j i with rfl | hji
      · exact le_normalizer
      · refine le_trans ?_ (centralizer_le_normalizer _)
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact (commute_of_commutator_eq_bot (hcommA j i hji) (Subgroup.mem_inf.1 hx).1
          (Subgroup.mem_inf.1 hy).1).symm
    have h2 : F ≤ N := iSup_le fun j => inf_le_inf_right _ (hAM j)
    have h2n : (F.subgroupOf N).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer h2]
      intro n hn
      exact mem_normalizer_iSup fun j => mem_normalizer_inf (hMnormA j (Subgroup.mem_inf.1 hn).1)
        (le_normalizer (Subgroup.mem_inf.1 hn).2)
    have h3 : N ≤ centralizer (S0 : Set G) := by
      intro n hn
      obtain ⟨hnM, hnu⟩ := Subgroup.mem_inf.1 hn
      rw [hmemW]
      exact ⟨mem_centralizer_iff.1 hnu u rfl |>.symm, mem_centralizer_iff.1 (hMc hnM) c rfl |>.symm⟩
    have h3n : (N.subgroupOf (centralizer (S0 : Set G))).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer h3]
      intro w hw
      obtain ⟨hwu, hwc⟩ := (hmemW w).1 hw
      have hwc' : w ∈ centralizer ({(c : G)} : Set G) := by
        rw [mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact hwc.symm
      have hwu' : w ∈ centralizer ({u} : Set G) := by
        rw [mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact hwu.symm
      exact mem_normalizer_inf (hCcH hwc') (le_normalizer hwu')
    have h4 : centralizer (S0 : Set G) ≤ normalizer (S0 : Set G) := centralizer_le_normalizer _
    have h4n := normal_centralizer_subgroupOf_normalizer S0
    refine ⟨CFSG.Assembly.IsSubnormal.step h1 h1n (CFSG.Assembly.IsSubnormal.step h2 h2n
      (CFSG.Assembly.IsSubnormal.step h3 h3n (CFSG.Assembly.IsSubnormal.step h4 h4n
        (CFSG.Assembly.IsSubnormal.refl _)))), h1.trans (h2.trans (h3.trans h4))⟩
  have hfactor : ∀ i, let B := fixedSubgroup (conjAut (A i) (hunorm i))
      layer B = ⊥ ∧ (∀ L : Subgroup B, CFSG.IsPComponent 2 L → CFSG.IsComponent L) ∧
        Even (Nat.card B) := by
    intro i B
    let e : B ≃* ↥(A i ⊓ centralizer ({u} : Set G)) :=
      (B.equivMapOfInjective (A i).subtype (A i).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_fixed_conjAut (hunorm i)))
    have hEi : layer B = ⊥ := (layer_eq_bot_iff_of_mulEquiv e).2 (hE i)
    have h2F := two_components_ordinary_of_localB hB hS0ne hS02 (hchain i).2 (hchain i).1
    have h2B : ∀ L : Subgroup B, CFSG.IsPComponent 2 L → CFSG.IsComponent L := fun L hL =>
      (isComponent_map_iff e L).1 (h2F _ (isPComponent_map_of_isPComponent 2 e hL))
    have hBeven : Even (Nat.card B) := by
      have hord : orderOf (⟨⟨c, hcAi i⟩, by
          change conjAut (A i) (hunorm i) ⟨c, hcAi i⟩ = ⟨c, hcAi i⟩
          apply Subtype.ext
          rw [coe_conjAut, ← hcu, mul_inv_cancel_right]⟩ : B) = 2 := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact hcord
      exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard _)
    exact ⟨hEi, h2B, hBeven⟩
  refine ⟨fun i => ?_, E0, ?_, hE0ne, hE0el, fun i => ?_⟩
  · obtain ⟨hEi, h2B, hBeven⟩ := hfactor i
    exact fixedFactorConclusions_of (hAq i) hu (hunorm i) (hucent i) hEi h2B hBeven
  · ext z
    exact hmemE0 z
  · intro B R P E0i
    obtain ⟨hEi, h2B, -⟩ := hfactor i
    obtain ⟨-, -, -, -, -, -, -, -, -, hcentral, -, -, -⟩ :=
      empty_layer_ordinary_two_components_force_characteristic_two_quotient h2B hEi
    have hE0B : E0 ≤ B.map (A i).subtype := by
      rw [map_fixed_conjAut]
      intro z hz
      obtain ⟨hzC0, -, hzu⟩ := (hmemE0 z).1 hz
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.1 hzC0 i, ?_⟩
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact hzu.symm
    have hE0cent : E0i ≤ center B := by
      intro w hw
      have hw' := (hmemE0 _).1 hw
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subtype.ext (mem_centralizer_iff.1 (hC0cent i hw'.1) _ (y : A i).2))
    have hE02 : IsPGroup 2 E0i := fun w => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [pow_one]
      exact ((hmemE0 _).1 w.2).2.1⟩
    exact ⟨hE0B, hcentral E0i hE0cent hE02⟩

end CFSG.LocalAnalysis.ComponentInitial
