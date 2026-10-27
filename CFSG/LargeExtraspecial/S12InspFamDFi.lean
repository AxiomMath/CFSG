module

public import CFSG.LargeExtraspecial.S12InspFamDK
public import CFSG.LargeExtraspecial.S12InspFamSix
public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Open

theorem s12_not_isSolvable_quotient_center {C : Type*} [Group C] [Finite C]
    (hC : commutator C = ⊤) (hZ : Nat.card (center C) = 2) :
    ¬ Group.IsSolvable (C ⧸ center C) := by
  intro hs
  have : Group.IsSolvable (center C) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext ((mem_center_iff.mp a.2) b).symm
  have hCs : Group.IsSolvable C := Group.isSolvable_of_ker_le_range (center C).subtype
    (QuotientGroup.mk' (center C)) (by rw [QuotientGroup.ker_mk', range_subtype])
  have : Nontrivial (center C) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Nontrivial C := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (center C)
    exact ⟨⟨a, b, fun h => hab (Subtype.ext h)⟩⟩
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial C
  rw [hC] at this
  exact lt_irrefl _ this

theorem s12_not_isSolvable_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ¬ (Nat.card L).Prime) : ¬ Group.IsSolvable L := fun hs => by
  obtain ⟨a, b, hab⟩ :=
    CFSG.Fischer.Classification.Recognition.exists_not_commute_of_isSimpleGroup hL
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b)

theorem s12_mul_comm_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {k : B}
    (h : ∀ x : A, e.symm k * x = x * e.symm k) (x : B) : k * x = x * k := by
  have := congrArg e (h (e.symm x))
  simpa using this

instance s12_normal_zpowers_subgroupOf_centralizer {X : Type*} [Group X] (d : X) :
    ((zpowers d).subgroupOf (centralizer ({d} : Set X))).Normal := by
  constructor
  intro n hn c
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
  have hc : (c : X) * d = d * c := mem_centralizer_singleton_iff.mp c.2
  have hck : Commute (c : X) (d ^ k) := (Commute.zpow_right hc k)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk]
  rw [hck.eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers d) k

theorem s12_zpowers_subgroupOf_central {X : Type*} [Group X] (d : X) :
    ∀ n ∈ (zpowers d).subgroupOf (centralizer ({d} : Set X)),
      ∀ x : centralizer ({d} : Set X), n * x = x * n := by
  intro n hn x
  rw [mem_subgroupOf] at hn
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
  have hx : (x : X) * d = d * x := mem_centralizer_singleton_iff.mp x.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
  exact ((Commute.zpow_right hx k).symm).eq

theorem s12_nonempty_mulEquiv_quotient_zpowers {X : Type*} [Group X] {d : X}
    {L : Subgroup X} (hCL : centralizer ({d} : Set X) = zpowers d ⊔ L)
    (hinf : zpowers d ⊓ L = ⊥) :
    Nonempty (L ≃* centralizer ({d} : Set X) ⧸ (zpowers d).subgroupOf (centralizer {d})) := by
  have hdC : zpowers d ≤ centralizer ({d} : Set X) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hLC : L ≤ centralizer ({d} : Set X) := hCL ▸ le_sup_right
  let ι : L →* centralizer ({d} : Set X) ⧸ (zpowers d).subgroupOf (centralizer {d}) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hLC)
  have hι : Function.Bijective ι := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
      have : (x : X) ∈ zpowers d ⊓ L := ⟨hx, x.2⟩
      rw [hinf, mem_bot] at this
      exact (mem_bot).mpr (Subtype.ext this)
    · rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range]
      have htop : L.subgroupOf (centralizer {d}) ⊔ (zpowers d).subgroupOf (centralizer {d}) =
          ⊤ := by
        rw [sup_comm, ← subgroupOf_sup hdC hLC, ← hCL, subgroupOf_self]
      have h1 := congrArg (Subgroup.map
        (QuotientGroup.mk' ((zpowers d).subgroupOf (centralizer ({d} : Set X))))) htop
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, ← MonoidHom.range_eq_map,
        QuotientGroup.range_mk'] at h1
  exact ⟨MulEquiv.ofBijective ι hι⟩

theorem s12_fi24_quotient_facts {X : Type*} [Group X] {d : X} {L : Subgroup X}
    (hCL : centralizer ({d} : Set X) = zpowers d ⊔ L) (hinf : zpowers d ⊓ L = ⊥)
    (eL : L ≃* CFSG.Blueprint.NativeSporadic.Fi23) :
    IsSimpleGroup (centralizer ({d} : Set X) ⧸ (zpowers d).subgroupOf (centralizer {d})) ∧
      ¬ Group.IsSolvable
        (centralizer ({d} : Set X) ⧸ (zpowers d).subgroupOf (centralizer {d})) := by
  obtain ⟨e₁⟩ := s12_nonempty_mulEquiv_quotient_zpowers hCL hinf
  have : IsSimpleGroup L :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 eL
  have hs : IsSimpleGroup
      (centralizer ({d} : Set X) ⧸ (zpowers d).subgroupOf (centralizer {d})) :=
    e₁.symm.isSimpleGroup
  refine ⟨hs, fun hsol => ?_⟩
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
  obtain ⟨a, b, hab⟩ :=
    @CFSG.Fischer.Classification.Recognition.exists_not_commute_of_isSimpleGroup _ _
      CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
      CFSG.Fischer.Classification.Recognition.card_Fi23_not_prime
  apply hab
  apply (eL.symm.trans e₁).injective
  rw [map_mul, map_mul, hcomm]

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem fischer_data_Xbar12 (hTri : FischerTrialityInput) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hdeg : ¬ S.IsNondeg12 g) :
    (∃ d₀ : S.Xbar12 g, (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) = {x | IsConj d₀ x}) ∧
      (∀ d ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)), orderOf d = 2) ∧
      (∀ d ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
        ∀ e ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
          orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∧
      closure (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) = ⊤ ∧
      center (S.Xbar12 g) = ⊥ ∧ IsSimpleGroup (commutator (S.Xbar12 g)) := by
  have hD := transpositionData_Xbar12 S14.rootInvolutionComponentsInput ht htA hS
  have hclass : ∃ d₀ : S.Xbar12 g,
      (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) = {x | IsConj d₀ x} :=
    ⟨hD.t', hD.preimage_eq_isConj⟩
  have hinv : ∀ d ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)), orderOf d = 2 := by
    intro d hd
    refine orderOf_eq_prime ?_ fun h => hD.ne_one _ hd (congrArg Subtype.val h)
    rw [pow_two]
    exact hD.invol' hd
  have hprod : ∀ d ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
      ∀ e ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
    intro d hd e he
    have hle : orderOf (d * e) ≤ 4 := by
      rw [s12_orderOf_mul_coe]
      exact hD.ord _ hd _ he
    have hne4 : orderOf (d * e) ≠ 4 := by
      rw [s12_orderOf_mul_coe]
      exact fun h => hdeg ⟨_, hd, _, he, h⟩
    have hpos : 0 < orderOf (d * e) := orderOf_pos _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hgen := s12_closure_preimage_eq_top hD.gen
  have hcenter := s12_center_eq_bot hS.center_trivial
  have hP : CFSG.Blueprint.Fischer.Pair (S.Xbar12 g)
      (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) :=
    ⟨inferInstance, hclass, hinv, hprod, hgen⟩
  have h2 : ∀ N : Subgroup (S.Xbar12 g), N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot (fun P h1 h2 h3 => noNormalTwo_Xbar12 P h1 h2 h3) N hN hp
  have h3 : ∀ N : Subgroup (S.Xbar12 g), N.Normal → IsPGroup 3 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot hS.core3_trivial N hN hp
  refine ⟨hclass, hinv, hprod, hgen, hcenter, ?_⟩
  by_cases hcos : ∀ d ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
      ∀ e ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
        d * e ∈ fischerQ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
  · exact (isSimpleGroup_commutator_iff hP hcenter h2 h3).2 hcos
  · exfalso
    push Not at hcos
    obtain ⟨hns, hno2⟩ := hTri (S.Xbar12 g) _ hP hcenter h2 h3 hcos hD.t' hD.mem
    have hmap : (fischerQ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⊓
        centralizer {hD.t'}).map (S.Xbar12 g).subtype =
        fischerQ (S.Ebar12 g) ⊓ centralizer {t} :=
      map_subtype_fischerQ_inf_centralizer hD.subset hD.t'
    have hsol := isSolvable_fischerQ_inf_centralizer haQ hne hn ht htA
      (hmap ▸ hno2.map_subtype)
    rw [← hmap] at hsol
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := ((fischerQ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⊓
        centralizer {hD.t'}).equivMapOfInjective (S.Xbar12 g).subtype
          (S.Xbar12 g).subtype_injective).toMonoidHom) (MulEquiv.injective _))

theorem centralizer_map_props {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (ht : t ∈ S.Lbar g) (htX : t ∈ S.Xbar12 g) {K : Subgroup S.O}
    (hKdef : K = (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)).map
      (S.Xbar12 g).subtype) :
    K ≤ S.Mbar ∧ (∀ c ∈ K, c * t = t * c) ∧ ∀ ℓ ∈ S.Lbar g, ∀ c ∈ K, ℓ * c * ℓ⁻¹ ∈ K := by
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hKt : ∀ c ∈ K, c * t = t * c := by
    rw [hKdef]
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    simpa using this
  refine ⟨hKdef ▸ (map_subtype_le _).trans Xbar12_le_Mbar, hKt, ?_⟩
  intro ℓ hℓ c hc
  rw [hKdef] at hc ⊢
  obtain ⟨x, hx, rfl⟩ := hc
  have hxX : ℓ * (x : S.O) * ℓ⁻¹ ∈ S.Xbar12 g :=
    (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 (S.Lbar_le_Mbar g hℓ)) x).mp x.2
  refine ⟨⟨_, hxX⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
  have hxt : (x : S.O) * t = t * x := hKt _ (hKdef ▸ ⟨x, hx, rfl⟩)
  have hℓt := hcomm hℓ
  have hℓt' : ℓ⁻¹ * t = t * ℓ⁻¹ := by
    calc ℓ⁻¹ * t = ℓ⁻¹ * (t * ℓ) * ℓ⁻¹ := by group
      _ = ℓ⁻¹ * (ℓ * t) * ℓ⁻¹ := by rw [hℓt]
      _ = t * ℓ⁻¹ := by group
  simp only [Subgroup.coe_mul]
  calc ℓ * (x : S.O) * ℓ⁻¹ * t = ℓ * x * (ℓ⁻¹ * t) := by group
    _ = ℓ * (x * t) * ℓ⁻¹ := by rw [hℓt']; group
    _ = ℓ * (t * x) * ℓ⁻¹ := by rw [hxt]
    _ = (ℓ * t) * x * ℓ⁻¹ := by group
    _ = t * (ℓ * x * ℓ⁻¹) := by rw [hℓt]; group

theorem s12_exists_hom_of_mulEquiv {A K H : Type*} [Group A] [Group K] [Group H] (e : A ≃* K)
    (ρ : A →* H) (hρ : Function.Surjective ρ) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) :
    ∃ ρ' : K →* H, Function.Surjective ρ' ∧ ∀ k ∈ ρ'.ker, ∀ x, k * x = x * k := by
  refine ⟨ρ.comp e.symm.toMonoidHom, hρ.comp e.symm.surjective, fun k hk x => ?_⟩
  have hk' : e.symm k ∈ ρ.ker := hk
  exact s12_mul_comm_of_mulEquiv e (hker _ hk') x

theorem false_of_centralizer_hom_simple {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)) →* H)
    (hρ : Function.Surjective ρ) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup S.O,
      K = (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)).map
        (S.Xbar12 g).subtype := ⟨_, rfl⟩
  obtain ⟨hKM, hKt, hconj⟩ := centralizer_map_props haQ ht htX hKdef
  obtain ⟨e⟩ : Nonempty ((centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)) ≃* K) :=
    ⟨((centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)).equivMapOfInjective
      (S.Xbar12 g).subtype (S.Xbar12 g).subtype_injective).trans
        (MulEquiv.subgroupCongr hKdef.symm)⟩
  have hLK : S.Lbar g ≤ normalizer (K : Set S.O) := fun ℓ hℓ =>
    mem_normalizer_of_conj_le (hconj ℓ hℓ) (hconj ℓ⁻¹ ((S.Lbar g).inv_mem hℓ))
  obtain ⟨ρ', hρ', hker'⟩ := s12_exists_hom_of_mulEquiv e ρ hρ hker
  exact false_of_hom_simple haQ hne hn ht htA hKM hKt hLK hH ρ' hρ' hker'

theorem false_of_centralizer_commutator_hom_simple {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : commutator (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)) →* H)
    (hρ : Function.Surjective ρ) (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup S.O,
      K = (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)).map
        (S.Xbar12 g).subtype := ⟨_, rfl⟩
  obtain ⟨hKM, hKt, hconj⟩ := centralizer_map_props haQ ht htX hKdef
  obtain ⟨ι, hιdef⟩ : ∃ ι : (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)) →* S.O,
      ι = (S.Xbar12 g).subtype.comp
        (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g)).subtype := ⟨_, rfl⟩
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact (S.Xbar12 g).subtype_injective.comp (Subgroup.subtype_injective _)
  have hιK : (⊤ : Subgroup (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} : Subgroup (S.Xbar12 g))).map ι =
      K := by
    rw [← MonoidHom.range_eq_map, hιdef, MonoidHom.range_comp, range_subtype, hKdef]
  have hmap : (commutator (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} :
      Subgroup (S.Xbar12 g))).map ι = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, hιK]
  obtain ⟨e⟩ : Nonempty (commutator (centralizer {(⟨t, htX⟩ : S.Xbar12 g)} :
      Subgroup (S.Xbar12 g)) ≃* (⁅K, K⁆ : Subgroup S.O)) :=
    ⟨((commutator _).equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hmap)⟩
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hconj' : ∀ ℓ ∈ S.Lbar g, ∀ c ∈ ⁅K, K⁆, ℓ * c * ℓ⁻¹ ∈ ⁅K, K⁆ := by
    intro ℓ hℓ c hc
    have hle : K.map (MulAut.conj ℓ).toMonoidHom ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hconj ℓ hℓ x hx
    have h1 : (⁅K, K⁆ : Subgroup S.O).map (MulAut.conj ℓ).toMonoidHom ≤ ⁅K, K⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    exact h1 ⟨c, hc, rfl⟩
  have hLK : S.Lbar g ≤ normalizer ((⁅K, K⁆ : Subgroup S.O) : Set S.O) := fun ℓ hℓ =>
    mem_normalizer_of_conj_le (hconj' ℓ hℓ) (hconj' ℓ⁻¹ ((S.Lbar g).inv_mem hℓ))
  obtain ⟨ρ', hρ', hker'⟩ := s12_exists_hom_of_mulEquiv e ρ hρ hker
  exact false_of_hom_simple haQ hne hn ht htA (hKK.trans hKM) (fun c hc => hKt c (hKK hc)) hLK
    hH ρ' hρ' hker'

theorem false_of_fi24 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    {L : Subgroup (S.Xbar12 g)}
    (hCL : centralizer {(⟨t, htX⟩ : S.Xbar12 g)} = zpowers (⟨t, htX⟩ : S.Xbar12 g) ⊔ L)
    (hinf : zpowers (⟨t, htX⟩ : S.Xbar12 g) ⊓ L = ⊥)
    (eL : L ≃* CFSG.Blueprint.NativeSporadic.Fi23) : False := by
  obtain ⟨hsimp, hns⟩ := s12_fi24_quotient_facts hCL hinf eL
  exact false_of_centralizer_hom_simple haQ hne hn ht htA htX hns (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) fun k hk x => by
      rw [QuotientGroup.ker_mk'] at hk
      exact s12_zpowers_subgroupOf_central _ k hk x

end Setting

theorem inspFi_of (hTri : FischerTrialityInput) (hSpT : InspSpTv) (hOT : InspOTv)
    (hPSU : InspPSU) (hF3 : InspF3) : InspFi := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, -⟩ := h
  have hdeg : ¬ S.IsNondeg12 g := fun h' => hND (Setting.isNondeg12_iff_inspNondeg.mp h')
  obtain ⟨hclass, hinv, hprod, hgen, hcenter, hsimple⟩ :=
    Setting.fischer_data_Xbar12 hTri haQ hne (by omega) ht htA hS hdeg
  have htX : t ∈ S.Xbar12 g := Setting.subset_Xbar12 (Setting.mem_Ebar12_of_mem_Lbar ht htA)
  have hd : (⟨t, htX⟩ : S.Xbar12 g) ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) :=
    Setting.mem_Ebar12_of_mem_Lbar ht htA
  obtain ⟨-, -, -, h22, h23, h24⟩ :=
    CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition (S.Xbar12 g) _
      hclass hinv hprod hgen hcenter hsimple _ hd
  have hcen : ∀ (C : Subgroup (S.Xbar12 g)) (k : C), k ∈ (QuotientGroup.mk' (center C)).ker →
      ∀ x : C, k * x = x * k := fun C k hk x => by
    rw [QuotientGroup.ker_mk'] at hk
    exact (mem_center_iff.mp hk x).symm
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned (S.Xbar12 g) _
      hclass hinv hprod hgen hcenter hsimple with h1 | h2 | h3 | h4 | h5 | ⟨φ, -⟩ | ⟨φ, -⟩ |
      ⟨φ, -⟩
  · exact inspSym G S g t haQ hne hn ht htA hS hred ⟨hND, h1⟩
  · exact hSpT G S g t haQ hne hn ht htA hS hred ⟨hND, h2⟩
  · exact hOT G S g t haQ hne hn ht htA hS hred ⟨hND, h3⟩
  · exact hPSU G S g t haQ hne hn ht htA hS hred ⟨hND, h4⟩
  · exact hF3 G S g t haQ hne hn ht htA hS hred ⟨hND, h5⟩
  · exfalso
    obtain ⟨hperf, -, hZ2, hLie⟩ := h22 ⟨φ⟩
    have := CFSG.Fischer.Classification.Recognition.isSimpleGroup_of_lieModel_PSU_six hLie
    exact Setting.false_of_centralizer_hom_simple haQ hne (by omega) ht htA htX
      (s12_not_isSolvable_quotient_center hperf hZ2) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (hcen _)
  · exfalso
    obtain ⟨hperf, -, hZ2, ⟨e⟩⟩ := h23 ⟨φ⟩
    have := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
    exact Setting.false_of_centralizer_hom_simple haQ hne (by omega) ht htA htX
      (s12_not_isSolvable_quotient_center hperf hZ2) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (hcen _)
  · exfalso
    obtain ⟨L, ⟨eL⟩, hCL, hinf, -⟩ := h24 ⟨φ⟩
    exact Setting.false_of_fi24 haQ hne (by omega) ht htA htX hCL hinf eL

end CFSG.LargeExtraspecial
