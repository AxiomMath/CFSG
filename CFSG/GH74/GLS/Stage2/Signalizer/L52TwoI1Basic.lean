module

import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.P27.S45E
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

namespace I1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem le_ker_of_odd_normal {P S : Type*} [Group P] [Finite P] [Group S] [IsSimpleGroup S]
    (hS : Even (Nat.card S)) (g : P →* S) (hg : Function.Surjective g)
    (M : Subgroup P) [M.Normal] (hM : Odd (Nat.card M)) : M ≤ g.ker := by
  have hn : (M.map g).Normal := Subgroup.Normal.map inferInstance g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map g) with h | h
  · rw [Subgroup.map_eq_bot_iff] at h
    exact h
  · exfalso
    have hd : Nat.card ↥(M.map g) ∣ Nat.card M := Subgroup.card_map_dvd M g
    rw [h, Subgroup.card_top] at hd
    exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hM hd)) hS

theorem isSimpleGroup_of_isL2 {X : Type} [Group X] {q : ℕ} (hq3 : 3 < q)
    (h : IVK.IsL2 X (fun r => r = q)) : IsSimpleGroup X := by
  obtain ⟨F, _, _, hP, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by rw [hP]; omega
  have : IsSimpleGroup (GorensteinWalter.PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans (IVK.L2.equivPSL F)).isSimpleGroup

theorem isQuasisimple_of_isL2 {X : Type} [Group X] {q : ℕ} (hq3 : 3 < q)
    (h : IVK.IsL2 X (fun r => r = q)) : IsQuasisimple X := by
  have hs := isSimpleGroup_of_isL2 hq3 h
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : Subgroup.center X = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      exact fun g => hcon g z
    have hb : Subgroup.center X = ⊥ := GH74.GLS.Stage2.Local.P27.S45.center_eq_bot_of_isL2 h
    rw [hb] at hc
    have := hs.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : X)
    exact ha (Subgroup.mem_bot.1 ((Subgroup.eq_top_iff' _).1 hc a))
  exact (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1

theorem isFourSubgroup_of_card_sq {G : Type} [Group G] (V : Subgroup G) (h4 : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v * v = 1) : IVK.IsFourSubgroup V := by
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 : v * w * (v * w) = 1 := hsq _ (V.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w hw)
    have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hv', hw']
  refine ⟨?_, h4⟩
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => by
        apply Subtype.ext
        simpa [sq] using hsq a a.2) }

theorem exists_isFourSubgroup_of_isL2 {X : Type} [Group X] {q : ℕ} (hq : Odd q)
    (h : IVK.IsL2 X (fun r => r = q)) : ∃ V : Subgroup X, IVK.IsFourSubgroup V := by
  obtain ⟨F₀, _, _, hF, ⟨e₀⟩⟩ := h
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hodd : Odd (Nat.card F₀) := hF ▸ hq
  have h2 : (2 : F₀) ≠ 0 := by
    have hc : ringChar F₀ ≠ 2 := by
      intro hc
      have := (FiniteField.even_card_iff_char_two).mp hc
      rw [← Nat.card_eq_fintype_card] at this
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Ring.two_ne_zero hc
  obtain ⟨H₀, ⟨eA⟩⟩ :=
    CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup (F := F₀) h2
  let ψ : X ≃* GorensteinWalter.PSL2 F₀ := e₀.trans (IVK.L2.equivPSL F₀)
  let M : Subgroup X := H₀.map ψ.symm.toMonoidHom
  let eM : M ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective H₀ ψ.symm.toMonoidHom ψ.symm.injective).symm.trans eA
  obtain ⟨V, hV4, hV⟩ := CFSG.Glauberman.Dickson.MaxCases.exists_kleinFour eM
  exact ⟨V, isFourSubgroup_of_card_sq V hV4 (fun v hv => ((hV v).mp hv).2)⟩

theorem exists_isFourSubgroup_of_surjective {P S : Type} [Group P] [Finite P] [Group S]
    (g : P →* S) (hg : Function.Surjective g) (hker : Odd (Nat.card g.ker))
    {V : Subgroup S} (hV : IVK.IsFourSubgroup V) : ∃ Q : Subgroup P, IVK.IsFourSubgroup Q := by
  have : IsElementaryAbelian 2 ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := IsElementaryAbelian.isPGroup 2 ↥V
  obtain ⟨Q, -, ⟨e⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 2
    Nat.prime_two g hg (Nat.coprime_two_left.2 hker) V hV2
  have hsq : ∀ w : ↥V, w * w = 1 := fun w => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 ↥V) w
    rwa [sq] at this
  refine ⟨Q, isFourSubgroup_of_card_sq Q ?_ (fun v hv => ?_)⟩
  · rw [Nat.card_congr e.toEquiv]
    exact hV.2
  · have h1 : e (⟨v, hv⟩ * ⟨v, hv⟩) = 1 := by rw [map_mul]; exact hsq _
    have h2 : (⟨v, hv⟩ * ⟨v, hv⟩ : ↥Q) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2

theorem le_of_perfect_of_le_sup_odd {Y : Type*} [Group Y] [Finite Y] {I E O : Subgroup Y}
    [E.Normal] (hI : ⁅I, I⁆ = I) (hO : Odd (Nat.card O)) (h : I ≤ E ⊔ O) : I ≤ E := by
  set π : Y →* Y ⧸ E := QuotientGroup.mk' E with hπ
  have hsup : (E ⊔ O).map π = O.map π := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hle : I.map π ≤ O.map π := hsup ▸ Subgroup.map_mono h
  have hodd : Odd (Nat.card ↥(I.map π)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hO (Subgroup.card_map_dvd O π)) (Subgroup.card_dvd_of_le hle)
  have hsolv : Group.IsSolvable ↥(I.map π) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : ⁅I.map π, I.map π⁆ = I.map π := by
    rw [← Subgroup.map_commutator, hI]
  have hbot : I.map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(I.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥(I.map π) := Subgroup.isPerfect_iff.2 hperf
    exact Group.IsPerfect.not_isSolvable ↥(I.map π) hsolv
  rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
  exact hbot

section Ambient

variable {G : Type} [Group G]

theorem pLayerOf_eq_map_pLayer (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

theorem mem_pPrimeCoreOf_iff {X : Subgroup G} {i : G} (hi : i ∈ X) :
    i ∈ pPrimeCoreOf 2 X ↔ (⟨i, hi⟩ : ↥X) ∈ pPrimeCore 2 ↥X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨i, hi⟩, h, rfl⟩

theorem le_pPrimeCoreOf_of_odd {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm h h.2 a ha⟩
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

variable [Finite G]

theorem odd_card_pPrimeCoreOf (X : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 X)) :=
  TwoThin.card_pPrimeCoreOf_odd X

theorem mem_pPrimeCoreOf_of_mem_pPrimeCoreOf {L I Y : Subgroup G} (hIL : I ≤ L) (hIY : I ≤ Y)
    (hS : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L)) (hSe : Even (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)))
    (hsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤)
    {i : G} (hi : i ∈ I) (hiY : i ∈ pPrimeCoreOf 2 Y) : i ∈ pPrimeCoreOf 2 L := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  let gI : ↥I →* ↥L ⧸ pPrimeCore 2 ↥L := ρ.comp (Subgroup.inclusion hIL)
  have hgI : Function.Surjective gI := by
    intro s
    have hs : s ∈ (I.subgroupOf L).map ρ := by rw [hsurj]; trivial
    obtain ⟨l, hl, rfl⟩ := hs
    exact ⟨⟨l, hl⟩, rfl⟩
  set M : Subgroup ↥I := (pPrimeCoreOf 2 Y).subgroupOf I with hM
  have hMn : M.Normal := ⟨fun a ha g => by
    rw [hM, Subgroup.mem_subgroupOf] at ha ⊢
    exact TwoThin.pPrimeCoreOf_normalized Y (hIY g.2) ha⟩
  have hModd : Odd (Nat.card M) := by
    have hmap : M.map I.subtype ≤ pPrimeCoreOf 2 Y := by
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    rw [← Subgroup.card_map_of_injective I.subtype_injective]
    exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf Y) (Subgroup.card_dvd_of_le hmap)
  have hle := le_ker_of_odd_normal hSe gI hgI M hModd
  have hker : gI ⟨i, hi⟩ = 1 := hle (show (⟨i, hi⟩ : ↥I) ∈ M from hiY)
  have h1 : ρ ⟨i, hIL hi⟩ = 1 := hker
  rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (mem_pPrimeCoreOf_iff (hIL hi)).2 h1

theorem isQuasisimple_of_surjective_of_ker_eq {P A B : Type*} [Group P] [Group A] [Group B]
    (f : P →* A) (g : P →* B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) (hA : IsQuasisimple A) : IsQuasisimple B :=
  LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq h).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg))) hA

theorem isQuasisimple_image {L I X : Subgroup G} (hIL : I ≤ L) (hIX : I ≤ X)
    (hXO : ∀ x ∈ X, ∀ o ∈ pPrimeCoreOf 2 L, x * o * x⁻¹ ∈ pPrimeCoreOf 2 L)
    (hXI : ∀ x ∈ X, ∀ i ∈ I, x * i * x⁻¹ ∈ I)
    (hS : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L)) (hSe : Even (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)))
    (hqs : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤) :
    IsQuasisimple ↥((I.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X))) := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hq
  let f : ↥I →* ↥L ⧸ pPrimeCore 2 ↥L := ρ.comp (Subgroup.inclusion hIL)
  let g : ↥I →* ↥((I.subgroupOf X).map q) :=
    (q.comp (Subgroup.inclusion hIX)).codRestrict _
      (fun i => ⟨⟨i, hIX i.2⟩, Subgroup.mem_subgroupOf.2 i.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro s
    have hs : s ∈ (I.subgroupOf L).map ρ := by rw [hsurj]; trivial
    obtain ⟨l, hl, rfl⟩ := hs
    exact ⟨⟨l, hl⟩, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hfk : ∀ i : ↥I, f i = 1 ↔ (i : G) ∈ pPrimeCoreOf 2 L := fun i => by
    rw [mem_pPrimeCoreOf_iff (hIL i.2)]
    exact QuotientGroup.eq_one_iff (⟨i, hIL i.2⟩ : ↥L)
  have hgk : ∀ i : ↥I, g i = 1 ↔ (i : G) ∈ pPrimeCoreOf 2 X := fun i => by
    rw [mem_pPrimeCoreOf_iff (hIX i.2)]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (⟨i, hIX i.2⟩ : ↥X)).1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (⟨i, hIX i.2⟩ : ↥X)).2 h)
  have hker : f.ker = g.ker := by
    ext i
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hfk, hgk]
    constructor
    · intro hiO
      have hN : I ⊓ pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 X := by
        refine le_pPrimeCoreOf_of_odd (inf_le_left.trans hIX) (fun x hx n hn => ?_) ?_
        · exact ⟨hXI x hx n hn.1, hXO x hx n hn.2⟩
        · exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf L)
            (Subgroup.card_dvd_of_le inf_le_right)
      exact hN ⟨i.2, hiO⟩
    · intro hiX
      exact mem_pPrimeCoreOf_of_mem_pPrimeCoreOf hIL hIX hS hSe hsurj i.2 hiX
  exact isQuasisimple_of_surjective_of_ker_eq f g hf hg hker hqs

theorem le_pLayerOf_of_perfect_normal {X I : Subgroup G} (hIX : I ≤ X)
    (hn : ∀ x ∈ X, ∀ i ∈ I, x * i * x⁻¹ ∈ I) (hperf : ⁅I, I⁆ = I)
    (hq : IsQuasisimple ↥((I.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)))) :
    I ≤ pLayerOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hqdef
  set I' : Subgroup ↥X := I.subgroupOf X with hI'
  have hI'n : I'.Normal := ⟨fun a ha g => by
    rw [hI', Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hn g g.2 a ha⟩
  have hK : IsComponent (I'.map q) :=
    ⟨hq, (hI'n.map q (QuotientGroup.mk'_surjective _)).isSubnormal⟩
  have hle1 : I'.map q ≤ (pLayer ↥X 2).map q := by
    rw [hqdef, ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient]
    exact le_sSup hK
  have hle2 : I' ≤ pLayer ↥X 2 ⊔ pPrimeCore 2 ↥X := by
    have h2 : I' ≤ ((pLayer ↥X 2).map q).comap q :=
      (Subgroup.le_comap_map q I').trans (Subgroup.comap_mono hle1)
    rw [Subgroup.comap_map_eq, hqdef, QuotientGroup.ker_mk'] at h2
    exact h2
  have hI'map : I'.map X.subtype = I := Subgroup.map_subgroupOf_eq_of_le hIX
  have hperf' : ⁅I', I'⁆ = I' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hI'map, hperf]
  have hchar : (pLayer ↥X 2).Characteristic :=
    ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
  have : (pLayer ↥X 2).Normal := inferInstance
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥X)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥X))
  have h3 : I' ≤ pLayer ↥X 2 := le_of_perfect_of_le_sup_odd hperf' hodd hle2
  rw [pLayerOf_eq_map_pLayer, ← hI'map]
  exact Subgroup.map_mono h3

theorem exists_perfect_core {L B X : Subgroup G} (hBL : B ≤ L)
    (hXB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B)
    (hperf : Group.IsPerfect (↥L ⧸ pPrimeCore 2 ↥L))
    (hcov : L ≤ B ⊔ pPrimeCoreOf 2 L) :
    ∃ I : Subgroup G, I ≤ B ∧ ⁅I, I⁆ = I ∧ (∀ x ∈ X, ∀ i ∈ I, x * i * x⁻¹ ∈ I) ∧
      (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤ := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  have hOL : pPrimeCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hsub : (pPrimeCoreOf 2 L).subgroupOf L = pPrimeCore 2 ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hcov' : B.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [← hsub, ← Subgroup.subgroupOf_sup hBL hOL]
    rw [eq_top_iff]
    intro l _
    exact hcov l.2
  let ρB : ↥B →* ↥L ⧸ pPrimeCore 2 ↥L := ρ.comp (Subgroup.inclusion hBL)
  have hρB : Function.Surjective ρB := by
    intro s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
    have hl : l ∈ B.subgroupOf L ⊔ pPrimeCore 2 ↥L := by rw [hcov']; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hl
    refine ⟨⟨y, hy⟩, ?_⟩
    change ρ y = ((y * z : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]
    rfl
  have hmap : (perfectResidual ↥B).map ρB = ⊤ := by
    have h : (perfectResidual ↥B).map ρB = perfectResidual (↥L ⧸ pPrimeCore 2 ↥L) :=
      RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ρB hρB
    rw [h]
    show (⨅ n : ℕ, derivedSeries (↥L ⧸ pPrimeCore 2 ↥L) n) = ⊤
    simp
  refine ⟨(perfectResidual ↥B).map B.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have hP : Group.IsPerfect ↥(perfectResidual ↥B) :=
      (perfect_residual_characterization (G := ↥B)).2.2.1
    have : Group.IsPerfect ↥((perfectResidual ↥B).map B.subtype) := Group.IsPerfect.map B.subtype
    exact Subgroup.isPerfect_iff.mp this
  · intro x hx i hi
    have hnorm : x ∈ normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      refine ⟨fun hb => hXB x hx b hb, fun hb => ?_⟩
      have h1 := hXB x⁻¹ (X.inv_mem hx) _ hb
      have e : x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b := by group
      rwa [e] at h1
    obtain ⟨y, hy, rfl⟩ := hi
    let φ : MulAut ↥B := B.normalizerMonoidHom ⟨x, hnorm⟩
    have hch : (perfectResidual ↥B).Characteristic := perfectResidual_characteristic'
    have hφ : φ y ∈ perfectResidual ↥B := by
      have := Subgroup.characteristic_iff_map_eq.mp hch φ
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hy
    refine ⟨φ y, hφ, ?_⟩
    simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  · rw [eq_top_iff]
    intro s _
    have hs : s ∈ (perfectResidual ↥B).map ρB := by rw [hmap]; trivial
    obtain ⟨y, hy, rfl⟩ := hs
    refine ⟨⟨(y : G), hBL y.2⟩, ?_, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem exists_isFourSubgroup_of_cover {L I : Subgroup G} {q : ℕ} (hqo : Odd q) (hIL : I ≤ L)
    (hS : IVK.IsL2 (↥L ⧸ pPrimeCore 2 ↥L) (fun r => r = q))
    (hsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤) :
    ∃ Q : Subgroup G, Q ≤ I ∧ IVK.IsFourSubgroup Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  let gI : ↥I →* ↥L ⧸ pPrimeCore 2 ↥L := ρ.comp (Subgroup.inclusion hIL)
  have hgI : Function.Surjective gI := by
    intro s
    have hs : s ∈ (I.subgroupOf L).map ρ := by rw [hsurj]; trivial
    obtain ⟨l, hl, rfl⟩ := hs
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : Odd (Nat.card gI.ker) := by
    have hmap : gI.ker.map I.subtype ≤ pPrimeCoreOf 2 L := by
      rintro _ ⟨k, hk, rfl⟩
      have h1 : ρ ⟨(k : G), hIL k.2⟩ = 1 := hk
      rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (mem_pPrimeCoreOf_iff (hIL k.2)).2 h1
    rw [← Subgroup.card_map_of_injective I.subtype_injective]
    exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf L) (Subgroup.card_dvd_of_le hmap)
  obtain ⟨V, hV⟩ := exists_isFourSubgroup_of_isL2 hqo hS
  obtain ⟨Q, hQ⟩ := exists_isFourSubgroup_of_surjective gI hgI hker hV
  have : IsElementaryAbelian 2 ↥Q := hQ.1
  refine ⟨Q.map I.subtype, Subgroup.map_subtype_le Q, ?_, ?_⟩
  · exact IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective I.subtype_injective]
    exact hQ.2

theorem odd_orderOf_of_comm_mem {L I Y : Subgroup G} (hIL : I ≤ L) (hIY : I ≤ Y)
    (hS : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L)) (hSe : Even (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)))
    (hZ : Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥)
    (hsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤)
    {i : G} (hi : i ∈ I) (hcomm : ∀ j ∈ I, ⁅i, j⁆ ∈ pPrimeCoreOf 2 Y) : Odd (orderOf i) := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hρ
  have hiL : i ∈ L := hIL hi
  have hcen : ρ ⟨i, hiL⟩ ∈ Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro t
    have ht : t ∈ (I.subgroupOf L).map ρ := by rw [hsurj]; trivial
    obtain ⟨j, hj, rfl⟩ := ht
    have hjI : (j : G) ∈ I := hj
    have hcI : ⁅i, (j : G)⁆ ∈ I := by
      rw [commutatorElement_def]
      exact I.mul_mem (I.mul_mem (I.mul_mem hi hjI) (I.inv_mem hi)) (I.inv_mem hjI)
    have hcL : ⁅i, (j : G)⁆ ∈ pPrimeCoreOf 2 L :=
      mem_pPrimeCoreOf_of_mem_pPrimeCoreOf hIL hIY hS hSe hsurj hcI (hcomm _ hjI)
    have h1 := (mem_pPrimeCoreOf_iff (hIL hcI)).1 hcL
    have h2 : ρ ⟨⁅i, (j : G)⁆, hIL hcI⟩ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    have h3 : ρ ⁅(⟨i, hiL⟩ : ↥L), j⁆ = 1 := h2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  rw [hZ, Subgroup.mem_bot, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have hmem : i ∈ pPrimeCoreOf 2 L := (mem_pPrimeCoreOf_iff hiL).2 hcen
  exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf L) (Subgroup.orderOf_dvd_natCard _ hmem)

theorem pLayerOf_inf_centralizer_le {H U : Subgroup G} (hUH : U ≤ H) (hU2 : IsPGroup 2 ↥U) :
    pLayerOf 2 (H ⊓ centralizer (U : Set G)) ≤ pLayerOf 2 H := by
  rw [pLayerOf_eq_map_pLayer, pLayerOf_eq_map_pLayer]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup ↥H := U.subgroupOf H with hA'
  have hA'2 : IsPGroup 2 ↥A' := hU2.comap_of_injective H.subtype H.subtype_injective
  have hbal := ClassicalInvolution.l2PrimeBalance ↥H A' hA'2
  set Z : Subgroup ↥H := centralizer (A' : Set ↥H) with hZ
  have hZmap : Z.map H.subtype = H ⊓ centralizer (U : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hz ⟨a, hUH ha⟩ ha)
    · intro hx
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (a : G) ha)
  let e : ↥Z ≃* ↥(H ⊓ centralizer (U : Set G)) :=
    (Z.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hZmap)
  have hlayer := ComponentClassification.UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e
  have key : (pLayer ↥(H ⊓ centralizer (U : Set G)) 2).map (H ⊓ centralizer (U : Set G)).subtype =
      ((pLayer ↥Z 2).map Z.subtype).map H.subtype := by
    rw [← hlayer, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [key]
  exact Subgroup.map_mono hbal

theorem barIn_le_layer_of_le_pLayerOf {H I : Subgroup G} (h : I ≤ pLayerOf 2 H) :
    barIn H I ≤ layer (HBar H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : I.subgroupOf H ≤ pLayer ↥H 2 := by
    intro y hy
    have hy' : (y : G) ∈ pLayerOf 2 H := h hy
    rw [pLayerOf_eq_map_pLayer] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rwa [hzy'] at hz
  calc barIn H I ≤ (pLayer ↥H 2).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :=
        Subgroup.map_mono h1
    _ = layer (HBar H) := ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient

end Ambient

end I1

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
