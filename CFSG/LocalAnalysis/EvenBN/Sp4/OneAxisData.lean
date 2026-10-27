module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisInvolutionExclusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem pull_eq_map {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X] (φ : L ≃* X)
    (S : Subgroup X) : pull φ S = S.map (L.subtype.comp φ.symm.toMonoidHom) := by
  rw [pull, comap_equiv_eq_map_symm', ← Subgroup.map_map]

structure OneAxisData {G : Type} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2]
    (n : ℕ) (φ : L ≃* antiSp K) (TG : Subgroup G) (t : G) (M : Subgroup G) : Prop
    extends AxisHyp L K n φ TG t M where
  torus : pull φ (diagTorus K) ≤ normalizer (M : Set G)
  elemAb₁ : IsElementaryAbelian 2 (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
  sup_t₁ : M ⊔ pull φ (rootA K Axis.one) ⊔ zpowers t =
    (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) :
      Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G) :
      Set G)).subtype

namespace OneAxisData

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

abbrev M₁ (_ : OneAxisData L K n φ TG t M) : Subgroup G := M ⊔ pull φ (rootA K Axis.one)

abbrev M₂ (_ : OneAxisData L K n φ TG t M) : Subgroup G :=
  M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom

abbrev V₁ (_ : OneAxisData L K n φ TG t M) : Subgroup G :=
  M ⊔ pull φ (rootA K Axis.one) ⊔
    (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom)

abbrev T₁ (_ : OneAxisData L K n φ TG t M) : Subgroup G :=
  pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
    pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
    pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
local notation "𝐁₁" => (zpowers t ⊔ pull φ (rootA K Axis.one) : Subgroup G)
local notation "𝐁₂" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

theorem t_mul_t (h : OneAxisData L K n φ TG t M) : t * t = 1 := h.heis.sec.two.t_mul_t

theorem comm_L (h : OneAxisData L K n φ TG t M) {x : G} (hx : x ∈ L) : t * x = x * t :=
  h.heis.sec.two.comm hx

theorem V₁_le_T₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) : h.V₁ ≤ h.T₁ :=
  h.V_le_S

theorem t_mem_T₁ (h : OneAxisData L K n φ TG t M) : t ∈ h.T₁ := t_mem_S h.heis

theorem t_not_mem_V₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) : t ∉ h.V₁ :=
  h.t_not_mem_V

theorem T₁_eq [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    h.T₁ = h.V₁ ⊔ zpowers t ∧ h.V₁ ⊓ zpowers t = ⊥ :=
  ⟨h.S_semidirect.2.symm, h.S_semidirect.1⟩

theorem t_mem_normalizer_V₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    t ∈ normalizer (h.V₁ : Set G) :=
  mem_normalizer_of_conj_le fun _ hx => h.conj_mem_V (t_mem_S h.heis) hx

theorem t_mem_normalizer_M₁ [Finite G] (h : OneAxisData L K n φ TG t M) :
    t ∈ normalizer (h.M₁ : Set G) :=
  h.S_le_normalizer₁ (t_mem_S h.heis)

theorem M₁_normal [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    (h.M₁.subgroupOf h.V₁).Normal :=
  ⟨fun _ hu v => mem_subgroupOf.mpr (h.conj₁ _ (h.V_le_S v.2) _ (mem_subgroupOf.mp hu))⟩

theorem M₁_inf_centralizer (h : OneAxisData L K n φ TG t M) :
    h.M₁ ⊓ centralizer ({t} : Set G) = 𝐀₁ := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf le_sup_right fun a ha => h.heis.sec.two.L_le (pull_le φ _ ha))
  obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
  have hxD : x ∈ 𝐃₁ := h.M₁_le_D₁ hxM
  have hxB : x ∈ 𝐁₁ := by
    rw [← h.heis.inf₁]
    exact mem_inf.mpr ⟨hxD, mem_inf.mpr ⟨hxC, map_subtype_le _ hxD⟩⟩
  rcases (mem_zpowers_sup_iff h.t_mul_t (TwoCoreSetup.comm_pull φ h.heis.sec.two)).mp hxB with
    hA | hA
  · exact hA
  · exfalso
    apply h.t_not_mem₁
    have := mul_mem ((le_sup_right : 𝐀₁ ≤ 𝐌₁) hA) (inv_mem hxM)
    rwa [mul_inv_cancel_right] at this

theorem exists_mem_M₁_conj_eq [Finite G] (h : OneAxisData L K n φ TG t M) {u : G}
    (hu : u ∈ 𝐔₁) : ∃ m ∈ h.M₁, m⁻¹ * t * m = t * u := by
  obtain ⟨d, hd, hdu⟩ := h.heis.surj₁ u hu
  have htN : zpowers t ≤ normalizer (𝐌₁ : Set G) := zpowers_le.mpr h.t_mem_normalizer_M₁
  rw [← h.sup_t₁, sup_comm, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ htN] at hd
  obtain ⟨c, hc, m, hm, rfl⟩ := hd
  have hct : c * t = t * c := by
    obtain ⟨j, rfl⟩ := hc
    exact (Commute.zpow_left (Commute.refl t) j).eq
  refine ⟨m, hm, ?_⟩
  have e : (c * m)⁻¹ * t * (c * m) = m⁻¹ * t * m := by
    calc (c * m)⁻¹ * t * (c * m) = m⁻¹ * (c⁻¹ * (t * c)) * m := by group
      _ = m⁻¹ * t * m := by rw [← hct, inv_mul_cancel_left]
  rw [← hdu, e]
  group

theorem exists_hAct [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) {s : G}
    (hs : s ∈ h.T₁) : ∃ x y d : K, HAct φ t s x y d :=
  h.heis.exists_hAct_of_mem_S hs

theorem conj_t_eq (h : OneAxisData L K n φ TG t M) {s : G} {x y d : K} (hs : HAct φ t s x y d) :
    s * t * s⁻¹ = t * ((φ.symm (uElt x y 0 0) : L) : G) ∧
      s⁻¹ * t * s = t * ((φ.symm (uElt x (y + d * x) 0 0) : L) : G) := by
  have key : ∀ {g : G} {a b c : K}, HAct φ t g a b c →
      g * t * g⁻¹ = t * ((φ.symm (uElt a b 0 0) : L) : G) := fun hg => by
    have e := commutator_t_eq h.heis.sec.two hg
    rw [h.comm_L (φ.symm _).2, ← e]
    group
  refine ⟨key hs, ?_⟩
  have e := key (hAct_inv hs)
  rwa [inv_inv] at e

theorem exists_mem_M₂_hAct [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) (x y : K) :
    ∃ m ∈ h.M₂, HAct φ t m x y 0 := by
  obtain ⟨d, hd, hdx⟩ := exists_D_hAct h.heis.sec x y
  obtain ⟨-, -, -, hsup⟩ := h.D₂_semidirect
  rw [← hsup, sup_comm, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ h.t_le_normalizer_M₂] at hd
  obtain ⟨c, hc, m, hm, rfl⟩ := hd
  have hcB : c⁻¹ ∈ 𝐁₂ := inv_mem (mem_sup_left hc)
  refine ⟨m, hm, ?_⟩
  have e := (hAct_of_mem_B h.heis.sec hcB).mul hdx
  rw [inv_mul_cancel_left] at e
  exact e.congr (zero_add x) (by ring) (add_zero 0)

theorem torus_le_normalizer_V₁ [Finite G] (h : OneAxisData L K n φ TG t M) :
    pull φ (diagTorus K) ≤ normalizer (h.V₁ : Set G) :=
  le_normalizer_sup (le_normalizer_sup h.torus
    (J₀_le_normalizer_pull fun _ hδ _ ha => diagTorus_conj_radA1 hδ ha))
    (le_normalizer_sup h.torus (AxisHyp.J₀_le_Mw h.torus))

theorem of_standard {G : Type} [Group G] [Finite G]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) (M : Subgroup G) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let A₁ := ((rootA K Axis.one).comap φ.toMonoidHom).map L.subtype
    let A₂ := ((rootA K Axis.two).comap φ.toMonoidHom).map L.subtype
    let B₁ := zpowers (t : G) ⊔ A₁
    let B₂ := zpowers (t : G) ⊔ A₂
    let N₁ := normalizer (B₁ : Set G)
    let N₂ := normalizer (B₂ : Set G)
    let D₁ := (CFSG.pCore 2 N₁).map N₁.subtype
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let S := Q ⊔ D₂
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let M₁ := M ⊔ A₁
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
    J₀ ≤ normalizer (M : Set G) → M ≤ D₁ ⊓ D₂ → IsElementaryAbelian 2 M →
    Nat.card M = (2 ^ n) ^ 3 → ZP ≤ M → IsElementaryAbelian 2 M₁ →
    Nat.card M₁ = (2 ^ n) ^ 4 → (M₁ ≤ S ∧ (M₁.subgroupOf S).Normal) →
    (M₁ ≤ D₁ ∧ (M₁.subgroupOf D₁).Normal ∧ M₁ ⊓ zpowers (t : G) = ⊥ ∧
      M₁ ⊔ zpowers (t : G) = D₁) →
      OneAxisData L K n φ TG t M := by
  intro TG PG Q ZP U₁ A₁ A₂ B₁ B₂ N₁ N₂ D₁ D₂ S J₀ M₁ hone hJ hMD hMab hMcard hZM hM₁
    hM₁card hM₁S hM₁D
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hT' := hS.T_eq_zpowers hO hLn
  have hS2 : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS.t_mul_t
      L_le := hS.L_le
      cent_le := hS.cent_le
      cent_inf := hS.cent_inf.trans hT'
      not_conj := hS.conj_not_mem_L hO hLn }
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hQ : Q = pull φ (antiUnipotent K) ⊔ TG := by
    show PG ⊔ TG = _
    rw [hPG]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    have h := center_pull_antiUnipotent (G := G) φ
    rw [← hPG] at h
    exact h
  have hH : Hyp L K n φ TG t := ⟨hS, hS2, hT', by rw [← hQ]; exact hone⟩
  have hNQ := hH.normalizer_Q_le
  have hNC := (hS.orbits hO hLn).2.2.2.2
  have hmove : ∃ g ∈ N₂, g * t ≠ t * g := by
    obtain ⟨m, hm, hmC⟩ := Set.not_subset.mp hNC
    exact ⟨m, (hNQ hm).2, fun hmt => hmC (mem_centralizer_singleton_iff.mpr hmt)⟩
  have h2 : SecondHyp L K n φ (t : G) := ⟨hS2, hH.fus_two.1, hmove⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hinf₁, -, _, e, he, -, -, -⟩ :=
    standard_symplectic_four_one_axis_radical_fusion_normalizers hO hL hLn hn hK T hT htT ht
      hcore P φ hφP hone
  have hh : HeisHyp L K n φ TG t :=
    { hyp := hH
      sec := h2
      normQ := hNQ
      inf₁ := hinf₁
      conj₁ := fun d hd => by
        rw [← he ⟨d, hd⟩]
        exact (e (⟨d, hd⟩ : D₁)).2
      mul₁ := fun d hd d' hd' => by
        have h1 := he (⟨d, hd⟩ * ⟨d', hd'⟩)
        rw [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, he, he] at h1
        exact h1.symm
      surj₁ := fun u hu => by
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨u, hu⟩)
        refine ⟨x, x.2, ?_⟩
        have h1 := he x
        rw [hx, MulEquiv.apply_symm_apply] at h1
        exact h1.symm }
  have hM₁n := (normal_subgroupOf_iff_le_normalizer hM₁S.1).mp hM₁S.2
  have hSeq : S = pull φ (antiUnipotent K) ⊔ TG ⊔ D₂ := by
    show Q ⊔ D₂ = _
    rw [hQ]
  rw [hSeq] at hM₁n
  rw [hZP] at hZM
  exact
    { heis := hh
      le_D₁ := hMD.trans inf_le_left
      le_D₂ := hMD.trans inf_le_right
      comm := fun _ hx _ hy => elemAb_comm hMab hx hy
      mul_self := fun _ hx => elemAb_mul_self hMab hx
      card := hMcard
      ZP_le := hZM
      card₁ := hM₁card
      conj₁ := fun s hs x hx => (mem_normalizer_iff.mp (hM₁n hs) x).mp hx
      t_not_mem₁ := fun h => by
        have h1 : (t : G) ∈ M₁ ⊓ zpowers (t : G) := mem_inf.mpr ⟨h, mem_zpowers _⟩
        rw [hM₁D.2.2.1, mem_bot] at h1
        exact hh.hyp.setup.t_ne_one h1
      torus := hJ
      elemAb₁ := hM₁
      sup_t₁ := hM₁D.2.2.2 }

end OneAxisData

end CFSG.LocalAnalysis.EvenBN.Sp4
