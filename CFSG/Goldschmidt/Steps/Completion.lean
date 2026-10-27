module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Assembly.BalancedOddCoreCompletion
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.PropHSetup

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Assembly.Dichotomy

namespace Completion

variable {G : Type*} [Group G]

theorem le_normalizer_oddCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreOf H : Set G) := by
  have heq : (oddCoreOf H).subgroupOf H = goldschmidtOddCore H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hn : ((oddCoreOf H).subgroupOf H).Normal := by
    rw [heq]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hn

theorem le_oddCoreOf {H N : Subgroup G} (hNH : N ≤ H) (hN : H ≤ Subgroup.normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf H := by
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ goldschmidtOddCore H :=
    le_sSup ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN, hodd'⟩
  have hm := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at hm

theorem eq_one_of_sq_eq_one {O : Subgroup G} (hO : Odd (Nat.card O)) {z : G} (hz : z ∈ O)
    (hz2 : z ^ 2 = 1) : z = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · have h2 : 2 ∣ Nat.card O := h ▸ O.orderOf_dvd_natCard hz
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hO)

theorem not_isCyclic {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcard : 4 ≤ Nat.card B) :
    ¬ IsCyclic B := by
  intro hcyc
  let : IsCyclic B := hcyc
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := B)
  have hdvd : Nat.card B ∣ 2 := hb ▸ orderOf_dvd_of_pow_eq_one (Subtype.ext (hB.2 b.1 b.2))
  have := Nat.le_of_dvd (by decide) hdvd
  omega

theorem le_centralizer_of_le_normalizer {O U : Subgroup G} (hO : Odd (Nat.card O))
    (hU : IsElemAbelian 2 U) (hOU : O ≤ Subgroup.normalizer (U : Set G))
    (hUO : U ≤ Subgroup.normalizer (O : Set G)) : O ≤ Subgroup.centralizer (U : Set G) := by
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxU : o * x * o⁻¹ * x⁻¹ ∈ U :=
    U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hOU ho) x).mp hx) (U.inv_mem hx)
  have hxO : o * x * o⁻¹ * x⁻¹ ∈ O := by
    rw [show o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) by group]
    exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hUO hx) o⁻¹).mp (O.inv_mem ho))
  have h1 := eq_one_of_sq_eq_one hO hxO (hU.2 _ hxU)
  calc x * o = (o * x * o⁻¹ * x⁻¹)⁻¹ * (o * x) := by group
    _ = o * x := by rw [h1, inv_one, one_mul]

theorem exists_conj_eq {W : Subgroup G} (hW : Odd (Nat.card W)) {u t : G} (hu : u ^ 2 = 1)
    (ht : t ^ 2 = 1) (hut : u⁻¹ * t ∈ W) : ∃ x ∈ W, x * u * x⁻¹ = t := by
  obtain ⟨w, hwW, rfl⟩ : ∃ w ∈ W, t = u * w := ⟨u⁻¹ * t, hut, by group⟩
  have hu2 : u * u = 1 := by rw [← sq, hu]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hconj : u * w * u = w⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc u * w * u * w = (u * w) ^ 2 := by rw [sq, mul_assoc]
      _ = 1 := ht
  obtain ⟨j, hj⟩ : Odd (orderOf w) := Odd.of_dvd_nat hW (W.orderOf_dvd_natCard hwW)
  have hy : u * w ^ (j + 1) * u = (w ^ (j + 1))⁻¹ := by
    have h := conj_pow (i := j + 1) (a := u) (b := w)
    rw [huinv, hconj, inv_pow] at h
    exact h.symm
  have hy' : u * (w ^ (j + 1))⁻¹ * u = w ^ (j + 1) := by
    calc u * (w ^ (j + 1))⁻¹ * u = u * (u * w ^ (j + 1) * u) * u := by rw [hy]
      _ = (u * u) * w ^ (j + 1) * (u * u) := by group
      _ = w ^ (j + 1) := by rw [hu2, one_mul, mul_one]
  have hy2 : w ^ (j + 1) * w ^ (j + 1) = w := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  refine ⟨(w ^ (j + 1))⁻¹, W.inv_mem (W.pow_mem hwW _), ?_⟩
  calc (w ^ (j + 1))⁻¹ * u * (w ^ (j + 1))⁻¹⁻¹
      = (u * u) * (w ^ (j + 1))⁻¹ * u * w ^ (j + 1) := by rw [hu2, one_mul, inv_inv]
    _ = u * (u * (w ^ (j + 1))⁻¹ * u) * w ^ (j + 1) := by group
    _ = u * w := by rw [hy', mul_assoc, hy2]

variable [Finite G]

theorem odd_card_oddCoreOf (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective,
    goldschmidtOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem le_of_inf_centralizer_le {U Y W : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUcard : 4 ≤ Nat.card U) (hY : Odd (Nat.card Y))
    (hUY : U ≤ Subgroup.normalizer (Y : Set G))
    (hle : ∀ a ∈ U, a ≠ 1 → Y ⊓ Subgroup.centralizer ({a} : Set G) ≤ W) : Y ≤ W := by
  let : IsMulCommutative U := hU.1
  let : CommGroup U := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 U) :=
    ⟨fun b => ⟨1, by simpa only [pow_one] using Subtype.ext (hU.2 b.1 b.2)⟩⟩
  let : MulDistribMulAction U Y := MulDistribMulAction.compHom Y (Subgroup.inclusion hUY)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Y) (A := U) 2 (by simpa only [Nat.coprime_two_left] using hY) (not_isCyclic hU hUcard)
  have hle' : (⨆ (a : U) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Y) ≤
      W.comap Y.subtype := by
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro r hr
    change ∀ c : Subgroup.zpowers a, c • r = r at hr
    have hc : a.val * r.val * a.val⁻¹ = r.val :=
      congrArg Subtype.val (hr ⟨a, Subgroup.mem_zpowers a⟩)
    have hra : (r : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r.val * a.val = a.val * r.val * a.val⁻¹ * a.val := by rw [hc]
        _ = a.val * r.val := by rw [inv_mul_cancel_right]
    exact hle a.1 a.2 (fun h => ha (Subtype.ext h)) ⟨r.2, hra⟩
  intro y hy
  have hmem : (⟨y, hy⟩ : Y) ∈
      (⨆ (a : U) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) Y) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

end Completion

open Completion in
theorem N37_of (h36 : S_N36) : S_N37 := by
  intro G _ _ _ hnab hIH S A U hAS hAab hcl hUA hUmin h8 hK1 W Y
  obtain ⟨hel, h4, hNA, hctl, -, -⟩ := N31 G hnab S A U hAS hAab hcl hUA hUmin
  obtain ⟨hUS, -, hUcl, -⟩ := hUmin
  obtain ⟨hbal, hfac⟩ := h36 G hnab hIH S U hUS hel hUcl hK1
  obtain ⟨⟨hUW, hWodd, hWfix⟩, -⟩ := balanced_oddCoreSpan_completed U hel h8 hbal
  have hWY : W ≤ Y := Subgroup.le_normalizer
  have hNUY : Subgroup.normalizer (U : Set G) ≤ Y := normalizer_le_oddCoreSpan_normalizer U
  have hUY : U ≤ Y := Subgroup.le_normalizer.trans hNUY
  have hcoreW : ∀ u ∈ U, u ≠ 1 → oddCoreOf (Subgroup.centralizer ({u} : Set G)) ≤ W :=
    fun u hu hu1 => involutionOddCore_le_span U hu hu1
  have hCWN : ∀ u ∈ U, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ W ⊔ Subgroup.normalizer (U : Set G) := by
    intro u hu hu1
    rw [hfac u hu hu1]
    exact sup_le_sup (hcoreW u hu hu1) inf_le_right
  have hCY : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ Y :=
    fun u hu hu1 => (hCWN u hu hu1).trans (sup_le hWY hNUY)
  refine ⟨hWodd, hWfix, hNUY, hCY, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro P hPS hP4
    have hE : oddCoreSpan (P ⊓ U) = W :=
      oddCoreSpan_eq_of_completed U (P ⊓ U) hel h8 ⟨hUW, hWodd, hWfix⟩ inf_le_right hP4
    have h := normalizer_le_oddCoreSpan_normalizer (P ⊓ U)
    rw [hE] at h
    exact (N3b G S U P hUcl hPS).trans h
  ·
    apply le_antisymm
    · refine le_of_inf_centralizer_le hel h4 (odd_card_oddCoreOf Y)
        (hUY.trans (le_normalizer_oddCoreOf Y)) fun u hu hu1 => ?_
      refine le_trans ?_ (hcoreW u hu hu1)
      refine le_oddCoreOf inf_le_right ?_
        (Odd.of_dvd_nat (odd_card_oddCoreOf Y) (Subgroup.card_dvd_of_le inf_le_left))
      exact le_trans (le_inf ((hCY u hu hu1).trans (le_normalizer_oddCoreOf Y))
        Subgroup.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf
    · exact le_oddCoreOf hWY le_rfl hWodd
  ·
    have hkey : ∀ g : G, ∀ u ∈ U, ∀ v ∈ U, u ∉ W → u⁻¹ * (g * v * g⁻¹) ∈ W →
        g ∈ W ⊔ Subgroup.normalizer (U : Set G) := by
      intro g u hu v hv huW hmem
      have hu1 : u ≠ 1 := fun h => huW (h ▸ W.one_mem)
      have ht : (g * v * g⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hel.2 v hv, mul_one, mul_inv_cancel]
      obtain ⟨x, hxW, hx⟩ := exists_conj_eq hWodd (hel.2 u hu) ht hmem
      have hv' : (x⁻¹ * g)⁻¹ * u * (x⁻¹ * g) = v := by
        calc (x⁻¹ * g)⁻¹ * u * (x⁻¹ * g) = g⁻¹ * (x * u * x⁻¹) * g := by group
          _ = v := by rw [hx]; group
      obtain ⟨m, hm, hmu⟩ := hctl u (x⁻¹ * g) (Subgroup.le_normalizer hu)
        (by rw [hv']; exact Subgroup.le_normalizer hv) ⟨1, by rw [pow_one]; exact hel.2 u hu⟩
      have hc : m * (x⁻¹ * g)⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc m * (x⁻¹ * g)⁻¹ * u = m * ((x⁻¹ * g)⁻¹ * u * (x⁻¹ * g)) * (x⁻¹ * g)⁻¹ := by group
          _ = m * (m⁻¹ * u * m) * (x⁻¹ * g)⁻¹ := by rw [← hmu]
          _ = u * (m * (x⁻¹ * g)⁻¹) := by group
      have hg : g = x * (m * (x⁻¹ * g)⁻¹)⁻¹ * m := by group
      rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hxW)
        (Subgroup.inv_mem _ (hCWN u hu hu1 hc))) (Subgroup.mem_sup_right hm)
    intro gbar hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf Y) gbar
    by_contra hbot
    apply hne
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    obtain ⟨⟨u, hu, rfl⟩, ⟨_, ⟨v, hv, rfl⟩, hva⟩⟩ := Subgroup.mem_inf.mp ha
    have huW : (u : G) ∉ W := fun h => ha1 (Subtype.ext
      ((QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr h)))
    have hmem : (u : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) ∈ W := by
      have h : QuotientGroup.mk' (W.subgroupOf Y) u =
          QuotientGroup.mk' (W.subgroupOf Y) (g * v * g⁻¹) := by
        rw [← hva]
        simp [MulAut.conj_apply]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
    obtain ⟨w, hw, n, hn, hwn⟩ :
        ∃ w ∈ W, ∃ n ∈ Subgroup.normalizer (U : Set G), w * n = (g : G) := by
      have h := hkey g u (Subgroup.mem_subgroupOf.mp hu) v (Subgroup.mem_subgroupOf.mp hv) huW
        hmem
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W _ hNUY] at h
      exact Set.mem_mul.mp h
    have hg : g = ⟨w, hWY hw⟩ * ⟨n, hNUY hn⟩ := Subtype.ext hwn.symm
    have hπw : QuotientGroup.mk' (W.subgroupOf Y) ⟨w, hWY hw⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)
    have hnN : (⟨n, hNUY hn⟩ : Y) ∈ Subgroup.normalizer ((U.subgroupOf Y : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_comap Y.subtype hn
    have hπn := Subgroup.le_normalizer_map (QuotientGroup.mk' (W.subgroupOf Y))
      (Subgroup.mem_map_of_mem _ hnN)
    rw [hg, map_mul, hπw, one_mul]
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hπn
  ·
    intro u hu hu1 g hg
    obtain ⟨y, hyY, hy⟩ := N5a G S A Y hAS hAab hcl (hNA.trans hNUY) u g (hUY hu) hg
      ⟨1, by rw [pow_one]; exact hel.2 u hu⟩
    have hc : g * y⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * y⁻¹ * u = g * (y⁻¹ * u * y) * y⁻¹ := by group
        _ = u * (g * y⁻¹) := by rw [hy]; group
    simpa using Y.mul_mem (hCY u hu hu1 hc) hyY
  ·
    rw [isTI_iff_centralizer_le_normalizer S hUS hUcl hel.1,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    constructor
    · intro hC
      refine iSup_le fun u => iSup_le fun hu => iSup_le fun hu1 => ?_
      have hUC : U ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨u, hu⟩))
      exact le_centralizer_of_le_normalizer (odd_card_involutionOddCore u) hel
        ((Subgroup.map_subtype_le _).trans (hC u hu hu1))
        (hUC.trans (le_normalizer_oddCoreOf _))
    · intro hWU u hu hu1
      rw [hfac u hu hu1]
      exact sup_le ((hcoreW u hu hu1).trans (hWU.trans (Subgroup.centralizer_le_normalizer _)))
        inf_le_right

end CFSG.Goldschmidt
