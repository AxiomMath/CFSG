module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoCaseIPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoSecCaseI
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section Lift

theorem exists_lift_commuting_of_mul_self (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n)) {a' : G} (ha' : a' ∈ centralizer ({z} : Set G))
    (ha'2 : a' * a' = 1) {c : Perm (Fin n)}
    (hc : c * permOf T.toBase θ ha' = permOf T.toBase θ ha' * c) (hc2 : c * c = 1) :
    ∃ (s : G) (hs : s ∈ centralizer ({z} : Set G)), permOf T.toBase θ hs = c ∧
      s * a' = a' * s ∧ s * s = 1 := by
  obtain ⟨y, hy, hya⟩ := exists_oddY_conj_swapIota T θ ha' ha'2
  have hwC := swapIota_mem_centralizer T θ c
  have hws : (swapIota T θ c : G) * (swapIota T θ (permOf T.toBase θ ha') : G) =
      (swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G) := by
    have : swapIota T θ c * swapIota T θ (permOf T.toBase θ ha') =
        swapIota T θ (permOf T.toBase θ ha') * swapIota T θ c := by
      rw [← map_mul, ← map_mul, hc]
    exact congrArg Subtype.val this
  have hwz := (swapIota_comm_z T θ c).symm
  have hyC := oddY_le_centralizer_z T.cyc hy
  have hyw := mul_mem hyC hwC
  have hsC := mul_mem hyw (inv_mem hyC)
  refine ⟨_, hsC, ?_, ?_, ?_⟩
  · rw [permOf_mul T.toBase θ hyw (inv_mem hyC) hsC, permOf_mul T.toBase θ hyC hwC hyw,
      permOf_inv T.toBase θ hyC (inv_mem hyC), permOf_eq_one_of_mem_oddY T.toBase θ hy hyC,
      permOf_swapIota]
    group
  · have key : ∀ t : G, (swapIota T θ c : G) * t = t * (swapIota T θ c : G) →
        a' = y * t * y⁻¹ →
          y * (swapIota T θ c : G) * y⁻¹ * a' = a' * (y * (swapIota T θ c : G) * y⁻¹) := by
      intro t hwt hat
      rw [hat]
      calc y * (swapIota T θ c : G) * y⁻¹ * (y * t * y⁻¹) =
          y * ((swapIota T θ c : G) * t) * y⁻¹ := by group
        _ = y * (t * (swapIota T θ c : G)) * y⁻¹ := by rw [hwt]
        _ = y * t * y⁻¹ * (y * (swapIota T θ c : G) * y⁻¹) := by group
    rcases hya with h | h
    · exact key _ hws h
    · refine key _ ?_ h
      calc (swapIota T θ c : G) * (z * (swapIota T θ (permOf T.toBase θ ha') : G)) =
          ((swapIota T θ c : G) * z) * (swapIota T θ (permOf T.toBase θ ha') : G) := by group
        _ = (z * (swapIota T θ c : G)) * (swapIota T θ (permOf T.toBase θ ha') : G) := by
          rw [hwz]
        _ = z * ((swapIota T θ c : G) * (swapIota T θ (permOf T.toBase θ ha') : G)) := by group
        _ = z * ((swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G)) := by
          rw [hws]
        _ = z * (swapIota T θ (permOf T.toBase θ ha') : G) * (swapIota T θ c : G) := by group
  · have hcc := swapIota_mul_self T θ hc2
    calc y * (swapIota T θ c : G) * y⁻¹ * (y * (swapIota T θ c : G) * y⁻¹) =
        y * ((swapIota T θ c : G) * (swapIota T θ c : G)) * y⁻¹ := by group
      _ = 1 := by rw [hcc]; group

end Lift

section Conj

omit [Finite G] in
private theorem conj_mem_oddCoreOf_of_mem {H : Subgroup G} {g o : G} (hg : g ∈ H)
    (ho : o ∈ oddCoreOf H) : g * o * g⁻¹ ∈ oddCoreOf H := by
  obtain ⟨hoH, hoO⟩ := mem_oddCoreOf_iff.1 ho
  exact mem_oddCoreOf_iff.2 ⟨mul_mem (mul_mem hg hoH) (inv_mem hg),
    (inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem _ hoO ⟨g, hg⟩⟩

omit [Finite G] in
private theorem mem_centralizer_conj_iff {c y d : G} :
    d ∈ centralizer ({c * y * c⁻¹} : Set G) ↔ c⁻¹ * d * c ∈ centralizer ({y} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * d * c * y = c⁻¹ * (d * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * d) * c := by rw [h]
      _ = y * (c⁻¹ * d * c) := by group
  · intro h
    calc d * (c * y * c⁻¹) = c * ((c⁻¹ * d * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * d * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * d := by group

theorem weakClaim_conj {x z c w a : G} (hw : c * x * c⁻¹ = w) (ha : c * z * c⁻¹ = a)
    (hWC : ∀ d ∈ centralizer ({x} : Set G), ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)),
      o * d ∈ centralizer ({z} : Set G)) :
    Odd (Nat.card (conjSub c (oddCoreOf (centralizer ({x} : Set G))))) ∧
      conjSub c (oddCoreOf (centralizer ({x} : Set G))) ≤ centralizer ({w} : Set G) ∧
      (∀ g ∈ centralizer ({w} : Set G), ∀ o ∈ conjSub c (oddCoreOf (centralizer ({x} : Set G))),
        g * o * g⁻¹ ∈ conjSub c (oddCoreOf (centralizer ({x} : Set G)))) ∧
      ∀ d ∈ centralizer ({w} : Set G),
        ∃ o ∈ conjSub c (oddCoreOf (centralizer ({x} : Set G))),
          o * d ∈ centralizer ({a} : Set G) := by
  subst hw ha
  refine ⟨?_, fun o ho => ?_, fun g hg o ho => ?_, fun d hd => ?_⟩
  · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective, oddCoreOf,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact ComponentClassification.SmallLocal.odd_card_oddCore
  · rw [mem_conjSub_iff] at ho
    exact mem_centralizer_conj_iff.2 (mem_oddCoreOf_iff.1 ho).1
  · rw [mem_conjSub_iff] at ho ⊢
    have h1 := conj_mem_oddCoreOf_of_mem (mem_centralizer_conj_iff.1 hg) ho
    have h2 : c⁻¹ * (g * o * g⁻¹) * c = c⁻¹ * g * c * (c⁻¹ * o * c) * (c⁻¹ * g * c)⁻¹ := by
      group
    rw [h2]
    exact h1
  · obtain ⟨o, ho, hod⟩ := hWC _ (mem_centralizer_conj_iff.1 hd)
    refine ⟨c * o * c⁻¹, mem_conjSub_iff.2 ?_, ?_⟩
    · have h1 : c⁻¹ * (c * o * c⁻¹) * c = o := by group
      rw [h1]
      exact ho
    · rw [mem_centralizer_conj_iff]
      have h1 : c⁻¹ * (c * o * c⁻¹ * d) * c = o * (c⁻¹ * d * c) := by group
      rw [h1]
      exact hod

end Conj

section Commutator

theorem permOf_commutator_fix (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {w a : G} (hw : w ∈ centralizer ({z} : Set G)) (hw2 : w * w = 1)
    (hw1 : permOf T.toBase θ hw ≠ 1) (ha : a ∈ centralizer ({z} : Set G))
    (haw : a ∈ centralizer ({w} : Set G)) {Y : Subgroup G} (hYodd : Odd (Nat.card Y))
    (hYw : Y ≤ centralizer ({w} : Set G))
    (hYn : ∀ g ∈ centralizer ({w} : Set G), ∀ o ∈ Y, g * o * g⁻¹ ∈ Y)
    (hWC : ∀ c ∈ centralizer ({w} : Set G), ∃ o ∈ Y, o * c ∈ centralizer ({a} : Set G))
    {π₀ : Perm (Fin n)} (hπ₀ : π₀ * permOf T.toBase θ hw = permOf T.toBase θ hw * π₀) :
    (∀ i, permOf T.toBase θ hw i ≠ i →
        (π₀ * permOf T.toBase θ ha * π₀⁻¹ * (permOf T.toBase θ ha)⁻¹) i = i) ∧
      ((fixFin (permOf T.toBase θ hw)).card ≠ 3 →
        π₀ * permOf T.toBase θ ha = permOf T.toBase θ ha * π₀) := by
  have ht2 : permOf T.toBase θ hw * permOf T.toBase θ hw = 1 := by
    rw [← permOf_mul T.toBase θ hw hw (mul_mem hw hw),
      permOf_congr T.toBase θ hw2 (mul_mem hw hw) (one_mem _), permOf_one]
  let ψ : ↥(centralizer ({z} : Set G)) →* Perm (Fin n) :=
    (rho θ T.hn).comp (Subgroup.inclusion (cent_le_normalizer T.std T.cyc))
  have hψ : ∀ (x : G) (hx : x ∈ centralizer ({z} : Set G)), ψ ⟨x, hx⟩ = permOf T.toBase θ hx :=
    fun _ _ => rfl
  let D : Subgroup (Perm (Fin n)) := (Y.subgroupOf (centralizer ({z} : Set G))).map ψ
  have hDodd : Odd (Nat.card D) := by
    have h1 : Nat.card (Y.subgroupOf (centralizer ({z} : Set G))) ∣ Nat.card Y :=
      Subgroup.card_comap_dvd_of_injective Y _ (Subgroup.subtype_injective _)
    exact (hYodd.of_dvd_nat h1).of_dvd_nat (Subgroup.card_map_dvd _ ψ)
  have hDt : D ≤ centralizer ({permOf T.toBase θ hw} : Set (Perm (Fin n))) := by
    rintro _ ⟨⟨p, hpC⟩, hp, rfl⟩
    have hpw : p * w = w * p :=
      mem_centralizer_singleton_iff.1 (hYw (Subgroup.mem_subgroupOf.1 hp))
    rw [mem_centralizer_singleton_iff, hψ, ← permOf_mul T.toBase θ hpC hw (mul_mem hpC hw),
      ← permOf_mul T.toBase θ hw hpC (mul_mem hw hpC)]
    exact permOf_congr T.toBase θ hpw _ _
  have hDn : ∀ g : Perm (Fin n), g * permOf T.toBase θ hw = permOf T.toBase θ hw * g →
      ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    rintro g hg _ ⟨⟨p, hpC⟩, hp, rfl⟩
    obtain ⟨t', ht'C, hpt', ht'w⟩ := exists_lift_commuting T θ hw hw2 hg
    refine ⟨⟨t', ht'C⟩ * ⟨p, hpC⟩ * ⟨t', ht'C⟩⁻¹, Subgroup.mem_subgroupOf.2
      (hYn t' (mem_centralizer_singleton_iff.2 ht'w) p (Subgroup.mem_subgroupOf.1 hp)), ?_⟩
    simp only [map_mul, map_inv]
    rw [hψ t' ht'C, hpt']
  obtain ⟨t, htC, hpt, htw⟩ := exists_lift_commuting T θ hw hw2 hπ₀
  obtain ⟨o, hoY, hoa⟩ := hWC t (mem_centralizer_singleton_iff.2 htw)
  have hoat : o * t * a = a * (o * t) := mem_centralizer_singleton_iff.1 hoa
  have hkY : t * a * t⁻¹ * a⁻¹ ∈ Y := by
    have h1 : t * a * t⁻¹ * a⁻¹ = o⁻¹ * (a * o * a⁻¹) := by
      calc t * a * t⁻¹ * a⁻¹ = o⁻¹ * (o * t * a) * t⁻¹ * a⁻¹ := by group
        _ = o⁻¹ * (a * (o * t)) * t⁻¹ * a⁻¹ := by rw [hoat]
        _ = o⁻¹ * (a * o * a⁻¹) := by group
    rw [h1]
    exact mul_mem (inv_mem hoY) (hYn a haw o hoY)
  have hkD : π₀ * permOf T.toBase θ ha * π₀⁻¹ * (permOf T.toBase θ ha)⁻¹ ∈ D := by
    refine ⟨⟨t, htC⟩ * ⟨a, ha⟩ * ⟨t, htC⟩⁻¹ * ⟨a, ha⟩⁻¹, Subgroup.mem_subgroupOf.2 hkY, ?_⟩
    simp only [map_mul, map_inv]
    rw [hψ t htC, hψ a ha, hpt]
  obtain ⟨h1, h2⟩ := fix_of_mem_oddNormal ht2 hw1 hDodd hDt hDn hkD
  refine ⟨h1, fun h3 => ?_⟩
  calc π₀ * permOf T.toBase θ ha =
      (π₀ * permOf T.toBase θ ha * π₀⁻¹ * (permOf T.toBase θ ha)⁻¹) *
        (permOf T.toBase θ ha * π₀) := by group
    _ = permOf T.toBase θ ha * π₀ := by rw [h2 h3, one_mul]

end Commutator

section Endgame

theorem false_of_caseI_of_weakClaim (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt θ z S₀)
    (hclaim : ∀ {x : G} (hx : x ∈ centralizer ({z} : Set G)), (permOf T.toBase θ hx).IsSwap →
      x * x = 1 → ∀ c ∈ centralizer ({x} : Set G), ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)),
        o * c ∈ centralizer ({z} : Set G)) : False := by
  classical
  have hz2 : z * z = 1 := T.cyc.mul_self
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hz1 : z ≠ 1 := fun h1 => by
    have := T.cyc.order
    rw [h1, orderOf_one] at this
    omega
  have hpz : permOf T.toBase θ hzC = 1 :=
    (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem)
  have hker : ∀ (m : G) (hm : m ∈ centralizer ({z} : Set G)), permOf T.toBase θ hm = 1 →
      m * m = 1 → m = 1 ∨ m = z := by
    intro m hm hp hm2
    have hmz : m ∈ zpowers z := mem_zpowers_of_two_pow T.cyc T.card
      ⟨(permOf_eq_one_iff T.toBase θ hm).1 hp, hm⟩ (k := 1) (by rw [pow_one, pow_two]; exact hm2)
    exact eq_one_or_eq_of_card_eq_two T.cyc T.card
      (by rw [eq_zpowers_of_card_eq_two_of_cyc T.cyc T.card]; exact hmz)
  have hnear : ∀ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b → b ≠ z →
      (permOf T.toBase θ hb).IsSwap → False := by
    intro b hb hzb hbz hsw
    obtain ⟨g, hg⟩ := isConj_iff.1 hzb
    exact near_partner_false T θ hk hkn hI hb hg hbz
      ⟨by rw [card_fixFin_of_isSwap hsw]; omega, by rw [card_fixFin_of_isSwap hsw]; omega⟩
  obtain ⟨g, hne, hcomm, -, -⟩ := exists_zstar_partner T.std T.cyc
  set c : G := g⁻¹ with hc
  set a : G := c * z * c⁻¹ with ha
  set a' : G := c⁻¹ * z * c with ha'
  have haeq : a = g⁻¹ * z * g := by rw [ha, hc, inv_inv]
  have haC : a ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, haeq]; exact hcomm
  have haz : a ≠ z := by rw [haeq]; exact hne
  have ha'C : a' ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, ha', hc, inv_inv]
    calc g * z * g⁻¹ * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * z) * g⁻¹ := by rw [hcomm]
      _ = z * (g * z * g⁻¹) := by group
  have ha'z : a' ≠ z := by
    intro h'
    apply hne
    rw [ha', hc, inv_inv] at h'
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h']
      _ = z := by group
  have ha'2 : a' * a' = 1 := by
    rw [ha']
    calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
      _ = 1 := by rw [hz2]; group
  have ha2 : a * a = 1 := by
    rw [ha]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  set σ' := permOf T.toBase θ ha'C with hσ'
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    rcases hker a' ha'C h1 ha'2 with h2 | h2
    · apply hz1
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = 1 := by rw [← ha', h2]; group
    · exact ha'z h2
  have hσ'2 : σ' * σ' = 1 := by
    rw [hσ', ← permOf_mul T.toBase θ ha'C ha'C (mul_mem ha'C ha'C),
      permOf_congr T.toBase θ ha'2 (mul_mem ha'C ha'C) (one_mem _), permOf_one]
  obtain ⟨τ, hτs, hτc, hτne⟩ := exists_swap_comm_ne (by omega) hσ'2 hσ'1
  have hτ2 : τ * τ = 1 := by
    obtain ⟨p, q, -, rfl⟩ := hτs
    exact swap_mul_self p q
  have hτ1 : τ ≠ 1 := by
    obtain ⟨p, q, hpq, rfl⟩ := hτs
    intro h
    have := congrArg (fun f : Perm (Fin n) => f p) h
    simp only [Perm.one_apply, swap_apply_left] at this
    exact hpq this.symm
  obtain ⟨xt, hxtC, hpxt, hxta', hxt2⟩ :=
    exists_lift_commuting_of_mul_self T θ ha'C ha'2 hτc hτ2
  have hxtz : xt * z = z * xt := mem_centralizer_singleton_iff.1 hxtC
  set ea : G := c * xt * c⁻¹ with hea
  have heaC : ea ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff, hea]
    calc c * xt * c⁻¹ * z = c * (xt * (c⁻¹ * z * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * z * c) * xt) * c⁻¹ := by rw [← ha', hxta']
      _ = z * (c * xt * c⁻¹) := by group
  have hea2 : ea * ea = 1 := by
    rw [hea]
    calc c * xt * c⁻¹ * (c * xt * c⁻¹) = c * (xt * xt) * c⁻¹ := by group
      _ = 1 := by rw [hxt2]; group
  have haea : a * ea = ea * a := by
    rw [ha, hea]
    calc c * z * c⁻¹ * (c * xt * c⁻¹) = c * (z * xt) * c⁻¹ := by group
      _ = c * (xt * z) * c⁻¹ := by rw [hxtz]
      _ = c * xt * c⁻¹ * (c * z * c⁻¹) := by group
  set s := permOf T.toBase θ haC with hs
  set e' := permOf T.toBase θ heaC with he'
  have hs2 : s * s = 1 := by
    rw [hs, ← permOf_mul T.toBase θ haC haC (mul_mem haC haC),
      permOf_congr T.toBase θ ha2 (mul_mem haC haC) (one_mem _), permOf_one]
  have he'2 : e' * e' = 1 := by
    rw [he', ← permOf_mul T.toBase θ heaC heaC (mul_mem heaC heaC),
      permOf_congr T.toBase θ hea2 (mul_mem heaC heaC) (one_mem _), permOf_one]
  have hse : s * e' = e' * s := by
    rw [hs, he', ← permOf_mul T.toBase θ haC heaC (mul_mem haC heaC),
      ← permOf_mul T.toBase θ heaC haC (mul_mem heaC haC)]
    exact permOf_congr T.toBase θ haea _ _
  have hxtz' : xt ≠ z := by
    intro h'
    have h1 := permOf_congr T.toBase θ h' hxtC hzC
    rw [hpxt, hpz] at h1
    exact hτ1 h1
  have hxta'z : xt ≠ a' * z := by
    intro h'
    have hm := mul_mem ha'C hzC
    have h1 := permOf_congr T.toBase θ h' hxtC hm
    rw [hpxt, permOf_mul T.toBase θ ha'C hzC hm, hpz, mul_one] at h1
    exact hτne h1
  have he'1 : e' ≠ 1 := by
    intro h1
    rcases hker ea heaC h1 hea2 with h2 | h2
    · apply hτ1
      have hxt1 : xt = 1 := by
        calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
          _ = 1 := by rw [← hea, h2]; group
      have h3 := permOf_congr T.toBase θ hxt1 hxtC (one_mem _)
      rw [hpxt, permOf_one] at h3
      exact h3
    · apply hτne
      have hxt' : xt = a' := by
        calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
          _ = c⁻¹ * z * c := by rw [← hea, h2]
      have h3 := permOf_congr T.toBase θ hxt' hxtC ha'C
      rw [hpxt] at h3
      exact h3
  have hswx : (permOf T.toBase θ hxtC).IsSwap := by rw [hpxt]; exact hτs
  obtain ⟨hY1odd, hY1le, hY1n, hY1WC⟩ :=
    weakClaim_conj hea.symm ha.symm (hclaim hxtC hswx hxt2)
  have haea' : a ∈ centralizer ({ea} : Set G) := mem_centralizer_singleton_iff.2 haea
  have hM1 : ∀ π₀ : Perm (Fin n), π₀ * e' = e' * π₀ →
      (∀ i, e' i ≠ i → (π₀ * s * π₀⁻¹ * s⁻¹) i = i) ∧
        ((fixFin e').card ≠ 3 → π₀ * s = s * π₀) := fun π₀ hπ₀ =>
    permOf_commutator_fix T θ heaC hea2 he'1 haC haea' hY1odd hY1le hY1n hY1WC hπ₀
  rcases perm_cases_of_comm_fix he'2 hs2 hse (fun π₀ hπ₀ => (hM1 π₀ hπ₀).1)
      (fun h3 π₀ hπ₀ => (hM1 π₀ hπ₀).2 h3) with
    hs1 | hse' | ⟨p, q, hpq, hp, hq, hcard, hs3 | hs4⟩
  ·
    rcases hker a haC hs1 ha2 with h1 | h1
    · apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [← ha, h1]; group
    · exact haz h1
  ·
    have hyC := mul_mem haC heaC
    have hy2 : a * ea * (a * ea) = 1 := by
      calc a * ea * (a * ea) = a * (ea * a) * ea := by group
        _ = a * (a * ea) * ea := by rw [← haea]
        _ = (a * a) * (ea * ea) := by group
        _ = 1 := by rw [ha2, hea2, one_mul]
    have hpy : permOf T.toBase θ hyC = 1 := by
      rw [permOf_mul T.toBase θ haC heaC hyC, ← hs, ← he', hse', he'2]
    rcases hker _ hyC hpy hy2 with h1 | h1
    ·
      apply hxtz'
      have h2 : ea = a := by
        calc ea = (a * a) * ea := by rw [ha2, one_mul]
          _ = a * (a * ea) := by group
          _ = a := by rw [h1, mul_one]
      calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
        _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [← hea, h2, ha]
        _ = z := by group
    ·
      apply hxta'z
      have h2 : ea = z * a := by
        calc ea = ea * (a * a) := by rw [ha2, mul_one]
          _ = a * ea * a := by rw [← mul_assoc, ← haea]
          _ = z * a := by rw [h1]
      calc xt = c⁻¹ * (c * xt * c⁻¹) * c := by group
        _ = c⁻¹ * (z * (c * z * c⁻¹)) * c := by rw [← hea, h2, ha]
        _ = a' * z := by rw [ha']; group
  ·
    exact hnear a haC (isConj_iff.2 ⟨c, ha.symm⟩) haz ⟨p, q, hpq, hs3⟩
  ·
    have hep : e' * swap p q = swap p q * e' := by
      rw [mul_swap_eq_swap_mul, hp, hq]
    have hyC : a * ea ∈ centralizer ({z} : Set G) := mul_mem haC heaC
    have hpy : permOf T.toBase θ hyC = swap p q := by
      rw [permOf_mul T.toBase θ haC heaC hyC, ← hs, ← he', hs4, mul_assoc, ← hep, ← mul_assoc,
        he'2, one_mul]
    have hy2 : a * ea * (a * ea) = 1 := by
      calc a * ea * (a * ea) = a * (ea * a) * ea := by group
        _ = a * (a * ea) * ea := by rw [← haea]
        _ = (a * a) * (ea * ea) := by group
        _ = 1 := by rw [ha2, hea2, one_mul]
    have hy1 : permOf T.toBase θ hyC ≠ 1 := by
      rw [hpy]
      intro h
      have := congrArg (fun f : Perm (Fin n) => f p) h
      simp only [Perm.one_apply, swap_apply_left] at this
      exact hpq this.symm
    have hzxtC : z * xt ∈ centralizer ({z} : Set G) := mul_mem hzC hxtC
    have hswzx : (permOf T.toBase θ hzxtC).IsSwap := by
      rw [permOf_mul T.toBase θ hzC hxtC hzxtC, hpz, one_mul, hpxt]
      exact hτs
    have hzxt2 : z * xt * (z * xt) = 1 := by
      calc z * xt * (z * xt) = z * (xt * z) * xt := by group
        _ = z * (z * xt) * xt := by rw [hxtz]
        _ = (z * z) * (xt * xt) := by group
        _ = 1 := by rw [hz2, hxt2, one_mul]
    have hyeq : c * (z * xt) * c⁻¹ = a * ea := by rw [ha, hea]; group
    obtain ⟨hY2odd, hY2le, hY2n, hY2WC⟩ :=
      weakClaim_conj hyeq ha.symm (hclaim hzxtC hswzx hzxt2)
    have hay : a ∈ centralizer ({a * ea} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc a * (a * ea) = a * (ea * a) := by rw [haea]
        _ = a * ea * a := by group
    have hfixpq : (fixFin (swap p q)).card = n - 2 := card_fixFin_of_isSwap ⟨p, q, hpq, rfl⟩
    have hcase2 := perm_cases_of_forall_comm (e' := swap p q) (s := s) (swap_mul_self p q)
      fun π₀ hπ₀ => (permOf_commutator_fix T θ hyC hy2 hy1 haC hay hY2odd hY2le hY2n hY2WC
        (π₀ := π₀) (by rw [hpy]; exact hπ₀)).2 (by rw [hpy, hfixpq]; omega)
    rcases hcase2 with h1 | h1 | ⟨p', q', hpq', hfix', -⟩
    ·
      have h2 : e' = swap p q := by
        rw [hs4] at h1
        calc e' = e' * swap p q * swap p q := by rw [mul_assoc, swap_mul_self, mul_one]
          _ = swap p q := by rw [h1, one_mul]
      rw [h2, hfixpq] at hcard
      omega
    ·
      apply he'1
      rw [hs4] at h1
      calc e' = e' * swap p q * swap p q := by rw [mul_assoc, swap_mul_self, mul_one]
        _ = 1 := by rw [h1, swap_mul_self]
    ·
      have h2 : (fixFin (swap p q)).card = 2 := by
        have : fixFin (swap p q) = {p', q'} := by
          ext i
          rw [mem_fixFin, hfix']
          simp
        rw [this, Finset.card_pair hpq']
      rw [hfixpq] at h2
      omega

theorem false_of_caseI_w (htri : ExactShapeTrichotomy) (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) (hn12 : n ≠ 12)
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt θ z S₀) : False :=
  false_of_caseI_of_weakClaim T θ hk hkn hI fun hx hτ hx2 =>
    twoSec_central_of_caseI htri hlookup hHN hOut hFour T θ hn hn12 hk hkn hI hx hτ hx2

end Endgame

end CFSG.OddStandard.AltStdCycTwo.Two
