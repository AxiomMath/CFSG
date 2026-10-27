module

public import CFSG.HardMathSupport.Dickson.ElementCaseBp.Fixed
public import CFSG.HardMathSupport.Dickson.ElementCaseBp.Moved

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance
open scoped commutatorElement

private theorem mem_normalizer_of_conjSub_eq' {Y : Type*} [Group Y] {g : Y} {K : Subgroup Y}
    (h : conjSub g K = K) : g ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (g := g) hy
    rwa [h] at this
  · intro hy
    have h1 : g * y * g⁻¹ ∈ conjSub g K := by rw [h]; exact hy
    have := mem_conjSub_iff.1 h1
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this

private theorem commutator_le_left_of_le_normalizer {Y : Type*} [Group Y] {K L : Subgroup Y}
    (hL : L ≤ Subgroup.normalizer (K : Set Y)) : ⁅K, L⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have h := (Subgroup.mem_normalizer_iff.mp (hL hl) k⁻¹).mp (K.inv_mem hk)
  have e : ⁅k, l⁆ = k * (l * k⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact K.mul_mem hk h

private theorem commutator_eq_bot_of_le_sSup {Y : Type*} [Group Y] {L O : Subgroup Y}
    {𝒦 : Set (Subgroup Y)} (hL : ⁅L, L⁆ = L) (hLE : L ≤ sSup 𝒦)
    (hK : ∀ K ∈ 𝒦, ⁅L, O⁆ ≤ Subgroup.centralizer (K : Set Y)) : ⁅L, O⁆ = ⊥ := by
  have h1 : sSup 𝒦 ≤ Subgroup.centralizer ((⁅L, O⁆ : Subgroup Y) : Set Y) :=
    sSup_le fun K hK' => Subgroup.le_centralizer_iff.mp (hK K hK')
  have h2 : ⁅⁅L, O⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp (hLE.trans h1))
  have h3 : ⁅⁅O, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm O L]; exact h2
  have h4 : ⁅⁅L, L⁆, O⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rwa [hL] at h4

theorem commutator_pLayer_pPrimeCore_centralizer_eq_bot {Z : Type} [Group Z] [Finite Z]
    {p : ℕ} [Fact p.Prime] (hO : CFSG.pPrimeCore p Z = ⊥)
    (hK : ∀ K : Subgroup Z, CFSG.IsComponent K →
      Group.IsSolvable
          (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥K ⧸ Subgroup.center ↥K)) ∧
        CFSG.Yardstones.Md42047359a2a.SimpleBp p (↥K ⧸ Subgroup.center ↥K))
    {x : Z} (hx : ∃ n : ℕ, x ^ p ^ n = 1) (hxc : x ^ p ∈ Subgroup.center Z)
    (hN : ∀ K : Subgroup Z, CFSG.IsComponent K →
      (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({x} : Set Z))).map
        (Subgroup.centralizer ({x} : Set Z)).subtype ≤ Subgroup.normalizer (K : Set Z)) :
    ⁅(CFSG.pLayer ↥(Subgroup.centralizer ({x} : Set Z)) p).map
        (Subgroup.centralizer ({x} : Set Z)).subtype,
      (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({x} : Set Z))).map
        (Subgroup.centralizer ({x} : Set Z)).subtype⁆ = ⊥ := by
  set C : Subgroup Z := Subgroup.centralizer ({x} : Set Z)
  set O : Subgroup Z := (CFSG.pPrimeCore p ↥C).map C.subtype
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L₀ hL₀ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  set L : Subgroup Z := L₀.map C.subtype
  have hLC : L ≤ C := Subgroup.map_subtype_le L₀
  have hLeq : L.subgroupOf C = L₀ :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective L₀
  have hL : CFSG.IsPComponent p (L.subgroupOf C) := by
    rw [hLeq]
    exact hL₀
  have hLperf : ⁅L, L⁆ = L := by
    have h1 := CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect p _ hL
    have h2 : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hLE : L ≤ CFSG.layer Z :=
    CFSG.ComponentClassification.LBalance.pComponent_centralizer_le_layer hO hx
      (fun K hKc => (hK K hKc).1) hLC hL
  have key : ∀ K : Subgroup Z, CFSG.IsComponent K →
      ⁅L, O⁆ ≤ Subgroup.centralizer (K : Set Z) := by
    intro K hKc
    by_cases hxK : x ∈ Subgroup.normalizer (K : Set Z)
    · exact commutator_le_centralizer_of_mem_normalizer hKc (hK K hKc).2 hxK hxc hLC hL hLE
        (hN K hKc)
    · have hmoved : conjSub x K ≠ K := fun h => hxK (mem_normalizer_of_conjSub_eq' h)
      have hOK : O ≤ Subgroup.centralizer (K : Set Z) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (commute_of_moved_of_pow_mem_center Fact.out hKc
          (p_dvd_card_center_quot Fact.out hO hKc) hxc hmoved hd
          (fun i => hN (conjSub (x ^ i) K) (isComponent_conjSub' hKc _) hd) k hk).symm
      have hKO : K ≤ Subgroup.centralizer (O : Set Z) := Subgroup.le_centralizer_iff.mp hOK
      have hLK : L ≤ Subgroup.normalizer (K : Set Z) :=
        hLE.trans (CFSG.LocalCores.layer_le_normalizer hKc)
      have h1 : ⁅⁅O, K⁆, L⁆ = ⊥ := by
        have h0 : ⁅O, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hOK
        rw [h0]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr bot_le
      have h2 : ⁅⁅K, L⁆, O⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((commutator_le_left_of_le_normalizer hLK).trans hKO)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_le_sSup (𝒦 := {K : Subgroup Z | CFSG.IsComponent K}) hLperf
      (hLE.trans (CFSG.layer.eq_sSup Z).le) key)

theorem elementCaseBp : CFSG.Yardstones.Md42047359a2a.ElementCaseBp := by
  intro Z _ _ p hp hO hK x hx hxc hN a ha b hb
  haveI : Fact p.Prime := ⟨hp⟩
  rw [CFSG.ComponentClassification.LBalance.primeCore_top] at hO
  rw [CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map] at ha
  rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map] at hb
  have hN' : ∀ K : Subgroup Z, CFSG.IsComponent K →
      (CFSG.pPrimeCore p ↥(Subgroup.centralizer ({x} : Set Z))).map
        (Subgroup.centralizer ({x} : Set Z)).subtype ≤ Subgroup.normalizer (K : Set Z) := by
    intro K hKc
    have h := hN K hKc
    rwa [CFSG.ComponentClassification.LBalance.primeCore_eq_map] at h
  have h := commutator_pLayer_pPrimeCore_centralizer_eq_bot hO hK hx hxc hN'
  have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
  exact (Subgroup.mem_centralizer_iff.mp h2 b hb).symm

end CFSG.HardMathSupport.Dickson.ElementCaseBp
