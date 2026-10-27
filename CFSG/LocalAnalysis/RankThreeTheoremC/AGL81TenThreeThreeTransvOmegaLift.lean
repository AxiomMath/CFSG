module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltSmall
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.OmegaMinusEight

open CFSG.Open CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

variable {A : Type} [Group A]

theorem commutator_pow_mem_pCoreOf {P : Subgroup A} {x : A}
    (hxP : x ∈ normalizer (P : Set A)) (hx : ∀ w ∈ P, x * w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 P)
    (n : ℕ) : ∀ w ∈ P, x ^ n * w * (x ^ n)⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
  have hxO : x ∈ normalizer (pCoreOf 2 P : Set A) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hxP
  intro w hw
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x * (x ^ n * w * (x ^ n)⁻¹ * w⁻¹) * x⁻¹ ∈ pCoreOf 2 P :=
      (mem_normalizer_iff.1 hxO _).1 ih
    have h2 := (pCoreOf 2 P).mul_mem h1 (hx w hw)
    have he : x * (x ^ n * w * (x ^ n)⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹) =
        x ^ (n + 1) * w * (x ^ (n + 1))⁻¹ * w⁻¹ := by group
    rwa [he] at h2

variable [Finite A]

theorem exists_mem_inf_centralizer_lift {P : Subgroup A} {z : A}
    (hzP : z ∈ normalizer (P : Set A)) (hodd : Odd (orderOf z))
    (hz : ∀ w ∈ P, z * w * z⁻¹ * w⁻¹ ∈ pCoreOf 2 P) (x : ↥P ⧸ CFSG.pCore 2 ↥P) :
    ∃ d : ↥(P ⊓ centralizer {z}),
      QuotientGroup.mk' (CFSG.pCore 2 ↥P) (inclusion inf_le_left d) = x := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, hh, hzh⟩ := exists_centralizing_lift hzP hodd w.2 (hz w w.2)
  exact ⟨⟨h, h.2, mem_centralizer_singleton_iff.2 hzh.symm⟩, hh⟩

theorem exists_card_inf_centralizer {P : Subgroup A} {z : A}
    (hzP : z ∈ normalizer (P : Set A)) (hodd : Odd (orderOf z))
    (hz : ∀ w ∈ P, z * w * z⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∃ j : ℕ, Nat.card ↥(P ⊓ centralizer {z}) = 2 ^ j * Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) := by
  set f : ↥(P ⊓ centralizer {z}) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp (inclusion inf_le_left) with hf
  have hsurj : Function.Surjective f := fun x => exists_mem_inf_centralizer_lift hzP hodd hz x
  have hker : f.ker = (CFSG.pCore 2 ↥P).comap (inclusion inf_le_left) := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).comap_of_injective _
      (inclusion_injective _)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (G := f.ker)).1 hp
  refine ⟨j, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, hj,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, mul_comm]

theorem mem_of_central_of_prime_order {C D : Subgroup A} (hDC : D ≤ C) {r : ℕ} (hr : r.Prime)
    {z : A} (hzC : z ∈ C) (hzr : orderOf z = r) (hcent : ∀ c ∈ C, c * z = z * c)
    (hdvd : ∀ k : ℕ, r ^ k ∣ Nat.card C → r ^ k ∣ Nat.card D) : z ∈ D := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  obtain ⟨S⟩ : Nonempty (Sylow r ↥D) := inferInstance
  set n := (Nat.card C).factorization r
  have h1 : (Nat.card D).factorization r ≤ n :=
    (Nat.factorization_le_iff_dvd hD0 hC0).2 (card_dvd_of_le hDC) r
  have h2 : n ≤ (Nat.card D).factorization r :=
    (hr.pow_dvd_iff_le_factorization hD0).1 (hdvd n (Nat.ordProj_dvd _ _))
  have hS : Nat.card ((S : Subgroup ↥D).map (inclusion hDC)) = r ^ n := by
    rw [card_map_of_injective (inclusion_injective hDC), S.card_eq_multiplicity,
      le_antisymm h1 h2]
  set T : Sylow r ↥C := Sylow.ofCard _ hS
  set z' : ↥C := ⟨z, hzC⟩ with hz'
  have hz'ord : orderOf z' = r := by rw [hz', Subgroup.orderOf_mk, hzr]
  have hnorm : (zpowers z').Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hm
    have hc : Commute g z' := Subtype.ext (hcent g g.2)
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers z' k
  have hp : IsPGroup r (zpowers z') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz'ord, pow_one]
  obtain ⟨d, -, hdz⟩ := hp.le_sylow_of_normal T (mem_zpowers z')
  have h3 : (d : A) = z := congrArg Subtype.val hdz
  rw [← h3]
  exact d.2

theorem card_dvd_factorial_relIndex {Y C : Subgroup A} [IsSimpleGroup ↥Y] (hCY : C ≤ Y)
    (hne : C ≠ Y) : Nat.card Y ∣ (C.relIndex Y).factorial := by
  set H : Subgroup ↥Y := C.subgroupOf Y
  have hHtop : H ≠ ⊤ := by
    intro h
    refine hne (le_antisymm hCY fun y hy => ?_)
    have : (⟨y, hy⟩ : ↥Y) ∈ H := h ▸ mem_top _
    exact this
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ H.normalCore_le)) hHtop
  have h1 := H.index_normalCore_dvd_factorial_index
  rwa [hcore, index_bot] at h1

theorem center_eq_bot_of_card_not_prime {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · exfalso
    have hcomm : ∀ a c : X, a * c = c * a := fun a c =>
      Subgroup.mem_center_iff.1 (hc ▸ mem_top c) a
    letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    exact h IsSimpleGroup.prime_card

theorem isQuasisimple_of_card_not_prime {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : CFSG.Open.IsQuasisimple X := by
  have hZ := center_eq_bot_of_card_not_prime h
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hc | hc
  · exfalso
    have hcomm : ∀ a c : X, a * c = c * a := fun a c => by
      have h1 : ⁅a, c⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← hc]
        exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top c)
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    exact h IsSimpleGroup.prime_card
  · exact hc

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.OmegaMinusEight
