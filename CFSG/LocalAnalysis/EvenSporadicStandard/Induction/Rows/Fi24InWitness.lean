module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InGeo

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Sporadic.Fi24
open CFSG.Fischer hiding OutTwo
open CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (edge_hW)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


local notation "W" => (LocalClass D24 tR ∩ LocalClass D24 xb)

attribute [local instance] fi24inKAction

theorem fi24in_exists_pair_odd :
    ∃ p q : ↥W, p ≠ q ∧ (p : R) * q = q * p ∧ ∃ H : Subgroup ↥fi24inK, Odd H.index ∧
      ∀ k ∈ H, (k • p = p ∧ k • q = q) ∨ (k • p = q ∧ k • q = p) := by
  have hfin : Finite ↥W := Nat.finite_of_card_ne_zero (by rw [fi24in_card_W]; norm_num)
  refine fi24in_exists_odd_index_edge (Γ := ↥fi24inK) (V := ↥W)
    (r := fun p q : ↥W => (p : R) * q = q * p) ?_ ?_ (d := 693) (m := 1755)
    ⟨346, by norm_num⟩ ⟨877, by norm_num⟩ ?_ ?_
  · intro k p q
    exact fi24in_commute_smul_iff k p q
  · intro p q h
    exact h.symm
  · rw [fi24in_card_W]
  · intro p
    exact fi24in_card_commuting_W p

theorem fi24in_mul_ne_tJ {p q : R} (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q) (hc : p * q = q * p) :
    p * q ≠ tR * xb := by
  intro h1
  obtain ⟨ψ, hψc, -⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  obtain ⟨w, hw, hne⟩ := edge_hW ψ hψc p hp
  have hwc : w * (p * q) = p * q * w := by
    rw [h1]
    exact (Commute.mul_right (hw.1.2.2 : Commute w tR) (hw.2.2.2 : Commute w xb)).eq
  rcases (commute_mul_iff pair_R hp.1.1 hq.1.1 hpq hc hw.1.1).1 hwc with h2 | h2 | h2
  · exact hne (by rw [h2])
  · exact hne (by rw [h2]; exact hc)
  · exact hne h2.1.2.2.symm

theorem fi24in_exists_witness :
    ∃ v : J, v ∈ vCandidates fi24inK tJ ∧
      twoAdic fi24inK ≤ twoAdic (fi24inK ⊓ centralizer ({v} : Set J)) ∧
      ∃ l : J, l * tJ * l⁻¹ = tJ * v := by
  obtain ⟨p, q, hpq, hcomm, H, hHodd, hH⟩ := fi24in_exists_pair_odd
  have hpD : (p : R) ∈ D24 := p.2.1.1
  have hqp : (q : R) ∈ LocalClass D24 (p : R) :=
    ⟨q.2.1.1, fun h => hpq (Subtype.ext h.symm), hcomm.symm⟩
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair hpD hqp
  have hpT : Commute (p : R) tR := p.2.1.2.2
  have hpx : Commute (p : R) xb := p.2.2.2.2
  have hqT : Commute (q : R) tR := q.2.1.2.2
  have hqx : Commute (q : R) xb := q.2.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : J, x = g⁻¹ * tJ * g := ⟨_, rfl⟩
  have hjx : jR x = (p : R) * q := by
    have e1 : (p : R) = (jR g)⁻¹ * tR * jR g := by
      calc (p : R) = (jR g)⁻¹ * (jR g * p * (jR g)⁻¹) * jR g := by group
        _ = (jR g)⁻¹ * tR * jR g := by rw [hg1]
    have e2 : (q : R) = (jR g)⁻¹ * xb * jR g := by
      calc (q : R) = (jR g)⁻¹ * (jR g * q * (jR g)⁻¹) * jR g := by group
        _ = (jR g)⁻¹ * xb * jR g := by rw [hg2]
    rw [hx, map_mul, map_mul, map_inv, jR_tJ, e1, e2]
    group
  have hxx : x * x = 1 := by
    rw [hx]
    calc g⁻¹ * tJ * g * (g⁻¹ * tJ * g) = g⁻¹ * (tJ * tJ) * g := by group
      _ = 1 := by rw [tJ_mul_tJ]; group
  have hxK : x ∈ fi24inK := by
    rw [mem_fi24inK_iff, hjx]
    exact ⟨((Commute.mul_right hpT hpx).mul_left (Commute.mul_right hqT hqx)).eq,
      (hpT.mul_left hqT).eq⟩
  have hxt : x ≠ tJ := by
    intro h
    exact fi24in_mul_ne_tJ p.2 q.2 (fun h => hpq (Subtype.ext h)) hcomm
      (by rw [← hjx, h, jR_tJ])
  have hxt' : x * tJ = tJ * x := by
    have h := (Subgroup.mem_inf.1 hxK).1
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hvv : tJ * x * (tJ * x) = 1 := by
    calc tJ * x * (tJ * x) = tJ * (x * tJ) * x := by group
      _ = tJ * (tJ * x) * x := by rw [hxt']
      _ = (tJ * tJ) * (x * x) := by group
      _ = 1 := by rw [tJ_mul_tJ, hxx, one_mul]
  have hv1 : tJ * x ≠ 1 := fun h => hxt (by
    calc x = tJ * (tJ * x) := by rw [← mul_assoc, tJ_mul_tJ, one_mul]
      _ = tJ := by rw [h, mul_one])
  have hvt : tJ * x ≠ tJ := fun h => tJ_ne_one (by
    have h1 : x = 1 := by
      calc x = tJ * (tJ * x) := by rw [← mul_assoc, tJ_mul_tJ, one_mul]
        _ = 1 := by rw [h, tJ_mul_tJ]
    calc tJ = g * x * g⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h1]; group)
  have hvK : tJ * x ∈ fi24inK := fi24inK.mul_mem fi24in_tJ_mem_K hxK
  refine ⟨tJ * x, fi24in_mem_vCandidates_K_iff.2 ⟨hvK, hv1, hvt, hvv⟩, ?_, g⁻¹, ?_⟩
  · have hHle : H.map fi24inK.subtype ≤ fi24inK ⊓ centralizer ({tJ * x} : Set J) := by
      rintro _ ⟨k, hk, rfl⟩
      refine Subgroup.mem_inf.2 ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkt : (k : J) * tJ = tJ * k := by
        have h := (Subgroup.mem_inf.1 k.2).1
        rw [Subgroup.mem_centralizer_singleton_iff] at h
        exact h
      have hkx : (k : J) * x = x * k := by
        apply jR_injective
        rw [map_mul, map_mul, hjx]
        have key : jR (k : J) * ((p : R) * q) * (jR (k : J))⁻¹ = (p : R) * q := by
          rcases hH k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have e1 := congrArg Subtype.val h1
            have e2 := congrArg Subtype.val h2
            rw [fi24in_smul_val] at e1 e2
            calc jR (k : J) * ((p : R) * q) * (jR (k : J))⁻¹ =
                (jR (k : J) * p * (jR (k : J))⁻¹) * (jR (k : J) * q * (jR (k : J))⁻¹) := by group
              _ = (p : R) * q := by rw [e1, e2]
          · have e1 := congrArg Subtype.val h1
            have e2 := congrArg Subtype.val h2
            rw [fi24in_smul_val] at e1 e2
            calc jR (k : J) * ((p : R) * q) * (jR (k : J))⁻¹ =
                (jR (k : J) * p * (jR (k : J))⁻¹) * (jR (k : J) * q * (jR (k : J))⁻¹) := by group
              _ = (q : R) * p := by rw [e1, e2]
              _ = (p : R) * q := hcomm.symm
        rw [mul_inv_eq_iff_eq_mul] at key
        exact key
      calc (k : J) * (tJ * x) = ((k : J) * tJ) * x := by group
        _ = tJ * ((k : J) * x) := by rw [hkt]; group
        _ = tJ * (x * k) := by rw [hkx]
        _ = tJ * x * k := by group
    have hrel : (fi24inK ⊓ centralizer ({tJ * x} : Set J)).relIndex fi24inK ∣ H.index := by
      have h1 := Subgroup.relIndex_dvd_of_le_left (L := fi24inK) hHle
      have h2 : (H.map fi24inK.subtype).relIndex fi24inK = H.index := by
        show ((H.map fi24inK.subtype).comap fi24inK.subtype).index = H.index
        rw [Subgroup.comap_map_eq_self_of_injective fi24inK.subtype_injective]
      rwa [h2] at h1
    exact (fi24in_twoAdic_eq_of_odd_relIndex inf_le_left (Odd.of_dvd_nat hHodd hrel)).ge
  · rw [inv_inv, ← hx, ← mul_assoc, tJ_mul_tJ, one_mul]

theorem fi24in_pairs_pinned : (vPairs (⊤ : Subgroup J) fi24inK tJ).Nonempty := by
  obtain ⟨v, hv, h2, l, hl⟩ := fi24in_exists_witness
  exact ⟨tJ * v, v, fi24in_mem_vMaximal_of_twoAdic hv h2, rfl, l, Subgroup.mem_top l, hl⟩

end CFSG.EvenSporadicStandard.Induction
