module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.Aut

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem map_mem_borel_iff {P : Subgroup K} {α : MulAut K} (hαP : ∀ p, α p ∈ P ↔ p ∈ P)
    (g : K) : α g ∈ borel P ↔ g ∈ borel P := by
  simp only [CFSG.GH74.Uniqueness.Bender.borel, mem_normalizer_iff]
  constructor
  · intro h y
    rw [← hαP y, ← hαP (g * y * g⁻¹), map_mul, map_mul, map_inv]
    exact h (α y)
  · intro h y
    obtain ⟨y', rfl⟩ := α.surjective y
    rw [hαP y', ← map_inv, ← map_mul, ← map_mul, hαP]
    exact h y'

omit [Finite K] in
theorem mul_conj (α : MulAut K) (g : K) : α * MulAut.conj g = MulAut.conj (α g) * α := by
  ext x
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem centralizes_rootCenter (e : K ≃* PSU3Model 2)
    (P : Sylow 2 K) {z : K} (hz : z ∈ rootCenter (P : Subgroup K)) (hz1 : z ≠ 1)
    (α : MulAut K) (hαP : ∀ p, α p ∈ (P : Subgroup K) ↔ p ∈ (P : Subgroup K)) (hαz : α z = z)
    (hα2 : α * α = MulAut.conj z) {t : K} (ht : t ∈ rootCenter (P : Subgroup K)) :
    α t = t := by
  have hB : BenderType K 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) := .unitary 2 le_rfl e
  obtain ⟨w, hc⟩ := hB.exists_benderCore P
  set Pg : Subgroup K := (P : Subgroup K) with hPg
  have hzP : z ∈ Pg := rootCenter_le _ hz
  have hzo : orderOf z = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hc.center_sq z hz) hz1
  have hαZ : ∀ y ∈ rootCenter Pg, α y ∈ rootCenter Pg := by
    intro y hy
    rw [mem_rootCenter_iff] at hy ⊢
    refine ⟨(hαP y).mpr hy.1, fun p hp => ?_⟩
    obtain ⟨p', rfl⟩ := α.surjective p
    rw [← map_mul, ← map_mul, hy.2 p' ((hαP p').mp hp)]
  have hαw : α w ∉ borel Pg := fun h => hc.not_mem ((map_mem_borel_iff hαP w).mp h)
  obtain ⟨p, hp, m, hm, hpm⟩ := hc.bruhat hαw
  set u : MulAut K := MulAut.conj p⁻¹ * α with hu
  have hu_apply : ∀ y, u y = p⁻¹ * α y * p := fun y => by
    rw [hu, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have huP : ∀ y, u y ∈ Pg ↔ y ∈ Pg := fun y => by
    rw [hu_apply, ← hαP y]
    constructor
    · intro h
      have := mul_mem (mul_mem hp h) (inv_mem hp)
      simpa [mul_assoc] using this
    · intro h
      exact mul_mem (mul_mem (inv_mem hp) h) hp
  have huB : ∀ y, u y ∈ borel Pg ↔ y ∈ borel Pg := map_mem_borel_iff huP
  set q : K := p⁻¹ * (α p)⁻¹ * z with hq
  have hqP : q ∈ Pg := mul_mem (mul_mem (inv_mem hp) (inv_mem ((hαP p).mpr hp))) hzP
  have huu : u * u = MulAut.conj q := by
    rw [hu, mul_assoc, ← mul_assoc α, mul_conj, mul_assoc, hα2, ← mul_assoc, ← map_mul,
      ← map_mul, map_inv, hq, mul_assoc]
  have hw2 : w * w = 1 := hc.sq_eq_one
  have hwi : w⁻¹ = w := inv_eq_of_mul_self hw2
  have hq1 : q = 1 := by
    have h1 : u w = w * (m * p) := by
      rw [hu_apply, hpm]
      group
    have hmp : m * p ∈ borel Pg := mul_mem hm (le_borel Pg hp)
    have h2 : (u * u) w = w * ((m * p) * u (m * p)) := by
      rw [MulAut.mul_apply, h1, map_mul, h1, mul_assoc]
    rw [huu, MulAut.conj_apply] at h2
    have hb : (m * p) * u (m * p) ∈ borel Pg := mul_mem hmp ((huB _).mpr hmp)
    have h3 : w * q * w⁻¹ ∈ borel Pg := by
      have : w * q * w⁻¹ = ((m * p) * u (m * p)) * q := by
        rw [hwi]
        calc w * q * w = w * (q * w * q⁻¹) * q := by group
          _ = w * (w * ((m * p) * u (m * p))) * q := by rw [h2]
          _ = ((m * p) * u (m * p)) * q := by rw [← mul_assoc w w, hw2, one_mul]
      rw [this]
      exact mul_mem hb (le_borel Pg hqP)
    have hcart : q ∈ cartan Pg w :=
      mem_inf.mpr ⟨le_borel Pg hqP, mem_conjugate_iff_mul_inv.mpr h3⟩
    have := hc.inf_eq
    have hmem : q ∈ Pg ⊓ cartan Pg w := mem_inf.mpr ⟨hqP, hcart⟩
    rw [this, mem_bot] at hmem
    exact hmem
  have hu2 : u * u = 1 := by rw [huu, hq1, map_one]
  have hcommZ : ∀ y ∈ rootCenter Pg, p⁻¹ * y * p = y := fun y hy => by
    rw [(mem_rootCenter_iff.mp hy).2 p⁻¹ (inv_mem hp)]
    group
  have hut : u t = α t := by rw [hu_apply, hcommZ _ (hαZ t ht)]
  have huz : u z = z := by rw [hu_apply, hαz, hcommZ z hz]
  rw [← hut]
  by_cases hinn : ∃ g : K, ∀ x : K, u x = g * x * g⁻¹
  ·
    obtain ⟨g, hg⟩ := hinn
    have hgg : g * g ∈ center K := by
      rw [mem_center_iff]
      intro x
      have h1 : (u * u) x = x := by rw [hu2, MulAut.one_apply]
      rw [MulAut.mul_apply, hg, hg] at h1
      calc x * (g * g) = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = g * g * x := by group
    rw [hB.center_eq_bot, mem_bot] at hgg
    have hgB : g ∈ borel Pg := by
      rw [CFSG.GH74.Uniqueness.Bender.borel, mem_normalizer_iff]
      intro y
      rw [← hg, huP]
    by_cases hg1 : g = 1
    · rw [hg, hg1]
      group
    · have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hgg) hg1
      have hgZ := hc.center_of_involution g hgB hgo
      rw [hg, ← (mem_rootCenter_iff.mp hgZ).2 t (rootCenter_le _ ht)]
      group
  ·
    obtain ⟨eF⟩ := hB.fixed_unitary u hu2 hinn
    set F : Subgroup K := autFixed u with hF
    have hzF : z ∈ F := huz
    have hBF : BenderType F 2 1 1 := .linear 2 le_rfl eF
    have hz2 : (⟨z, hzF⟩ : F) * ⟨z, hzF⟩ = 1 := Subtype.ext (hc.center_sq z hz)
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 F, (⟨z, hzF⟩ : F) ∈ (Q : Subgroup F) := by
      have hzp : IsPGroup 2 (zpowers (⟨z, hzF⟩ : F)) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, pow_one]
        apply orderOf_eq_prime (by rw [sq]; exact hz2)
        intro h
        exact hz1 (congrArg Subtype.val h)
      obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
      exact ⟨Q, hQ (mem_zpowers _)⟩
    obtain ⟨w', hc'⟩ := hBF.exists_benderCore Q
    have hQ4 : Nat.card (Q : Subgroup F) = 4 := by
      have := hc'.card_eq
      norm_num at this
      exact this
    have hRQ : rootCenter (Q : Subgroup F) = (Q : Subgroup F) := by
      refine eq_of_le_of_card_ge (rootCenter_le _) ?_
      rw [hQ4, hc'.card_center]
      norm_num
    set V : Subgroup K := (Q : Subgroup F).map F.subtype with hV
    have hV4 : Nat.card V = 4 := by
      rw [hV, card_map_of_injective F.subtype_injective, hQ4]
    have hVZ : V ≤ rootCenter Pg := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : v ∈ rootCenter (Q : Subgroup F) := by rw [hRQ]; exact hv
      have hvz : (v : K) * z = z * v :=
        congrArg Subtype.val ((mem_rootCenter_iff.mp hvR).2 ⟨z, hzF⟩ hQ).symm
      have hvB : (v : K) ∈ borel Pg := by
        refine hc.mem_borel_of_conj (le_borel Pg hzP) hzo ?_
        rw [show (v : K)⁻¹ * z * v = z by rw [mul_assoc, ← hvz]; group]
        exact le_borel Pg hzP
      by_cases hv1 : (v : K) = 1
      · change (v : K) ∈ rootCenter Pg
        rw [hv1]
        exact one_mem _
      · have hv2 : (v : K) * v = 1 := congrArg Subtype.val (hc'.center_sq v hvR)
        exact hc.center_of_involution _ hvB (orderOf_eq_prime (by rw [sq]; exact hv2) hv1)
    have hVeq : V = rootCenter Pg := by
      refine eq_of_le_of_card_ge hVZ ?_
      rw [hV4, hc.card_center]
      norm_num
    have htV : t ∈ V := by rw [hVeq]; exact ht
    obtain ⟨v, -, rfl⟩ := htV
    exact v.2

end CFSG.ComponentClassification.Foote5.Asc25
