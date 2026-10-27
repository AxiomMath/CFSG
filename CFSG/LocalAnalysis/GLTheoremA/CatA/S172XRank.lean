module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.S172 (Cfg172)

variable {Ω : Type} [Group Ω]

theorem exists_elemAbelian_sup_zpowers [Finite Ω] {S : Subgroup Ω} {p : ℕ} (hp : p.Prime) {x : Ω}
    (hx : x ∈ Subgroup.centralizer (S : Set Ω)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    {E P : Subgroup ↥S} (hE : IsElemAbelian p E) (hEZ : E ⊓ Subgroup.center ↥S = ⊥)
    (hP1 : P ≠ ⊥) (hP2 : IsPGroup 2 P) (hEP : E ≤ Subgroup.normalizer (P : Set ↥S)) :
    ∃ F Q : Subgroup Ω, IsElemAbelian p F ∧ Nat.card F = p * Nat.card E ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      F ≤ Subgroup.normalizer (Q : Set Ω) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hZc : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) := Subgroup.zpowers_le.2 hx
  have hZab : IsElemAbelian p (Subgroup.zpowers x) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a rfl b rfl
      rfl
    · rintro a rfl
      exact hxp
  have hE' : IsElemAbelian p (E.map S.subtype) := hE.map S.subtype
  have hcomm : ∀ a ∈ E.map S.subtype, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rintro _ ⟨e, he, rfl⟩ b hb
    exact Subgroup.mem_centralizer_iff.1 (hZc hb) (e : Ω) e.2
  have hinf : E.map S.subtype ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨e, he, rfl⟩, haZ⟩
    have hec : e ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hZc haZ) (g : Ω) g.2)
    have h1 : e ∈ E ⊓ Subgroup.center ↥S := ⟨he, hec⟩
    rw [hEZ] at h1
    have he1 : e = 1 := h1
    subst he1
    exact Subgroup.one_mem _
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (E.map S.subtype)
    (Subgroup.zpowers x) hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, Subgroup.card_map_of_injective S.subtype_injective,
    Nat.card_zpowers, orderOf_eq_prime hxp hx1] at hcard
  have hQS : ((P.map S.subtype : Subgroup Ω) : Set Ω) ⊆ (S : Set Ω) := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  refine ⟨E.map S.subtype ⊔ Subgroup.zpowers x, P.map S.subtype,
    hE'.sup_of_commute hZab hcomm, ?_, ?_, hP2.map S.subtype, sup_le ?_ ?_⟩
  · rw [hcard, mul_comm]
  · intro h
    exact hP1 (Subgroup.map_injective S.subtype_injective (by rw [h, Subgroup.map_bot]))
  · exact (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map S.subtype)
  · exact hZc.trans ((Subgroup.centralizer_le hQS).trans (Subgroup.centralizer_le_normalizer _))

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

theorem isElemAbelian_range_β {p : ℕ} (hB : IsElemAbelian p B) : IsElemAbelian p M.β.range := by
  refine ⟨⟨⟨fun a c => ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨c', hc'⟩ := c.2
    apply Subtype.ext
    show (a : G₀) * c = c * a
    rw [← ha', ← hc', ← map_mul, ← map_mul]
    exact congrArg M.β (Subtype.ext (hB.comm a'.2 c'.2))
  · obtain ⟨b, rfl⟩ := hg
    rw [← map_pow, show b ^ p = 1 from Subtype.ext (hB.2 _ b.2), map_one]

theorem card_ker_β {p : ℕ} (hp : p.Prime) (hB : IsElemAbelian p B) {x : Ω} (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hx : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x) :
    Nat.card M.β.ker = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hker : M.β.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, M.β_eq_one_iff_mem_zpowers hx, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
    orderOf_eq_prime hxp hx1]

theorem card_range_β [Finite Ω] {p m : ℕ} {D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg172 p S B D K x) (hR : LiftableRank p G₀ m) : Nat.card M.β.range = p ^ m := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hker := M.card_ker_β hp hcfg.elem hcfg.mem hcfg.ne_one hcfg.cent
  have hmul := Subgroup.card_ker_mul_card_range M.β
  rw [hker] at hmul
  refine le_antisymm (hR.1 _ (M.isElemAbelian_range_β hcfg.elem)) ?_
  obtain ⟨E, P, hE, hEcard, hEker, hP1, hP2, hEP⟩ :=
    hR.exists_elemAbelian_lift hp hcfg.odd M.π M.surj (by rw [M.ker_π])
  rw [M.ker_π] at hEker
  obtain ⟨F, Q, hF, hFcard, hQ1, hQ2, hFQ⟩ := exists_elemAbelian_sup_zpowers hp
    ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)) hcfg.ne_one (hcfg.elem.2 x hcfg.mem)
    hE hEker hP1 hP2 hEP
  have h1 := card_le_pow_glaTwoLocalRank hp hF hQ1 hQ2 hFQ
  rw [hFcard, hEcard] at h1
  have h3 : p * p ^ m ≤ p * Nat.card M.β.range :=
    calc p * p ^ m ≤ p ^ GLATwoLocalRank p Ω := h1
      _ ≤ Nat.card B := hcfg.rank
      _ = p * Nat.card M.β.range := hmul.symm
  exact Nat.le_of_mul_le_mul_left h3 hp.pos

end S172Model

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
