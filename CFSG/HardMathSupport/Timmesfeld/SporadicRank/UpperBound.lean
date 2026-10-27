module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.Open CFSG.SectionRank

theorem pRank_le_of_sylow {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (P : Subgroup X) (hP : Nat.card P = p ^ (Nat.card X).factorization p) {k : ℕ}
    (h : ∀ E : Subgroup X, E ≤ P → IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ k := by
  have := Fact.mk hp
  refine pRank_le hp.one_lt fun E _ hE => ?_
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  let S : Sylow p X := Sylow.ofCard P hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  have hSg : ((g • S : Sylow p X) : Subgroup X) =
      (S : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]; rfl
  have hEP : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup X) := hEQ hx
    rw [← hg, hSg] at hxQ
    obtain ⟨y, hy, rfl⟩ := hxQ
    have hyP : y ∈ P := hy
    simpa [MulAut.conj_apply, mul_assoc] using hyP
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have := h _ hEP (isElemAbelian_map hE (MulAut.conj g⁻¹).toMonoidHom)
  rwa [hcard] at this

theorem exists_exponents {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hC : ∀ x : G, (∀ a ∈ N, x * a = a * x) → x ∈ N) {n t : ℕ}
    (hN : Nat.card N = p ^ n) (hG : Nat.card G = p ^ (n + t)) {z : ℕ}
    (hz : Nat.card ↥(N ⊓ Subgroup.center G) ≤ p ^ z)
    (E : Subgroup G) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ a j, Nat.card E = p ^ (a + j) ∧ a ≤ n ∧ j ≤ t ∧ (0 < j → a < n) ∧ (j = t → a ≤ z) := by
  let f : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hfker : f.ker = N.subgroupOf E := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hfrange : f.range = E.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEN : Nat.card (E ⊓ N : Subgroup G) = Nat.card (f.ker) := by
    rw [hfker]
    have : N.subgroupOf E = (E ⊓ N).subgroupOf E := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ N ≤ E)).toEquiv).symm
  have hdecomp : Nat.card E = Nat.card (E ⊓ N : Subgroup G) *
      Nat.card (E.map (QuotientGroup.mk' N)) := by
    have := Subgroup.card_ker_mul_card_range f
    rw [hfrange] at this
    rw [hEN, ← this]
  have hQ : Nat.card (G ⧸ N) = p ^ t := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hG, hN, pow_add] at h1
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n)
    rw [← h1]
    ring
  obtain ⟨a, ha, haE⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (E ⊓ N : Subgroup G) ∣ p ^ n from
      hN ▸ Subgroup.card_dvd_of_le (inf_le_right : E ⊓ N ≤ N))
  obtain ⟨j, hj, hjE⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (E.map (QuotientGroup.mk' N)) ∣ p ^ t from
      hQ ▸ Subgroup.card_subgroup_dvd_card _)
  refine ⟨a, j, by rw [hdecomp, haE, hjE, pow_add], ha, hj, fun hj0 => ?_, fun hjt => ?_⟩
  · refine lt_of_le_of_ne ha fun han => ?_
    have hNE : N ≤ E := by
      have : E ⊓ N = N := Subgroup.eq_of_le_of_card_ge (inf_le_right)
        (by rw [haE, hN, han])
      exact this ▸ inf_le_left
    have hEN' : E ≤ N := fun x hx => hC x fun a ha' => hEc x hx a (hNE ha')
    have : E.map (QuotientGroup.mk' N) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hEN' hx
    rw [this, Subgroup.card_bot] at hjE
    have h1 : p ^ j = 1 := hjE.symm
    rcases Nat.pow_eq_one.mp h1 with h | h
    · exact absurd h hp.ne_one
    · omega
  ·
    have htop : E.map (QuotientGroup.mk' N) = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [hjE, hjt, hQ]
    have hcenter : E ⊓ N ≤ N ⊓ Subgroup.center G := by
      refine fun x hx => ⟨hx.2, ?_⟩
      show x ∈ Subgroup.center G
      rw [Subgroup.mem_center_iff]
      intro g
      have hgq : (QuotientGroup.mk g : G ⧸ N) ∈ E.map (QuotientGroup.mk' N) := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨e, he, hge⟩ := hgq
      have hn : e⁻¹ * g ∈ N := by
        rw [← QuotientGroup.eq]
        exact hge
      obtain ⟨m, hm, hgm⟩ : ∃ m ∈ N, g = e * m := ⟨e⁻¹ * g, hn, by group⟩
      rw [hgm, mul_assoc, ← hNc x hx.2 m hm, ← mul_assoc, ← hEc x hx.1 e he, mul_assoc]
    have := Subgroup.card_le_of_le hcenter
    rw [haE] at this
    have h2 : p ^ a ≤ p ^ z := this.trans hz
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

theorem card_elemAbelian_le_of_setup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (A P : Subgroup X) (hAP : A ≤ P) (hnorm : P ≤ Subgroup.normalizer (A : Set X))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hC : ∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) {n t z : ℕ}
    (hA : Nat.card A = p ^ n) (hP : Nat.card P = p ^ (n + t))
    (hz : Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set X)) ≤ p ^ z)
    (E : Subgroup X) (hEP : E ≤ P) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ a j, Nat.card E = p ^ (a + j) ∧ a ≤ n ∧ j ≤ t ∧ (0 < j → a < n) ∧ (j = t → a ≤ z) := by
  have hNn : (A.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).2 hnorm
  have hNcard : Nat.card (A.subgroupOf P) = p ^ n := by
    rw [← hA]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hEcard : Nat.card (E.subgroupOf P) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  have hz' : Nat.card ↥((A.subgroupOf P) ⊓ Subgroup.center ↥P) ≤ p ^ z := by
    refine le_trans ?_ hz
    have hle : ((A.subgroupOf P) ⊓ Subgroup.center ↥P).map P.subtype ≤
        A ⊓ Subgroup.centralizer (P : Set X) := by
      rintro _ ⟨x, ⟨hxA, hxZ⟩, rfl⟩
      refine ⟨hxA, ?_⟩
      show (x : X) ∈ Subgroup.centralizer (P : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hxZ ⟨g, hg⟩
      exact congrArg Subtype.val this
    rw [← Subgroup.card_map_of_injective P.subtype_injective]
    exact Subgroup.card_le_of_le hle
  obtain ⟨a, j, h1, h2, h3, h4, h5⟩ := exists_exponents (G := ↥P) hp (A.subgroupOf P)
    (fun a ha b hb => Subtype.ext (hAc a ha b hb))
    (fun x hx => hC x x.2 fun a ha => by
      have := hx ⟨a, hAP ha⟩ ha
      exact congrArg Subtype.val this) hNcard hP hz'
    (E.subgroupOf P) (fun x hx y hy => Subtype.ext (hEc x hx y hy))
  exact ⟨a, j, by rw [← hEcard]; exact h1, h2, h3, h4, h5⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
