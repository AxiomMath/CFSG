module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveScalar

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.Asc75Lemma31

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_card_eq_two [Finite G] {H : Subgroup G} (h2 : Nat.card H = 2) {a b : G}
    (ha : a ∈ H) (ha1 : a ≠ 1) (hb : b ∈ H) : b = 1 ∨ b = a := by
  have hle : zpowers a ≤ H := zpowers_le.mpr ha
  have hdvd : orderOf a ∣ 2 := by
    rw [← Nat.card_zpowers, ← h2]
    exact card_dvd_of_le hle
  have hord : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h1
  have heq : zpowers a = H := eq_of_le_of_card_ge hle (by rw [h2, Nat.card_zpowers, hord])
  exact eq_one_or_eq_of_mem_zpowers hord (heq ▸ hb)

section ElemAbelian

variable [Finite G] {E : Subgroup G} (hE : IsElemAbelian 2 E) {u : G}
  (huN : u ∈ normalizer (E : Set G)) (hu2 : u * u ∈ centralizer (E : Set G))
include hE huN hu2

omit [Finite G] hE hu2 in
theorem mul_conj_mem (e : G) (he : e ∈ E) : u * e * u⁻¹ * e ∈ E :=
  mul_mem ((mem_normalizer_iff.mp huN e).mp he) he

omit [Finite G] in
theorem mul_conj_comm (e : G) (he : e ∈ E) : u * (u * e * u⁻¹ * e) = (u * e * u⁻¹ * e) * u := by
  have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have he' : u * e * u⁻¹ ∈ E := (mem_normalizer_iff.mp huN e).mp he
  have h1 : u * u * e = e * (u * u) := (mem_centralizer_iff.mp hu2 e he).symm
  calc u * (u * e * u⁻¹ * e) = (u * u * e) * u⁻¹ * e := by group
    _ = (e * (u * u)) * u⁻¹ * e := by rw [h1]
    _ = e * (u * e * u⁻¹) * u := by group
    _ = (u * e * u⁻¹) * e * u := by rw [hab e he _ he']
    _ = (u * e * u⁻¹ * e) * u := by group

theorem card_le_sq_card_inf_centralizer :
    Nat.card E ≤ Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 := by
  have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let δ : ↥E →* ↥E :=
    { toFun := fun e => ⟨u * e * u⁻¹ * e, mul_conj_mem huN e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb' : u * (b : G) * u⁻¹ ∈ E := (mem_normalizer_iff.mp huN b).mp b.2
        simp only [coe_mul]
        calc u * ((a : G) * b) * u⁻¹ * (a * b) = (u * a * u⁻¹) * ((u * b * u⁻¹) * a) * b := by
              group
          _ = (u * a * u⁻¹) * (a * (u * b * u⁻¹)) * b := by rw [hab _ hb' _ a.2]
          _ = u * a * u⁻¹ * a * (u * b * u⁻¹ * b) := by group }
  have hker : Nat.card δ.ker = Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    have h1 : δ.ker = (E ⊓ centralizer ({u} : Set G)).subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      have he2 : (e : G) * e = 1 := by rw [← sq]; exact hE.2 e e.2
      constructor
      · intro he
        have h2 : u * (e : G) * u⁻¹ * e = 1 := congrArg Subtype.val he
        refine mem_inf.mpr ⟨e.2, mem_centralizer_singleton_iff.mpr ?_⟩
        have h3 : u * (e : G) * u⁻¹ = e := by
          calc u * (e : G) * u⁻¹ = u * e * u⁻¹ * e * e := by
                rw [mul_assoc (u * (e : G) * u⁻¹) (e : G) (e : G), he2, mul_one]
            _ = e := by rw [h2, one_mul]
        calc (e : G) * u = u * e * u⁻¹ * u := by rw [h3]
          _ = u * e := by group
      · intro he
        apply Subtype.ext
        have h3 : u * (e : G) = e * u := (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2).symm
        change u * (e : G) * u⁻¹ * e = 1
        rw [h3, mul_inv_cancel_right, he2]
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card δ.range ≤ Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    have hle : δ.range ≤ (E ⊓ centralizer ({u} : Set G)).subgroupOf E := by
      rintro _ ⟨e, rfl⟩
      rw [mem_subgroupOf]
      exact mem_inf.mpr ⟨mul_conj_mem huN e e.2,
        mem_centralizer_singleton_iff.mpr (mul_conj_comm hE huN hu2 e e.2).symm⟩
    calc Nat.card δ.range ≤ Nat.card ((E ⊓ centralizer ({u} : Set G)).subgroupOf E) :=
          card_le_of_le hle
      _ = Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) :=
          Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range δ
  rw [hker] at h1
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ hrange

theorem exists_conj_eq_mul_of_sq_le
    (hcard : Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 ≤ Nat.card E) {c : G}
    (hcE : c ∈ E) (hcu : u * c = c * u) : ∃ e ∈ E, e⁻¹ * u * e = u * c := by
  have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let δ : ↥E →* ↥E :=
    { toFun := fun e => ⟨u * e * u⁻¹ * e, mul_conj_mem huN e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb' : u * (b : G) * u⁻¹ ∈ E := (mem_normalizer_iff.mp huN b).mp b.2
        simp only [coe_mul]
        calc u * ((a : G) * b) * u⁻¹ * (a * b) = (u * a * u⁻¹) * ((u * b * u⁻¹) * a) * b := by
              group
          _ = (u * a * u⁻¹) * (a * (u * b * u⁻¹)) * b := by rw [hab _ hb' _ a.2]
          _ = u * a * u⁻¹ * a * (u * b * u⁻¹ * b) := by group }
  set C := (E ⊓ centralizer ({u} : Set G)).subgroupOf E with hCdef
  have hCcard : Nat.card C = Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hker : δ.ker = C := by
    ext e
    rw [MonoidHom.mem_ker, hCdef, mem_subgroupOf]
    have he2 : (e : G) * e = 1 := by rw [← sq]; exact hE.2 e e.2
    constructor
    · intro he
      have h2 : u * (e : G) * u⁻¹ * e = 1 := congrArg Subtype.val he
      refine mem_inf.mpr ⟨e.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h3 : u * (e : G) * u⁻¹ = e := by
        calc u * (e : G) * u⁻¹ = u * e * u⁻¹ * e * e := by
              rw [mul_assoc (u * (e : G) * u⁻¹) (e : G) (e : G), he2, mul_one]
          _ = e := by rw [h2, one_mul]
      calc (e : G) * u = u * e * u⁻¹ * u := by rw [h3]
        _ = u * e := by group
    · intro he
      apply Subtype.ext
      have h3 : u * (e : G) = e * u := (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2).symm
      change u * (e : G) * u⁻¹ * e = 1
      rw [h3, mul_inv_cancel_right, he2]
  have hle : δ.range ≤ C := by
    rintro _ ⟨e, rfl⟩
    rw [hCdef, mem_subgroupOf]
    exact mem_inf.mpr ⟨mul_conj_mem huN e e.2,
      mem_centralizer_singleton_iff.mpr (mul_conj_comm hE huN hu2 e e.2).symm⟩
  have heq : δ.range = C := by
    apply eq_of_le_of_card_ge hle
    have h1 := Subgroup.card_ker_mul_card_range δ
    rw [hker] at h1
    have hpos : 0 < Nat.card C := Nat.card_pos
    rw [hCcard] at hpos ⊢
    rw [hCcard] at h1
    rw [sq] at hcard
    have h2 : Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) *
        Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ≤
        Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) * Nat.card δ.range := by
      rw [h1]; exact hcard
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hcC : (⟨c, hcE⟩ : ↥E) ∈ δ.range := by
    rw [heq, hCdef, mem_subgroupOf]
    exact mem_inf.mpr ⟨hcE, mem_centralizer_singleton_iff.mpr hcu.symm⟩
  obtain ⟨e, he⟩ := hcC
  have he' : u * (e : G) * u⁻¹ * e = c := congrArg Subtype.val he
  refine ⟨e, e.2, ?_⟩
  have he2 : (e : G) * e = 1 := by rw [← sq]; exact hE.2 e e.2
  have heinv : (e : G)⁻¹ = e := by
    calc (e : G)⁻¹ = (e : G)⁻¹ * (e * e) := by rw [he2, mul_one]
      _ = e := by group
  have h1 : u * u * e = e * (u * u) := (mem_centralizer_iff.mp hu2 e e.2).symm
  rw [← he', heinv]
  calc (e : G) * u * e = e * (u * u) * u⁻¹ * e := by group
    _ = u * u * e * u⁻¹ * e := by rw [h1]
    _ = u * (u * e * u⁻¹ * e) := by group

end ElemAbelian

section FourGroup

variable [Finite G]

theorem exists_fixed_of_card_four {E Q : Subgroup G} (hE4 : Nat.card E = 4) (hQ : IsPGroup 2 Q)
    (hQE : Q ≤ normalizer (E : Set G)) :
    ∃ e₀ ∈ E, e₀ ≠ 1 ∧ ∀ q ∈ Q, q * e₀ * q⁻¹ = e₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α := {e : ↥E // e ≠ 1}
  have hmem : ∀ (q : ↥Q) (e : ↥E), (q : G) * e * (q : G)⁻¹ ∈ E := fun q e =>
    (mem_normalizer_iff.mp (hQE q.2) e).mp e.2
  have hne : ∀ (q : ↥Q) (e : α), (⟨(q : G) * e.1 * (q : G)⁻¹, hmem q e.1⟩ : ↥E) ≠ 1 := by
    intro q e he
    apply e.2
    apply Subtype.ext
    have h1 : (q : G) * e.1 * (q : G)⁻¹ = 1 := congrArg Subtype.val he
    calc ((e.1 : ↥E) : G) = (q : G)⁻¹ * ((q : G) * e.1 * (q : G)⁻¹) * q := by group
      _ = 1 := by rw [h1]; group
  let : MulAction ↥Q α :=
    { smul := fun q e => ⟨⟨(q : G) * e.1 * (q : G)⁻¹, hmem q e.1⟩, hne q e⟩
      one_smul := fun e => Subtype.ext (Subtype.ext (by
        change ((1 : ↥Q) : G) * e.1 * ((1 : ↥Q) : G)⁻¹ = e.1
        simp))
      mul_smul := fun q r e => Subtype.ext (Subtype.ext (by
        change ((q * r : ↥Q) : G) * e.1 * ((q * r : ↥Q) : G)⁻¹ =
          (q : G) * ((r : G) * e.1 * (r : G)⁻¹) * (q : G)⁻¹
        simp only [coe_mul]
        group)) }
  have hα : Nat.card α = 3 := by
    classical
    have := Fintype.ofFinite ↥E
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hE4]
  obtain ⟨⟨e, he1⟩, he⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card α (by rw [hα]; decide)
  refine ⟨e, e.2, fun h1 => he1 (Subtype.ext h1), fun q hq => ?_⟩
  have h2 := congrArg (fun a : α => ((a.1 : ↥E) : G)) (he ⟨q, hq⟩)
  exact h2

theorem mul_mem_centralizer_of_card_four {E Q : Subgroup G} (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) (hQ : IsPGroup 2 Q) (hQE : Q ≤ normalizer (E : Set G)) {a b : G}
    (ha : a ∈ Q) (hb : b ∈ Q) (haC : a ∉ centralizer (E : Set G))
    (hbC : b ∉ centralizer (E : Set G)) : a * b ∈ centralizer (E : Set G) := by
  obtain ⟨e₀, he₀, he₀1, hfix⟩ := exists_fixed_of_card_four hE4 hQ hQE
  obtain ⟨e₁, he₁, he₁1, he₁0⟩ := exists_ne_one_ne hE4 hE2 he₀
  have hE : ∀ w ∈ E, w = 1 ∨ w = e₀ ∨ w = e₁ ∨ w = e₀ * e₁ := fun w hw =>
    mem_four hE4 hE2 he₀ he₁ he₀1 he₁1 he₁0.symm hw
  have hconjE : ∀ q ∈ Q, ∀ w ∈ E, q * w * q⁻¹ ∈ E := fun q hq w hw =>
    (mem_normalizer_iff.mp (hQE hq) w).mp hw
  have himg : ∀ q ∈ Q, q * e₁ * q⁻¹ = e₁ ∨ q * e₁ * q⁻¹ = e₀ * e₁ := by
    intro q hq
    rcases hE _ (hconjE q hq e₁ he₁) with h1 | h1 | h1 | h1
    · exfalso
      apply he₁1
      calc e₁ = q⁻¹ * (q * e₁ * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply he₁0
      calc e₁ = q⁻¹ * (q * e₁ * q⁻¹) * q := by group
        _ = q⁻¹ * (q * e₀ * q⁻¹) * q := by rw [h1, hfix q hq]
        _ = e₀ := by group
    · exact Or.inl h1
    · exact Or.inr h1
  have hcen : ∀ q ∈ Q, q * e₁ * q⁻¹ = e₁ → q ∈ centralizer (E : Set G) := by
    intro q hq hq1
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : q * w * q⁻¹ = w := by
      rcases hE w hw with rfl | rfl | rfl | rfl
      · group
      · exact hfix q hq
      · exact hq1
      · calc q * (e₀ * e₁) * q⁻¹ = (q * e₀ * q⁻¹) * (q * e₁ * q⁻¹) := by group
          _ = e₀ * e₁ := by rw [hfix q hq, hq1]
    calc w * q = q * w * q⁻¹ * q := by rw [hw']
      _ = q * w := by group
  have ha1 : a * e₁ * a⁻¹ = e₀ * e₁ := (himg a ha).resolve_left fun h1 => haC (hcen a ha h1)
  have hb1 : b * e₁ * b⁻¹ = e₀ * e₁ := (himg b hb).resolve_left fun h1 => hbC (hcen b hb h1)
  apply hcen _ (mul_mem ha hb)
  calc a * b * e₁ * (a * b)⁻¹ = a * (b * e₁ * b⁻¹) * a⁻¹ := by group
    _ = (a * e₀ * a⁻¹) * (a * e₁ * a⁻¹) := by rw [hb1]; group
    _ = e₀ * (e₀ * e₁) := by rw [hfix a ha, ha1]
    _ = e₁ := by rw [← mul_assoc, hE2 e₀ he₀, one_mul]

theorem card_inf_centralizer_of_card_four {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) {u : G} (huN : u ∈ normalizer (E : Set G))
    (hu2 : u * u ∈ centralizer (E : Set G)) (huC : u ∉ centralizer (E : Set G)) :
    Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) = 2 := by
  have h1 := card_le_sq_card_inf_centralizer hE huN hu2
  have hdvd : Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ∣ 4 :=
    hE4 ▸ card_dvd_of_le inf_le_left
  have hne4 : Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ≠ 4 := by
    intro h4
    apply huC
    have heq : E ⊓ centralizer ({u} : Set G) = E :=
      eq_of_le_of_card_ge inf_le_left (by rw [h4, hE4])
    rw [mem_centralizer_iff]
    intro e he
    rw [← heq] at he
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2)
  have hmem : Nat.card (E ⊓ centralizer ({u} : Set G) : Subgroup G) ∈ Nat.divisors 4 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [h4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rw [hE4] at h1
  rcases hmem with h | h | h
  · rw [h] at h1; norm_num at h1
  · exact h
  · exact absurd h hne4

end FourGroup

@[expose] def IsRootInv (A : Subgroup G) (d : G) : Prop :=
  ∃ c : G, d ∈ rightConjugate (centralizer (A : Set G)) c

theorem IsRootInv.conj {A : Subgroup G} {d : G} (hd : IsRootInv A d) (k : G) :
    IsRootInv A (k⁻¹ * d * k) := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨c * k, ?_⟩
  rw [mem_rightConjugate_iff] at hc ⊢
  convert hc using 1
  group

theorem IsRootInv.of_isConj {A : Subgroup G} {d d' : G} (hd : IsRootInv A d)
    (hdd' : IsConj d d') : IsRootInv A d' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hdd'
  have := hd.conj c⁻¹
  rwa [inv_inv, hc] at this

namespace Setting310

variable [Finite G] {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem inf_R_T : R ⊓ T = ⊥ := by
  have hTN : T ≤ normalizer (R : Set G) := le_normalizer_of_le h.loc.elem le_sup_left le_sup_right
  have hc := card_sup_mul_card_inf_of_le hTN
  obtain ⟨c, hTc, -⟩ := Lemma36.exists_conj_eq h.sylowR h.loc.sylowT
  have hT4 : Nat.card T = 4 := by rw [hTc, rightConjugate_card, h.cardR]
  rw [sup_comm, h.loc.card, inf_comm, h.cardR, hT4] at hc
  have h1 : Nat.card (R ⊓ T : Subgroup G) = 1 := by omega
  exact card_eq_one.mp h1

theorem exists_eq_rightConjugate_T : ∃ c : G, T = rightConjugate R c := by
  obtain ⟨c, hTc, -⟩ := Lemma36.exists_conj_eq h.sylowR h.loc.sylowT
  exact ⟨c, hTc⟩

theorem isRootInv_of_mem_R {r : G} (hr : r ∈ R) : IsRootInv A r :=
  ⟨1, by rw [rightConjugate_one]; exact h.sylowR.le hr⟩

theorem isRootInv_of_mem_V {v : G} (hv : v ∈ R ⊔ T) (hv0 : v ∉ V₀) : IsRootInv A v := by
  obtain ⟨x, -, hvx⟩ := h.loc.cover v hv hv0
  exact ⟨x, (map_mono h.sylowR.le) hvx⟩

theorem not_isRootInv_of_isConj {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) {y : G} (hwy : IsConj w y) :
    ¬ IsRootInv A y := by
  intro hy
  obtain ⟨c, hc⟩ := hy.of_isConj hwy.symm
  have h1 : w ∈ V₀ ⊓ rightConjugate (centralizer (A : Set G)) c := mem_inf.mpr ⟨hw, hc⟩
  rw [h.loc.noRoot, mem_bot] at h1
  exact hw1 h1

theorem rightConjugate_inf_eq_bot {a b : G} (ha : rightConjugate R a ≤ R ⊔ T)
    (hb : rightConjugate R b ≤ R ⊔ T) (hne : rightConjugate R a ≠ rightConjugate R b) :
    rightConjugate R a ⊓ rightConjugate R b = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hK
  have hKte := tightlyEmbedded_centralizer h.hyp.standard
  have hVK : ∀ c : G, rightConjugate R c ≤ R ⊔ T →
      (R ⊔ T) ⊓ rightConjugate K c = rightConjugate R c := by
    intro c hc
    have hS := AschbacherTheorem3.isSylowOf_rightConjugate h.sylowR c
    have hp : IsPGroup 2 ↥((R ⊔ T) ⊓ rightConjugate K c) :=
      (IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)).to_le inf_le_left
    exact hS.eq_of_le (le_inf hc (map_mono h.sylowR.le)) inf_le_right hp
  have hba : b * a⁻¹ ∉ normalizer (K : Set G) := by
    intro hN
    apply hne
    have h1 : rightConjugate K b = rightConjugate K a := by
      have e : rightConjugate K b = rightConjugate (rightConjugate K (b * a⁻¹)) a := by
        rw [rightConjugate_mul]; group
      rw [e, (rightConjugate_eq_self_iff K _).mpr hN]
    rw [← hVK a ha, ← hVK b hb, h1]
  have h2 := two_subgroup_inf_conjugate_eq_bot K (rightConjugate R (b * a⁻¹)) hKte
    (h.sylowR.isPGroup.map _) (b * a⁻¹) hba (map_mono h.sylowR.le)
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hva, hvb⟩ := mem_inf.mp hv
  rw [mem_rightConjugate_iff] at hva hvb
  have h3 : a * v * a⁻¹ ∈ rightConjugate R (b * a⁻¹) ⊓ K := by
    refine mem_inf.mpr ⟨?_, h.sylowR.le hva⟩
    rw [mem_rightConjugate_iff]
    convert hvb using 1
    group
  rw [h2, mem_bot] at h3
  rw [mem_bot]
  calc v = a⁻¹ * (a * v * a⁻¹) * a := by group
    _ = 1 := by rw [h3]; group

theorem rightConjugate_eq_of_mem {a b v : G} (ha : rightConjugate R a ≤ R ⊔ T)
    (hb : rightConjugate R b ≤ R ⊔ T) (hva : v ∈ rightConjugate R a)
    (hvb : v ∈ rightConjugate R b) (hv1 : v ≠ 1) : rightConjugate R a = rightConjugate R b := by
  by_contra hne
  have h1 : v ∈ rightConjugate R a ⊓ rightConjugate R b := mem_inf.mpr ⟨hva, hvb⟩
  rw [h.rightConjugate_inf_eq_bot ha hb hne, mem_bot] at h1
  exact hv1 h1

theorem exists_mul_mem_rightConjugate {a : G} (ha : rightConjugate R a ≤ R ⊔ T) {r : G}
    (hr : r ∈ R) : ∃ w ∈ V₀, r * w ∈ rightConjugate R a := by
  set L := rightConjugate R a with hL
  have hL4 : Nat.card L = 4 := by rw [hL, rightConjugate_card, h.cardR]
  have hLV₀ : L ⊓ V₀ = ⊥ := h.loc.spread a ha
  have hV₀N : V₀ ≤ normalizer (L : Set G) := le_normalizer_of_le h.loc.elem ha h.V₀_le
  have hc := card_sup_mul_card_inf_of_le hV₀N
  rw [inf_comm, hLV₀, card_bot, mul_one, h.card_V₀, hL4] at hc
  have hsup : V₀ ⊔ L = R ⊔ T :=
    eq_of_le_of_card_ge (sup_le h.V₀_le ha) (by rw [hc, h.loc.card])
  have hrV : r ∈ V₀ ⊔ L := hsup ▸ mem_sup_left hr
  rw [sup_comm] at hrV
  obtain ⟨l, hl, w, hw, hlw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hrV
  refine ⟨w⁻¹, inv_mem hw, ?_⟩
  rw [hlw, mul_inv_cancel_right]
  exact hl

theorem mem_centralizer_of_mem_centralizer_V₀ {n : G}
    (hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) (hnR : n ∈ normalizer (R : Set G))
    (hn2 : IsPGroup 2 (zpowers n)) (hnC : n ∈ centralizer (V₀ : Set G)) :
    n ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  have hw : ∀ w ∈ V₀, n * w * n⁻¹ = w := fun w hw => by
    rw [← mem_centralizer_iff.mp hnC w hw]; group
  obtain ⟨r₀, hr₀, hr₀1, hfix⟩ := exists_fixed_of_card_four h.cardR hn2 (zpowers_le.mpr hnR)
  have hr₀n : n * r₀ * n⁻¹ = r₀ := hfix n (mem_zpowers n)
  obtain ⟨t₀, ht₀, w₀, hw₀, hr₀t⟩ := h.exists_mul_T (mem_sup_left hr₀)
  have ht₀e : t₀ = r₀ * w₀⁻¹ := by rw [hr₀t]; group
  have ht₀n : n * t₀ * n⁻¹ = t₀ := by
    rw [ht₀e]
    calc n * (r₀ * w₀⁻¹) * n⁻¹ = (n * r₀ * n⁻¹) * (n * w₀ * n⁻¹)⁻¹ := by group
      _ = r₀ * w₀⁻¹ := by rw [hr₀n, hw w₀ hw₀]
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply hr₀1
    have h2 : r₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr₀, by
      rw [ht₀e] at h1
      have : r₀ = w₀ := by
        calc r₀ = r₀ * w₀⁻¹ * w₀ := by group
          _ = w₀ := by rw [h1, one_mul]
      rw [this]; exact hw₀⟩
    rwa [h.inf_R_V₀, mem_bot] at h2
  obtain ⟨c, hTc⟩ := h.exists_eq_rightConjugate_T
  have hTV : rightConjugate R c ≤ R ⊔ T := hTc ▸ le_sup_right
  have hTnV : rightConjugate R (c * n⁻¹) ≤ R ⊔ T := by
    rw [← rightConjugate_mul]
    exact Lemma36.rightConjugate_le hTV (inv_mem hnV)
  have hTn : rightConjugate R (c * n⁻¹) = rightConjugate R c := by
    refine h.rightConjugate_eq_of_mem hTnV hTV ?_ (hTc ▸ ht₀) ht₀1
    rw [← rightConjugate_mul, mem_rightConjugate_iff, inv_inv, ← hTc]
    have : n⁻¹ * t₀ * n = t₀ := by
      calc n⁻¹ * t₀ * n = n⁻¹ * (n * t₀ * n⁻¹) * n := by rw [ht₀n]
        _ = t₀ := by group
    rw [this]
    exact ht₀
  have hnT : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
    intro t ht
    rw [hTc] at ht ⊢
    rw [← hTn, mem_rightConjugate_iff]
    rw [mem_rightConjugate_iff] at ht
    convert ht using 1
    group
  have hnr : ∀ r ∈ R, n * r * n⁻¹ = r := by
    intro r hr
    obtain ⟨t, ht, w, hw', hrt⟩ := h.exists_mul_T (mem_sup_left hr)
    have hrn : n * r * n⁻¹ ∈ R := (mem_normalizer_iff.mp hnR r).mp hr
    have h1 : (n * r * n⁻¹) * r⁻¹ = (n * t * n⁻¹) * t⁻¹ := by
      rw [hrt]
      calc n * (t * w) * n⁻¹ * (t * w)⁻¹ = (n * t * n⁻¹) * (n * w * n⁻¹) * w⁻¹ * t⁻¹ := by
            group
        _ = (n * t * n⁻¹) * t⁻¹ := by rw [hw w hw']; group
    have h2 : (n * r * n⁻¹) * r⁻¹ ∈ R ⊓ T :=
      mem_inf.mpr ⟨mul_mem hrn (inv_mem hr), h1 ▸ mul_mem (hnT t ht) (inv_mem ht)⟩
    rw [h.inf_R_T, mem_bot] at h2
    calc n * r * n⁻¹ = (n * r * n⁻¹) * r⁻¹ * r := by group
      _ = r := by rw [h2, one_mul]
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨r, hr, w, hw', rfl⟩ := h.exists_mul hv
  have h1 : n * (r * w) * n⁻¹ = r * w := by
    calc n * (r * w) * n⁻¹ = (n * r * n⁻¹) * (n * w * n⁻¹) := by group
      _ = r * w := by rw [hnr r hr, hw w hw']
  calc r * w * n = n * (r * w) * n⁻¹ * n := by rw [h1]
    _ = n * (r * w) := by group

theorem mem_centralizer_of_mem_centralizer_R {n : G}
    (hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) (hn2 : IsPGroup 2 (zpowers n))
    (hnC : n ∈ centralizer (R : Set G)) :
    n ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  have hr : ∀ r ∈ R, n * r * n⁻¹ = r := fun r hr => by
    rw [← mem_centralizer_iff.mp hnC r hr]; group
  have hnV₀ : n ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hnV
  obtain ⟨w₀, hw₀, hw₀1, hfix⟩ := exists_fixed_of_card_four h.card_V₀ hn2 (zpowers_le.mpr hnV₀)
  have hw₀n : n * w₀ * n⁻¹ = w₀ := hfix n (mem_zpowers n)
  have hTN : T ≤ normalizer (R : Set G) := le_normalizer_of_le h.loc.elem le_sup_left le_sup_right
  obtain ⟨r₀, hr₀, t₀, ht₀, hw₀rt⟩ := exists_mul_of_mem_sup_of_le_normalizer hTN (h.V₀_le hw₀)
  have ht₀e : t₀ = r₀⁻¹ * w₀ := by rw [hw₀rt]; group
  have ht₀n : n * t₀ * n⁻¹ = t₀ := by
    rw [ht₀e]
    calc n * (r₀⁻¹ * w₀) * n⁻¹ = (n * r₀ * n⁻¹)⁻¹ * (n * w₀ * n⁻¹) := by group
      _ = r₀⁻¹ * w₀ := by rw [hr r₀ hr₀, hw₀n]
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply hw₀1
    have h2 : w₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨by
      rw [ht₀e] at h1
      have : w₀ = r₀ := by
        calc w₀ = r₀ * (r₀⁻¹ * w₀) := by group
          _ = r₀ := by rw [h1, mul_one]
      rw [this]; exact hr₀, hw₀⟩
    rwa [h.inf_R_V₀, mem_bot] at h2
  obtain ⟨c, hTc⟩ := h.exists_eq_rightConjugate_T
  have hTV : rightConjugate R c ≤ R ⊔ T := hTc ▸ le_sup_right
  have hTnV : rightConjugate R (c * n⁻¹) ≤ R ⊔ T := by
    rw [← rightConjugate_mul]
    exact Lemma36.rightConjugate_le hTV (inv_mem hnV)
  have hTn : rightConjugate R (c * n⁻¹) = rightConjugate R c := by
    refine h.rightConjugate_eq_of_mem hTnV hTV ?_ (hTc ▸ ht₀) ht₀1
    rw [← rightConjugate_mul, mem_rightConjugate_iff, inv_inv, ← hTc]
    have : n⁻¹ * t₀ * n = t₀ := by
      calc n⁻¹ * t₀ * n = n⁻¹ * (n * t₀ * n⁻¹) * n := by rw [ht₀n]
        _ = t₀ := by group
    rw [this]
    exact ht₀
  have hnT : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
    intro t ht
    rw [hTc] at ht ⊢
    rw [← hTn, mem_rightConjugate_iff]
    rw [mem_rightConjugate_iff] at ht
    convert ht using 1
    group
  have hnw : ∀ w ∈ V₀, n * w * n⁻¹ = w := by
    intro w hw
    obtain ⟨r, hr', t, ht, hwrt⟩ := exists_mul_of_mem_sup_of_le_normalizer hTN (h.V₀_le hw)
    have hwn : n * w * n⁻¹ ∈ V₀ := (mem_normalizer_iff.mp hnV₀ w).mp hw
    have h1 : w⁻¹ * (n * w * n⁻¹) = t⁻¹ * (n * t * n⁻¹) := by
      rw [hwrt]
      calc (r * t)⁻¹ * (n * (r * t) * n⁻¹) = t⁻¹ * r⁻¹ * (n * r * n⁻¹) * (n * t * n⁻¹) := by
            group
        _ = t⁻¹ * (n * t * n⁻¹) := by rw [hr r hr']; group
    have h2 : w⁻¹ * (n * w * n⁻¹) ∈ T ⊓ V₀ :=
      mem_inf.mpr ⟨h1 ▸ mul_mem (inv_mem ht) (hnT t ht), mul_mem (inv_mem hw) hwn⟩
    rw [h.sup_T_V₀.1, mem_bot] at h2
    calc n * w * n⁻¹ = w * (w⁻¹ * (n * w * n⁻¹)) := by group
      _ = w := by rw [h2, mul_one]
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨r, hr', w, hw', rfl⟩ := h.exists_mul hv
  have h1 : n * (r * w) * n⁻¹ = r * w := by
    calc n * (r * w) * n⁻¹ = (n * r * n⁻¹) * (n * w * n⁻¹) := by group
      _ = r * w := by rw [hr r hr', hnw w hw']
  calc r * w * n = n * (r * w) * n⁻¹ * n := by rw [h1]
    _ = n * (r * w) := by group

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem inf_normalizer_R_eq : P ⊓ normalizer (R : Set G) = R ⊔ T := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  apply le_antisymm
  · intro p hp
    obtain ⟨hpP, hpN⟩ := mem_inf.mp hp
    have hR : rightConjugate R p⁻¹ = R := (rightConjugate_eq_self_iff R _).mpr (inv_mem hpN)
    rw [← hPC]
    exact mem_inf.mpr ⟨hpP, h.mem_centralizer_of_transv_of_eq (hP.le hpP) hR⟩
  · exact le_inf hVP (le_normalizer_of_le h.loc.elem le_sup_left le_rfl)

theorem exists_mem_P_transvHom (hP64 : Nat.card P = 64) {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1)
    {w : G} (hw : w ∈ V₀) : ∃ p ∈ P, r₀⁻¹ * (p * r₀ * p⁻¹) = w := by
  set f := transvHom (T := T) (V₀ := V₀) hr₀ with hf
  let φ : ↥P →* ↥V₀ := f.comp (inclusion hP.le)
  have hker : φ.ker = (R ⊔ T).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change f (inclusion hP.le p) = 1 ↔ _
    rw [← MonoidHom.mem_ker, h.ker_transvHom hr₀ hr₀1, mem_subgroupOf]
    change (p : G) ∈ centralizer _ ↔ _
    constructor
    · intro hpC
      rw [← hPC]
      exact mem_inf.mpr ⟨p.2, hpC⟩
    · intro hpV
      rw [← hPC] at hpV
      exact (mem_inf.mp hpV).2
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hcard : Nat.card φ.range = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv, h.loc.card, hP64] at h1
    omega
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard, h.card_V₀])
  obtain ⟨p, hp⟩ := (MonoidHom.range_eq_top.mp htop) ⟨w, hw⟩
  exact ⟨p, p.2, congrArg Subtype.val hp⟩

theorem exists_mul_mem_normalizer_R (hP64 : Nat.card P = 64) {n : G}
    (hn : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) :
    ∃ p ∈ P, n * p ∈ normalizer (R : Set G) := by
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hL : rightConjugate R n ≤ R ⊔ T := Lemma36.rightConjugate_le le_sup_left hn
  obtain ⟨w, hw, hrw⟩ := h.exists_mul_mem_rightConjugate hL hr₀
  obtain ⟨p, hp, hpw⟩ := h.exists_mem_P_transvHom hP hPC hP64 hr₀ hr₀1 hw
  have hpr : p * r₀ * p⁻¹ = r₀ * w := by rw [← hpw]; group
  have hpV : p ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := (hP.le hp).1
  have hLp : rightConjugate R p⁻¹ ≤ R ⊔ T := Lemma36.rightConjugate_le le_sup_left (inv_mem hpV)
  have hrw1 : r₀ * w ≠ 1 := by
    intro h1
    apply hr₀1
    have h2 : r₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr₀, by
      have : r₀ = w⁻¹ := by
        calc r₀ = r₀ * w * w⁻¹ := by group
          _ = w⁻¹ := by rw [h1, one_mul]
      rw [this]; exact inv_mem hw⟩
    rwa [h.inf_R_V₀, mem_bot] at h2
  have hmem : r₀ * w ∈ rightConjugate R p⁻¹ := by
    rw [mem_rightConjugate_iff, ← hpr]
    convert hr₀ using 1
    group
  have heq := h.rightConjugate_eq_of_mem hLp hL hmem hrw hrw1
  refine ⟨p, hp, ?_⟩
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← heq, rightConjugate_mul,
    inv_mul_cancel, rightConjugate_one]

theorem card_le_of_le_normalizer_V (hP64 : Nat.card P = 64) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQV : Q ≤ normalizer ((R ⊔ T : Subgroup G) : Set G)) (hPQ : P ≤ Q) : Nat.card Q ≤ 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => h.mul_self (h.V₀_le hx)
  have hQP : Q ⊓ transvGroup (R ⊔ T) V₀ = P :=
    hP.eq_of_le (le_inf hPQ hP.le) inf_le_right (hQ.to_le inf_le_left)
  have hQNP : Q ≤ normalizer (P : Set G) := by
    intro q hq
    rw [← hQP]
    exact mem_normalizer_inf (le_normalizer hq) (h.le_normalizer_transvGroup (hQV hq))
  set Q₂ := Q ⊓ normalizer (R : Set G) with hQ₂
  have hQ₂P : Q₂ ⊔ P = Q := by
    refine le_antisymm (sup_le inf_le_left hPQ) fun q hq => ?_
    obtain ⟨p, hp, hqp⟩ := h.exists_mul_mem_normalizer_R hP hPC hP64 (hQV hq)
    have : q = (q * p) * p⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨mul_mem hq (hPQ hp), hqp⟩))
      (mem_sup_right (inv_mem hp))
  have hQ₂P' : Q₂ ⊓ P = R ⊔ T := by
    rw [hQ₂, inf_comm, ← inf_assoc, inf_eq_left.mpr hPQ]
    exact h.inf_normalizer_R_eq hP hPC
  have hcard1 := card_sup_mul_card_inf_of_le (hQ₂.symm ▸ inf_le_left.trans hQNP :
    Q₂ ≤ normalizer (P : Set G))
  rw [hQ₂P, hQ₂P', h.loc.card, hP64] at hcard1
  have hQ₂p : IsPGroup 2 Q₂ := hQ.to_le inf_le_left
  have hQ₂V₀ : Q₂ ≤ normalizer (V₀ : Set G) := fun q hq =>
    h.normalizer_le_normalizer_V₀ (hQV (mem_inf.mp hq).1)
  have hker : Q₂ ⊓ centralizer (V₀ : Set G) ≤ R ⊔ T := by
    have hle : Q₂ ⊓ centralizer (V₀ : Set G) ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      intro n hn
      obtain ⟨hnQ₂, hnC⟩ := mem_inf.mp hn
      obtain ⟨hnQ, hnR⟩ := mem_inf.mp hnQ₂
      exact h.mem_centralizer_of_mem_centralizer_V₀ (hQV hnQ) hnR
        (hQ.to_le (zpowers_le.mpr hnQ)) hnC
    have hX : Q ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T :=
      h.eq_of_le_centralizer (le_inf (hVP.trans hPQ) (le_centralizer_self_of_isElemAbelian
        h.loc.elem)) inf_le_right (hQ.to_le inf_le_left)
    intro n hn
    rw [← hX]
    exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hn).1).1, hle hn⟩
  have hcard2 : Nat.card Q₂ ≤ 2 * 16 := by
    by_cases hall : Q₂ ≤ centralizer (V₀ : Set G)
    · have h1 : Q₂ ≤ R ⊔ T := fun q hq => hker (mem_inf.mpr ⟨hq, hall hq⟩)
      have h2 := card_le_of_le h1
      rw [h.loc.card] at h2
      omega
    · obtain ⟨a, haQ, haC⟩ := IsConcreteLE.not_le_iff_exists.mp hall
      have hidx : ((Q₂ ⊓ centralizer (V₀ : Set G)).subgroupOf Q₂).index = 2 := by
        rw [Subgroup.index_eq_two_iff_exists_notMem_and]
        refine ⟨⟨a, haQ⟩, fun h1 => haC (mem_subgroupOf.mp h1 |> fun h2 => (mem_inf.mp h2).2),
          fun b => ?_⟩
        by_cases hbC : (b : G) ∈ centralizer (V₀ : Set G)
        · exact Or.inr (mem_subgroupOf.mpr (mem_inf.mpr ⟨b.2, hbC⟩))
        · left
          rw [mem_subgroupOf]
          exact mem_inf.mpr ⟨mul_mem b.2 haQ, mul_mem_centralizer_of_card_four h.card_V₀ hV₀2
            hQ₂p hQ₂V₀ b.2 haQ hbC haC⟩
      have h1 := Subgroup.card_mul_index ((Q₂ ⊓ centralizer (V₀ : Set G)).subgroupOf Q₂)
      rw [hidx, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
      have h2 := card_le_of_le hker
      rw [h.loc.card] at h2
      omega
  omega

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
