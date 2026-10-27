module

public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}

theorem ncard_triples_eq (hD : DoublyTransitive M) (U : Set X)
    (Q : X → Subgroup X → Subgroup X → Prop)
    (hQ : ∀ v δ δ' (g : X), Q (g⁻¹ * v * g) (conjugate δ g) (conjugate δ' g) ↔ Q v δ δ')
    (hU : ∀ v ∈ U, ∀ g : X, g⁻¹ * v * g ∈ U) {α β : Subgroup X} (hα : α ∈ omega M)
    (hβ : β ∈ omega M) (hαβ : α ≠ β) :
    {p : X × Subgroup X × Subgroup X | p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧
        p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2}.ncard =
      (omega M).ncard * ((omega M).ncard - 1) * {v ∈ U | Q v α β}.ncard := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (Subgroup X) := Fintype.ofFinite _
  let Ωf : Finset (Subgroup X) := Finset.univ.filter (· ∈ omega M)
  let Pf : Finset (Subgroup X × Subgroup X) := Ωf.offDiag
  let Ff : Subgroup X × Subgroup X → Finset X :=
    fun q => Finset.univ.filter (fun v => v ∈ U ∧ Q v q.1 q.2)
  let Tf : Finset (X × Subgroup X × Subgroup X) := Finset.univ.filter
    (fun p => p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧ p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2)
  have hΩ : (omega M).ncard = Ωf.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext β'
    simp [Ωf]
  have hT : {p : X × Subgroup X × Subgroup X | p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧
      p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2}.ncard = Tf.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp [Tf]
  have hF0 : {v ∈ U | Q v α β}.ncard = (Ff (α, β)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [Ff]
  have hPmem : ∀ q : Subgroup X × Subgroup X,
      q ∈ Pf ↔ q.1 ∈ omega M ∧ q.2 ∈ omega M ∧ q.1 ≠ q.2 := by
    intro q
    simp [Pf, Ωf, Finset.mem_offDiag]
  have hTmem : ∀ p : X × Subgroup X × Subgroup X, p ∈ Tf ↔ (p.1 ∈ U ∧ p.2.1 ∈ omega M ∧
      p.2.2 ∈ omega M ∧ p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2) := by
    intro p
    simp [Tf]
  have hFmem : ∀ (b : Subgroup X × Subgroup X) (v : X), v ∈ Ff b ↔ (v ∈ U ∧ Q v b.1 b.2) := by
    intro b v
    simp [Ff]
  have hfiber : ∀ b ∈ Pf, (Tf.filter fun a => (a.2.1, a.2.2) = b).card = (Ff b).card := by
    intro b hb
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, hTmem] at hp
      obtain ⟨⟨hpU, -, -, -, hpQ⟩, hpb⟩ := hp
      have h1 : p.2.1 = b.1 := congrArg Prod.fst hpb
      have h2 : p.2.2 = b.2 := congrArg Prod.snd hpb
      rw [hFmem]
      exact ⟨hpU, h1 ▸ h2 ▸ hpQ⟩
    · intro p hp p' hp' h
      rw [Finset.mem_filter] at hp hp'
      obtain ⟨-, hpb⟩ := hp
      obtain ⟨-, hpb'⟩ := hp'
      refine Prod.ext h (Prod.ext ?_ ?_)
      · exact (congrArg Prod.fst hpb).trans (congrArg Prod.fst hpb').symm
      · exact (congrArg Prod.snd hpb).trans (congrArg Prod.snd hpb').symm
    · intro v hv
      rw [hFmem] at hv
      obtain ⟨hvU, hvQ⟩ := hv
      obtain ⟨hb1, hb2, hb12⟩ := (hPmem b).mp hb
      refine ⟨(v, b.1, b.2), ?_, rfl⟩
      rw [Finset.mem_filter, hTmem]
      exact ⟨⟨hvU, hb1, hb2, hb12, hvQ⟩, rfl⟩
  have hconst : ∀ b ∈ Pf, (Ff b).card = (Ff (α, β)).card := by
    intro b hb
    obtain ⟨hb1, hb2, hb12⟩ := (hPmem b).mp hb
    obtain ⟨g, hg1, hg2⟩ := hD α hα β hβ hαβ b.1 hb1 b.2 hb2 hb12
    refine (Finset.card_bij (fun v _ => g⁻¹ * v * g) ?_ ?_ ?_).symm
    · intro v hv
      rw [hFmem] at hv ⊢
      refine ⟨hU v hv.1 g, ?_⟩
      have := (hQ v α β g).mpr hv.2
      rwa [hg1, hg2] at this
    · intro v _ v' _ h
      simpa using h
    · intro w hw
      rw [hFmem] at hw
      refine ⟨g * w * g⁻¹, ?_, by group⟩
      rw [hFmem]
      have hwU : g * w * g⁻¹ ∈ U := by
        have := hU w hw.1 g⁻¹
        rwa [inv_inv] at this
      refine ⟨hwU, ?_⟩
      refine (hQ (g * w * g⁻¹) α β g).mp ?_
      rw [hg1, hg2]
      have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [e]
      exact hw.2
  have hsum : Tf.card = ∑ b ∈ Pf, (Tf.filter fun a => (a.2.1, a.2.2) = b).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := fun a : X × Subgroup X × Subgroup X => (a.2.1, a.2.2)) (fun p hp => ?_)
    have hp' := (hTmem p).mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr ((hPmem _).mpr ⟨hp'.2.1, hp'.2.2.1, hp'.2.2.2.1⟩)
  rw [hT, hF0, hsum, Finset.sum_congr rfl (fun b hb => (hfiber b hb).trans (hconst b hb)),
    Finset.sum_const, smul_eq_mul, hΩ, Finset.offDiag_card]
  congr 1
  rw [Nat.mul_sub_one]

omit [Finite X] in
theorem card_eq_mul_of_fiber_const {A B : Type*} [DecidableEq B] (T : Finset A) (f : A → B)
    (Bf : Finset B) (b₀ : B) (hmaps : ∀ a ∈ T, f a ∈ Bf)
    (hconst : ∀ b ∈ Bf, (T.filter fun a => f a = b).card = (T.filter fun a => f a = b₀).card) :
    T.card = Bf.card * (T.filter fun a => f a = b₀).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := T) (t := Bf) hmaps,
    Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

theorem ncard_triples_eq_mul (U : Set X) (Q : X → Subgroup X → Subgroup X → Prop)
    (hQ : ∀ v δ δ' (g : X), Q (g⁻¹ * v * g) (conjugate δ g) (conjugate δ' g) ↔ Q v δ δ')
    {u : X} (hu : u ∈ U) (hUu : ∀ v ∈ U, ∃ g : X, v = g⁻¹ * u * g) :
    {p : X × Subgroup X × Subgroup X | p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧
        p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2}.ncard =
      U.ncard * {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
        Q u p.1 p.2}.ncard := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (Subgroup X) := Fintype.ofFinite _
  let Uf : Finset X := Finset.univ.filter (· ∈ U)
  let Tf : Finset (X × Subgroup X × Subgroup X) := Finset.univ.filter
    (fun p => p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧ p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2)
  have hTmem : ∀ p : X × Subgroup X × Subgroup X, p ∈ Tf ↔ (p.1 ∈ U ∧ p.2.1 ∈ omega M ∧
      p.2.2 ∈ omega M ∧ p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2) := by
    intro p
    simp [Tf]
  have hUmem : ∀ v : X, v ∈ Uf ↔ v ∈ U := by
    intro v
    simp [Uf]
  have hT : {p : X × Subgroup X × Subgroup X | p.1 ∈ U ∧ p.2.1 ∈ omega M ∧ p.2.2 ∈ omega M ∧
      p.2.1 ≠ p.2.2 ∧ Q p.1 p.2.1 p.2.2}.ncard = Tf.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp [Tf]
  have hU' : U.ncard = Uf.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [Uf]
  have hconst : ∀ v ∈ Uf, (Tf.filter fun a => a.1 = v).card = (Tf.filter fun a => a.1 = u).card := by
    intro v hv
    obtain ⟨g, hg⟩ := hUu v ((hUmem v).mp hv)
    refine Finset.card_bij (fun a _ => (u, conjugate a.2.1 g⁻¹, conjugate a.2.2 g⁻¹)) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter, hTmem] at ha ⊢
      obtain ⟨⟨-, h1, h2, h3, h4⟩, h5⟩ := ha
      refine ⟨⟨hu, conjugate_mem_omega h1 _, conjugate_mem_omega h2 _, ?_, ?_⟩, rfl⟩
      · intro h
        exact h3 (conjugate_injective _ h)
      · have := (hQ a.1 a.2.1 a.2.2 g⁻¹).mpr h4
        have e : (g⁻¹)⁻¹ * a.1 * g⁻¹ = u := by rw [h5, hg]; group
        rwa [e] at this
    · intro a ha b hb h
      rw [Finset.mem_filter] at ha hb
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, h1, h2⟩ := h
      exact Prod.ext (ha.2.trans hb.2.symm)
        (Prod.ext (conjugate_injective _ h1) (conjugate_injective _ h2))
    · intro b hb
      rw [Finset.mem_filter, hTmem] at hb
      obtain ⟨⟨-, h1, h2, h3, h4⟩, h5⟩ := hb
      have h5' : b.1 = u := h5
      refine ⟨(v, conjugate b.2.1 g, conjugate b.2.2 g), ?_, ?_⟩
      · rw [Finset.mem_filter, hTmem]
        refine ⟨⟨(hUmem v).mp hv, conjugate_mem_omega h1 _, conjugate_mem_omega h2 _, ?_, ?_⟩, rfl⟩
        · intro h
          exact h3 (conjugate_injective _ h)
        · have := (hQ b.1 b.2.1 b.2.2 g).mpr h4
          rwa [h5', ← hg] at this
      · refine Prod.ext (by rw [h5']) (Prod.ext ?_ ?_)
        · show conjugate (conjugate b.2.1 g) g⁻¹ = b.2.1
          rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
        · show conjugate (conjugate b.2.2 g) g⁻¹ = b.2.2
          rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have hmaps : ∀ a ∈ Tf, a.1 ∈ Uf := fun a ha => (hUmem _).mpr ((hTmem a).mp ha).1
  have hfin := card_eq_mul_of_fiber_const Tf (fun a => a.1) Uf u hmaps hconst
  have hFu : {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
      Q u p.1 p.2}.ncard = (Tf.filter fun a => a.1 = u).card := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun p _ => (u, p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      have hp' : p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧ Q u p.1 p.2 := hp
      rw [Finset.mem_coe, Finset.mem_filter, hTmem]
      exact ⟨⟨hu, hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2⟩, rfl⟩
    · intro p q _ _ h
      have h' := congrArg (fun a : X × Subgroup X × Subgroup X => (a.2.1, a.2.2)) h
      exact h'
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter, hTmem] at hb
      obtain ⟨⟨-, h1, h2, h3, h4⟩, h5⟩ := hb
      have h5' : b.1 = u := h5
      refine ⟨(b.2.1, b.2.2), ⟨h1, h2, h3, ?_⟩, ?_⟩
      · rw [← h5']
        exact h4
      · exact Prod.ext h5'.symm rfl
  rw [hT, hU', hFu]
  exact hfin

theorem ncard_pairs_identity (hD : DoublyTransitive M) (U : Set X)
    (Q : X → Subgroup X → Subgroup X → Prop)
    (hQ : ∀ v δ δ' (g : X), Q (g⁻¹ * v * g) (conjugate δ g) (conjugate δ' g) ↔ Q v δ δ')
    (hU : ∀ v ∈ U, ∀ g : X, g⁻¹ * v * g ∈ U) {u : X} (hu : u ∈ U)
    (hUu : ∀ v ∈ U, ∃ g : X, v = g⁻¹ * u * g) {α β : Subgroup X} (hα : α ∈ omega M)
    (hβ : β ∈ omega M) (hαβ : α ≠ β) :
    (omega M).ncard * ((omega M).ncard - 1) * {v ∈ U | Q v α β}.ncard =
      U.ncard * {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
        Q u p.1 p.2}.ncard := by
  rw [← ncard_triples_eq hD U Q hQ hU hα hβ hαβ, ncard_triples_eq_mul U Q hQ hu hUu]

end CFSG.GH74.Uniqueness
