module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Sylow

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

private theorem ao1_card_ne_even {ω : α} (hα : Odd (Fintype.card α)) :
    Even (Fintype.card {x : α // x ≠ ω}) := by
  obtain ⟨k, hk⟩ := hα
  have h1 : Fintype.card {x : α // x ≠ ω} = Fintype.card α - Fintype.card {x : α // x = ω} :=
    Fintype.card_subtype_compl (fun x : α => x = ω)
  rw [Fintype.card_subtype_eq ω] at h1
  exact ⟨k, by omega⟩

private theorem ao1_ofSubtype_fix {ω : α} (q : FpfInv {x : α // x ≠ ω}) :
    Equiv.Perm.ofSubtype q.μ ω = ω :=
  Equiv.Perm.ofSubtype_apply_of_not_mem q.μ (fun h => h rfl)

private theorem ao1_ofSubtype_apply_of_ne {ω : α} (q : FpfInv {x : α // x ≠ ω}) {x : α}
    (hx : x ≠ ω) : Equiv.Perm.ofSubtype q.μ x = (q.μ ⟨x, hx⟩ : α) :=
  Equiv.Perm.ofSubtype_apply_of_mem q.μ hx

private theorem ao1_ofSubtype_inv {ω : α} (q : FpfInv {x : α // x ≠ ω}) (x : α) :
    Equiv.Perm.ofSubtype q.μ (Equiv.Perm.ofSubtype q.μ x) = x := by
  by_cases hx : x = ω
  · rw [hx, ao1_ofSubtype_fix q, ao1_ofSubtype_fix q]
  · have hy : (q.μ ⟨x, hx⟩ : α) ≠ ω := (q.μ ⟨x, hx⟩).2
    rw [ao1_ofSubtype_apply_of_ne q hx, ao1_ofSubtype_apply_of_ne q hy]
    have h2 : (⟨(q.μ ⟨x, hx⟩ : α), hy⟩ : {y : α // y ≠ ω}) = q.μ ⟨x, hx⟩ := rfl
    rw [h2]
    exact congrArg Subtype.val (q.inv ⟨x, hx⟩)

private theorem ao1_ofSubtype_fpf {ω : α} (q : FpfInv {x : α // x ≠ ω}) {x : α}
    (hx : x ≠ ω) : Equiv.Perm.ofSubtype q.μ x ≠ x := by
  intro h
  rw [ao1_ofSubtype_apply_of_ne q hx] at h
  exact q.fpf ⟨x, hx⟩ (Subtype.ext h)

theorem exists_oddInv (hα : Odd (Fintype.card α)) : Nonempty (OddInv α) := by
  have hpos : 0 < Fintype.card α := by
    obtain ⟨k, hk⟩ := hα
    omega
  obtain ⟨ω⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨q⟩ := exists_fpfInv (ao1_card_ne_even (ω := ω) hα)
  exact ⟨⟨Equiv.Perm.ofSubtype q.μ, ω, ao1_ofSubtype_inv q, ao1_ofSubtype_fix q,
    fun x hx => ao1_ofSubtype_fpf q hx⟩⟩

@[expose] def OddInv.transport (p : OddInv α) (σ : Perm α) : OddInv α where
  μ := σ * p.μ * σ⁻¹
  ω := σ p.ω
  inv := by
    intro x
    simp [Perm.mul_apply, p.inv]
  fix := by
    simp [Perm.mul_apply, p.fix]
  fpf := by
    intro x hx h
    have h1 : σ (p.μ (σ⁻¹ x)) = x := by simpa [Perm.mul_apply] using h
    have h2 : p.μ (σ⁻¹ x) = σ⁻¹ x := by
      have h' := congrArg (⇑σ⁻¹) h1
      simpa using h'
    have h3 : σ⁻¹ x ≠ p.ω := by
      intro h'
      apply hx
      have h'' := congrArg (⇑σ) h'
      simpa using h''
    exact p.fpf _ h3 h2

theorem OddInv.transport_μ_apply (p : OddInv α) (σ : Perm α) (x : α) :
    (p.transport σ).μ (σ x) = σ (p.μ x) := by
  simp [OddInv.transport, Perm.mul_apply]

@[expose] def sylOddSub (p : OddInv α) : Subgroup (Perm α) where
  carrier := {σ | ∀ x, σ x = x ∨ σ x = p.μ x}
  mul_mem' := by
    intro a b ha hb z
    have ha' : ∀ x, a x = x ∨ a x = p.μ x := ha
    have hb' : ∀ x, b x = x ∨ b x = p.μ x := hb
    rcases hb' z with h | h
    · rw [Perm.mul_apply, h]
      exact ha' z
    · rw [Perm.mul_apply, h]
      rcases ha' (p.μ z) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [h', p.inv])
  one_mem' := fun z => Or.inl rfl
  inv_mem' := by
    intro σ hσ z
    have hσ' : ∀ x, σ x = x ∨ σ x = p.μ x := hσ
    have h1 : σ (σ⁻¹ z) = z := sylApplyInv σ z
    rcases hσ' (σ⁻¹ z) with h | h
    · exact Or.inl (h1.symm.trans h).symm
    · have hz : z = p.μ (σ⁻¹ z) := h1.symm.trans h
      have h2 : p.μ z = σ⁻¹ z := by
        have := congrArg p.μ hz
        rwa [p.inv] at this
      exact Or.inr h2.symm

theorem mem_sylOddSub {p : OddInv α} {σ : Perm α} :
    σ ∈ sylOddSub p ↔ ∀ x, σ x = x ∨ σ x = p.μ x := Iff.rfl

private theorem ao1_sylOddSub_mul_self {p : OddInv α} {σ : Perm α} (hσ : σ ∈ sylOddSub p) :
    σ * σ = 1 := by
  have hσ' := mem_sylOddSub.mp hσ
  ext z
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hσ' z with h | h
  · rw [h, h]
  · rw [h]
    rcases hσ' (p.μ z) with h' | h'
    · by_cases hzω : z = p.ω
      · exact h'.trans (by rw [hzω]; exact p.fix)
      · exact absurd (σ.injective (h.trans h'.symm)).symm (p.fpf z hzω)
    · rw [h', p.inv]

theorem isPGroup_two_sylOddSub (p : OddInv α) :
    IsPGroup 2 ↥((sylOddSub p).subgroupOf (alternatingGroup α)) := by
  intro g
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hg := ao1_sylOddSub_mul_self (Subgroup.mem_subgroupOf.mp g.2)
  simpa [pow_two] using hg

theorem swap_mul_swap_mem_alt_odd (p : OddInv α) {x y : α} (hx : x ≠ p.ω) (hy : y ≠ p.ω) :
    swap x (p.μ x) * swap y (p.μ y) ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (p.fpf x hx).symm, Equiv.Perm.sign_swap (p.fpf y hy).symm]
  rfl

private theorem ao1_swap_pair_apply (p : OddInv α) (x z : α) :
    swap x (p.μ x) z = z ∨ swap x (p.μ x) z = p.μ z := by
  by_cases hzx : z = x
  · subst hzx
    exact Or.inr (Equiv.swap_apply_left _ _)
  by_cases hzμ : z = p.μ x
  · subst hzμ
    exact Or.inr (by rw [Equiv.swap_apply_right, p.inv])
  exact Or.inl (Equiv.swap_apply_of_ne_of_ne hzx hzμ)

theorem swap_mul_swap_mem_sylOddSub (p : OddInv α) (x y : α) :
    swap x (p.μ x) * swap y (p.μ y) ∈ sylOddSub p :=
  mul_mem (mem_sylOddSub.mpr (ao1_swap_pair_apply p x))
    (mem_sylOddSub.mpr (ao1_swap_pair_apply p y))

private theorem ao2_fixed_point {Y : Subgroup (Perm α)} (hdvd : ¬ 2 ∣ Fintype.card α)
    (hY : IsPGroup 2 ↥Y) : ∃ z : α, ∀ g ∈ Y, g z = z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd' : ¬ 2 ∣ Nat.card α := by
    rwa [Nat.card_eq_fintype_card]
  obtain ⟨z, hz⟩ := hY.nonempty_fixed_point_of_prime_not_dvd_card α hdvd'
  refine ⟨z, fun g hg => ?_⟩
  exact MulAction.mem_fixedPoints.mp hz ⟨g, hg⟩

private theorem ao2_exists_outside (p : OddInv α) (h5 : 5 ≤ Fintype.card α) (z : α) :
    ∃ y : α, y ∉ ({p.ω, z, p.μ z} : Finset α) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 : (Finset.univ : Finset α).card ≤ ({p.ω, z, p.μ z} : Finset α).card :=
    Finset.card_le_card fun y _ => hcon y
  have h2 : ({p.ω, z, p.μ z} : Finset α).card ≤ 3 := Finset.card_le_three
  rw [Finset.card_univ] at h1
  omega

theorem exists_contained_of_sylow_odd (hα : Odd (Fintype.card α))
    {T : Subgroup ↥(alternatingGroup α)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    ∃ p : OddInv α, p.Contained (T.map (alternatingGroup α).subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p₀⟩ := exists_oddInv hα
  obtain ⟨S, hBS⟩ := (isPGroup_two_sylOddSub p₀).exists_le_sylow
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at this
  let T' : Sylow 2 ↥(alternatingGroup α) := hT.2.1.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(alternatingGroup α) S T'
  have hgT : (S : Subgroup ↥(alternatingGroup α)).map (MulAut.conj g).toMonoidHom = T := by
    have h := congrArg
      (fun Q : Sylow 2 ↥(alternatingGroup α) => (Q : Subgroup ↥(alternatingGroup α))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  refine ⟨p₀.transport (g : Perm α), ?_⟩
  intro x y hx hy _ _
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = (g : Perm α) x₀ :=
    ⟨(g : Perm α)⁻¹ x, (sylApplyInv _ _).symm⟩
  obtain ⟨y₀, rfl⟩ : ∃ y₀, y = (g : Perm α) y₀ :=
    ⟨(g : Perm α)⁻¹ y, (sylApplyInv _ _).symm⟩
  have hx₀ : x₀ ≠ p₀.ω := fun h => hx (congrArg (⇑(g : Perm α)) h)
  have hy₀ : y₀ ≠ p₀.ω := fun h => hy (congrArg (⇑(g : Perm α)) h)
  rw [OddInv.transport_μ_apply p₀ (g : Perm α) x₀, OddInv.transport_μ_apply p₀ (g : Perm α) y₀,
    Equiv.swap_apply_apply (g : Perm α) x₀ (p₀.μ x₀),
    Equiv.swap_apply_apply (g : Perm α) y₀ (p₀.μ y₀)]
  have key : (g : Perm α) * swap x₀ (p₀.μ x₀) * (g : Perm α)⁻¹ *
      ((g : Perm α) * swap y₀ (p₀.μ y₀) * (g : Perm α)⁻¹) =
      (g : Perm α) * (swap x₀ (p₀.μ x₀) * swap y₀ (p₀.μ y₀)) * (g : Perm α)⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  let u : ↥(alternatingGroup α) :=
    ⟨swap x₀ (p₀.μ x₀) * swap y₀ (p₀.μ y₀), swap_mul_swap_mem_alt_odd p₀ hx₀ hy₀⟩
  have hu : u ∈ (sylOddSub p₀).subgroupOf (alternatingGroup α) :=
    Subgroup.mem_subgroupOf.mpr (swap_mul_swap_mem_sylOddSub p₀ x₀ y₀)
  have hconj : MulAut.conj g u ∈ T := by
    rw [← hgT]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hBS hu)
  refine Subgroup.mem_map.mpr ⟨MulAut.conj g u, hconj, ?_⟩
  rfl

theorem fixes_omega_of_contained (p : OddInv α) (hα : Odd (Fintype.card α))
    (h5 : 5 ≤ Fintype.card α) {T : Subgroup ↥(alternatingGroup α)} (hT2 : IsPGroup 2 ↥T)
    (hC : p.Contained (T.map (alternatingGroup α).subtype)) :
    ∀ t ∈ T, (t : Perm α) p.ω = p.ω := by
  have hdvd : ¬ 2 ∣ Fintype.card α := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hα
    omega
  have hY : IsPGroup 2 ↥(T.map (alternatingGroup α).subtype) :=
    hT2.map (alternatingGroup α).subtype
  obtain ⟨z, hz⟩ := ao2_fixed_point hdvd hY
  have hzω : z = p.ω := by
    by_contra hne
    obtain ⟨y, hy⟩ := ao2_exists_outside p h5 z
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    obtain ⟨hyω, hyz, hyμ⟩ := hy
    have hσ := hC z y hne hyω hyz hyμ
    have hzy : z ≠ y := fun h => hyz h.symm
    have hzμ : z ≠ p.μ y := fun h => hyμ (by rw [h, p.inv])
    have hσz : (swap z (p.μ z) * swap y (p.μ y)) z = p.μ z := by
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzy hzμ, Equiv.swap_apply_left]
    have hfix := hz _ hσ
    rw [hσz] at hfix
    exact p.fpf z hne hfix
  intro t ht
  have htY : (alternatingGroup α).subtype t ∈ T.map (alternatingGroup α).subtype :=
    Subgroup.mem_map_of_mem (alternatingGroup α).subtype ht
  rw [← hzω]
  exact hz _ htY

theorem exists_oddInv_of_sylow (hα : Odd (Fintype.card α)) (h5 : 5 ≤ Fintype.card α)
    {T : Subgroup ↥(alternatingGroup α)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    ∃ p : OddInv α, (∀ t ∈ T, (t : Perm α) p.ω = p.ω) ∧
      p.Contained (T.map (alternatingGroup α).subtype) := by
  obtain ⟨p, hp⟩ := exists_contained_of_sylow_odd hα hT
  exact ⟨p, fixes_omega_of_contained p hα h5 hT.2.1 hp, hp⟩

end CFSG.QuasithinUnique.L246C127.AltBig
