module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem needsThree_of_relIndex [Finite G] {p : ℕ} [Fact p.Prime] {U Z : Subgroup G}
    (hZU : Z ≤ U) (hcomm : ⁅U, U⁆ ≤ Z) (hpow : ∀ u ∈ U, u ^ p ∈ Z)
    (h3 : p ^ 3 ≤ Z.relIndex U) : NeedsThree U Z := by
  intro a ha b hb hgen
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hZn : (Z.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ⁅(g : G), (n : G)⁆ ∈ Z := hcomm (Subgroup.commutator_mem_commutator g.2 n.2)
    have h2 : ((g * n * g⁻¹ : U) : G) = ⁅(g : G), (n : G)⁆ * (n : G) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact Z.mul_mem h1 hn
  set Q := ↥U ⧸ Z.subgroupOf U with hQ
  set xa : Q := QuotientGroup.mk (⟨a, ha⟩ : ↥U) with hxa
  set xb : Q := QuotientGroup.mk (⟨b, hb⟩ : ↥U) with hxb
  have hcommQ : ∀ x y : Q, x * y = y * x := by
    intro x y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : ⁅(v : G)⁻¹, (u : G)⁻¹⁆ ∈ Z :=
      hcomm (Subgroup.commutator_mem_commutator (U.inv_mem v.2) (U.inv_mem u.2))
    have h2 : (((u * v)⁻¹ * (v * u) : U) : G) = ⁅(v : G)⁻¹, (u : G)⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact h1
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcommQ }
  have hxap : xa ^ p = 1 := by
    rw [hxa, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hpow a ha
  have hxbp : xb ^ p = 1 := by
    rw [hxb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hpow b hb
  have hred : ∀ x : Q, x ^ p = 1 → ∀ m : ℤ, ∃ i : Fin p, x ^ m = x ^ (i : ℕ) := by
    intro x hx m
    have hpos : (0 : ℤ) < p := by exact_mod_cast hp
    have h1 : 0 ≤ m % (p : ℤ) := Int.emod_nonneg _ hpos.ne'
    have h2 : m % (p : ℤ) < p := Int.emod_lt_of_pos _ hpos
    have h4 : ((m % (p : ℤ)).toNat : ℤ) = m % p := Int.toNat_of_nonneg h1
    refine ⟨⟨(m % (p : ℤ)).toNat, by omega⟩, ?_⟩
    have h3 : x ^ m = x ^ (m % (p : ℤ)) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod m p]
      rw [zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, one_mul]
    have h5 : x ^ (m % (p : ℤ)) = x ^ ((m % (p : ℤ)).toNat) := by
      rw [← zpow_natCast, h4]
    exact h3.trans h5
  have htop : ∀ q : Q, q ∈ Subgroup.closure ({xa, xb} : Set Q) := by
    set H : Subgroup Q := Subgroup.closure {xa, xb} with hH
    set π : ↥U →* Q := QuotientGroup.mk' (Z.subgroupOf U) with hπ
    have hle : Subgroup.closure {a, b} ⊔ Z ≤ (H.comap π).map U.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
      · rintro x (rfl | rfl)
        · exact ⟨⟨x, ha⟩, Subgroup.subset_closure (Or.inl rfl), rfl⟩
        · exact ⟨⟨x, hb⟩, Subgroup.subset_closure (Or.inr rfl), rfl⟩
      · intro z hz
        refine ⟨⟨z, hZU hz⟩, ?_, rfl⟩
        have h1 : π ⟨z, hZU hz⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hz)
        show π ⟨z, hZU hz⟩ ∈ H
        rw [h1]
        exact H.one_mem
    have hsup : U ≤ (H.comap π).map U.subtype := fun u hu => hle (hgen.symm ▸ hu)
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u', hu', hu'e⟩ := hsup u.2
    have : u' = u := Subtype.ext hu'e
    rw [this] at hu'
    exact hu'
  have hsurj : Function.Surjective
      (fun ij : Fin p × Fin p => xa ^ (ij.1 : ℕ) * xb ^ (ij.2 : ℕ)) := by
    intro q
    obtain ⟨m, n, hmn⟩ := Subgroup.mem_closure_pair.1 (htop q)
    obtain ⟨i, hi⟩ := hred xa hxap m
    obtain ⟨j, hj⟩ := hred xb hxbp n
    refine ⟨(i, j), ?_⟩
    show xa ^ (i : ℕ) * xb ^ (j : ℕ) = q
    rw [← hmn, hi, hj]
  have hcard : Nat.card Q ≤ p * p := by
    calc Nat.card Q ≤ Nat.card (Fin p × Fin p) := Nat.card_le_card_of_surjective _ hsurj
      _ = p * p := by simp
  have hrel : Z.relIndex U = Nat.card Q := rfl
  have : p ^ 3 ≤ p * p := by
    rw [hrel] at h3
    exact h3.trans hcard
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  nlinarith

end CFSG.AGLEmbedding.ParabAutIrr
