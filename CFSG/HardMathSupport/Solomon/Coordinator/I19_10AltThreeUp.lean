module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Perm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem i1910a3_card_fixed_ne_three
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3eq : p = 3)
    (H : Subgroup (Perm Ω)) (hH : alternatingGroup Ω ≤ H)
    (d : Perm Ω) (hd : orderOf d = p)
    (N : Subgroup (Perm Ω))
    (hNle : N ≤ H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))
    (hNnorm : (N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))).Normal)
    (hNcop : Nat.Coprime p (Nat.card N))
    (z : Perm Ω) (hz : z ∈ N) (hz1 : z ≠ 1) :
    Fintype.card {x // d x = x} ≠ p := by
  have : Fact p.Prime := ⟨hp⟩
  intro hcard
  set α := {x // d x = x} with hαdef
  have hcardα : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have hzc : z * d = d * z := by
    have := (Subgroup.mem_centralizer_iff.mp (hNle hz).2) d (Set.mem_singleton d)
    exact this.symm
  have hzd : ∀ x, z (d x) = d (z x) := fun x => by
    have := congrArg (fun f : Perm Ω => f x) hzc
    simpa only [Perm.mul_apply] using this
  have h₁ : ∀ x, d (z x) = z x ↔ d x = x := fun x => by
    rw [← hzd]; exact z.injective.eq_iff
  have h₂ : ∀ x, z x ≠ x → d x = x := fun x hx => by
    by_contra h
    exact hx (fixes_supp_of_mem hp hp2 H hH d hd N hNle hNnorm hNcop hz h)
  let z' : Perm α := z.subtypePerm h₁
  have hz' : (Perm.ofSubtype z' : Perm Ω) = z := Perm.ofSubtype_subtypePerm h₁ h₂
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    rw [← hz', h, map_one]
  let K := H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω))
  let ψ : alternatingGroup α →* Perm Ω :=
    (Perm.ofSubtype : Perm α →* Perm Ω).comp (alternatingGroup α).subtype
  have hψinj : Function.Injective ψ :=
    Perm.ofSubtype_injective.comp (alternatingGroup α).subtype_injective
  have hψK : ∀ a, ψ a ∈ K := by
    intro a
    refine ⟨hH ?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · have := a.2
      rw [mem_alternatingGroup] at this ⊢
      show Perm.sign (Perm.ofSubtype (a : Perm α)) = 1
      rw [Perm.sign_ofSubtype]; exact this
    · intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hdisj : Perm.Disjoint (Perm.ofSubtype (a : Perm α) : Perm Ω) h := by
        intro y
        by_cases hy : h y = y
        · exact Or.inr hy
        · exact Or.inl (Perm.ofSubtype_apply_of_not_mem _ hy)
      exact hdisj.commute.symm.eq
  have hcardα' : Fintype.card α = 3 := by rw [hcard, hp3eq]
  have : Nontrivial α := by rw [← Fintype.one_lt_card_iff_nontrivial]; omega
  have hcardA : Nat.card (alternatingGroup α) = 3 := by
    rw [nat_card_alternatingGroup, hcardα, hcardα']
    rfl
  obtain ⟨x, hx⟩ : ∃ x : α, z' x ≠ x := by
    by_contra h
    push Not at h
    exact hz'1 (Equiv.ext h)
  obtain ⟨y, hy⟩ : ∃ y, y = z' x := ⟨_, rfl⟩
  have hxy : x ≠ y := fun h => hx (by rw [hy] at h; exact h.symm)
  obtain ⟨w, hwx, hwy⟩ : ∃ w : α, w ≠ x ∧ w ≠ y := by
    have hcl : ({x, y} : Finset α).card ≤ 2 := Finset.card_le_two
    have : 0 < (({x, y} : Finset α)ᶜ).card := by
      rw [Finset.card_compl]; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.1 this
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    exact ⟨w, hw.1, hw.2⟩
  have hywd : y ≠ w := fun h => hwy h.symm
  have hxw : x ≠ w := fun h => hwx h.symm
  have hall : ∀ t : α, t = x ∨ t = y ∨ t = w := by
    have hcl : ({x, y, w} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hywd]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hxw⟩
    have hu : ({x, y, w} : Finset α) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcl, hcardα'])
    intro t
    have : t ∈ ({x, y, w} : Finset α) := by rw [hu]; exact Finset.mem_univ t
    simpa using this
  set c : Perm α := swap x y * swap y w with hcdef
  have hcx : c x = y := by
    simp only [hcdef, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hxy hxw, swap_apply_left]
  have hcy : c y = w := by
    simp only [hcdef, Perm.mul_apply]
    rw [swap_apply_left, swap_apply_of_ne_of_ne hwx hwy]
  have hcw : c w = x := by
    simp only [hcdef, Perm.mul_apply]
    rw [swap_apply_right, swap_apply_right]
  have hcsign : Perm.sign c = 1 := by
    rw [hcdef, map_mul, Perm.sign_swap hxy, Perm.sign_swap hywd]
    decide
  have hsign : Perm.sign (z' * c * z'⁻¹ * c⁻¹) = 1 := by simp [hcsign]
  let a : alternatingGroup α := ⟨c, mem_alternatingGroup.mpr hcsign⟩
  let b : alternatingGroup α := ⟨_, mem_alternatingGroup.mpr hsign⟩
  have hbN : ψ b ∈ N := by
    have hK1 : (⟨z⁻¹, hNle (N.inv_mem hz)⟩ : K) ∈ N.subgroupOf K := N.inv_mem hz
    have := hNnorm.conj_mem _ hK1 ⟨ψ a, hψK a⟩
    have hcz : ψ a * z⁻¹ * (ψ a)⁻¹ ∈ N := this
    have : ψ b = z * (ψ a * z⁻¹ * (ψ a)⁻¹) := by
      show Perm.ofSubtype (z' * (a : Perm α) * z'⁻¹ * (a : Perm α)⁻¹) =
        z * (Perm.ofSubtype (a : Perm α) * z⁻¹ * (Perm.ofSubtype (a : Perm α))⁻¹)
      simp only [map_mul, map_inv, hz']
      group
    rw [this]
    exact N.mul_mem hz hcz
  have hb3 : b ^ 3 = 1 := by
    have := pow_card_eq_one' (G := alternatingGroup α) (x := b)
    rwa [hcardA] at this
  have ha3 : a ^ 3 = 1 := by
    have := pow_card_eq_one' (G := alternatingGroup α) (x := a)
    rwa [hcardA] at this
  by_cases hb1 : b = 1
  · have hb' : z' * c * z'⁻¹ * c⁻¹ = 1 := congrArg Subtype.val hb1
    have hcomm : z' * c = c * z' := by
      calc z' * c = (z' * c * z'⁻¹ * c⁻¹) * c * z' := by group
        _ = c * z' := by rw [hb']; simp
    have e1 : z' y = w := by
      have := congrArg (fun f : Perm α => f x) hcomm
      simp only [Perm.mul_apply, hcx, ← hy, hcy] at this
      exact this
    have e2 : z' w = x := by
      have := congrArg (fun f : Perm α => f y) hcomm
      simp only [Perm.mul_apply, hcy, e1, hcw] at this
      exact this
    have hzc' : z' = c := by
      ext t
      rcases hall t with rfl | rfl | rfl
      · rw [← hy, hcx]
      · rw [e1, hcy]
      · rw [e2, hcw]
    have hc3 : c ^ 3 = 1 := congrArg Subtype.val ha3
    have hz3 : z ^ p = 1 := by
      rw [← hz', ← map_pow, hp3eq, hzc', hc3, map_one]
    exact hz1 (eq_one_of_pow_eq_one_of_mem N hNcop hz hz3)
  · have hψb : (ψ b) ^ p = 1 := by rw [← map_pow, hp3eq, hb3, map_one]
    have := eq_one_of_pow_eq_one_of_mem N hNcop hbN hψb
    exact hb1 (hψinj (this.trans (map_one ψ).symm))

end CFSG.HardMathSupport.Solomon.Coordinator
