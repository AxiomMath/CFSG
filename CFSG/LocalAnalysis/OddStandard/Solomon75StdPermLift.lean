module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
open scoped commutatorElement
open AhatData

variable {n : ℕ} {K : Type} [Group K]

@[expose] def IsPairLift (C : AhatData.CoverSetup n K) (σ : Perm (Fin n)) (r : K) : Prop :=
  ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c ∧ C.ρ r = swap a b * swap c d

theorem exists_isPairLift (C : AhatData.CoverSetup n K) {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    {m : ℕ} (hm : σ.support.card = 2 * m) (hm2 : 2 ≤ m) : ∃ r : K, IsPairLift C σ r := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd⟩ := exists_two_pairs hσ hm hm2
  have hsign : sign (swap a b * swap c d) = 1 := by
    rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
  exact ⟨x, a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd, hx⟩

namespace IsPairLift

variable {C : AhatData.CoverSetup n K} {σ : Perm (Fin n)} {r : K}

theorem apply_eq {α : MulAut K} (h : C.Induces α σ) (hr : IsPairLift C σ r) : α r = r := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd, hρ⟩ := hr
  exact h.apply_eq_of_dbl_swapped hab hac had hbc hbd hcd ha hb hc hd hρ

theorem sq_ne_one (hn : 8 ≤ n) (hr : IsPairLift C σ r) : r * r ≠ 1 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, -, -, -, -, hρ⟩ := hr
  exact C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hρ

theorem sq_mem_center (hr : IsPairLift C σ r) : r * r ∈ center K := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, -, -, -, -, hρ⟩ := hr
  exact C.sq_mem_center (by rw [hρ]; exact dbl_mul_self hab hac had hbc hbd hcd)

theorem comm_of_fixed (hr : IsPairLift C σ r) {g : Perm (Fin n)}
    (hg : ∀ x, σ x ≠ x → g x = x) : g * C.ρ r = C.ρ r * g := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd, hρ⟩ := hr
  have ga : g a = a := hg a (by rw [ha]; exact hab.symm)
  have gb : g b = b := hg b (by rw [hb]; exact hab)
  have gc : g c = c := hg c (by rw [hc]; exact hcd.symm)
  have gd : g d = d := hg d (by rw [hd]; exact hcd)
  rw [hρ, ← mul_assoc, mul_swap_comm_of_fixed ga gb, mul_assoc, mul_swap_comm_of_fixed gc gd,
    mul_assoc]

end IsPairLift

theorem AhatData.CoverSetup.Induces.le_fixSub_of_oddGenerated {C : AhatData.CoverSetup n K}
    {α : MulAut K} {τ : Perm (Fin n)} (h : C.Induces α τ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * τ = τ * C.ρ x)
    (hgen : Subgroup.closure {x : ↥H | Odd (orderOf x)} = ⊤) : H ≤ AhatData.fixSub α := by
  have hodd : ∀ x : ↥H, Odd (orderOf x) → h.commHom H hH x = 1 := by
    intro x hx
    have h1 : orderOf (h.commHom H hH x) ∣ orderOf x := orderOf_map_dvd _ _
    have h2 : orderOf (h.commHom H hH x) ∣ 2 := by
      have := _root_.orderOf_dvd_natCard (h.commHom H hH x)
      rwa [C.center_card] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact orderOf_eq_one_iff.1 h3
    · exfalso
      rw [h3] at h1
      obtain ⟨k, hk⟩ := h1
      obtain ⟨m, hm⟩ := hx
      omega
  have hle : Subgroup.closure {x : ↥H | Odd (orderOf x)} ≤ (h.commHom H hH).ker := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hodd x hx
  rw [hgen] at hle
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥H) ∈ (h.commHom H hH).ker := hle (Subgroup.mem_top _)
  rw [h.ker_commHom H hH] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem comm_of_forall_fixed {σ g : Perm (Fin n)} (hg : ∀ x, σ x ≠ x → g x = x) :
    g * σ = σ * g := by
  refine (Equiv.Perm.Disjoint.commute (fun x => ?_)).eq
  by_cases h : σ x = x
  · exact Or.inr h
  · exact Or.inl (hg x h)

theorem closure_threeCycles_altFixOf (σ : Perm (Fin n)) :
    Subgroup.closure {c : Perm (Fin n) | c.IsThreeCycle ∧ c ∈ altFixOf σ} = altFixOf σ := by
  classical
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun c hc => hc.2
  · intro g hg
    have hcomm : g * σ = σ * g := comm_of_forall_fixed hg.1
    have hg1 : ∀ x, σ (g x) = g x ↔ σ x = x := fun x => by
      have : σ (g x) = g (σ x) := by
        have := congrArg (fun e : Perm (Fin n) => e x) hcomm.symm
        simpa [Perm.mul_apply] using this
      rw [this]
      exact g.injective.eq_iff
    have hg2 : ∀ x, g x ≠ x → σ x = x := fun x hx => by
      by_contra h
      exact hx (hg.1 x h)
    let g' : Perm {x : Fin n // σ x = x} := g.subtypePerm hg1
    have hsign : sign g' = 1 := by
      rw [Perm.sign_subtypePerm g hg1 hg2]
      exact hg.2
    have hg'alt : g' ∈ alternatingGroup {x : Fin n // σ x = x} := Perm.mem_alternatingGroup.2 hsign
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hg'alt
    have hmap : Equiv.Perm.ofSubtype g' ∈
        (Subgroup.closure {c : Perm {x : Fin n // σ x = x} | c.IsThreeCycle}).map
          (Equiv.Perm.ofSubtype : Perm {x : Fin n // σ x = x} →* Perm (Fin n)) :=
      ⟨g', hg'alt, rfl⟩
    rw [MonoidHom.map_closure] at hmap
    have hback : Equiv.Perm.ofSubtype g' = g := Equiv.Perm.ofSubtype_subtypePerm hg1 hg2
    rw [hback] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨c', hc', rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have := hc'
      unfold Equiv.Perm.IsThreeCycle at this ⊢
      rw [Equiv.Perm.cycleType_ofSubtype]
      exact this
    · intro x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem c' (by simpa using hx)
    · rw [Equiv.Perm.sign_ofSubtype]
      exact hc'.sign

theorem exists_lift_pow_three (C : AhatData.CoverSetup n K) {c : Perm (Fin n)}
    (hc : c.IsThreeCycle) : ∃ y : K, C.ρ y = c ∧ y ^ 3 = 1 := by
  obtain ⟨x, hx⟩ := C.exists_ρ_eq (hc.sign)
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc.orderOf] at this
  have hx3 : x ^ 3 ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_pow, hx, hc3]
  by_cases h1 : x ^ 3 = 1
  · exact ⟨x, hx, h1⟩
  · have hz2 : x ^ 3 * x ^ 3 = 1 := C.sq_of_mem_center hx3
    have hcomm : Commute x (x ^ 3) := (Commute.refl x).pow_right 3
    refine ⟨x * x ^ 3, ?_, ?_⟩
    · rw [map_mul, hx, (C.ρ_eq_one_iff).2 hx3, mul_one]
    · rw [hcomm.mul_pow]
      calc x ^ 3 * (x ^ 3) ^ 3 = (x ^ 3 * x ^ 3) * (x ^ 3 * x ^ 3) := by group
        _ = 1 := by rw [hz2, one_mul]

theorem oddGenerated_altFixOf_comap (C : AhatData.CoverSetup n K) (hn : 8 ≤ n)
    {σ : Perm (Fin n)} (hf : σ.support.card + 4 ≤ n) :
    Subgroup.closure {x : ↥((altFixOf σ).comap C.ρ) | Odd (orderOf x)} = ⊤ := by
  classical
  set E : Subgroup K := (altFixOf σ).comap C.ρ with hE
  let Mρ : ↥E →* Perm (Fin n) := C.ρ.comp E.subtype
  set H₃ : Subgroup ↥E := Subgroup.closure {x : ↥E | Odd (orderOf x)} with hH₃
  have hStep1 : altFixOf σ ≤ H₃.map Mρ := by
    rw [← closure_threeCycles_altFixOf σ, Subgroup.closure_le]
    rintro c ⟨hc3, hcE⟩
    obtain ⟨y, hy, hy3⟩ := exists_lift_pow_three C hc3
    have hyE : y ∈ E := by
      rw [hE, Subgroup.mem_comap, hy]
      exact hcE
    refine ⟨⟨y, hyE⟩, Subgroup.subset_closure ?_, hy⟩
    show Odd (orderOf (⟨y, hyE⟩ : ↥E))
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy3)
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_distinct ((σ.support)ᶜ) (by rw [Finset.card_compl, Fintype.card_fin]; omega)
  have hfx : ∀ x ∈ (σ.support)ᶜ, σ x = x := fun x hx => by
    simpa [Perm.notMem_support] using hx
  have hu : swap a b * swap c d ∈ altFixOf σ := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hxa : x ≠ a := fun e => hx (by rw [e]; exact hfx a ha)
      have hxb : x ≠ b := fun e => hx (by rw [e]; exact hfx b hb)
      have hxc : x ≠ c := fun e => hx (by rw [e]; exact hfx c hc)
      have hxd : x ≠ d := fun e => hx (by rw [e]; exact hfx d hd)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]
    · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
  obtain ⟨y', hy'H, hy'ρ⟩ := hStep1 hu
  have hρy' : C.ρ (y' : K) = swap a b * swap c d := hy'ρ
  have hc₀ne : (y' : K) * (y' : K) ≠ 1 := C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hρy'
  have hc₀cen : (y' : K) * (y' : K) ∈ center K :=
    C.sq_mem_center (by rw [hρy']; exact dbl_mul_self hab hac had hbc hbd hcd)
  have hc₀H : y' * y' ∈ H₃ := H₃.mul_mem hy'H hy'H
  rw [eq_top_iff]
  intro x _
  have hx : C.ρ (x : K) ∈ altFixOf σ := x.2
  obtain ⟨y, hyH, hyx⟩ := hStep1 hx
  have hyx' : C.ρ (y : K) = C.ρ (x : K) := hyx
  have hcen : (y : K)⁻¹ * (x : K) ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hyx', inv_mul_cancel]
  by_cases h1 : (y : K)⁻¹ * (x : K) = 1
  · have : x = y := Subtype.ext (inv_mul_eq_one.1 h1).symm
    rw [this]
    exact hyH
  · have h2 : (y : K)⁻¹ * (x : K) = (y' : K) * (y' : K) :=
      C.center_eq_of_ne_one hcen hc₀cen h1 hc₀ne
    have h3 : x = y * (y' * y') := Subtype.ext (by
      have : (x : K) = (y : K) * ((y' : K) * (y' : K)) := by rw [← h2]; group
      simpa using this)
    rw [h3]
    exact H₃.mul_mem hyH hc₀H

theorem altFixOf_comap_le_fixSub (C : AhatData.CoverSetup n K) (hn : 8 ≤ n) {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (hf : σ.support.card + 4 ≤ n) :
    (altFixOf σ).comap C.ρ ≤ fixSub α :=
  h.le_fixSub_of_oddGenerated _ (fun _ hx => comm_of_forall_fixed hx.1)
    (oddGenerated_altFixOf_comap C hn hf)

namespace IsPairLift

variable {C : AhatData.CoverSetup n K} {σ : Perm (Fin n)} {r : K}

theorem comm_of_mem_altFixOf_comap (hn : 8 ≤ n) (hr : IsPairLift C σ r)
    (hf : σ.support.card + 4 ≤ n) {x : K} (hx : x ∈ (altFixOf σ).comap C.ρ) : x * r = r * x := by
  have hle := (C.induces_conj r).le_fixSub_of_oddGenerated ((altFixOf σ).comap C.ρ)
    (fun y hy => hr.comm_of_fixed hy.1) (oddGenerated_altFixOf_comap C hn hf)
  rw [fixSub_conj] at hle
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem comm_of_mem_fixedCompOf (hr : IsPairLift C σ r) {x : K}
    (hx : x ∈ C.fixedCompOf σ) : x * r = r * x := by
  have hle := (C.induces_conj r).commutator_le_fixSub ((altFixOf σ).comap C.ρ)
    (fun y hy => hr.comm_of_fixed hy.1)
  rw [fixSub_conj] at hle
  exact mem_centralizer_singleton_iff.1 (hle hx)

end IsPairLift

end CFSG.OddStandard.Solomon75
