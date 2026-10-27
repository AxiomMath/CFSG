module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Lift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Succ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.ρ_comm_of_mem_fixSub {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) {x : K} (hx : x ∈ fixSub α) :
    C.ρ x * σ = σ * C.ρ x := by
  have h1 := h.map_ρ x
  rw [mem_fixSub.1 hx] at h1
  calc C.ρ x * σ = (σ * C.ρ x * σ⁻¹) * σ := by rw [← h1]
    _ = σ * C.ρ x := by group

theorem CoverSetup.Induces.exists_mem_fixSub_of_odd_generated [Finite K] {C : CoverSetup n K}
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) {Q : Subgroup (Perm (Fin n))}
    (hQA : Q ≤ alternatingGroup (Fin n)) (hQσ : ∀ q ∈ Q, q * σ = σ * q)
    {S : Set (Perm (Fin n))} (hS : Subgroup.closure S = Q) (hodd : ∀ g ∈ S, Odd (orderOf g)) :
    ∀ q ∈ Q, ∃ x ∈ fixSub α, C.ρ x = q := by
  classical
  set B : Subgroup K := Q.comap C.ρ with hB
  have hBσ : ∀ x ∈ B, C.ρ x * σ = σ * C.ρ x := fun x hx => hQσ _ hx
  have hidx := h.index_fixSub_le_two B hBσ
  let φ : ↥B →* ↥Q := (C.ρ.comp B.subtype).codRestrict Q (fun x => x.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hQA hq))
    exact ⟨⟨x, by rw [hB, Subgroup.mem_comap, hx]; exact hq⟩, Subtype.ext hx⟩
  set D : Subgroup ↥B := (fixSub α).subgroupOf B with hD
  have hdvd : (D.map φ).index ∣ D.index := Subgroup.index_map_dvd D hφ
  have hDpos : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : (D.map φ).index ≤ 2 := (Nat.le_of_dvd hDpos hdvd).trans hidx
  have hgen : Subgroup.closure (((↑) : ↥Q → Perm (Fin n)) ⁻¹' S) = ⊤ := by
    have := Subgroup.closure_closure_coe_preimage (k := S)
    rwa [hS] at this
  have hodd' : ∀ g ∈ (((↑) : ↥Q → Perm (Fin n)) ⁻¹' S), Odd (orderOf g) := fun g hg => by
    rw [← Subgroup.orderOf_coe]
    exact hodd _ hg
  have htop : D.map φ = ⊤ := eq_top_of_index_le_two_of_closure_odd hgen hodd' hle
  intro q hq
  have hmem : (⟨q, hq⟩ : ↥Q) ∈ D.map φ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨b, hb, hbq⟩ := Subgroup.mem_map.1 hmem
  refine ⟨(b : K), ?_, congrArg Subtype.val hbq⟩
  exact (Subgroup.mem_subgroupOf.1 hb)

theorem CoverSetup.Induces.exists_lift_pairHom [Finite K] {C : CoverSetup n K}
    {α : MulAut K} {k : ℕ} {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk)) :
    ∀ τ ∈ alternatingGroup (Fin k), ∃ x ∈ fixSub α, C.ρ x = pairHom n k hk τ := by
  intro τ hτ
  set Q : Subgroup (Perm (Fin n)) := (alternatingGroup (Fin k)).map (pairHom n k hk) with hQ
  have hQA : Q ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨t, -, rfl⟩
    rw [Perm.mem_alternatingGroup]
    exact sign_pairHom t
  have hQσ : ∀ q ∈ Q, q * stdInv n k hk = stdInv n k hk * q := by
    rintro _ ⟨t, -, rfl⟩
    exact pairHom_comm_stdInv t
  let S : Set (Perm (Fin n)) := (pairHom n k hk) '' {c : Perm (Fin k) | c.IsThreeCycle}
  have hS : Subgroup.closure S = Q := by
    rw [← MonoidHom.map_closure, Equiv.Perm.closure_three_cycles_eq_alternating]
  have hodd : ∀ g ∈ S, Odd (orderOf g) := by
    rintro _ ⟨c, hc, rfl⟩
    have h3 : orderOf (pairHom n k hk c) ∣ 3 := by
      have := orderOf_map_dvd (pairHom n k hk) c
      rwa [Equiv.Perm.IsThreeCycle.orderOf hc] at this
    exact Odd.of_dvd_nat (by decide : Odd 3) h3
  exact h.exists_mem_fixSub_of_odd_generated hQA hQσ hS hodd _ ⟨τ, hτ, rfl⟩

theorem CoverSetup.map_comap_eq_of_le (C : CoverSetup n K) {Q : Subgroup (Perm (Fin n))}
    (hQ : Q ≤ alternatingGroup (Fin n)) : (Q.comap C.ρ).map C.ρ = Q := by
  rw [Subgroup.map_comap_eq]
  refine inf_eq_right.2 fun q hq => ?_
  obtain ⟨x, hx⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hQ hq))
  exact ⟨x, hx⟩

theorem CoverSetup.Induces.exists_dblPair_mem_fixSub {C : CoverSetup n K} {α : MulAut K}
    {k : ℕ} {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk)) (i l : Fin k) (hil : i ≠ l) :
    ∃ x ∈ fixSub α, C.ρ x = dblPair n k hk i l := by
  set a := pairEmb n k hk (i, 0) with ha
  set b := pairEmb n k hk (i, 1) with hb
  set c := pairEmb n k hk (l, 0) with hc
  set d := pairEmb n k hk (l, 1) with hd
  have hinj := (pairEmb n k hk).injective
  have hab : a ≠ b := fun e => by have := hinj e; simp at this
  have hac : a ≠ c := fun e => hil (by have := hinj e; simp_all)
  have had : a ≠ d := fun e => hil (by have := hinj e; simp_all)
  have hbc : b ≠ c := fun e => hil (by have := hinj e; simp_all)
  have hbd : b ≠ d := fun e => hil (by have := hinj e; simp_all)
  have hcd : c ≠ d := fun e => by have := hinj e; simp at this
  have hsign : sign (dblPair n k hk i l) = 1 := by
    rw [dblPair, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
  refine ⟨x, ?_, hx⟩
  have hσa : stdInv n k hk a = b := by
    rw [ha, stdInv_apply_pair]
    rfl
  have hσb : stdInv n k hk b = a := by
    rw [hb, stdInv_apply_pair]
    rfl
  have hσc : stdInv n k hk c = d := by
    rw [hc, stdInv_apply_pair]
    rfl
  have hσd : stdInv n k hk d = c := by
    rw [hd, stdInv_apply_pair]
    rfl
  exact h.apply_eq_of_dbl_swapped hab hac had hbc hbd hcd hσa hσb hσc hσd hx

@[expose] def CoverSetup.fixedComp (C : CoverSetup n K) (k : ℕ) (hk : 2 * k ≤ n) : Subgroup K :=
  ⁅(altFix n k hk).comap C.ρ, (altFix n k hk).comap C.ρ⁆

theorem CoverSetup.Induces.fixedComp_isDoubleCover (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {k : ℕ} {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk))
    (hm : 5 ≤ n - 2 * k) :
    C.fixedComp k hk ≤ fixSub α ∧ IsDoubleCoverOfAlt ↥(C.fixedComp k hk) (n - 2 * k) ∧
      (C.fixedComp k hk).map C.ρ = altFix n k hk := by
  set m := n - 2 * k with hm_def
  set E : Subgroup K := (altFix n k hk).comap C.ρ with hE
  have hEσ : ∀ x ∈ E, C.ρ x * stdInv n k hk = stdInv n k hk * C.ρ x := fun x hx =>
    altFix_comm_stdInv hx
  set L : Subgroup K := ⁅E, E⁆ with hL
  have hLfix : L ≤ fixSub α := h.commutator_le_fixSub E hEσ
  have hEmap : E.map C.ρ = altFix n k hk := C.map_comap_eq_of_le altFix_le_alternatingGroup
  have haltPerf : ⁅altFix n k hk, altFix n k hk⁆ = altFix n k hk := by
    rw [← map_alternatingGroup_eq_altFix, ← Subgroup.map_commutator]
    congr 1
    have : Group.IsPerfect (alternatingGroup (Fin m)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
    exact Subgroup.isPerfect_iff.1 this
  have hLmap : L.map C.ρ = altFix n k hk := by
    rw [hL, Subgroup.map_commutator, hEmap, haltPerf]
  have hcen : ∀ a ∈ E, ∃ l ∈ L, l⁻¹ * a ∈ center K := by
    intro a ha
    have : C.ρ a ∈ L.map C.ρ := by rw [hLmap]; exact ha
    obtain ⟨l, hl, hla⟩ := this
    exact ⟨l, hl, by rw [← C.ρ_eq_one_iff, map_mul, map_inv, hla, inv_mul_cancel]⟩
  have hLperf : ⁅L, L⁆ = L := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
    · rw [hL]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨l₁, hl₁, hc₁⟩ := hcen a ha
      obtain ⟨l₂, hl₂, hc₂⟩ := hcen b hb
      have e₁ : a = l₁ * (l₁⁻¹ * a) := by group
      have e₂ : b = l₂ * (l₂⁻¹ * b) := by group
      have : ⁅a, b⁆ = ⁅l₁, l₂⁆ := by
        rw [e₁, e₂]
        exact (CFSG.SectionRank.commutatorElement_mul_mem_center l₁ l₂ hc₁ hc₂).trans (by
          simp)
      rw [this]
      exact Subgroup.commutator_mem_commutator hl₁ hl₂
  have hm4 : 4 ≤ m := by omega
  set a := fixEmb n k hk ⟨0, by omega⟩ with ha
  set b := fixEmb n k hk ⟨1, by omega⟩ with hb
  set c := fixEmb n k hk ⟨2, by omega⟩ with hc
  set d := fixEmb n k hk ⟨3, by omega⟩ with hd
  have hinj := (fixEmb n k hk).injective
  have hab : a ≠ b := fun e => by have := hinj e; simp at this
  have hac : a ≠ c := fun e => by have := hinj e; simp at this
  have had : a ≠ d := fun e => by have := hinj e; simp at this
  have hbc : b ≠ c := fun e => by have := hinj e; simp at this
  have hbd : b ≠ d := fun e => by have := hinj e; simp at this
  have hcd : c ≠ d := fun e => by have := hinj e; simp at this
  set u : Perm (Fin n) := swap a b * swap c d with hu
  have hu_mem : u ∈ altFix n k hk := by
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨p, rfl⟩ := hx
      have h1 : pairEmb n k hk p ≠ a := pairEmb_ne_fixEmb p _
      have h2 : pairEmb n k hk p ≠ b := pairEmb_ne_fixEmb p _
      have h3 : pairEmb n k hk p ≠ c := pairEmb_ne_fixEmb p _
      have h4 : pairEmb n k hk p ≠ d := pairEmb_ne_fixEmb p _
      rw [hu, Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
    · rw [hu, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
  obtain ⟨x, hxL, hxρ⟩ : ∃ x ∈ L, C.ρ x = u := by
    have : u ∈ L.map C.ρ := by rw [hLmap]; exact hu_mem
    obtain ⟨x, hx, hxu⟩ := this
    exact ⟨x, hx, hxu⟩
  have hxx : x * x ≠ 1 := C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hxρ
  have hxxL : x * x ∈ L := L.mul_mem hxL hxL
  have hxxc : x * x ∈ center K := C.sq_mem_center (by
    rw [hxρ, hu]
    exact dbl_mul_self hab hac had hbc hbd hcd)
  have hZL : center K ≤ L := by
    intro c' hc'
    by_cases h1 : c' = 1
    · rw [h1]
      exact L.one_mem
    · rw [C.center_eq_of_ne_one hc' hxxc h1 hxx]
      exact hxxL
  let eAlt : alternatingGroup (Fin m) ≃* altFix n k hk :=
    (Subgroup.equivMapOfInjective _ _
      (Equiv.Perm.viaEmbeddingHom_injective (fixEmb n k hk))).trans
      (MulEquiv.subgroupCongr map_alternatingGroup_eq_altFix)
  let ρL₀ : L →* altFix n k hk := (C.ρ.comp L.subtype).codRestrict (altFix n k hk) (fun x => by
    have : C.ρ x ∈ L.map C.ρ := ⟨x, x.2, rfl⟩
    rwa [hLmap] at this)
  let ρL : L →* alternatingGroup (Fin m) := eAlt.symm.toMonoidHom.comp ρL₀
  have hρL : ∀ x : L, ρL x = 1 ↔ (x : K) ∈ center K := fun x => by
    show eAlt.symm (ρL₀ x) = 1 ↔ _
    rw [map_eq_one_iff _ eAlt.symm.injective, ← C.ρ_eq_one_iff]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hsurj : Function.Surjective ρL := by
    intro a
    have : (eAlt a : Perm (Fin n)) ∈ L.map C.ρ := by rw [hLmap]; exact (eAlt a).2
    obtain ⟨l, hl, hla⟩ := this
    refine ⟨⟨l, hl⟩, ?_⟩
    show eAlt.symm (ρL₀ ⟨l, hl⟩) = a
    have : ρL₀ ⟨l, hl⟩ = eAlt a := Subtype.ext hla
    rw [this, MulEquiv.symm_apply_apply]
  have hkc : ρL.ker ≤ center ↥L := by
    intro x hx
    have hxc : (x : K) ∈ center K := (hρL x).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hxc g)
  have hkereq : ρL.ker = (center K).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, hρL, Subgroup.mem_subgroupOf]
  have hk2 : Nat.card ρL.ker = 2 := by
    rw [hkereq, ← C.center_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  exact ⟨hLfix, isDoubleCoverOfAlt_of_ker (by omega) (Subgroup.isPerfect_iff.2 hLperf) ρL hsurj
    hkc hk2, hLmap⟩

end AhatData

end CFSG.OddStandard.Solomon75
