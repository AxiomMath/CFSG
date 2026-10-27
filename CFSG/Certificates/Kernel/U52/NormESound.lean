module

public import Certificates.Data.Kernel.U52.NormE
public import CFSG.Certificates.Kernel.U52.NormSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.U52N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

@[expose] def Lists (n w : Nat) (KL : List Nat) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ k ∈ H, ∃ P ∈ KL, P >>> (n * w) = 0 ∧ PRep n w P k) ∧ ∀ P ∈ KL, ∃ k ∈ H, PRep n w P k

theorem Lists.memN (hw : n + 1 < 2 ^ w) {KL : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
    (hL : Lists n w KL H) {P : Nat} {z : Equiv.Perm (Fin n)} (hP0 : P >>> (n * w) = 0)
    (hP : PRep n w P z) (hz : z ∈ H) : U52N.memN P KL = true := by
  obtain ⟨Q, hQ, hQ0, hQz⟩ := hL.1 z hz
  rw [memN_iff, eq_of_prep hw hP0 hQ0 hP hQz]
  exact hQ

theorem Lists.mem {KL : List Nat} {H : Subgroup (Equiv.Perm (Fin n))} (hL : Lists n w KL H)
    {P : Nat} {z : Equiv.Perm (Fin n)} (hP : PRep n w P z) (h : U52N.memN P KL = true) : z ∈ H := by
  obtain ⟨k, hk, hkP⟩ := hL.2 P (memN_iff.1 h)
  rw [PRep.unique' hP hkP]
  exact hk

theorem khOK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {KL nK : List Nat}
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : Lists n w nK K) {c κ : Nat → Equiv.Perm (Fin n)}
    (hc : ∀ m < KL.length, PRep n w (KL.getD m 0) (c m))
    (hκ : ∀ i < 9, PRep n w (nK.getD i 0) (κ i))
    (h : khOK n w (mask w) (pidn n w) KL nK = true) :
    KL.length = 18 ∧ (∃ m < 18, c m = 1) ∧
    (∀ m < 18, ∀ s < 3, ∃ m' < 18, c m * c ([1, 3, 9].getD s 0) = c m') ∧
    (∀ i < 9, c i = κ i ∧ c (i + 9) = c 9 * κ i) ∧ (∀ m < 18, c m * c m ∈ K) := by
  unfold khOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hlen, hid⟩, hcl⟩, hpre, hsq⟩ := h
  have hidx : ∀ {P : Nat}, P ∈ KL → ∃ m < 18, KL.getD m 0 = P := fun hP => by
    obtain ⟨m, hm, he⟩ := List.mem_iff_getElem.1 hP
    exact ⟨m, hlen ▸ hm, by rw [List.getD_eq_getElem _ _ hm, he]⟩
  have hmem : ∀ m < 18, KL.getD m 0 ∈ KL := fun m hm => by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hm)]
    exact List.getElem_mem _
  have hc' : ∀ m < 18, PRep n w (KL.getD m 0) (c m) := fun m hm => hc m (hlen ▸ hm)
  refine ⟨hlen, ?_, fun m hm s hs => ?_, fun i hi => ?_, fun m hm => ?_⟩
  · obtain ⟨m, hm, he⟩ := hidx (memN_iff.1 hid)
    exact ⟨m, hm, PRep.unique' (hc' m hm) (by rw [he]; exact prep_pidn hn hw)⟩
  · have hg : KL.getD ([1, 3, 9].getD s 0) 0 ∈ khG KL := by
      interval_cases s <;> simp [khG]
    obtain ⟨m', hm', he⟩ := hidx (memN_iff.1 (hcl _ (hmem m hm) _ hg))
    have hs' : [1, 3, 9].getD s 0 < 18 := by interval_cases s <;> decide
    refine ⟨m', hm', PRep.unique' (prep_pcomp (by omega) (hc' m hm) (hc' _ hs')) ?_⟩
    rw [← he]
    exact hc' m' hm'
  · have h1 := CFSG.KS.allN_spec hpre i hi
    simp only [Bool.and_eq_true, Nat.beq_eq] at h1
    refine ⟨PRep.unique' (hc' i (by omega)) (by rw [h1.1]; exact hκ i hi), ?_⟩
    refine PRep.unique' (hc' (i + 9) (by omega)) ?_
    rw [h1.2]
    exact prep_pcomp (by omega) (hc' 9 (by norm_num)) (hκ i hi)
  · exact hK.mem (prep_pcomp (by omega) (hc' m hm) (hc' m hm)) (hsq _ (hmem m hm))

theorem hatT_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {fix : Nat} (hfix : fix < n)
    {KL ris : List Nat} {H : Subgroup (Equiv.Perm (Fin n))} (hL : Lists n w KL H)
    (hG : ∀ g ∈ khG KL, ∃ k ∈ H, PRep n w g k) {e : Nat} {x : Equiv.Perm (Fin n)}
    (he : PRep n w e x) (h : hatT n w (mask w) fix KL ris e = true)
    (hxfix : x ⟨fix, hfix⟩ ≠ ⟨fix, hfix⟩) (hxH : ∀ k ∈ H, x * k * x⁻¹ ∈ H) (hxx : x * x ∈ H) :
    ∃ r ∈ ris, ∀ ρ : Equiv.Perm (Fin n), PRep n w r ρ → ρ * x ∈ H := by
  have h32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold hatT at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  rcases h with ((h1 | h2) | h3) | h4
  · exact absurd (Fin.ext ((he ⟨fix, hfix⟩).symm.trans h1)) hxfix
  · rw [hL.memN hw (CFSG.KS.PF.pcomp_shr _ _ h32 hw0) (prep_pcomp h32 he he) hxx] at h2
    exact absurd h2 (by decide)
  · obtain ⟨r, hr, hm⟩ := List.any_eq_true.1 h3
    exact ⟨r, hr, fun ρ hρ => hL.mem (prep_pcomp h32 hρ he) hm⟩
  · exfalso
    have : ((khG KL).all fun g => KL.any fun c =>
        Nat.beq (pcomp n w (mask w) e g) (pcomp n w (mask w) c e)) = true := by
      refine List.all_eq_true.2 fun g hg => ?_
      obtain ⟨k, hk, hgk⟩ := hG g hg
      obtain ⟨C, hC, -, hCk⟩ := hL.1 _ (hxH k hk)
      refine List.any_eq_true.2 ⟨C, hC, ?_⟩
      rw [Nat.beq_eq]
      have h2 := prep_pcomp h32 hCk he
      have e' : x * k * x⁻¹ * x = x * k := by group
      rw [e'] at h2
      exact eq_of_prep hw (CFSG.KS.PF.pcomp_shr _ _ h32 hw0) (CFSG.KS.PF.pcomp_shr _ _ h32 hw0)
        (prep_pcomp h32 he hgk) h2
    rw [h4] at this
    exact absurd this (by decide)

theorem hatB_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {nK S0 : List Nat}
    {K S : Subgroup (Equiv.Perm (Fin n))} (hK : Lists n w nK K)
    (hS : ∀ c < S0.length, ∃ s ∈ S, PRep n w (S0.getD c 0) s) {e k : Nat} {sw : List Nat}
    {x : Equiv.Perm (Fin n)} (he : PRep n w e x)
    (h : hatB n w (mask w) (pidn n w) nK S0 e k sw = true) (hxx : x * x ∈ K) (hx : x ∉ K) :
    ∃ κ ∈ K, x * κ ∈ S ∧ x * κ ≠ 1 := by
  classical
  have h32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold hatB at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
    List.all_eq_true] at h
  rcases h with (h1 | h2) | ⟨⟨h3, h4⟩, hk, hsw⟩
  · rw [hK.memN hw (CFSG.KS.PF.pcomp_shr _ _ h32 hw0) (prep_pcomp h32 he he) hxx] at h1
    exact absurd h1 (by decide)
  · exact absurd (hK.mem he h2) hx
  · have hkm : nK.getD k 0 ∈ nK := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem _
    obtain ⟨κ, hκ, hκP⟩ := hK.2 _ hkm
    let g : Nat → Equiv.Perm (Fin n) := fun c =>
      if hc : c < S0.length then Classical.choose (hS c hc) else 1
    have hg : ∀ c ∈ sw, PRep n w (S0.getD c 0) (g c) := fun c hc => by
      have hcl := hsw c hc
      simp only [g, dif_pos hcl]
      exact (Classical.choose_spec (hS c hcl)).2
    have hgS : ∀ c ∈ sw, g c ∈ S := fun c hc => by
      have hcl := hsw c hc
      simp only [g, dif_pos hcl]
      exact (Classical.choose_spec (hS c hcl)).1
    have hprod := prep_evP hn hw hg
    have hxk := prep_pcomp h32 he hκP
    rw [h3] at hxk
    refine ⟨κ, hκ, ?_, fun h1 => ?_⟩
    · rw [PRep.unique' hxk hprod]
      exact Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
        exact hgS c hc
    · have hP := prep_pcomp h32 he hκP
      rw [h1] at hP
      rw [eq_of_prep hw (CFSG.KS.PF.pcomp_shr _ _ h32 hw0) (CFSG.KS.PF.pidn_shr hn hw) hP
        (prep_pidn hn hw)] at h4
      simp at h4

theorem hatF_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {nK : List Nat}
    {C : List (List Nat)} {K : Subgroup (Equiv.Perm (Fin n))} (hK : Lists n w nK K) {e : Nat}
    {x : Equiv.Perm (Fin n)} (he : PRep n w e x) (h : hatF n w (mask w) nK C e = true)
    (hxx : x * x ∈ K) : ∃ c ∈ C, e ∈ c := by
  have h32 : n < 2 ^ 32 := by omega
  unfold hatF at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h1 | h2
  · rw [hK.memN hw (CFSG.KS.PF.pcomp_shr _ _ h32 (CFSG.KS.PF.w_pos hw)) (prep_pcomp h32 he he)
      hxx] at h1
    exact absurd h1 (by decide)
  · obtain ⟨c, hc, hm⟩ := List.any_eq_true.1 h2
    exact ⟨c, hc, memN_iff.1 hm⟩

end CFSG.KS.U52N

end
