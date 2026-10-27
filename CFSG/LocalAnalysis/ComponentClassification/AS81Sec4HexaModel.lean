module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowCheck

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

noncomputable abbrev hexaT : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaTGens
noncomputable abbrev hexaM : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaMGens
noncomputable abbrev hexaR0 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaR0Gens
noncomputable abbrev hexaC0 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaCGens
noncomputable abbrev hexaN0 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaN0Gens
noncomputable abbrev hexaT0P : Equiv.Perm (Fin 64) := permOfArr 64 hexaT0

theorem exists_mem_not_mem_finset {G : Type*} {V : Set G} (S : Finset G)
    (h : S.card < Nat.card V) : ∃ v ∈ V, v ∉ S := by
  by_contra hc
  push Not at hc
  have := Nat.card_mono (Finset.finite_toSet S) hc
  rw [Nat.card_coe_set_eq (S : Set G), Set.ncard_coe_finset] at this
  omega

theorem exists_three {G : Type*} [Group G] {V : Subgroup G} (h4 : 4 < Nat.card V) :
    ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b := by
  classical
  obtain ⟨a, ha, ha1⟩ := exists_mem_not_mem_finset (V := (V : Set G)) {1}
    (by rw [Finset.card_singleton]; exact lt_trans (by norm_num) h4)
  obtain ⟨b, hb, hb1⟩ := exists_mem_not_mem_finset (V := (V : Set G)) {1, a}
    (lt_of_le_of_lt Finset.card_le_two (lt_trans (by norm_num) h4))
  obtain ⟨c, hc, hc1⟩ := exists_mem_not_mem_finset (V := (V : Set G)) {1, a, b, a * b}
    (lt_of_le_of_lt Finset.card_le_four h4)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1 hc1
  exact ⟨a, ha, b, hb, c, hc, ha1, hb1.1, hc1.1, hb1.2, hc1.2.1, hc1.2.2.1, hc1.2.2.2⟩

theorem comm_of_sq {G : Type*} [Group G] {V : Subgroup G} (hsq : ∀ v ∈ V, v * v = 1) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq _ (V.mul_mem ha hb))
  rw [mul_inv_rev, ha', hb'] at hab
  exact hab.symm

section Blocks

variable {α : Type*} {k : ℕ}

structure IsBlockSys (C : Subgroup (Equiv.Perm α)) (P : α → Prop) (b : α → Fin k)
    (rep : Fin k → α) : Prop where
  rep_mem : ∀ i, P (rep i)
  b_rep : ∀ i, b (rep i) = i
  map : ∀ σ ∈ C, ∀ a, P a → P (σ a) ∧ b (σ a) = b (σ (rep (b a)))

variable {C : Subgroup (Equiv.Perm α)} {P : α → Prop} {b : α → Fin k} {rep : Fin k → α}

theorem IsBlockSys.apply_mul (h : IsBlockSys C P b rep) {σ τ : Equiv.Perm α} (hσ : σ ∈ C)
    (hτ : τ ∈ C) (i : Fin k) : b ((σ * τ) (rep i)) = b (σ (rep (b (τ (rep i))))) := by
  rw [Equiv.Perm.mul_apply]
  exact (h.map σ hσ _ (h.map τ hτ _ (h.rep_mem i)).1).2

@[expose] def IsBlockSys.hom (h : IsBlockSys C P b rep) : ↥C →* Equiv.Perm (Fin k) where
  toFun σ :=
    { toFun := fun i => b ((σ : Equiv.Perm α) (rep i))
      invFun := fun i => b (((σ⁻¹ : ↥C) : Equiv.Perm α) (rep i))
      left_inv := fun i => by
        show b (((σ⁻¹ : ↥C) : Equiv.Perm α) (rep (b ((σ : Equiv.Perm α) (rep i))))) = i
        rw [← h.apply_mul (σ⁻¹).2 σ.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Equiv.Perm.one_apply, h.b_rep]
      right_inv := fun i => by
        show b ((σ : Equiv.Perm α) (rep (b (((σ⁻¹ : ↥C) : Equiv.Perm α) (rep i))))) = i
        rw [← h.apply_mul σ.2 (σ⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Equiv.Perm.one_apply, h.b_rep] }
  map_one' := Equiv.ext fun i => by
    change b ((1 : Equiv.Perm α) (rep i)) = i
    rw [Equiv.Perm.one_apply, h.b_rep]
  map_mul' σ τ := Equiv.ext fun i => by
    change b (((σ * τ : ↥C) : Equiv.Perm α) (rep i)) = b ((σ : Equiv.Perm α)
      (rep (b ((τ : Equiv.Perm α) (rep i)))))
    rw [Subgroup.coe_mul]
    exact h.apply_mul σ.2 τ.2 i

theorem IsBlockSys.hom_apply (h : IsBlockSys C P b rep) (σ : ↥C) (i : Fin k) :
    h.hom σ i = b ((σ : Equiv.Perm α) (rep i)) := rfl

end Blocks

section Labels

variable {n k : ℕ} [NeZero n] [NeZero k]

@[expose] def labP (k : ℕ) (blk : Array ℕ) (v : Fin n) : Prop := blk[v.val]! < k

@[expose] def labB (k : ℕ) [NeZero k] (blk : Array ℕ) (v : Fin n) : Fin k := Fin.ofNat k blk[v.val]!

@[expose] def labRep (n : ℕ) [NeZero n] (rep : Array ℕ) (i : Fin k) : Fin n :=
  Fin.ofNat n rep[i.val]!

omit [NeZero n] [NeZero k] in
theorem blockN_parts {C : List (Array ℕ)} {blk rep : Array ℕ} (h : blockN n k C blk rep = true) :
    (∀ i < k, rep[i]! < n ∧ blk[rep[i]!]! = i) ∧
      ∀ t ∈ C, ∀ v < n, blk[v]! < k → blk[t[v]!]! < k ∧ blk[t[v]!]! = blk[t[rep[blk[v]!]!]!]! := by
  simp only [blockN, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  refine ⟨h.1, fun t ht v hv hb => ?_⟩
  have := h.2 t ht v hv
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at this
  rcases this with h1 | h1
  · exact absurd hb h1
  · exact h1

theorem isBlockSys_of_blockN {gs : List (Array ℕ)} {m : ℕ} {blk rep : Array ℕ}
    (hC : enumCheckN n gs m = true) (h : blockN n k (eltsN n gs) blk rep = true) :
    IsBlockSys (grpN n gs) (labP k blk) (labB k blk) (labRep n rep) := by
  obtain ⟨hr, hm⟩ := blockN_parts h
  have hrep : ∀ i : Fin k, ((labRep n rep i : Fin n) : ℕ) = rep[i.val]! := fun i => by
    rw [labRep, Fin.val_ofNat, Nat.mod_eq_of_lt (hr i.val i.2).1]
  have hb : ∀ v : Fin n, labP k blk v → ((labB k blk v : Fin k) : ℕ) = blk[v.val]! := fun v hv => by
    rw [labB, Fin.val_ofNat, Nat.mod_eq_of_lt hv]
  refine ⟨fun i => ?_, fun i => ?_, fun σ hσ a ha => ?_⟩
  · change blk[((labRep n rep i : Fin n) : ℕ)]! < k
    rw [hrep, (hr i.val i.2).2]
    exact i.2
  · have hP : labP k blk (labRep n rep i) := by
      change blk[((labRep n rep i : Fin n) : ℕ)]! < k
      rw [hrep, (hr i.val i.2).2]
      exact i.2
    exact Fin.ext (by rw [hb _ hP, hrep, (hr i.val i.2).2])
  · obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hC).1 hσ
    obtain ⟨h1, h2⟩ := hm t ht a.val a.2 ha
    have hσa : ((σ a : Fin n) : ℕ) = t[a.val]! := (hrt a).symm
    have hPa : labP k blk (σ a) := by
      change blk[((σ a : Fin n) : ℕ)]! < k
      rw [hσa]
      exact h1
    have hrb : ((labRep n rep (labB k blk a) : Fin n) : ℕ) = rep[blk[a.val]!]! := by
      rw [hrep, hb a ha]
    have hσr : ((σ (labRep n rep (labB k blk a)) : Fin n) : ℕ) = t[rep[blk[a.val]!]!]! := by
      rw [← hrb]
      exact (hrt _).symm
    refine ⟨hPa, Fin.ext ?_⟩
    rw [hb _ hPa, labB, Fin.val_ofNat, hσa, hσr, h2]
    exact (Nat.mod_eq_of_lt (h2 ▸ h1)).symm

theorem all_of_hom_eq_one {gs : List (Array ℕ)} {m : ℕ} {blk rep : Array ℕ}
    (hC : enumCheckN n gs m = true) (hb : blockN n k (eltsN n gs) blk rep = true)
    {σ : ↥(grpN n gs)} {t : Array ℕ} (ht : t ∈ eltsN n gs) (hrt : Rep n t σ)
    (hσ : (isBlockSys_of_blockN hC hb).hom σ = 1) :
    (List.range k).all (fun i => blk[t[rep[i]!]!]! == i) = true := by
  obtain ⟨hr, hm⟩ := blockN_parts hb
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hj : (isBlockSys_of_blockN hC hb).hom σ ⟨i, hi'⟩ = ⟨i, hi'⟩ := by rw [hσ]; rfl
  rw [IsBlockSys.hom_apply] at hj
  have hrep : ((labRep n rep (⟨i, hi'⟩ : Fin k) : Fin n) : ℕ) = rep[i]! := by
    rw [labRep, Fin.val_ofNat, Nat.mod_eq_of_lt (hr i hi').1]
  have hσr : (((σ : Equiv.Perm (Fin n)) (labRep n rep ⟨i, hi'⟩) : Fin n) : ℕ) = t[rep[i]!]! := by
    rw [← hrep]
    exact (hrt _).symm
  have hlt : blk[t[rep[i]!]!]! < k :=
    (hm t ht (rep[i]!) (hr i hi').1 (by rw [(hr i hi').2]; exact hi')).1
  have hv := congrArg Fin.val hj
  rw [labB, Fin.val_ofNat, hσr, Nat.mod_eq_of_lt hlt] at hv
  simpa using hv

end Labels

structure HexaFacts : Prop where
  normT : hexaM ≤ normalizer (hexaT : Set (Equiv.Perm (Fin 64)))
  R0T : hexaR0 ≤ hexaT
  orbit : ∀ t ∈ hexaT, t ≠ 1 → ∀ V : Subgroup (Equiv.Perm (Fin 64)), V ≤ hexaM →
    (∀ v ∈ V, v * t = t * v) → (∀ v ∈ V, v * v = 1) → 4 < Nat.card V →
    ∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P
  cent : hexaM ⊓ centralizer {hexaT0P} = hexaC0
  gens : ∀ a ∈ hexaCGens, permOfArr 64 a ^ 4 = 1
  move : ∀ m ∈ hexaM, ∃ g ∈ hexaC0, ∃ r ∈ hexaR0, m⁻¹ * g * m * r * (m⁻¹ * g * m)⁻¹ ∉ hexaR0
  normN : hexaC0 ≤ normalizer (hexaN0 : Set (Equiv.Perm (Fin 64)))
  cardN : Nat.card hexaN0 = 8
  normalE8 : ∀ V : Subgroup (Equiv.Perm (Fin 64)), V ≤ hexaC0 → (∀ v ∈ V, v * v = 1) →
    (∀ t ∈ hexaT, (∀ v ∈ V, t * v = v * t) → t = 1 ∨ t = hexaT0P) → V ≤ hexaN0
  iso : Nonempty (↥hexaC0 ≃* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))
  fuse : ∃ a ∈ hexaN0, ∃ x ∈ hexaT, a * x * a⁻¹ * x⁻¹ ≠ 1 ∧ a * x * a⁻¹ * x⁻¹ ≠ hexaT0P ∧
    ∃ m ∈ hexaM, m * (a * x * a⁻¹ * x⁻¹) * m⁻¹ = hexaT0P

theorem hexaCheck_parts (h : hexaCheck = true) :
    enumCheckN 64 hexaTGens 64 = true ∧ enumCheckN 64 hexaMGens 2160 = true ∧
    enumCheckN 64 hexaCGens 48 = true ∧ enumCheckN 64 hexaN0Gens 8 = true ∧
    enumCheckN 64 hexaR0Gens 4 = true ∧ validA 64 hexaT0 = true ∧
    hexaR0Gens.all (inLN 64 (eltsN 64 hexaTGens)) = true ∧
    hexaMGens.all (fun g => hexaTGens.all fun q =>
      inLN 64 (eltsN 64 hexaTGens) (conjA 64 g q)) = true ∧
    orbitW 64 (eltsN 64 hexaTGens) (eltsN 64 hexaMGens) hexaT0 hexaOrbConj = true ∧
    hexaCGens.all (inLN 64 (eltsN 64 hexaMGens)) = true ∧
    hexaCGens.all (fun g => commN 64 g hexaT0) = true ∧
    ((eltsN 64 hexaMGens).filter fun m => commN 64 m hexaT0).length = 48 ∧
    hexaCGens.all (fun g => eqA 64 (powN 64 g 4) (idA 64)) = true ∧
    moveN 64 (eltsN 64 hexaMGens) hexaCGens hexaR0Gens (eltsN 64 hexaR0Gens) = true ∧
    hexaCGens.all (fun g => hexaN0Gens.all fun q =>
      inLN 64 (eltsN 64 hexaN0Gens) (conjA 64 g q)) = true ∧
    normalE8N 64 (eltsN 64 hexaTGens) (eltsN 64 hexaCGens) (eltsN 64 hexaN0Gens) hexaT0 = true ∧
    blockN 64 4 (eltsN 64 hexaCGens) hexaBlk4 hexaRep4 = true ∧
    blockN 64 2 (eltsN 64 hexaCGens) hexaBlk2 hexaRep2 = true ∧
    faithfulN 64 (eltsN 64 hexaCGens) hexaBlk4 hexaRep4 4 hexaBlk2 hexaRep2 2 = true ∧
    fuseW 64 (eltsN 64 hexaTGens) (eltsN 64 hexaMGens) (eltsN 64 hexaN0Gens) hexaT0
      hexaFuseW = true := by
  simp only [hexaCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

section Sound

variable (h : hexaCheck = true)
include h

theorem rep_t0 : Rep 64 hexaT0 hexaT0P := rep_of_validA (hexaCheck_parts h).2.2.2.2.2.1

omit h in
theorem exists_rep_of_mem {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckN 64 gs m = true)
    {x : Equiv.Perm (Fin 64)} (hx : x ∈ grpN 64 gs) :
    ∃ t ∈ eltsN 64 gs, Rep 64 t x ∧ validA 64 t = true := by
  obtain ⟨t, ht, hr⟩ := (mem_grpN_iff hg).1 hx
  exact ⟨t, ht, hr, validA_of_mem_elts hg ht⟩

omit h in
theorem mem_invCentN {L : List (Array ℕ)} {a t : Array ℕ} {A T : Equiv.Perm (Fin 64)}
    (ha : a ∈ L) (hra : Rep 64 a A) (hrt : Rep 64 t T) (hc : A * T = T * A) (h2 : A * A = 1)
    (h1 : A ≠ 1) : a ∈ invCentN 64 L t := by
  refine List.mem_filter.2 ⟨ha, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨(commN_iff hra hrt).2 hc, (eqA_iff (rep_mulN hra hra) rep_idA).2 h2⟩, ?_⟩
  by_contra hc'
  exact h1 ((eqA_iff hra rep_idA).1 (by simpa using hc'))

omit h in
theorem of_mem_invCentN {L : List (Array ℕ)} {a t : Array ℕ} {A T : Equiv.Perm (Fin 64)}
    (ha : a ∈ invCentN 64 L t) (hra : Rep 64 a A) (hrt : Rep 64 t T) :
    a ∈ L ∧ A * T = T * A ∧ A * A = 1 ∧ A ≠ 1 := by
  obtain ⟨haL, hb⟩ := List.mem_filter.1 ha
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
  refine ⟨haL, (commN_iff hra hrt).1 hb.1.1, (eqA_iff (rep_mulN hra hra) rep_idA).1 hb.1.2,
    fun h1 => ?_⟩
  rw [(eqA_iff hra rep_idA).2 h1] at hb
  exact absurd hb.2 (by decide)

theorem normT_of : hexaM ≤ normalizer (hexaT : Set (Equiv.Perm (Fin 64))) := by
  obtain ⟨hT, hM, -, -, -, -, -, hnT, -⟩ := hexaCheck_parts h
  exact le_normalizer_of_all hT (fun g hg => validA_of_mem hM hg) hnT

theorem R0T_of : hexaR0 ≤ hexaT := by
  obtain ⟨hT, -, -, -, hR, -, hRT, -⟩ := hexaCheck_parts h
  exact grpN_le_of_all hT hR hRT

theorem orbit_of : ∀ t ∈ hexaT, t ≠ 1 → ∀ V : Subgroup (Equiv.Perm (Fin 64)), V ≤ hexaM →
    (∀ v ∈ V, v * t = t * v) → (∀ v ∈ V, v * v = 1) → 4 < Nat.card V →
    ∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P := by
  obtain ⟨hT, hM, -, -, -, -, -, -, hob, -⟩ := hexaCheck_parts h
  intro t ht ht1 V hVM hVt hsq h4
  obtain ⟨t', ht', hrt, -⟩ := exists_rep_of_mem hT ht
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem ht'
  have hb := List.all_eq_true.1 hob i (List.mem_range.2 hi)
  rw [getElem!_pos (eltsN 64 hexaTGens) i hi, hti] at hb
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with (hb | ⟨hw, hb⟩) | hb
  · exact absurd ((eqA_iff hrt rep_idA).1 hb) ht1
  · rw [getElem!_pos (eltsN 64 hexaMGens) _ hw] at hb
    obtain ⟨m', hm', he⟩ : ∃ m' ∈ eltsN 64 hexaMGens, eqA 64 (conjA 64 m' t') hexaT0 = true :=
      ⟨_, List.getElem_mem hw, hb⟩
    have hvm := validA_of_mem_elts hM hm'
    refine ⟨permOfArr 64 m', (mem_grpN_iff hM).2 ⟨m', hm', rep_of_validA hvm⟩, ?_⟩
    exact (eqA_iff (rep_conjA hvm hrt) (rep_t0 h)).1 he
  · exfalso
    obtain ⟨a, ha, b, hb', c, hc, ha1, hb1, hc1, hba, hca, hcb, hcab⟩ := exists_three h4
    obtain ⟨a', ha', hra, -⟩ := exists_rep_of_mem hM (hVM ha)
    obtain ⟨b', hb'', hrb, -⟩ := exists_rep_of_mem hM (hVM hb')
    obtain ⟨c', hc', hrc, -⟩ := exists_rep_of_mem hM (hVM hc)
    have ia := mem_invCentN ha' hra hrt (hVt a ha) (hsq a ha) ha1
    have ib := mem_invCentN hb'' hrb hrt (hVt b hb') (hsq b hb') hb1
    have ic := mem_invCentN hc' hrc hrt (hVt c hc) (hsq c hc) hc1
    have key := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hb a' ia) b' ib) c' ic
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at key
    rcases key with (((((h1 | h1) | h1) | h1) | h1) | h1) | h1
    · exact absurd ((commN_iff hra hrb).2 (comm_of_sq hsq ha hb')) (by rw [h1]; decide)
    · exact absurd ((commN_iff hra hrc).2 (comm_of_sq hsq ha hc)) (by rw [h1]; decide)
    · exact absurd ((commN_iff hrb hrc).2 (comm_of_sq hsq hb' hc)) (by rw [h1]; decide)
    · exact hba ((eqA_iff hrb hra).1 h1)
    · exact hca ((eqA_iff hrc hra).1 h1)
    · exact hcb ((eqA_iff hrc hrb).1 h1)
    · exact hcab ((eqA_iff hrc (rep_mulN hra hrb)).1 h1)

theorem cent_of : hexaM ⊓ centralizer {hexaT0P} = hexaC0 := by
  obtain ⟨-, hM, hC, -, -, -, -, -, -, hCM, hCt, hlen, -⟩ := hexaCheck_parts h
  have rt := rep_t0 h
  have hle : hexaC0 ≤ hexaM ⊓ centralizer {hexaT0P} := by
    refine grpN_le fun a ha => ⟨?_, ?_⟩
    · exact mem_of_inLN hM (List.all_eq_true.1 hCM a ha) (rep_of_validA (validA_of_mem hC ha))
    · exact mem_centralizer_singleton_iff.mpr ((commN_iff (rep_of_validA (validA_of_mem hC ha))
        rt).1 (List.all_eq_true.1 hCt a ha))
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_grpN hC, ← hlen]
  refine card_le_length (S := ((hexaM ⊓ centralizer {hexaT0P} : Subgroup (Equiv.Perm (Fin 64))) :
    Set (Equiv.Perm (Fin 64)))) ?_
  rintro x ⟨hxM, hxc⟩
  obtain ⟨t, ht, hr, -⟩ := exists_rep_of_mem hM hxM
  exact ⟨t, List.mem_filter.2 ⟨ht, (commN_iff hr rt).2 (mem_centralizer_singleton_iff.mp hxc)⟩,
    hr⟩

theorem gens_of : ∀ a ∈ hexaCGens, permOfArr 64 a ^ 4 = 1 := by
  obtain ⟨-, -, hC, -, -, -, -, -, -, -, -, -, hpow, -⟩ := hexaCheck_parts h
  intro a ha
  exact eq_of_eqA (rep_powN (rep_of_validA (validA_of_mem hC ha)) 4) rep_idA
    (List.all_eq_true.1 hpow a ha)

theorem move_of : ∀ m ∈ hexaM, ∃ g ∈ hexaC0, ∃ r ∈ hexaR0,
    m⁻¹ * g * m * r * (m⁻¹ * g * m)⁻¹ ∉ hexaR0 := by
  obtain ⟨-, hM, hC, -, hR, -, -, -, -, -, -, -, -, hmv, -⟩ := hexaCheck_parts h
  intro m hm
  obtain ⟨m', hm', hrm, hvm⟩ := exists_rep_of_mem hM hm
  obtain ⟨g', hg', hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 hmv m' hm')
  obtain ⟨r', hr', hb'⟩ := List.any_eq_true.1 hb
  have hvg := validA_of_mem hC hg'
  have hvr := validA_of_mem hR hr'
  have rep1 := rep_conjInvA hvm (rep_conjA hvg (rep_conjA hvm (rep_of_validA hvr)))
  rw [permOfArr_eq_of_rep hrm] at rep1
  refine ⟨permOfArr 64 g', gen_mem_grpN hg', permOfArr 64 r', gen_mem_grpN hr', ?_⟩
  have hn := not_mem_of_inLN hR rep1 hb'
  convert hn using 1
  group

theorem normN_of : hexaC0 ≤ normalizer (hexaN0 : Set (Equiv.Perm (Fin 64))) := by
  obtain ⟨-, -, hC, hN, -, -, -, -, -, -, -, -, -, -, hnN, -⟩ := hexaCheck_parts h
  exact le_normalizer_of_all hN (fun g hg => validA_of_mem hC hg) hnN

theorem cardN_of : Nat.card hexaN0 = 8 := card_grpN (hexaCheck_parts h).2.2.2.1

theorem normalE8_of : ∀ V : Subgroup (Equiv.Perm (Fin 64)), V ≤ hexaC0 → (∀ v ∈ V, v * v = 1) →
    (∀ t ∈ hexaT, (∀ v ∈ V, t * v = v * t) → t = 1 ∨ t = hexaT0P) → V ≤ hexaN0 := by
  obtain ⟨hT, -, hC, hN, -, -, -, -, -, -, -, -, -, -, -, hne, -⟩ := hexaCheck_parts h
  have rt := rep_t0 h
  have hCt : ∀ x ∈ hexaC0, x * hexaT0P = hexaT0P * x := fun x hx => by
    have hx' : x ∈ hexaM ⊓ centralizer {hexaT0P} := (cent_of h).symm ▸ hx
    exact mem_centralizer_singleton_iff.mp hx'.2
  intro V hVC hsq hcen v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact one_mem _
  obtain ⟨a', ha', hra, -⟩ := exists_rep_of_mem hC (hVC hv)
  have ia := mem_invCentN ha' hra rt (hCt v (hVC hv)) (hsq v hv) hv1
  have hb := List.all_eq_true.1 hne a' ia
  rw [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · exact mem_of_inLN hN hb hra
  · exfalso
    obtain ⟨t', ht', hb2⟩ := List.any_eq_true.1 hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb2
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb2
    have hrt := rep_of_validA (validA_of_mem_elts hT ht')
    have hτ : permOfArr 64 t' ∈ hexaT := (mem_grpN_iff hT).2 ⟨t', ht', hrt⟩
    have hcomm : ∀ w ∈ V, permOfArr 64 t' * w = w * permOfArr 64 t' := by
      intro w hw
      by_cases hw1 : w = 1
      · rw [hw1, mul_one, one_mul]
      obtain ⟨b', hb', hrb, -⟩ := exists_rep_of_mem hC (hVC hw)
      have ib := mem_invCentN hb' hrb rt (hCt w (hVC hw)) (hsq w hw) hw1
      have hb3 := List.all_eq_true.1 h3 b' ib
      rw [Bool.or_eq_true, Bool.not_eq_true'] at hb3
      rcases hb3 with hb3 | hb3
      · exact absurd ((commN_iff hra hrb).2 (comm_of_sq hsq hv hw)) (by rw [hb3]; decide)
      · exact ((commN_iff hrb hrt).1 hb3).symm
    rcases hcen _ hτ hcomm with he | he
    · rw [(eqA_iff hrt rep_idA).2 he] at h1
      exact absurd h1 (by decide)
    · rw [(eqA_iff hrt rt).2 he] at h2
      exact absurd h2 (by decide)

theorem iso_of : Nonempty (↥hexaC0 ≃* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) := by
  obtain ⟨-, -, hC, -, -, -, -, -, -, -, -, -, -, -, -, -, hb4, hb2, hf, -⟩ := hexaCheck_parts h
  have h4 := isBlockSys_of_blockN (k := 4) hC hb4
  have h2 := isBlockSys_of_blockN (k := 2) hC hb2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : Equiv.Perm (Fin 2) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) (by rw [Nat.card_perm]; simp)
      (by rw [Nat.card_eq_fintype_card]; simp)
  let φ : ↥hexaC0 →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2) :=
    h4.hom.prod (e.toMonoidHom.comp h2.hom)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hσ' : (h4.hom σ, e (h2.hom σ)) = (1, 1) := hσ
    have hσ4 : h4.hom σ = 1 := congrArg Prod.fst hσ'
    have hσ2 : h2.hom σ = 1 := (MulEquiv.map_eq_one_iff e).1 (congrArg Prod.snd hσ')
    obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_mem hC σ.2
    have hb := List.all_eq_true.1 hf t ht
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hb
    rcases hb with (hb | hb) | hb
    · rw [all_of_hom_eq_one hC hb4 ht hrt hσ4] at hb
      exact absurd hb (by decide)
    · rw [all_of_hom_eq_one hC hb2 ht hrt hσ2] at hb
      exact absurd hb (by decide)
    · exact Subtype.ext ((eqA_iff hrt rep_idA).1 hb)
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by
    rw [card_grpN hC, Nat.card_prod, Nat.card_perm,
      Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))]
    simp [Nat.factorial])
  exact ⟨MulEquiv.ofBijective φ hbij⟩

theorem fuse_of : ∃ a ∈ hexaN0, ∃ x ∈ hexaT, a * x * a⁻¹ * x⁻¹ ≠ 1 ∧
    a * x * a⁻¹ * x⁻¹ ≠ hexaT0P ∧ ∃ m ∈ hexaM, m * (a * x * a⁻¹ * x⁻¹) * m⁻¹ = hexaT0P := by
  obtain ⟨hT, hM, -, hN, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfu⟩ :=
    hexaCheck_parts h
  have rt := rep_t0 h
  simp only [fuseW, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hfu
  obtain ⟨⟨⟨⟨⟨ia, ix⟩, im⟩, h1⟩, h2⟩, he⟩ := hfu
  rw [getElem!_pos (eltsN 64 hexaN0Gens) _ ia, getElem!_pos (eltsN 64 hexaTGens) _ ix] at h1 h2 he
  rw [getElem!_pos (eltsN 64 hexaMGens) _ im] at he
  have ha' := List.getElem_mem ia
  have hx' := List.getElem_mem ix
  have hm' := List.getElem_mem im
  have hva := validA_of_mem_elts hN ha'
  have hvx := validA_of_mem_elts hT hx'
  have hvm := validA_of_mem_elts hM hm'
  have rc := rep_commutatorA hva hvx
  rw [commutatorElement_def] at rc
  refine ⟨_, (mem_grpN_iff hN).2 ⟨_, ha', rep_of_validA hva⟩, _,
    (mem_grpN_iff hT).2 ⟨_, hx', rep_of_validA hvx⟩, fun he1 => ?_, fun he2 => ?_, _,
    (mem_grpN_iff hM).2 ⟨_, hm', rep_of_validA hvm⟩, (eqA_iff (rep_conjA hvm rc) rt).1 he⟩
  · rw [(eqA_iff rc rep_idA).2 he1] at h1
    exact absurd h1 (by decide)
  · rw [(eqA_iff rc rt).2 he2] at h2
    exact absurd h2 (by decide)

theorem hexaFacts_of : HexaFacts :=
  ⟨normT_of h, R0T_of h, orbit_of h, cent_of h, gens_of h, move_of h, normN_of h, cardN_of h,
    normalE8_of h, iso_of h, fuse_of h⟩

end Sound

theorem hexaFacts : HexaFacts := hexaFacts_of hexa_check

end CFSG.ComponentClassification.AS81.Hexa
