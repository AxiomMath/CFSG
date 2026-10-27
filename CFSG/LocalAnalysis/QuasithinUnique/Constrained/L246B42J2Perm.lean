module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Engine
public import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem j2P_le_R : j2P ≤ j2R := le_sup_left

theorem j2Gen0_eq : j2Gen 0 = permOfArr 315 j2A0A := by simp [j2Gen, j2StrongPerm, j2A0A]

theorem j2Gen1_eq : j2Gen 1 = permOfArr 315 j2A1A := by simp [j2Gen, j2StrongPerm, j2A1A]

theorem pRep_j2A0P : PRep 315 j2A0P (j2Gen 0) := by
  have h := rep_permOfArr j2_perm_check.1
  refine ⟨?_, ?_⟩
  · rw [j2Gen0_eq]
    exact h.1
  · rw [j2Gen0_eq]
    exact h.2

theorem pRep_j2A1P : PRep 315 j2A1P (j2Gen 1) := by
  have h := rep_permOfArr j2_perm_check.2.1
  refine ⟨?_, ?_⟩
  · rw [j2Gen1_eq]
    exact h.1
  · rw [j2Gen1_eq]
    exact h.2

theorem regIn_j2P : RegIn 315 j2P [j2A0P, j2A1P] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨j2Gen 0, Subgroup.subset_closure (by simp), pRep_j2A0P⟩
  · exact ⟨j2Gen 1, Subgroup.subset_closure (by simp), pRep_j2A1P⟩

theorem rep_j2A0 : Rep 315 j2A0A (j2Gen 0) := by
  have := pRep_j2A0P.1
  exact this

theorem rep_j2A1 : Rep 315 j2A1A (j2Gen 1) := by
  have := pRep_j2A1P.1
  exact this

theorem pRep_j2TP {k : ℕ} (hk : permOK 315 (j2CentTbl k) = true)
    (hsq : tp 315 (j2CentTbl k) * tp 315 (j2CentTbl k) = 1) :
    PRep 315 (j2TP k) (tp 315 (j2CentTbl k)) :=
  PRep.of_sq (rep_permOfArr hk).1 hsq

theorem pRep_j2SP {k : ℕ} (hk : permOK 315 (j2CentTbl k) = true) :
    PRep 315 (j2SP k) (tp 315 (j2CentTbl k)) :=
  rep_permOfArr hk

theorem j2S_le_R
    : j2S ≤ j2R := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.1

theorem card_j2R
    : Nat.card j2R = 1209600 :=
  ctuc_j2_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1

theorem j2_normal
    : ∀ x ∈ j2R, ∀ p ∈ j2P, x * p * x⁻¹ ∈ j2P := by
  intro x hx p hp
  have hN := ctuc_j2_normalizing_involution_permutation_model.2.2.2.2.2.2.2.1
  have := hN.conj_mem ⟨p, j2P_le_R hp⟩ (by simpa [Subgroup.mem_subgroupOf] using hp) ⟨x, hx⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem j2_normal'
    : ∀ x ∈ j2R, ∀ p ∈ j2P, x⁻¹ * p * x ∈ j2P := by
  intro x hx p hp
  have := j2_normal x⁻¹ (j2R.inv_mem hx) p hp
  simpa using this

theorem j2SylGens_mem : ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8], tp 315 (j2CentTbl k) ∈ j2S := by
  intro k hk
  refine Subgroup.subset_closure ⟨j2CentTbl k, ?_, rfl⟩
  show j2CentTbl k ∈ j2SylowGenTbls.toArray
  rw [List.mem_toArray]
  have hk' : 1 ≤ k ∧ k ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  exact List.mem_map.2 ⟨k - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel hk'.1]⟩

theorem regIn_j2SylGens
    : RegIn 315 j2R j2SylGens := by
  intro r hr
  simp only [j2SylGens, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, j2S_le_R (j2SylGens_mem 1 (by simp)), pRep_j2SP (j2_perm_check.2.2 1 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 2 (by simp)), pRep_j2SP (j2_perm_check.2.2 2 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 3 (by simp)), pRep_j2SP (j2_perm_check.2.2 3 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 4 (by simp)), pRep_j2SP (j2_perm_check.2.2 4 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 5 (by simp)), pRep_j2SP (j2_perm_check.2.2 5 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 6 (by simp)), pRep_j2SP (j2_perm_check.2.2 6 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 7 (by simp)), pRep_j2SP (j2_perm_check.2.2 7 (by simp))⟩
  · exact ⟨_, j2S_le_R (j2SylGens_mem 8 (by simp)), pRep_j2SP (j2_perm_check.2.2 8 (by simp))⟩

theorem j2_rank_R
    : ∀ B : Subgroup ↥j2R, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 :=
  sylVerify_sound (N := 256) (a := 8) (m := 4725) (by norm_num) (by rw [card_j2R]; norm_num)
    (by decide) regIn_j2SylGens j2_syl_check

theorem gen_of_check
    {t : PArr} {τ : Equiv.Perm (Fin 315)} (ht : PRep 315 t τ)
    {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} {k : ℕ} (hws : ws.length = k)
    (hc : threeConjCheck 315 [j2A0P, j2A1P] t ws prog [j2A0A, j2A1A] = true) :
    GenSet j2P k {τ} := by
  obtain ⟨gs, hlen, hgs, hmem⟩ := threeConj_sound regIn_j2P ht hc
  refine ⟨gs, hlen.trans hws, hgs, ?_⟩
  have h0 := hmem j2A0A (by simp) _ rep_j2A0
  have h1 := hmem j2A1A (by simp) _ rep_j2A1
  rw [j2P]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact h0
  · exact h1

theorem rows_cases : ∀ r ∈ j2Rows,
    r.rep = j2CentTbl 9 ∨ r.rep = j2CentTbl 17 ∨ r.rep = j2CentTbl 31 := by
  intro r hr
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (by simp))

theorem rows_sq
    : ∀ r ∈ j2Rows, tp 315 r.rep * tp 315 r.rep = 1 := by
  intro r hr
  have h2 := (ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.1 r hr).2.1
  have := pow_orderOf_eq_one (tp 315 r.rep)
  rw [h2, sq] at this
  exact this

theorem j2_gen4
    {x : Equiv.Perm (Fin 315)} (hxR : x ∈ j2R) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    GenSet j2P 4 {x} := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨r, hr, g, hg, hxg⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.1 x hxR hord
  have hsq := rows_sq r hr
  have cert : GenSet j2P 4 {tp 315 r.rep} := by
    rcases rows_cases r hr with hrep | hrep | hrep
    · rw [hrep] at hsq ⊢
      exact gen_of_check (pRep_j2TP (j2_perm_check.2.2 9 (by simp)) hsq) (by decide)
        j2_row0_check
    · rw [hrep] at hsq ⊢
      exact gen_of_check (pRep_j2TP (j2_perm_check.2.2 17 (by simp)) hsq) (by decide)
        j2_row1_check
    · rw [hrep] at hsq ⊢
      exact gen_of_check (pRep_j2TP (j2_perm_check.2.2 31 (by simp)) hsq) (by decide)
        j2_row2_check
  refine GenSet.transfer (s := g⁻¹) (fun p hp => ?_) (fun p hp => ?_) (fun t' ht' => ?_) cert
  · have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hp) hg
    simpa [mul_assoc] using this
  · have := j2P.mul_mem (j2P.mul_mem hg hp) (j2P.inv_mem hg)
    simpa [mul_assoc] using this
  · rw [Set.mem_singleton_iff] at ht'
    rw [ht', hxg]
    refine Subgroup.subset_closure ?_
    simp [mul_assoc]

structure SylModel (n N ng : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) (par lab tab : List ℕ)
    (Al : Array (Array ℕ)) (E gp : ℕ → Equiv.Perm (Fin n)) (Sy : Subgroup (Equiv.Perm (Fin n))) :
    Prop where
  rep : ∀ k < N, Rep n Al[k]! (E k)
  memH : ∀ k < N, E k ∈ H
  one : E 0 = 1
  inj : ∀ i < N, ∀ j < N, E i = E j → i = j
  step : ∀ k < N, k ≠ 0 → par.getD k 0 < k ∧ lab.getD k 0 < ng ∧
    E k = E (par.getD k 0) * gp (lab.getD k 0)
  mulgen : ∀ i < N, ∀ j < ng, tab.getD (i * ng + j) 0 < N ∧
    E (tab.getD (i * ng + j) 0) = E i * gp j
  mem_Sy : ∀ x, x ∈ Sy ↔ ∃ k < N, x = E k
  Sy_le : Sy ≤ H
  card_Sy : Nat.card Sy = N

theorem sylModel {n N : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {gens : List PArr}
    (hgens : RegIn n H gens) {par lab tab : List ℕ} {Al : Array (Array ℕ)} {r : ℕ}
    (hv : sylVerify n N gens par lab tab Al r = true) :
    ∃ (E gp : ℕ → Equiv.Perm (Fin n)) (Sy : Subgroup (Equiv.Perm (Fin n))),
      SylModel n N gens.length H par lab tab Al E gp Sy := by
  classical
  simp only [sylVerify, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨hsz, hN0⟩, h0⟩, hpar⟩, htab⟩, hinv⟩, hnd⟩, hcnt⟩ := hv
  have hgj : ∀ j : ℕ, ∃ g ∈ H, PRep n (gens.getD j (pId n)) g := fun j => hgens.getD j
  choose gp hgpH hgpRep using hgj
  set E : ℕ → Equiv.Perm (Fin n) := fun k => permOfArr n Al[k]! with hE
  have hrep : ∀ k < N, Rep n Al[k]! (E k) := fun k hk => (rep_permOfArr (hinv k hk)).1
  have hE0 : E 0 = 1 := (eqA_iff (hrep 0 hN0) rep_idA).1 h0
  have hstep : ∀ k < N, k ≠ 0 → par.getD k 0 < k ∧ lab.getD k 0 < gens.length ∧
      E k = E (par.getD k 0) * gp (lab.getD k 0) := by
    intro k hk hk0
    have h := hpar k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hp, hl⟩, he⟩
    · exact absurd h hk0
    · refine ⟨hp, hl, ?_⟩
      have hr2 : Rep n (compA n Al[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)
          (E (par.getD k 0) * gp (lab.getD k 0)) :=
        rep_compA (hrep _ (hp.trans hk)) (hgpRep _).1
      exact (eqA_iff (hrep k hk) hr2).1 he
  have htabE : ∀ i < N, ∀ j < gens.length, tab.getD (i * gens.length + j) 0 < N ∧
      E (tab.getD (i * gens.length + j) 0) = E i * gp j := by
    intro i hi j hj
    obtain ⟨hk, he⟩ := htab i hi j hj
    refine ⟨hk, ?_⟩
    have hr2 : Rep n (compA n Al[i]! (gens.getD j (pId n)).1) (E i * gp j) :=
      rep_compA (hrep i hi) (hgpRep j).1
    exact ((eqA_iff hr2 (hrep _ hk)).1 he).symm
  set rg : List (Equiv.Perm (Fin n)) := (List.range gens.length).map gp with hrg
  have hrgmem : ∀ g ∈ rg, g ∈ H := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact hgpH j
  have hEclos : ∀ k < N, E k ∈ Subgroup.closure {g | g ∈ rg} := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [hE0]
        exact Subgroup.one_mem _
      · obtain ⟨hp, hl, he⟩ := hstep k hk hk0
        rw [he]
        refine Subgroup.mul_mem _ (ih _ hp (hp.trans hk)) (Subgroup.subset_closure ?_)
        exact List.mem_map.2 ⟨_, List.mem_range.2 hl, rfl⟩
  have hEH : ∀ k < N, E k ∈ H := by
    intro k hk
    have : Subgroup.closure {g | g ∈ rg} ≤ H :=
      (Subgroup.closure_le H).2 fun g hg => hrgmem g hg
    exact this (hEclos k hk)
  have hinjE : ∀ i < N, ∀ j < N, E i = E j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h := hnd j hj i hlt
      have hEq : eqA n Al[j]! Al[i]! = true := (eqA_iff (hrep j hj) (hrep i hi)).2 hij.symm
      rw [hEq] at h
      exact absurd h (by simp)
    · have h := hnd i hi j hlt
      have hEq : eqA n Al[i]! Al[j]! = true := (eqA_iff (hrep i hi) (hrep j hj)).2 hij
      rw [hEq] at h
      exact absurd h (by simp)
  obtain ⟨Sy, hSy⟩ := exists_subgroup_of_gens rg ((List.range N).map E)
    (List.mem_map.2 ⟨0, List.mem_range.2 hN0, hE0⟩)
    (by
      intro x hx g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      obtain ⟨hk, hik⟩ := htabE i (List.mem_range.1 hi) j (List.mem_range.1 hj)
      exact List.mem_map.2 ⟨_, List.mem_range.2 hk, hik⟩)
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hEclos i (List.mem_range.1 hi))
  have hmemSy : ∀ x, x ∈ Sy ↔ ∃ k < N, x = E k := by
    intro x
    rw [hSy]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact ⟨i, List.mem_range.1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  refine ⟨E, gp, Sy, ⟨hrep, hEH, hE0, hinjE, fun k hk hk0 => hstep k hk hk0,
    fun i hi j hj => ?_, hmemSy, fun x hx => ?_, ?_⟩⟩
  · obtain ⟨hk, he⟩ := htabE i hi j hj
    exact ⟨hk, he⟩
  · obtain ⟨k, hk, rfl⟩ := (hmemSy x).1 hx
    exact hEH k hk
  · let e : Fin N → Sy := fun k => ⟨E k, (hmemSy _).2 ⟨k, k.2, rfl⟩⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b hab => ?_, fun y => ?_⟩
      · exact Fin.ext (hinjE a a.2 b b.2 (congrArg Subtype.val hab))
      · obtain ⟨k, hk, hy⟩ := (hmemSy y).1 y.2
        exact ⟨⟨k, hk⟩, Subtype.ext hy.symm⟩
    rw [← Nat.card_fin N]
    exact (Nat.card_congr (Equiv.ofBijective e he)).symm

theorem exists_conj_mem_Sy {n a m : ℕ} {H Sy B : Subgroup (Equiv.Perm (Fin n))} (hSyH : Sy ≤ H)
    (hSy : Nat.card Sy = 2 ^ a) (hH : Nat.card H = 2 ^ a * m) (hm : Odd m) (hBH : B ≤ H)
    (hB : ∀ x ∈ B, x * x = 1) : ∃ g ∈ H, ∀ x ∈ B, g * x * g⁻¹ ∈ Sy := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup ↥H := Sy.subgroupOf H with hS'
  have hS'card : Nat.card S' = 2 ^ a := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyH).toEquiv, hSy]
  have hpg : IsPGroup 2 S' := IsPGroup.of_card hS'card
  have hidx : S'.index = m := by
    have h1 := S'.card_mul_index
    rw [hS'card, hH] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hodd : ¬ 2 ∣ S'.index := by
    rw [hidx]
    intro hd
    obtain ⟨k, hk⟩ := hm
    omega
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  have hBp : IsPGroup 2 B' := by
    intro x
    refine ⟨1, ?_⟩
    have := hB (x : Equiv.Perm (Fin n)) (Subgroup.mem_subgroupOf.1 x.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H Q (hpg.toSylow hodd)
  refine ⟨(g : Equiv.Perm (Fin n)), g.2, fun x hx => ?_⟩
  have hxB : (⟨x, hBH hx⟩ : ↥H) ∈ B' := by simpa [hB', Subgroup.mem_subgroupOf] using hx
  have hxQ : (⟨x, hBH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ hxB
  have hmem : g * ⟨x, hBH hx⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 ↥H) : Set ↥H) := by
    rw [Sylow.coe_smul]
    exact ⟨⟨x, hBH hx⟩, hxQ, rfl⟩
  rw [hg] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem fourgroup_gen {G : Type*} [Group G] {A B u v : G} (hA : A * A = 1) (hB : B * B = 1)
    (huv : u ≠ v) (hu : u = A ∨ u = B ∨ u = A * B) (hv : v = A ∨ v = B ∨ v = A * B) :
    A ∈ Subgroup.closure ({u, v} : Set G) ∧ B ∈ Subgroup.closure ({u, v} : Set G) := by
  have hu' : u ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hv' : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have e1 : B = A * (A * B) := by rw [← mul_assoc, hA, one_mul]
  have e2 : A = A * B * B := by rw [mul_assoc, hB, mul_one]
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
  · exact absurd (hu.trans hv.symm) huv
  · exact ⟨by rw [← hu]; exact hu', by rw [← hv]; exact hv'⟩
  · have h1 : A ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hu]; exact hu'
    have h2 : A * B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hv]; exact hv'
    exact ⟨h1, by rw [e1]; exact Subgroup.mul_mem _ h1 h2⟩
  · exact ⟨by rw [← hv]; exact hv', by rw [← hu]; exact hu'⟩
  · exact absurd (hu.trans hv.symm) huv
  · have h1 : B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hu]; exact hu'
    have h2 : A * B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hv]; exact hv'
    exact ⟨by rw [e2]; exact Subgroup.mul_mem _ h2 h1, h1⟩
  · have h1 : A ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hv]; exact hv'
    have h2 : A * B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hu]; exact hu'
    exact ⟨h1, by rw [e1]; exact Subgroup.mul_mem _ h1 h2⟩
  · have h1 : B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hv]; exact hv'
    have h2 : A * B ∈ Subgroup.closure ({u, v} : Set G) := by rw [← hu]; exact hu'
    exact ⟨by rw [e2]; exact Subgroup.mul_mem _ h2 h1, h1⟩
  · exact absurd (hu.trans hv.symm) huv

theorem conj_mem_closure_pair {G : Type*} [Group G] {A u v x y s : G}
    (hA : A ∈ Subgroup.closure ({u, v} : Set G)) (hx : s⁻¹ * u * s = x) (hy : s⁻¹ * v * s = y) :
    s⁻¹ * A * s ∈ Subgroup.closure ({x, y} : Set G) := by
  have h1 : s⁻¹ * A * s ∈ (Subgroup.closure ({u, v} : Set G)).map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨A, hA, by simp⟩
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨t, ht, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · left
    show s⁻¹ * t * s⁻¹⁻¹ = x
    rw [inv_inv]
    exact hx
  · right
    show s⁻¹ * t * s⁻¹⁻¹ = y
    rw [inv_inv]
    exact hy

theorem genset_pair_conj
    {A B x y s : Equiv.Perm (Fin 315)} (hs : s ∈ j2R) (hA : A * A = 1)
    (hB : B * B = 1) (hne : s * x * s⁻¹ ≠ s * y * s⁻¹)
    (hu : s * x * s⁻¹ = A ∨ s * x * s⁻¹ = B ∨ s * x * s⁻¹ = A * B)
    (hv : s * y * s⁻¹ = A ∨ s * y * s⁻¹ = B ∨ s * y * s⁻¹ = A * B)
    (hg : GenSet j2P 2 {A, B}) : GenSet j2P 2 {x, y} := by
  obtain ⟨hAu, hBu⟩ := fourgroup_gen hA hB hne hu hv
  refine GenSet.transfer (s := s) (j2_normal s hs) (j2_normal' s hs) (fun t' ht' => ?_) hg
  have hx : s⁻¹ * (s * x * s⁻¹) * s = x := by group
  have hy : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  rcases ht' with rfl | rfl
  · exact conj_mem_closure_pair hAu hx hy
  · exact conj_mem_closure_pair hBu hx hy

section Triple

variable {E gp : ℕ → Equiv.Perm (Fin 315)} {Sy : Subgroup (Equiv.Perm (Fin 315))}

theorem j2_mul_spec
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy) :
    ∀ j < 256, ∀ i < 256, j2Mul i j < 256 ∧ E (j2Mul i j) = E i * E j := by
  have h := j2_idx_check.1
  simp only [j2MulOK, allLt_iff, Bool.and_eq_true, decide_eq_true_eq] at h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hi
    obtain ⟨hlt, hrec⟩ := h i hi j hj
    refine ⟨hlt, ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      simp only [ite_true, beq_iff_eq] at hrec
      rw [hrec, hM.one, mul_one]
    · simp only [hj0, ite_false, beq_iff_eq] at hrec
      obtain ⟨hpar, hlab, hEj⟩ := hM.step j hj hj0
      have hp := ih (j2Par.getD j 0) hpar (hpar.trans hj) i hi
      obtain ⟨-, hEt⟩ := hM.mulgen (j2Mul i (j2Par.getD j 0)) hp.1 (j2Lab.getD j 0) hlab
      rw [hrec, hEt, hp.2, hEj, mul_assoc]

theorem j2_mul_spec'
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy) :
    ∀ i < 256, ∀ j < 256, j2Mul i j < 256 ∧ E (j2Mul i j) = E i * E j :=
  fun i hi j hj => j2_mul_spec hM j hj i hi

theorem j2_inv_spec
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy) :
    ∀ s < 256, j2Inv s < 256 ∧ E (j2Inv s) = (E s)⁻¹ := by
  have h := j2_idx_check.2.1
  simp only [j2InvOK, allLt_iff, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  intro s hs
  obtain ⟨hlt, h0⟩ := h s hs
  refine ⟨hlt, ?_⟩
  have h1 := (j2_mul_spec' hM s hs _ hlt).2
  rw [h0, hM.one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem j2_reps_spec : ∀ ab ∈ j2Reps, ab.1 < 256 ∧ ab.2 < 256 := by
  have h := j2_idx_check.2.2.1
  simp only [j2RepsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  intro ab hab
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h ab hab
  exact ⟨h1, h2⟩

theorem j2_sq_of_isInv
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy) {k : ℕ}
    (hk : k < 256) (hi : isInvF j2Mul k = true) : E k * E k = 1 := by
  obtain ⟨-, h0⟩ := isInvF_iff.1 hi
  have := (j2_mul_spec' hM k hk k hk).2
  rw [h0, hM.one] at this
  exact this.symm

theorem j2_pair_genset
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    {e : ℕ × ℕ × List (List ℤ) × List (ℤ × ℤ)} (he : e ∈ j2PairData) :
    GenSet j2P 2 {E e.1, E e.2.1} := by
  have hcert := List.all_eq_true.1 j2_pair_check e he
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨hlen, hc⟩ := hcert
  have hrep : (e.1, e.2.1) ∈ j2Reps := List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨ha, hb⟩ := j2_reps_spec _ hrep
  have hall := j2_idx_check.2.2.1
  simp only [j2RepsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨-, hia⟩, hib⟩ := hall _ hrep
  have hsqa : E e.1 * E e.1 = 1 := j2_sq_of_isInv hM ha hia
  have hsqb : E e.2.1 * E e.2.1 = 1 := j2_sq_of_isInv hM hb hib
  have hts : ∀ t ∈ [(j2Al[e.1]!, j2Al[e.1]!), (j2Al[e.2.1]!, j2Al[e.2.1]!)],
      ∃ τ ∈ ({E e.1, E e.2.1} : Set (Equiv.Perm (Fin 315))), PRep 315 t τ := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨E e.1, by simp, PRep.of_sq (hM.rep _ ha) hsqa⟩
    · exact ⟨E e.2.1, by simp, PRep.of_sq (hM.rep _ hb) hsqb⟩
  obtain ⟨gs, hgl, hgs, hmem⟩ := multiConj_sound regIn_j2P hts hc
  refine ⟨gs, hgl.trans hlen, hgs, ?_⟩
  have h0 := hmem j2A0A (by simp) _ rep_j2A0
  have h1 := hmem j2A1A (by simp) _ rep_j2A1
  rw [j2P]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact h0
  · exact h1

theorem j2_good_genset
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    (hSyR : Sy ≤ j2R) {i j : ℕ} (hi : i < 256) (hj : j < 256) (hg : j2Good i j = true) :
    GenSet j2P 2 {E i, E j} := by
  have h1 : goodPairF 256 j2Mul j2Inv j2Reps i j = true :=
    goodTblF_spec (N := 256) (mulF := j2Mul) (invF := j2Inv) (reps := j2Reps) hi hj hg
  obtain ⟨ab, hab, s, hs, hne, hu, hv⟩ := goodPairF_spec (j2_mul_spec' hM) (j2_inv_spec hM)
    (fun a ha b hb hab => hM.inj a ha b hb hab) j2_reps_spec hi hj h1
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hab
  have hrep : (e.1, e.2.1) ∈ j2Reps := List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨ha, hb⟩ := j2_reps_spec _ hrep
  have hall := j2_idx_check.2.2.1
  simp only [j2RepsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨-, hia⟩, hib⟩ := hall _ hrep
  have hsR : E s ∈ j2R := hSyR ((hM.mem_Sy _).2 ⟨s, hs, rfl⟩)
  exact genset_pair_conj hsR (j2_sq_of_isInv hM ha hia) (j2_sq_of_isInv hM hb hib) hne hu hv
    (j2_pair_genset hM he)

theorem j2_triple
    (hM : SylModel 315 256 8 j2R j2Par j2Lab j2Tab j2Al E gp Sy)
    {x y z : Equiv.Perm (Fin 315)} (hl : IndepList [x, y, z]) (hx : x ∈ Sy) (hy : y ∈ Sy)
    (hz : z ∈ Sy) :
    GenSet j2P 2 {x, y} ∨ GenSet j2P 2 {x, z} ∨ GenSet j2P 2 {y, z} := by
  obtain ⟨i, hi, rfl⟩ := (hM.mem_Sy x).1 hx
  obtain ⟨j, hj, rfl⟩ := (hM.mem_Sy y).1 hy
  obtain ⟨k, hk, rfl⟩ := (hM.mem_Sy z).1 hz
  obtain ⟨hx2, hy2, hz2, hx1, hy1, hz1, hxy, hxz, hyz, hne1, hne2, hne3, hne4⟩ :=
    indepList_three hl
  have hmul := j2_mul_spec' hM
  have hinj := hM.inj
  have hinv : ∀ {m : ℕ}, m < 256 → E m * E m = 1 → E m ≠ 1 → isInvF j2Mul m = true := by
    intro m hm hsq hne
    rw [isInvF_iff]
    refine ⟨fun h0 => hne (by rw [h0, hM.one]), ?_⟩
    apply hinj _ (hmul m hm m hm).1 0 (by norm_num)
    rw [(hmul m hm m hm).2, hsq, hM.one]
  have hcomm : ∀ {a b : ℕ}, a < 256 → b < 256 → E a * E b = E b * E a →
      j2Mul a b = j2Mul b a := by
    intro a b ha hb h
    apply hinj _ (hmul a ha b hb).1 _ (hmul b hb a ha).1
    rw [(hmul a ha b hb).2, (hmul b hb a ha).2, h]
  have key := tripleOKF_spec (good := j2Good) j2_idx_check.2.2.2 hi hj hk (hinv hi hx2 hx1)
    (hinv hj hy2 hy1) (hinv hk hz2 hz1) (fun h => hne1 (by rw [h])) (fun h => hne2 (by rw [h]))
    (fun h => hne3 (by rw [h, (hmul j hj k hk).2])) (fun h => hne4 (by rw [h]))
    (hcomm hi hj hxy) (hcomm hi hk hxz) (hcomm hj hk hyz)
  have hSyR : Sy ≤ j2R := hM.Sy_le
  rcases key with h | h | h
  · exact Or.inl (j2_good_genset hM hSyR hi hj h)
  · exact Or.inr (Or.inl (j2_good_genset hM hSyR hi hk h))
  · exact Or.inr (Or.inr (j2_good_genset hM hSyR hj hk h))

end Triple

theorem j2_genSub_R
    : ∀ B : Subgroup (Equiv.Perm (Fin 315)), B ≤ j2R →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → B ≠ ⊥ →
    ∃ gs : List (Equiv.Perm (Fin 315)), (∀ g ∈ gs, g ∈ j2P) ∧ Nat.card B ^ gs.length < 2 ^ 12 ∧
      j2P ≤ Subgroup.closure {y | ∃ c ∈ gs, ∃ b ∈ B, y = c * b * c⁻¹} := by
  intro B hBR hcomm hsq hne
  obtain ⟨E, gp, Sy, hM⟩ := sylModel regIn_j2SylGens j2_syl_check
  have hrank : Nat.card B ≤ 2 ^ 4 := by
    have := j2_rank_R (B.subgroupOf j2R) (fun x hx y hy => Subtype.ext (hcomm _ hx _ hy))
      (fun x hx => Subtype.ext (hsq _ hx))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR).toEquiv] at this
  by_cases h8 : 8 ≤ Nat.card B
  · obtain ⟨g, hgR, hg⟩ := exists_conj_mem_Sy (a := 8) (m := 4725) hM.Sy_le
      (by rw [hM.card_Sy]; norm_num) (by rw [card_j2R]; norm_num) (by decide) hBR hsq
    set B' : Subgroup (Equiv.Perm (Fin 315)) := B.map (MulAut.conj g).toMonoidHom with hB'
    have hB'Sy : ∀ x ∈ B', x ∈ Sy := by
      rintro _ ⟨b, hb, rfl⟩
      exact hg b hb
    have hB'comm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
      calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
        _ = _ := by group
    have hB'sq : ∀ x ∈ B', x * x = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      show g * a * g⁻¹ * (g * a * g⁻¹) = 1
      calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [hsq a ha]; group
    have hB'card : Nat.card B' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    obtain ⟨l, hl, hlen, hlB⟩ :=
      exists_indepList_of_lt_card B' hB'comm hB'sq 2 (by rw [hB'card]; omega)
    obtain ⟨x, y, z, rfl⟩ : ∃ x y z, l = [x, y, z] := by
      match l, hlen with
      | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
    have hxB : x ∈ B' := hlB x (by simp)
    have hyB : y ∈ B' := hlB y (by simp)
    have hzB : z ∈ B' := hlB z (by simp)
    have hpair : ∃ u ∈ B', ∃ v ∈ B', GenSet j2P 2 {u, v} := by
      rcases j2_triple hM hl (hB'Sy _ hxB) (hB'Sy _ hyB) (hB'Sy _ hzB) with h | h | h
      · exact ⟨x, hxB, y, hyB, h⟩
      · exact ⟨x, hxB, z, hzB, h⟩
      · exact ⟨y, hyB, z, hzB, h⟩
    obtain ⟨u, hu, v, hv, hgen⟩ := hpair
    have hback : GenSet j2P 2 (B : Set (Equiv.Perm (Fin 315))) := by
      refine GenSet.transfer (s := g) (j2_normal g hgR) (j2_normal' g hgR) (fun t' ht' => ?_) hgen
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
      rcases ht' with rfl | rfl
      · obtain ⟨b, hb, rfl⟩ := hu
        refine Subgroup.subset_closure ?_
        have : g⁻¹ * (g * b * g⁻¹) * g = b := by group
        simpa [MulAut.conj_apply, this] using hb
      · obtain ⟨b, hb, rfl⟩ := hv
        refine Subgroup.subset_closure ?_
        have : g⁻¹ * (g * b * g⁻¹) * g = b := by group
        simpa [MulAut.conj_apply, this] using hb
    obtain ⟨gs, hgl, hgs, hle⟩ := hback
    refine ⟨gs, hgs, ?_, hle⟩
    rw [hgl]
    calc Nat.card B ^ 2 ≤ (2 ^ 4) ^ 2 := Nat.pow_le_pow_left hrank 2
      _ < 2 ^ 12 := by norm_num
  · push Not at h8
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hb2 : b ^ 2 = 1 := by rw [sq]; exact hsq b hbB
    have hgen := GenSet.mono (T := (B : Set (Equiv.Perm (Fin 315)))) (fun t ht => by
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact Subgroup.subset_closure hbB) (j2_gen4 (hBR hbB) hb2 hb1')
    obtain ⟨gs, hgl, hgs, hle⟩ := hgen
    refine ⟨gs, hgs, ?_, hle⟩
    rw [hgl]
    calc Nat.card B ^ 4 ≤ 7 ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ < 2 ^ 12 := by norm_num

end CFSG.QuasithinUnique.Bridge.J2Excl
