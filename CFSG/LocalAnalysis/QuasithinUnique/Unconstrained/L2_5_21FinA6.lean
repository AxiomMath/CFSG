module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinDS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport

public section

namespace CFSG.QuasithinUnique.Out21.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def m10Reps : List P10 := [1, A6Models.tMulFrob]

@[expose] def pglReps : List P10 := [1, A6Models.tMul]

@[expose] def m10Gens : List P10 := [A6Models.tAdd, A6Models.tSq, A6Models.tInv, A6Models.tMulFrob]

@[expose] def pglGens : List P10 := [A6Models.tAdd, A6Models.tSq, A6Models.tInv, A6Models.tMul]

theorem m10_eq : A6Models.m10 = Subgroup.closure {g | g ∈ m10Gens} := by
  unfold A6Models.m10 m10Gens
  congr 1
  ext g
  simp

theorem pgl29_eq : A6Models.pgl29 = Subgroup.closure {g | g ∈ pglGens} := by
  unfold A6Models.pgl29 pglGens
  congr 1
  ext g
  simp

theorem tMulFrob_eq : A6Models.tMulFrob = A6Models.tMul * A6Models.tFrob := by decide

theorem tMul_mem_autA6 : A6Models.tMul ∈ A6Models.autA6 := by
  rw [autA6_eq]
  exact Subgroup.subset_closure (by simp [autGens])

theorem tFrob_mem_autA6 : A6Models.tFrob ∈ A6Models.autA6 := by
  rw [autA6_eq]
  exact Subgroup.subset_closure (by simp [autGens])

theorem tMulFrob_mem_autA6 : A6Models.tMulFrob ∈ A6Models.autA6 := by
  rw [tMulFrob_eq]
  exact Subgroup.mul_mem _ tMul_mem_autA6 tFrob_mem_autA6

theorem tAdd_mem_psl29 : A6Models.tAdd ∈ A6Models.psl29 := by
  rw [psl29_eq]; exact Subgroup.subset_closure (by simp [pslGens])

theorem tSq_mem_psl29 : A6Models.tSq ∈ A6Models.psl29 := by
  rw [psl29_eq]; exact Subgroup.subset_closure (by simp [pslGens])

theorem tInv_mem_psl29 : A6Models.tInv ∈ A6Models.psl29 := by
  rw [psl29_eq]; exact Subgroup.subset_closure (by simp [pslGens])

theorem tMulFrob_sq_mem : A6Models.tMulFrob * A6Models.tMulFrob ∈ A6Models.psl29 := by
  rw [mem_psl29_iff, code_mul]
  have : Core.pslLit.contains (Core.cmul (code A6Models.tMulFrob) (code A6Models.tMulFrob)) = true := by
    decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem tMul_sq_mem : A6Models.tMul * A6Models.tMul ∈ A6Models.psl29 := by
  rw [mem_psl29_iff, code_mul]
  have : Core.pslLit.contains (Core.cmul (code A6Models.tMul) (code A6Models.tMul)) = true := by
    decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem tMulFrob_not_mem_psl29 : A6Models.tMulFrob ∉ A6Models.psl29 := by
  rw [mem_psl29_iff]
  have : Core.pslLit.contains (code A6Models.tMulFrob) = false := by decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem tMul_not_mem_psl29 : A6Models.tMul ∉ A6Models.psl29 := by
  rw [mem_psl29_iff]
  have : Core.pslLit.contains (code A6Models.tMul) = false := by decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem mem_closure_psl_cosets {t : P10} (ht : t ∈ A6Models.autA6)
    (ht2 : t * t ∈ A6Models.psl29) (gens : List P10)
    (hgens : ∀ g ∈ gens, g ∈ A6Models.psl29 ∨ g = t) (hsub : ∀ g ∈ pslGens, g ∈ gens)
    (htg : t ∈ gens) (x : P10) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔ ∃ r ∈ [1, t], x * r⁻¹ ∈ A6Models.psl29 := by
  refine mem_closure_iff_of_cosets (N := A6Models.psl29) ?_ ?_ (by simp) ?_ x
  · rw [psl29_eq]
    exact Subgroup.closure_mono fun g hg => hsub g hg
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure htg
  · intro r hr g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hrA : r ∈ A6Models.autA6 := by
      rcases hr with rfl | rfl
      · exact Subgroup.one_mem _
      · exact ht
    rcases hgens g hg with hgp | rfl
    · refine ⟨r, by simpa using hr, ?_⟩
      have := psl29_normal r hrA g hgp
      simpa [mul_assoc] using this
    · rcases hr with rfl | rfl
      · exact ⟨g, by simp, by simp⟩
      · exact ⟨1, by simp, by simpa using ht2⟩

theorem mem_m10_iff (x : P10) :
    x ∈ A6Models.m10 ↔ ∃ r ∈ m10Reps, x * r⁻¹ ∈ A6Models.psl29 := by
  rw [m10_eq]
  exact mem_closure_psl_cosets tMulFrob_mem_autA6 tMulFrob_sq_mem m10Gens
    (by intro g hg
        simp only [m10Gens, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inl tAdd_mem_psl29
        · exact Or.inl tSq_mem_psl29
        · exact Or.inl tInv_mem_psl29
        · exact Or.inr rfl)
    (by intro g hg
        simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false] at hg
        simp only [m10Gens, List.mem_cons, List.not_mem_nil, or_false]
        rcases hg with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h)))
    (by simp [m10Gens]) x

theorem mem_pgl29_iff (x : P10) :
    x ∈ A6Models.pgl29 ↔ ∃ r ∈ pglReps, x * r⁻¹ ∈ A6Models.psl29 := by
  rw [pgl29_eq]
  exact mem_closure_psl_cosets tMul_mem_autA6 tMul_sq_mem pglGens
    (by intro g hg
        simp only [pglGens, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inl tAdd_mem_psl29
        · exact Or.inl tSq_mem_psl29
        · exact Or.inl tInv_mem_psl29
        · exact Or.inr rfl)
    (by intro g hg
        simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false] at hg
        simp only [pglGens, List.mem_cons, List.not_mem_nil, or_false]
        rcases hg with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h)))
    (by simp [pglGens]) x

@[expose] def cosetList (tC : List ℕ) : List (List ℕ) :=
  Core.pslLit ++ Core.pslLit.map fun c => Core.cmul c tC

theorem length_cosetList (tC : List ℕ) : (cosetList tC).length = 720 := by
  unfold cosetList
  rw [List.length_append, List.length_map, Core.psl_length]

theorem card_le_of_cosets {X : Subgroup P10} {t : P10}
    (hX : ∀ x ∈ X, ∃ r ∈ [(1 : P10), t], x * r⁻¹ ∈ A6Models.psl29) : Nat.card X ≤ 720 := by
  have himg : code '' (X : Set P10) ⊆ ↑(cosetList (code t)).toFinset := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hxr⟩ := hX x hx
    have hy := (mem_psl29_iff _).mp hxr
    simp only [Finset.mem_coe, List.mem_toFinset, cosetList, List.mem_append, List.mem_map]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1
    · left
      subst h1
      simpa using hy
    · right
      refine ⟨code (x * r⁻¹), hy, ?_⟩
      subst h1
      rw [← code_mul]
      congr 1
      group
  calc Nat.card X = Nat.card (code '' (X : Set P10)) :=
        (Nat.card_image_of_injective code_injective _).symm
    _ ≤ Nat.card ↥(↑(cosetList (code t)).toFinset : Set (List ℕ)) :=
        Nat.card_mono (Set.toFinite _) himg
    _ = (cosetList (code t)).toFinset.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ (cosetList (code t)).length := List.toFinset_card_le _
    _ = 720 := length_cosetList _

theorem psl29_le_m10 : A6Models.psl29 ≤ A6Models.m10 := by
  rw [psl29_eq, m10_eq]
  exact Subgroup.closure_mono fun g hg => by
    have hg' : g ∈ pslGens := hg
    show g ∈ m10Gens
    simp only [pslGens, m10Gens, List.mem_cons, List.not_mem_nil, or_false] at hg' ⊢
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem psl29_le_pgl29 : A6Models.psl29 ≤ A6Models.pgl29 := by
  rw [psl29_eq, pgl29_eq]
  exact Subgroup.closure_mono fun g hg => by
    have hg' : g ∈ pslGens := hg
    show g ∈ pglGens
    simp only [pslGens, pglGens, List.mem_cons, List.not_mem_nil, or_false] at hg' ⊢
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem tMulFrob_mem_m10 : A6Models.tMulFrob ∈ A6Models.m10 := by
  rw [m10_eq]; exact Subgroup.subset_closure (by simp [m10Gens])

theorem tMul_mem_pgl29 : A6Models.tMul ∈ A6Models.pgl29 := by
  rw [pgl29_eq]; exact Subgroup.subset_closure (by simp [pglGens])

theorem card_m10 : Nat.card ↥A6Models.m10 = 720 := by
  have hle : Nat.card ↥A6Models.m10 ≤ 720 := card_le_of_cosets fun x hx => (mem_m10_iff x).mp hx
  have hdvd : 360 ∣ Nat.card ↥A6Models.m10 := by
    rw [← card_psl29]; exact Subgroup.card_dvd_of_le psl29_le_m10
  have hne : Nat.card ↥A6Models.m10 ≠ 360 := by
    intro h
    have : A6Models.psl29 = A6Models.m10 :=
      Subgroup.eq_of_le_of_card_ge psl29_le_m10 (by rw [h, card_psl29])
    exact tMulFrob_not_mem_psl29 (this ▸ tMulFrob_mem_m10)
  have hpos : 0 < Nat.card ↥A6Models.m10 := Nat.card_pos
  omega

theorem card_pgl29 : Nat.card ↥A6Models.pgl29 = 720 := by
  have hle : Nat.card ↥A6Models.pgl29 ≤ 720 := card_le_of_cosets fun x hx => (mem_pgl29_iff x).mp hx
  have hdvd : 360 ∣ Nat.card ↥A6Models.pgl29 := by
    rw [← card_psl29]; exact Subgroup.card_dvd_of_le psl29_le_pgl29
  have hne : Nat.card ↥A6Models.pgl29 ≠ 360 := by
    intro h
    have : A6Models.psl29 = A6Models.pgl29 :=
      Subgroup.eq_of_le_of_card_ge psl29_le_pgl29 (by rw [h, card_psl29])
    exact tMul_not_mem_psl29 (this ▸ tMul_mem_pgl29)
  have hpos : 0 < Nat.card ↥A6Models.pgl29 := Nat.card_pos
  omega

theorem m10_involution_mem_psl29 {x : P10} (hx : x ∈ A6Models.m10) (hx2 : x * x = 1) :
    x ∈ A6Models.psl29 := by
  obtain ⟨r, hr, hxr⟩ := (mem_m10_iff x).mp hx
  simp only [m10Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa using hxr
  · exfalso
    have hy := (mem_psl29_iff _).mp hxr
    have hxe : x = (x * A6Models.tMulFrob⁻¹) * A6Models.tMulFrob := by group
    have hcheck : Core.pslLit.all (fun c =>
        Core.cmul (Core.cmul c (code A6Models.tMulFrob)) (Core.cmul c (code A6Models.tMulFrob)) !=
          Core.cid) = true := by decide +kernel
    rw [List.all_eq_true] at hcheck
    have h1 := hcheck _ hy
    have hcx : code x = Core.cmul (code (x * A6Models.tMulFrob⁻¹)) (code A6Models.tMulFrob) := by
      rw [← code_mul, ← hxe]
    have h2 : Core.cmul (code x) (code x) = Core.cid := by
      rw [← code_mul, hx2, code_one]
    rw [hcx] at h2
    simp [h2] at h1

theorem pgl29_le_autA6 : A6Models.pgl29 ≤ A6Models.autA6 := by
  rw [pgl29_eq, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ pglGens := hg
  simp only [pglGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl
  · exact psl29_le_autA6 tAdd_mem_psl29
  · exact psl29_le_autA6 tSq_mem_psl29
  · exact psl29_le_autA6 tInv_mem_psl29
  · exact tMul_mem_autA6

theorem card_psl29_centralizer_pgl29 {y : P10} (hy : y ∈ A6Models.pgl29) (hy2 : y * y = 1)
    (hypsl : y ∉ A6Models.psl29) :
    Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({y} : Set P10)) = 10 := by
  have hne : y ≠ 1 := fun h => hypsl (h ▸ Subgroup.one_mem _)
  have hs6 : y ∉ s6 := by
    intro hs
    obtain ⟨r', hr', hyr'⟩ := (mem_s6_iff_exists y).mp hs
    obtain ⟨r, hr, hyr⟩ := (mem_pgl29_iff y).mp hy
    simp only [s6RepsP, List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [pglReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr' with rfl | rfl
    · exact hypsl (by simpa using hyr')
    · rcases hr with rfl | rfl
      · exact hypsl (by simpa using hyr)
      · have h3 : A6Models.tMul * A6Models.tFrob⁻¹ ∈ A6Models.psl29 := by
          have := A6Models.psl29.mul_mem (A6Models.psl29.inv_mem hyr) hyr'
          simpa [mul_assoc] using this
        have hnot : A6Models.tMul * A6Models.tFrob⁻¹ ∉ A6Models.psl29 := by
          rw [mem_psl29_iff, code_mul]
          have : Core.pslLit.contains
              (Core.cmul (code A6Models.tMul) (code A6Models.tFrob⁻¹)) = false := by decide +kernel
          simpa [List.contains_eq_any_beq] using this
        exact hnot h3
  exact card_psl29_centralizer_of_not_mem (pgl29_le_autA6 hy) hy2 hne hypsl hs6

@[expose] def m10RepsInvC : List (List ℕ) := (m10Reps.map (·⁻¹)).map code

@[expose] def pglRepsInvC : List (List ℕ) := (pglReps.map (·⁻¹)).map code

@[expose] def inM10C (c : List ℕ) : Bool :=
  m10RepsInvC.any fun rinv => Core.pslLit.contains (Core.cmul c rinv)

@[expose] def inPglC (c : List ℕ) : Bool :=
  pglRepsInvC.any fun rinv => Core.pslLit.contains (Core.cmul c rinv)

theorem mem_m10_iff_code (x : P10) : x ∈ A6Models.m10 ↔ inM10C (code x) = true := by
  rw [mem_m10_iff, inM10C, List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hxr⟩
    refine ⟨code r⁻¹, ?_, ?_⟩
    · unfold m10RepsInvC
      exact List.mem_map_of_mem (List.mem_map_of_mem hr)
    · rw [← code_mul]
      simpa [List.contains_eq_any_beq, mem_psl29_iff] using (mem_psl29_iff _).1 hxr
  · rintro ⟨rinv, hrinv, hmem⟩
    unfold m10RepsInvC at hrinv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
    refine ⟨r', hr', ?_⟩
    rw [mem_psl29_iff, code_mul]
    simpa [List.contains_eq_any_beq] using hmem

theorem mem_pgl29_iff_code (x : P10) : x ∈ A6Models.pgl29 ↔ inPglC (code x) = true := by
  rw [mem_pgl29_iff, inPglC, List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hxr⟩
    refine ⟨code r⁻¹, ?_, ?_⟩
    · unfold pglRepsInvC
      exact List.mem_map_of_mem (List.mem_map_of_mem hr)
    · rw [← code_mul]
      simpa [List.contains_eq_any_beq, mem_psl29_iff] using (mem_psl29_iff _).1 hxr
  · rintro ⟨rinv, hrinv, hmem⟩
    unfold pglRepsInvC at hrinv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
    refine ⟨r', hr', ?_⟩
    rw [mem_psl29_iff, code_mul]
    simpa [List.contains_eq_any_beq] using hmem

@[expose] def qmL : List (List ℕ) := Core.p0Lit.filter inM10C

@[expose] def qpL : List (List ℕ) := Core.p0Lit.filter inPglC

theorem mem_Qm_iff (x : P10) : x ∈ P0 ⊓ A6Models.m10 ↔ code x ∈ qmL := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_m10_iff_code, qmL, List.mem_filter]

theorem mem_Qp_iff (x : P10) : x ∈ P0 ⊓ A6Models.pgl29 ↔ code x ∈ qpL := by
  rw [Subgroup.mem_inf, mem_P0_iff, mem_pgl29_iff_code, qpL, List.mem_filter]

theorem surj_Qm : ∀ c ∈ qmL, ∃ x ∈ P0 ⊓ A6Models.m10, code x = c := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := exists_P0_of_code (List.mem_filter.mp hc).1
  exact ⟨x, (mem_Qm_iff x).mpr hc, rfl⟩

theorem surj_Qp : ∀ c ∈ qpL, ∃ x ∈ P0 ⊓ A6Models.pgl29, code x = c := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := exists_P0_of_code (List.mem_filter.mp hc).1
  exact ⟨x, (mem_Qp_iff x).mpr hc, rfl⟩

theorem qmL_nodup : qmL.Nodup := Core.p0_nodup.filter _

theorem qpL_nodup : qpL.Nodup := Core.p0_nodup.filter _

theorem qmL_length : qmL.length = 16 := by decide +kernel

theorem qpL_length : qpL.length = 16 := by decide +kernel

theorem card_Qm : Nat.card ↥(P0 ⊓ A6Models.m10) = 16 :=
  (card_eq_of_code_mem qmL_nodup mem_Qm_iff surj_Qm).trans qmL_length

theorem card_Qp : Nat.card ↥(P0 ⊓ A6Models.pgl29) = 16 :=
  (card_eq_of_code_mem qpL_nodup mem_Qp_iff surj_Qp).trans qpL_length

theorem factorization_720 : (720 : ℕ).factorization 2 = 4 := by norm_num [Nat.factorization]

theorem isSylowTwoOf_Qm : IsSylowTwoOf (P0 ⊓ A6Models.m10) A6Models.m10 := by
  refine isSylowTwoOf_of_card_eq inf_le_right (IsPGroup.of_card (n := 4) (by rw [card_Qm]; norm_num)) ?_
  rw [card_Qm, twoPart, card_m10, factorization_720]
  norm_num

theorem isSylowTwoOf_Qp : IsSylowTwoOf (P0 ⊓ A6Models.pgl29) A6Models.pgl29 := by
  refine isSylowTwoOf_of_card_eq inf_le_right (IsPGroup.of_card (n := 4) (by rw [card_Qp]; norm_num)) ?_
  rw [card_Qp, twoPart, card_pgl29, factorization_720]
  norm_num

theorem dsData_of_codes {Q : Subgroup P10} {qL : List (List ℕ)} (hnd : qL.Nodup)
    (hmem : ∀ x : P10, x ∈ Q ↔ code x ∈ qL) (hsurj : ∀ c ∈ qL, ∃ x ∈ Q, code x = c)
    (hlen : qL.length = 16) {a : P10} (haQ : a ∈ Q) (ha4 : a ^ 4 ≠ 1) (ha8 : a ^ 8 = 1)
    (hcent : qL.all (fun c => (List.range 8).any (fun k => c == Core.cpow (code a) k) ||
      (List.range 8).all (fun k => !(Core.cmul c (Core.cpow (code a) k) ==
        Core.cmul (Core.cpow (code a) k) c) ||
        Core.cmul (Core.cpow (code a) k) (Core.cpow (code a) k) == Core.cid)) = true) :
    ∃ R : Subgroup ↥Q, DS.DSData R := by
  have hcardQ : Nat.card ↥Q = 16 := (card_eq_of_code_mem hnd hmem hsurj).trans hlen
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf a = 8 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := a) (by simpa using ha4) (by simpa using ha8)
    simpa using h
  have hRle : Subgroup.zpowers a ≤ Q := (Subgroup.zpowers_le).mpr haQ
  have hRcard : Nat.card ↥((Subgroup.zpowers a).subgroupOf Q) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv, Nat.card_zpowers, horder]
  have hidx : ((Subgroup.zpowers a).subgroupOf Q).index = 2 := by
    have h := Subgroup.card_mul_index ((Subgroup.zpowers a).subgroupOf Q)
    rw [hRcard, hcardQ] at h
    omega
  refine ⟨(Subgroup.zpowers a).subgroupOf Q, ?_, ?_, hidx, by rw [hRcard]; norm_num, ?_⟩
  · exact IsPGroup.of_card (n := 4) (by rw [hcardQ]; norm_num)
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hRle)).mpr inferInstance
  · intro g hg r hr hgr
    have hgz : (g : P10) ∉ Subgroup.zpowers a := fun h => hg (Subgroup.mem_subgroupOf.mpr h)
    have hrz : (r : P10) ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.mp hr
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrz
    have hk' : (r : P10) = a ^ (k % 8).toNat := by
      have h1 : a ^ (k % (orderOf a : ℤ)) = a ^ k := zpow_mod_orderOf a k
      rw [horder] at h1
      have h2 : (0 : ℤ) ≤ k % 8 := Int.emod_nonneg _ (by norm_num)
      have h3 : a ^ k = a ^ ((k % 8).toNat : ℤ) := by
        rw [← h1]; congr 1; omega
      rw [← hk, h3, zpow_natCast]
    have hk8 : (k % 8).toNat < 8 := by omega
    have hgc := (List.all_eq_true.mp hcent) (code g) ((hmem g).mp g.2)
    rw [Bool.or_eq_true] at hgc
    rcases hgc with h1 | h1
    · exfalso
      obtain ⟨j, hj, hjc⟩ := List.any_eq_true.mp h1
      simp only [beq_iff_eq, List.mem_range] at hjc hj
      apply hgz
      have : (g : P10) = a ^ j := code_injective (by rw [code_pow]; exact hjc)
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
    · have h2 := (List.all_eq_true.mp h1) (k % 8).toNat (List.mem_range.mpr hk8)
      rw [Bool.or_eq_true] at h2
      have hcomm : Core.cmul (code g) (Core.cpow (code a) (k % 8).toNat) =
          Core.cmul (Core.cpow (code a) (k % 8).toNat) (code g) := by
        rw [← code_pow, ← code_mul, ← code_mul, ← hk']
        have : (g : P10) * r = r * g := congrArg Subtype.val hgr
        rw [this]
      rcases h2 with h3 | h3
      · simp [hcomm] at h3
      · simp only [beq_iff_eq] at h3
        apply Subtype.ext
        show (r : P10) * r = 1
        apply code_injective
        rw [code_mul, code_one, hk', code_pow]
        exact h3

@[expose] def aM : P10 := A6Models.perm10 [[0, 4, 3, 8, 9, 5, 6, 7], [1, 2]]

@[expose] def aP : P10 := A6Models.perm10 [[0, 4, 6, 7, 9, 5, 3, 8]]

theorem aM_mem : aM ∈ P0 ⊓ A6Models.m10 := by
  rw [mem_Qm_iff]
  have : qmL.contains (code aM) = true := by decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem aP_mem : aP ∈ P0 ⊓ A6Models.pgl29 := by
  rw [mem_Qp_iff]
  have : qpL.contains (code aP) = true := by decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem aM_pow4 : aM ^ 4 ≠ 1 := by decide +kernel

theorem aM_pow8 : aM ^ 8 = 1 := by decide +kernel

theorem aP_pow4 : aP ^ 4 ≠ 1 := by decide +kernel

theorem aP_pow8 : aP ^ 8 = 1 := by decide +kernel

theorem Qm_hasDS : ∃ R : Subgroup ↥(P0 ⊓ A6Models.m10), DS.DSData R :=
  dsData_of_codes qmL_nodup mem_Qm_iff surj_Qm qmL_length aM_mem aM_pow4 aM_pow8 (by decide +kernel)

theorem Qp_hasDS : ∃ R : Subgroup ↥(P0 ⊓ A6Models.pgl29), DS.DSData R :=
  dsData_of_codes qpL_nodup mem_Qp_iff surj_Qp qpL_length aP_mem aP_pow4 aP_pow8 (by decide +kernel)

theorem hasDS_of_sylow_equiv {A : Type} [Group A] [Finite A] {M : Subgroup P10}
    (φ : A ≃* ↥M) {Q : Subgroup P10} (hQ : IsSylowTwoOf Q M)
    (hDS : ∃ R : Subgroup ↥Q, DS.DSData R) {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) :
    ∃ R : Subgroup ↥P, DS.DSData R := by
  have : Finite ↥M := Finite.of_equiv A φ.toEquiv
  have hP1 : IsSylowTwoOf (P.map φ.toMonoidHom) ⊤ := Unc25K1.isSylowTwoOf_top_map φ hP
  set P₁ : Subgroup P10 := (P.map φ.toMonoidHom).map M.subtype with hP₁
  have hP₁M : P₁ ≤ M := Subgroup.map_subtype_le _
  have hP₁S : IsSylowTwoOf P₁ M := by
    rw [Unc25Small.isSylowTwoOf_subgroupOf_top_iff hP₁M]
    have hsub : P₁.subgroupOf M = P.map φ.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [hsub]
    exact hP1
  obtain ⟨g, -, hg⟩ := hQ.exists_conj hP₁S
  let e1 : ↥P ≃* ↥(P.map φ.toMonoidHom) := Subgroup.equivMapOfInjective P φ.toMonoidHom φ.injective
  let e2 : ↥(P.map φ.toMonoidHom) ≃* ↥P₁ :=
    Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective
  let e3 : ↥P₁ ≃* ↥(Q.map (MulAut.conj g).toMonoidHom) := MulEquiv.subgroupCongr hg
  let e4 : ↥Q ≃* ↥(Q.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact hasDS_of_mulEquiv (e4.trans (e3.symm.trans (e2.symm.trans e1.symm))) hDS

theorem hasDS_of_sylow_m10 {A : Type} [Group A] [Finite A] (φ : A ≃* ↥A6Models.m10)
    {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) : ∃ R : Subgroup ↥P, DS.DSData R :=
  hasDS_of_sylow_equiv φ isSylowTwoOf_Qm Qm_hasDS hP

theorem hasDS_of_sylow_pgl29 {A : Type} [Group A] [Finite A] (φ : A ≃* ↥A6Models.pgl29)
    {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) : ∃ R : Subgroup ↥P, DS.DSData R :=
  hasDS_of_sylow_equiv φ isSylowTwoOf_Qp Qp_hasDS hP

open Equiv Equiv.Perm in
theorem perm6_inv_conj_z : ∀ i : Perm (Fin 6), sign i = 1 → i * i = 1 → i ≠ 1 →
    ∃ k : Perm (Fin 6), sign k = 1 ∧ k * (swap 0 1 * swap 2 3) * k⁻¹ = i := by
  decide +kernel

open Equiv Equiv.Perm in
theorem a6_involutions_conj {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    ∀ i j : X, i * i = 1 → j * j = 1 → i ≠ 1 → j ≠ 1 → ∃ k : X, k * i * k⁻¹ = j := by
  have hz : (swap (0 : Fin 6) 1 * swap 2 3) ∈ alternatingGroup (Fin 6) := by
    rw [mem_alternatingGroup]; decide
  let z : alternatingGroup (Fin 6) := ⟨_, hz⟩
  have key : ∀ i : X, i * i = 1 → i ≠ 1 → ∃ k : alternatingGroup (Fin 6), k * z * k⁻¹ = e i := by
    intro i hi2 hi1
    have h2 : e i * e i = 1 := by rw [← map_mul, hi2, map_one]
    have h1 : e i ≠ 1 := fun h => hi1 (e.injective (h.trans (map_one e).symm))
    have hs : sign (e i : Perm (Fin 6)) = 1 := (mem_alternatingGroup).mp (e i).2
    obtain ⟨k, hk, hkz⟩ := perm6_inv_conj_z (e i : Perm (Fin 6)) hs
      (by simpa using congrArg Subtype.val h2) (fun h => h1 (Subtype.ext h))
    exact ⟨⟨k, mem_alternatingGroup.mpr hk⟩, Subtype.ext (by simpa using hkz)⟩
  intro i j hi2 hj2 hi1 hj1
  obtain ⟨k₁, hk₁⟩ := key i hi2 hi1
  obtain ⟨k₂, hk₂⟩ := key j hj2 hj1
  refine ⟨e.symm (k₂ * k₁⁻¹), e.injective ?_⟩
  have h : e (e.symm (k₂ * k₁⁻¹) * i * (e.symm (k₂ * k₁⁻¹))⁻¹) =
      (k₂ * k₁⁻¹) * e i * (k₂ * k₁⁻¹)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [h, ← hk₁, ← hk₂]
  group

end CFSG.QuasithinUnique.Out21.A6
