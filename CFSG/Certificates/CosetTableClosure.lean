module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem invCode_two_mul (i : ℕ) : invCode (2 * i) = 2 * i + 1 := by
  have h : Nat.beq (Nat.mod (2 * i) 2) 0 = true := by
    rw [Nat.beq_eq]
    exact Nat.mul_mod_right 2 i
  rw [invCode, h]
  rfl

theorem invCode_two_mul_add_one (i : ℕ) : invCode (2 * i + 1) = 2 * i := by
  have h : Nat.beq (Nat.mod (2 * i + 1) 2) 0 = false := by
    cases hb : Nat.beq (Nat.mod (2 * i + 1) 2) 0 with
    | false => rfl
    | true =>
      rw [Nat.beq_eq] at hb
      have : (2 * i + 1) % 2 = 1 := by omega
      exact absurd hb (by rw [show Nat.mod (2 * i + 1) 2 = (2 * i + 1) % 2 from rfl, this]; simp)
  rw [invCode, h]
  rfl

section Closure

variable {G : Type*} [Group G] {m : ℕ} (gen : ℕ → G)

abbrev letterClosure : Subgroup G := Subgroup.closure (gen '' Set.Iio (2 * m))

noncomputable def letterIn (x : ℕ) : letterClosure (m := m) gen :=
  if hx : x < 2 * m then ⟨gen x, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩ else 1

theorem letterIn_of_lt {x : ℕ} (hx : x < 2 * m) :
    letterIn (m := m) gen x = ⟨gen x, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩ :=
  dite_eq_left hx

theorem coe_evalWord_letterIn {w : List ℕ} (hw : ∀ c ∈ w, c < 2 * m) :
    ((evalWord (letterIn (m := m) gen) w : letterClosure (m := m) gen) : G) = evalWord gen w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalWord_cons, evalWord_cons, Subgroup.coe_mul,
      ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'), letterIn_of_lt gen (hw c (by simp))]

theorem closure_letterIn :
    Subgroup.closure (letterIn (m := m) gen '' Set.Iio (2 * m)) = ⊤ := by
  have h : letterIn (m := m) gen '' Set.Iio (2 * m) =
      ((↑) : letterClosure (m := m) gen → G) ⁻¹' (gen '' Set.Iio (2 * m)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [letterIn_of_lt gen hx]⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext (by rw [letterIn_of_lt gen hx]; exact hxy)⟩
  rw [h]
  exact Subgroup.closure_closure_coe_preimage

theorem mem_closure_of_checkHLT_one (hinv : ∀ i < m, gen (2 * i + 1) = (gen (2 * i))⁻¹)
    {rels subs : List (List ℕ)}
    (hrels : ∀ r ∈ rels, (∀ c ∈ r, c < 2 * m) ∧ evalWord gen r = 1)
    (hsubs : ∀ u ∈ subs, ∀ c ∈ u, c < 2 * m) {cap : ℕ}
    (h : checkHLT (mkParams (2 * m) (invArr m) rels subs) cap 1 = true) :
    ∀ x < 2 * m, gen x ∈ Subgroup.closure {g | ∃ u ∈ subs, evalWord gen u = g} := by
  set K := Subgroup.closure {g | ∃ u ∈ subs, evalWord gen u = g}
  set Y := letterClosure (m := m) gen
  set gen' := letterIn (m := m) gen
  have hg : ∀ {x : ℕ} (hx : x < 2 * m),
      gen' x = ⟨gen x, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩ := fun hx => letterIn_of_lt gen hx
  have hinvL : ∀ x < 2 * m, (invArr m).getD x 0 < 2 * m := fun x hx => by
    rw [invArr_getD hx]
    exact invCode_lt hx
  have hginv : ∀ x < 2 * m, gen' ((invArr m).getD x 0) = (gen' x)⁻¹ := by
    intro x hx
    rw [invArr_getD hx]
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [invCode_two_mul, hg (by omega), hg hx]
      exact Subtype.ext (hinv i (by omega))
    · rw [invCode_two_mul_add_one, hg (by omega), hg hx]
      refine Subtype.ext ?_
      show gen (2 * i) = (gen (2 * i + 1))⁻¹
      rw [hinv i (by omega), inv_inv]
  have hall : ∀ r ∈ rels ++ rels.map (invWord (invArr m)),
      (∀ y ∈ r, y < 2 * m) ∧ evalWord gen' r = 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨hl, he⟩ := hrels r hr
      exact ⟨hl, Subtype.ext (by rw [coe_evalWord_letterIn gen hl, he]; rfl)⟩
    · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hl, he⟩ := hrels r0 hr0
      refine ⟨fun y hy => ?_, ?_⟩
      · simp only [invWord, List.mem_map, List.mem_reverse] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact hinvL z (hl z hz)
      · have he' : evalWord gen' r0 = 1 :=
          Subtype.ext (by rw [coe_evalWord_letterIn gen hl, he]; rfl)
        rw [evalWord_invWord (fun y hy => hginv y (hl y hy)), he', inv_one]
  have hP : Good gen' (K.subgroupOf Y) (mkParams (2 * m) (invArr m) rels subs) := by
    refine ⟨hinvL, hginv, ?_, ?_, ?_⟩
    · intro x p hp
      obtain ⟨h1, r, hr, hpr⟩ := mem_scans hp
      obtain ⟨hl, he⟩ := hall r hr
      exact ⟨h1, letters_rotation hpr hl, evalWord_rotation hpr he⟩
    · intro p hp
      obtain ⟨h1, hp1⟩ := mem_subs hp
      refine ⟨h1, hsubs _ hp1, ?_⟩
      rw [Subgroup.mem_subgroupOf, coe_evalWord_letterIn gen (hsubs _ hp1)]
      exact Subgroup.subset_closure ⟨p.1, hp1, rfl⟩
    · intro p hp
      simp only [mkParams, List.mem_map] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      exact ⟨rfl, (hrels w hw).1, (hall w (List.mem_append_left _ hw)).2⟩
  obtain ⟨hfin, hle⟩ := index_le_of_checkHLT hP (closure_letterIn gen) h
  have htop : K.subgroupOf Y = ⊤ := Subgroup.index_eq_one.mp (by
    have := hfin.index_ne_zero
    omega)
  intro x hx
  have hmem : gen' x ∈ K.subgroupOf Y := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf, hg hx] at hmem
  exact hmem

end Closure

end CFSG.CosetTable
