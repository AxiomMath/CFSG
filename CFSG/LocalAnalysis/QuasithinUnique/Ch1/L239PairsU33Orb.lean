module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Elts
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagon

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F] {hF : Nat.card F = 9}

section Closure

variable (hF)

theorem exists_mem_orbit_point {H : Subgroup (StatedSU 3 3 F)} {p₀ : NonisoLine F} {ℓ₀ : HexLine F}
    (hT1 : ∀ T : HexLine F, p₀ ∈ T.1 → ∃ k ∈ H, lineActLin hF k ℓ₀ = T)
    (hT2 : ∀ q ∈ ℓ₀.1, ∃ k ∈ H, lineAct hF k p₀ = q) (q : NonisoLine F) :
    ∃ h ∈ H, lineAct hF h p₀ = q := by
  have hconn := (hexagon_facts hF).1
  let W : NonisoLine F ⊕ HexLine F → Prop :=
    Sum.elim (fun p => ∃ h ∈ H, lineAct hF h p₀ = p) (fun T => ∃ h ∈ H, lineActLin hF h ℓ₀ = T)
  have hstep : ∀ u v, (incGraph F).Adj u v → W u → W v := by
    intro u v huv hu
    rcases u with p | T <;> rcases v with p' | T'
    · exact absurd huv (not_incGraph_adj_inl_inl p p')
    ·
      obtain ⟨h, hh, hp⟩ := hu
      have hpT : p ∈ T'.1 := (incGraph_adj_inl_inr p T').1 huv
      have h1 : p₀ ∈ (lineActLin hF h⁻¹ T').1 := by
        have := (lineAct_mem_lineActLin hF h⁻¹ T' p).2 hpT
        rwa [← hp, ← lineAct_mul, inv_mul_cancel, lineAct_one] at this
      obtain ⟨k, hk, hkT⟩ := hT1 _ h1
      refine ⟨h * k, H.mul_mem hh hk, ?_⟩
      rw [lineActLin_mul, hkT, ← lineActLin_mul, mul_inv_cancel, lineActLin_one]
    ·
      obtain ⟨h, hh, hT⟩ := hu
      have hpT : p' ∈ T.1 := (incGraph_adj_inr_inl T p').1 huv
      have h1 : lineAct hF h⁻¹ p' ∈ ℓ₀.1 := by
        have := (lineAct_mem_lineActLin hF h⁻¹ T p').2 hpT
        rwa [← hT, ← lineActLin_mul, inv_mul_cancel, lineActLin_one] at this
      obtain ⟨k, hk, hkq⟩ := hT2 _ h1
      refine ⟨h * k, H.mul_mem hh hk, ?_⟩
      rw [lineAct_mul, hkq, ← lineAct_mul, mul_inv_cancel, lineAct_one]
    · exact absurd huv (not_incGraph_adj_inr_inr T T')
  have hall : ∀ v, Relation.ReflTransGen (incGraph F).Adj (Sum.inl p₀) v → W v := by
    intro v hv
    induction hv with
    | refl => exact ⟨1, H.one_mem, lineAct_one hF p₀⟩
    | tail _ hadj ih => exact hstep _ _ hadj ih
  have hreach := hconn.preconnected (Sum.inl p₀) (Sum.inl q)
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  exact hall _ hreach

end Closure

section Lines

variable (d : Idata F)

theorem gEl_mul_self : gEl hF d * gEl hF d = (gEl hF d)⁻¹ := by
  have h3 : gEl hF d * gEl hF d * gEl hF d = 1 := by
    rw [← pow_two, ← pow_succ]
    exact gEl_pow_three
  exact eq_inv_of_mul_eq_one_left h3

theorem lineAct_gEl_inv_zero : lineAct hF (gEl hF d)⁻¹ (Pt hF 0) = Pt hF 0 := by
  have := congrArg (lineAct hF (gEl hF d)⁻¹) (lineAct_gEl_zero (hF := hF) (d := d))
  rw [← lineAct_mul, inv_mul_cancel, lineAct_one] at this
  exact this.symm

theorem mem_lines_through (T : HexLine F) (hT : Pt hF 0 ∈ T.1) :
    T = ell0 hF ∨ T = lineActLin hF (gEl hF d) (ell0 hF) ∨
      T = lineActLin hF (gEl hF d)⁻¹ (ell0 hF) := by
  have hfin : Finite (HexLine F) := finite_hexLine hF
  set g := gEl hF d with hg
  have h0 : Pt hF 0 ∈ (ell0 hF).1 := Pt_mem_ell0 0
  have h1 : Pt hF 0 ∈ (lineActLin hF g (ell0 hF)).1 := by
    have := (lineAct_mem_lineActLin hF g (ell0 hF) (Pt hF 0)).2 h0
    rwa [lineAct_gEl_zero] at this
  have h2 : Pt hF 0 ∈ (lineActLin hF g⁻¹ (ell0 hF)).1 := by
    have := (lineAct_mem_lineActLin hF g⁻¹ (ell0 hF) (Pt hF 0)).2 h0
    rwa [lineAct_gEl_inv_zero] at this
  have hne1 : lineActLin hF g (ell0 hF) ≠ ell0 hF := fun h =>
    gEl_not_mem_stab0 (mem_stab0_iff.2 h)
  have hne2 : lineActLin hF g⁻¹ (ell0 hF) ≠ ell0 hF := fun h =>
    gEl_not_mem_stab0 (inv_mem_iff.1 (mem_stab0_iff.2 h))
  have hne3 : lineActLin hF g (ell0 hF) ≠ lineActLin hF g⁻¹ (ell0 hF) := by
    intro h
    have := congrArg (lineActLin hF g) h
    rw [← lineActLin_mul, ← lineActLin_mul, mul_inv_cancel, lineActLin_one, gEl_mul_self] at this
    exact hne2 this
  have hS3 : ({ell0 hF, lineActLin hF g (ell0 hF), lineActLin hF g⁻¹ (ell0 hF)} :
      Set (HexLine F)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, hne1.symm, hne2.symm, hne3, rfl⟩
  have hX : {T : HexLine F | Pt hF 0 ∈ T.1}.ncard = 3 := ncard_lines_through hF _
  have hsub : ({ell0 hF, lineActLin hF g (ell0 hF), lineActLin hF g⁻¹ (ell0 hF)} :
      Set (HexLine F)) ⊆ {T : HexLine F | Pt hF 0 ∈ T.1} := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hX, hS3]) (Set.toFinite _)
  have hmem : T ∈ ({ell0 hF, lineActLin hF g (ell0 hF), lineActLin hF g⁻¹ (ell0 hF)} :
      Set (HexLine F)) := heq ▸ hT
  simpa using hmem

include d in
theorem exists_lineActLin_eq (T : HexLine F) : ∃ h : StatedSU 3 3 F, lineActLin hF h (ell0 hF) = T := by
  obtain ⟨p, hp⟩ : T.1.Nonempty := by
    rw [← Finset.card_pos, T.2.1]
    norm_num
  obtain ⟨h, hh⟩ := lineAct_transitive hF p (Pt hF 0)
  have hmem : Pt hF 0 ∈ (lineActLin hF h T).1 := by
    have := (lineAct_mem_lineActLin hF h T p).2 hp
    rwa [hh] at this
  have key : ∀ k : StatedSU 3 3 F, lineActLin hF h T = lineActLin hF k (ell0 hF) →
      ∃ h' : StatedSU 3 3 F, lineActLin hF h' (ell0 hF) = T := by
    intro k hk
    refine ⟨h⁻¹ * k, ?_⟩
    rw [lineActLin_mul, ← hk, ← lineActLin_mul, inv_mul_cancel, lineActLin_one]
  rcases mem_lines_through d _ hmem with h1 | h1 | h1
  · exact key 1 (by rw [h1, lineActLin_one])
  · exact key _ h1
  · exact key _ h1

include d in
theorem card_stab0 : Nat.card (stab0 hF) = 96 := by
  classical
  have hfin : Finite (HexLine F) := finite_hexLine hF
  let _ : MulAction (StatedSU 3 3 F) (HexLine F) :=
    { smul := lineActLin hF, one_smul := lineActLin_one hF, mul_smul := lineActLin_mul hF }
  have hstab : MulAction.stabilizer (StatedSU 3 3 F) (ell0 hF) = stab0 hF := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  have horb : MulAction.orbit (StatedSU 3 3 F) (ell0 hF) = Set.univ := by
    ext T
    simp only [Set.mem_univ, iff_true]
    obtain ⟨h, hh⟩ := exists_lineActLin_eq d T
    exact ⟨h, hh⟩
  have hidx := MulAction.index_stabilizer (StatedSU 3 3 F) (ell0 hF)
  have hmul := (MulAction.stabilizer (StatedSU 3 3 F) (ell0 hF)).index_mul_card
  rw [hstab] at hidx hmul
  rw [horb, Set.ncard_univ, card_hexLine hF] at hidx
  rw [hidx, card_statedSU hF] at hmul
  omega

theorem eq_top_of_mem {H : Subgroup (StatedSU 3 3 F)}
    (hK1 : ∀ g, lineAct hF g (Pt hF 0) = Pt hF 0 → g ∈ H) (hg : gEl hF d ∈ H)
    (hc : cEl hF ∈ H) : H = ⊤ := by
  have hT1 : ∀ T : HexLine F, Pt hF 0 ∈ T.1 → ∃ k ∈ H, lineActLin hF k (ell0 hF) = T := by
    intro T hT
    rcases mem_lines_through d T hT with h | h | h
    · exact ⟨1, H.one_mem, by rw [h, lineActLin_one]⟩
    · exact ⟨_, hg, h.symm⟩
    · exact ⟨_, H.inv_mem hg, h.symm⟩
  have hT2 : ∀ q ∈ (ell0 hF).1, ∃ k ∈ H, lineAct hF k (Pt hF 0) = q := by
    intro q hq
    rcases mem_ell0.1 hq with rfl | rfl | rfl
    · exact ⟨1, H.one_mem, lineAct_one hF _⟩
    · exact ⟨_, hc, lineAct_cEl 0⟩
    · exact ⟨cEl hF * cEl hF, H.mul_mem hc hc, by
        rw [lineAct_mul, lineAct_cEl, lineAct_cEl]
        rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, hq⟩ := exists_mem_orbit_point hF hT1 hT2 (lineAct hF g (Pt hF 0))
  have h1 : h⁻¹ * g ∈ H := hK1 _ (by
    rw [lineAct_mul, ← hq, ← lineAct_mul, inv_mul_cancel, lineAct_one])
  have h2 := H.mul_mem hh h1
  simpa using h2

end Lines

end CFSG.QuasithinUnique.Vol2Native.L239.U33
