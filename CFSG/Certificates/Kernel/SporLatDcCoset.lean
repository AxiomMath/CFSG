module

public import CFSG.Certificates.Kernel.SporLatDcRec

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

private theorem lab_eq_labF_act {x : List ℕ} (g : Γ) :
    lab n ptLab x g = labF (fun p => act n g p) x := by
  have h1 : lab n ptLab x g = sortN (x.map fun p => act n g p) := ptAct_tab _ _
  rw [h1, labF, sortN_eq]

private theorem labF_eq_of_act {x : List ℕ} (hx : ∀ p ∈ x, p < n) {f : ℕ → ℕ} {g : Γ}
    (h : ∀ p ∈ x, f p = act n g p) : labF f x = lab n ptLab x g := by
  rw [lab_eq_labF_act, labF, labF]
  congr 1
  exact List.map_congr_left h

private theorem letter_mem_stab {i : ℕ} (hi : i < P.C.ng) :
    P.els.getD (2 + i) 1 ∈ stab (Γ := Γ) (n := n) hlaw P.hΔ := by
  rw [mem_stab]
  have hns : i < P.C.ns := by
    have := ng_le_ns P
    omega
  rw [← labF_eq_of_act (fun p hp => delta_lt P hp) (g := P.els.getD (2 + i) 1)
    (f := P.C.L (2 + i)) (fun p hp => (P.act_letter (by omega) (delta_lt P hp)).symm)]
  exact sLet_fixes P hns

private theorem S_le_stab : P.S ≤ stab (Γ := Γ) (n := n) hlaw P.hΔ := by
  rw [S, Subgroup.closure_le]
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  rw [List.getElem_take] at hxi
  have hi' : i < P.C.ng := by
    have h := hi
    rw [List.length_take] at h
    omega
  have hi'' : i < P.sl.length := by
    have h1 := P.hsl
    have h2 := ng_le_ns P
    omega
  have heq : P.els.getD (2 + i) 1 = x := by
    rw [P.els_getD_sl (show 2 ≤ 2 + i from by omega), show 2 + i - 2 = i from by omega,
      List.getD_eq_getElem P.sl 1 hi'', hxi]
  rw [← heq]
  exact letter_mem_stab P hi'

private theorem fibre_stab (g0 : Γ) :
    Nat.card {g : Γ // lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ g0} =
      Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Fintype ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun g =>
        (⟨g.1⁻¹ * g0, (lab_eq_iff hlaw P.hΔ g.1 g0).mp g.2⟩ :
          ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ))
      invFun := fun s => (⟨g0 * (s : Γ)⁻¹, by
        have hs' : lab n ptLab P.C.Δ (s : Γ)⁻¹ = P.C.Δ := by
          rw [← mem_stab (Γ := Γ) (n := n) hlaw P.hΔ]
          exact (stab (Γ := Γ) (n := n) hlaw P.hΔ).inv_mem s.2
        rw [lab_mul hlaw P.hΔ, hs']
        rfl⟩ :
        {g : Γ // lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ g0})
      left_inv := fun g => by ext; group
      right_inv := fun s => by ext; group }

private theorem GOrb_card_mul :
    P.GOrb.card * Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) = Nat.card Γ := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Fintype ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := Fintype.ofFinite _
  have hmaps : Set.MapsTo (fun g : Γ => lab n ptLab P.C.Δ g)
      ↑(Finset.univ : Finset Γ) ↑P.GOrb := by
    intro g _
    exact (mem_GOrb (P := P) (M := lab n ptLab P.C.Δ g)).mpr ⟨g, rfl⟩
  have h1 : (Finset.univ : Finset Γ).card =
      ∑ M ∈ P.GOrb, (Finset.univ.filter (fun g : Γ => lab n ptLab P.C.Δ g = M)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ M ∈ P.GOrb,
      (Finset.univ.filter (fun g : Γ => lab n ptLab P.C.Δ g = M)).card =
        Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := by
    intro M hM
    rw [mem_GOrb] at hM
    obtain ⟨g0, rfl⟩ := hM
    have hcard : (Finset.univ.filter
        (fun g : Γ => lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ g0)).card =
        Fintype.card {g : Γ // lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ g0} :=
      (Fintype.card_subtype _).symm
    rw [hcard, ← Nat.card_eq_fintype_card]
    exact fibre_stab P g0
  rw [Finset.card_univ, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h1
  conv_rhs => rw [Nat.card_eq_fintype_card]
  rw [← h1]

private theorem N_pos : 0 < P.C.N := by
  have hpos : 0 < P.C.N * P.s := by
    rw [← P.hN]
    exact Nat.card_pos
  exact Nat.pos_of_mul_pos_right hpos

private theorem GOrb_card_le : P.GOrb.card ≤ P.C.N := by
  classical
  haveI : Fintype ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := Fintype.ofFinite _
  have hincl : Function.Injective
      (fun s : ↥P.S => (⟨s.1, S_le_stab P s.2⟩ : ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ))) :=
    fun a b h => Subtype.ext (congrArg (fun x : ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) => (x : Γ)) h)
  have hcard : Nat.card ↥P.S ≤ Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) :=
    Nat.card_le_card_of_injective _ hincl
  have hS : Nat.card ↥P.S = P.s := S_card P
  have h1 := GOrb_card_mul P
  have h3 : P.GOrb.card * P.s ≤ P.C.N * P.s := by
    calc P.GOrb.card * P.s ≤ P.GOrb.card * Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := by
          rw [hS] at hcard
          exact Nat.mul_le_mul_left _ hcard
      _ = Nat.card Γ := h1
      _ = P.C.N * P.s := P.hN
  exact Nat.le_of_mul_le_mul_right h3 (by rw [← hS]; exact Nat.card_pos)

private theorem GOrb_card_eq : P.GOrb.card = P.C.N := by
  refine le_antisymm (GOrb_card_le P) ?_
  rw [← card_unionSx P]
  exact Finset.card_le_card (unionSx_subset_GOrb P)

private theorem stab_card : Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) = P.s := by
  have h1 := GOrb_card_mul P
  rw [GOrb_card_eq P, P.hN] at h1
  exact Nat.eq_of_mul_eq_mul_left (N_pos P) h1

private theorem stab_eq_S : stab (Γ := Γ) (n := n) hlaw P.hΔ = P.S := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  have hS_card : (Finset.univ.filter (fun x : Γ => x ∈ P.S)).card = Nat.card ↥P.S := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hstab_card :
      (Finset.univ.filter (fun x : Γ => x ∈ stab (Γ := Γ) (n := n) hlaw P.hΔ)).card =
        Nat.card ↥(stab (Γ := Γ) (n := n) hlaw P.hΔ) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hsub : (Finset.univ.filter (fun x : Γ => x ∈ P.S)) ⊆
      (Finset.univ.filter (fun x : Γ => x ∈ stab (Γ := Γ) (n := n) hlaw P.hΔ)) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      S_le_stab P (Finset.mem_filter.mp hx).2⟩
  have hcard : (Finset.univ.filter
        (fun x : Γ => x ∈ stab (Γ := Γ) (n := n) hlaw P.hΔ)).card ≤
      (Finset.univ.filter (fun x : Γ => x ∈ P.S)).card := by
    rw [hS_card, hstab_card, stab_card P, S_card P]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  ext x
  constructor
  · intro hx
    have hx' : x ∈ Finset.univ.filter (fun x : Γ => x ∈ P.S) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    exact (Finset.mem_filter.mp hx').2
  · intro hx
    exact S_le_stab P hx

theorem lab_eq_iff_S (g : Γ) : lab n ptLab P.C.Δ g = P.C.Δ ↔ g ∈ P.S := by
  rw [← mem_stab (Γ := Γ) (n := n) hlaw P.hΔ, ← stab_eq_S P]

theorem cover_rec (g : Γ) :
    ∃ r ∈ P.recs, ∃ s ∈ P.S, ∃ t ∈ P.S, g = s * evalElt P.els r.w * t := by
  have hM : lab n ptLab P.C.Δ g ∈ P.GOrb :=
    (mem_GOrb (P := P) (M := lab n ptLab P.C.Δ g)).mpr ⟨g, rfl⟩
  have hU : P.unionSx = P.GOrb := by
    refine Finset.eq_of_subset_of_card_le (unionSx_subset_GOrb P) ?_
    rw [card_unionSx P, GOrb_card_eq P]
  rw [← hU] at hM
  rw [mem_unionSx] at hM
  obtain ⟨r, hr, hM⟩ := hM
  rw [mem_Sx] at hM
  obtain ⟨s, hs, hM⟩ := hM
  have hlab : lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ (s * evalElt P.els r.w) := by
    rw [hM, recs_lab_eq P hr]
    exact lab_lab P.hΔ s (evalElt P.els r.w)
  have hmem : g⁻¹ * (s * evalElt P.els r.w) ∈ P.S := by
    rw [← lab_eq_iff_S P]
    exact (lab_eq_iff hlaw P.hΔ g (s * evalElt P.els r.w)).mp hlab
  refine ⟨r, hr, s, hs, (g⁻¹ * (s * evalElt P.els r.w))⁻¹, P.S.inv_mem hmem, ?_⟩
  group

end DcSoundCtx

end CFSG.KC.SLDc

end
