module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalOmega
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUInput

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28

attribute [local irreducible] txL tU tZ tO tzc gW

section VSub


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem gElt_eps (heps : epsOK tzc gW = true) {j : ℕ} (hj : j < 4) :
    gElt M j * zE M * (gElt M j)⁻¹ = if j % 2 = 1 then zE M * zE M else zE M := by
  have h := epsOK_spec heps j hj
  rw [← gInv_eq M hj]
  have hv : Valid (mulCode (mulCode (wordCode gW[j]!) tzc) (wordCode (gW[j]!).reverse)) :=
    valid_mulCode (valid_mulCode (valid_wordCode _) valid_tzc) (valid_wordCode _)
  have hrho : M.rho (gElt M j * zE M * gInv M j) =
      decode (mulCode (mulCode (wordCode gW[j]!) tzc) (wordCode (gW[j]!).reverse)) :=
    M.rho_mul_code (valid_mulCode (valid_wordCode _) valid_tzc) (valid_wordCode _)
      (M.rho_mul_code (valid_wordCode _) valid_tzc (rho_gElt M j) (rho_zE M)) (rho_gInv M j)
  by_cases hj2 : j % 2 = 1
  · rw [ite_eq_left hj2] at h ⊢
    exact (M.eq_iff_codes hv (valid_mulCode valid_tzc valid_tzc) hrho
      (M.rho_mul_code valid_tzc valid_tzc (rho_zE M) (rho_zE M))).2 h
  · rw [ite_eq_right hj2] at h ⊢
    exact (M.eq_iff_codes hv valid_tzc hrho (rho_zE M)).2 h

theorem zE_sq : zE M * zE M = (zE M)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((pow_three' (zE M)).symm.trans (zE_pow_three M))

@[expose] def Cen (x : adjointGroup .G2 K) : Prop := x * zE M * x⁻¹ = zE M

@[expose] def Inv (x : adjointGroup .G2 K) : Prop := x * zE M * x⁻¹ = (zE M)⁻¹

variable {M}

theorem Cen.mul {x y : adjointGroup .G2 K} (hx : Cen M x) (hy : Cen M y) : Cen M (x * y) := by
  unfold Cen at *
  calc x * y * zE M * (x * y)⁻¹ = x * (y * zE M * y⁻¹) * x⁻¹ := by group
    _ = zE M := by rw [hy, hx]

theorem Inv.mul_inv {x y : adjointGroup .G2 K} (hx : Inv M x) (hy : Inv M y) : Cen M (x * y) := by
  unfold Cen Inv at *
  calc x * y * zE M * (x * y)⁻¹ = x * (y * zE M * y⁻¹) * x⁻¹ := by group
    _ = (x * zE M * x⁻¹)⁻¹ := by rw [hy]; group
    _ = zE M := by rw [hx, inv_inv]

theorem Cen.mul_inv {x y : adjointGroup .G2 K} (hx : Cen M x) (hy : Inv M y) : Inv M (x * y) := by
  unfold Cen Inv at *
  calc x * y * zE M * (x * y)⁻¹ = x * (y * zE M * y⁻¹) * x⁻¹ := by group
    _ = (x * zE M * x⁻¹)⁻¹ := by rw [hy]; group
    _ = (zE M)⁻¹ := by rw [hx]

theorem Inv.mul_cen {x y : adjointGroup .G2 K} (hx : Inv M x) (hy : Cen M y) : Inv M (x * y) := by
  unfold Cen Inv at *
  calc x * y * zE M * (x * y)⁻¹ = x * (y * zE M * y⁻¹) * x⁻¹ := by group
    _ = (zE M)⁻¹ := by rw [hy, hx]

theorem Cen.inv' {x : adjointGroup .G2 K} (hx : Cen M x) : Cen M x⁻¹ := by
  unfold Cen at *
  rw [inv_inv]
  calc x⁻¹ * zE M * x = x⁻¹ * (x * zE M * x⁻¹) * x := by rw [hx]
    _ = zE M := by group

theorem Inv.inv' {x : adjointGroup .G2 K} (hx : Inv M x) : Inv M x⁻¹ := by
  unfold Inv at *
  have h1 : x * (zE M)⁻¹ * x⁻¹ = zE M := by
    have := congrArg (fun w => w⁻¹) hx
    simpa [mul_inv_rev, mul_assoc] using this
  rw [inv_inv]
  calc x⁻¹ * zE M * x = x⁻¹ * (x * (zE M)⁻¹ * x⁻¹) * x := by rw [h1]
    _ = (zE M)⁻¹ := by group

variable (M)

theorem not_cen_of_inv {x : adjointGroup .G2 K} (hx : Inv M x) : ¬ Cen M x := by
  intro hc
  unfold Cen Inv at *
  have h1 : zE M = (zE M)⁻¹ := hc.symm.trans hx
  have h2 : zE M * zE M = 1 := mul_eq_one_iff_eq_inv.mpr h1
  apply zE_ne_one M
  have h3 := zE_pow_three M
  rw [pow_three', h2, one_mul] at h3
  exact h3

theorem cen_or_inv {s : adjointGroup .G2 K} (hs : s ∈ SX M) : Cen M s ∨ Inv M s := by
  have h : s * zE M * s⁻¹ ∈ Subgroup.zpowers (zE M) :=
    (Subgroup.mem_normalizer_iff.mp hs (zE M)).mp (Subgroup.mem_zpowers _)
  rcases mem_zpowers_cases (zE_pow_three M) h with h1 | h1 | h1
  · exfalso
    apply zE_ne_one M
    have e : zE M = s⁻¹ * (s * zE M * s⁻¹) * s := by group
    rw [e, h1]
    simp
  · exact Or.inl h1
  · exact Or.inr h1

theorem mem_VX_iff {x : adjointGroup .G2 K} : x ∈ VX M ↔ Cen M x := by
  unfold VX Cen
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have := h (zE M) (Set.mem_singleton _)
    calc x * zE M * x⁻¹ = zE M * x * x⁻¹ := by rw [this]
      _ = zE M := by group
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc zE M * x = (x * zE M * x⁻¹) * x := by rw [h]
      _ = x * zE M := by group

theorem VX_le_SX : VX M ≤ SX M := by
  intro x hx
  have hc := (mem_VX_iff M).mp hx
  apply mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have e : x * zE M ^ k * x⁻¹ = (x * zE M * x⁻¹) ^ k := by rw [conj_zpow]
  rw [e, hc]
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem inv_g1 (heps : epsOK tzc gW = true) : Inv M (gElt M 1) := by
  have := gElt_eps M heps (j := 1) (by norm_num)
  unfold Inv
  rw [this, ite_eq_left (by norm_num), zE_sq]

theorem inv_g3 (heps : epsOK tzc gW = true) : Inv M (gElt M 3) := by
  have := gElt_eps M heps (j := 3) (by norm_num)
  unfold Inv
  rw [this, ite_eq_left (by norm_num), zE_sq]

theorem cen_g0 (heps : epsOK tzc gW = true) : Cen M (gElt M 0) := by
  have := gElt_eps M heps (j := 0) (by norm_num)
  unfold Cen
  rw [this, ite_eq_right (by norm_num)]

theorem cen_g2 (heps : epsOK tzc gW = true) : Cen M (gElt M 2) := by
  have := gElt_eps M heps (j := 2) (by norm_num)
  unfold Cen
  rw [this, ite_eq_right (by norm_num)]

theorem gElt_mem_SX {j : ℕ} (hj : j < 4) : gElt M j ∈ SX M :=
  PX_le_SX M (gElt_mem_PX M hj)

theorem card_SX_eq (heps : epsOK tzc gW = true) : Nat.card (SX M) = 2 * Nat.card (VX M) := by
  have h2 : ((VX M).subgroupOf (SX M)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨gElt M 1, gElt_mem_SX M (by norm_num)⟩, fun ⟨s, hs⟩ => ?_⟩
    have hb := inv_g1 M heps
    rcases cen_or_inv M hs with h | h
    · right
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact (mem_VX_iff M).mpr h
      · rw [Subgroup.mem_subgroupOf]
        exact fun hmem => not_cen_of_inv M (h.mul_inv hb) ((mem_VX_iff M).mp hmem)
    · left
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact (mem_VX_iff M).mpr (h.mul_inv hb)
      · rw [Subgroup.mem_subgroupOf]
        exact fun hmem => not_cen_of_inv M h ((mem_VX_iff M).mp hmem)
  have h3 := Subgroup.relIndex_mul_card (VX M) (SX M)
  rw [Subgroup.relIndex, h2, inf_eq_left.mpr (VX_le_SX M)] at h3
  exact h3.symm

@[expose] noncomputable def HG : Subgroup (adjointGroup .G2 K) :=
  Subgroup.closure (Set.range fun k : Fin 7 => hElt M k)

theorem hElt_zero : hElt M 0 = gElt M 0 := rfl

theorem hElt_one : hElt M 1 = gElt M 1 * gElt M 0 * (gElt M 1)⁻¹ := by
  rw [← gInv_eq M (by norm_num : 1 < 4)]
  show M.wordElt (gW[1]! ++ gW[0]! ++ (gW[1]!).reverse) = _
  rw [wordElt_append, wordElt_append]
  rfl

theorem hElt_two : hElt M 2 = gElt M 1 * gElt M 1 := by
  show M.wordElt (gW[1]! ++ gW[1]!) = _
  rw [wordElt_append]
  rfl

theorem hElt_three : hElt M 3 = gElt M 2 := rfl

theorem hElt_four : hElt M 4 = gElt M 1 * gElt M 2 * (gElt M 1)⁻¹ := by
  rw [← gInv_eq M (by norm_num : 1 < 4)]
  show M.wordElt (gW[1]! ++ gW[2]! ++ (gW[1]!).reverse) = _
  rw [wordElt_append, wordElt_append]
  rfl

theorem hElt_five : hElt M 5 = gElt M 3 * (gElt M 1)⁻¹ := by
  rw [← gInv_eq M (by norm_num : 1 < 4)]
  show M.wordElt (gW[3]! ++ (gW[1]!).reverse) = _
  rw [wordElt_append]
  rfl

theorem hElt_six : hElt M 6 = gElt M 1 * gElt M 3 := by
  show M.wordElt (gW[1]! ++ gW[3]!) = _
  rw [wordElt_append]
  rfl

theorem mem_HG {k : ℕ} (hk : k < 7) : hElt M k ∈ HG M :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem HG_le_VX (heps : epsOK tzc gW = true) : HG M ≤ VX M := by
  unfold HG
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  show hElt M k ∈ VX M
  rw [mem_VX_iff]
  have ha := cen_g0 M heps
  have hb := inv_g1 M heps
  have hc := cen_g2 M heps
  have hd := inv_g3 M heps
  fin_cases k
  · show Cen M (hElt M 0)
    rw [hElt_zero]
    exact ha
  · show Cen M (hElt M 1)
    rw [hElt_one]
    exact (hb.mul_cen ha).mul_inv hb.inv'
  · show Cen M (hElt M 2)
    rw [hElt_two]
    exact hb.mul_inv hb
  · show Cen M (hElt M 3)
    rw [hElt_three]
    exact hc
  · show Cen M (hElt M 4)
    rw [hElt_four]
    exact (hb.mul_cen hc).mul_inv hb.inv'
  · show Cen M (hElt M 5)
    rw [hElt_five]
    exact hd.mul_inv hb.inv'
  · show Cen M (hElt M 6)
    rw [hElt_six]
    exact hb.mul_inv hd

theorem conj_g1_mem_HG : ∀ x ∈ HG M, gElt M 1 * x * (gElt M 1)⁻¹ ∈ HG M := by
  have h0 := mem_HG (M := M) (k := 0) (by norm_num)
  have h1 := mem_HG (M := M) (k := 1) (by norm_num)
  have h2 := mem_HG (M := M) (k := 2) (by norm_num)
  have h3 := mem_HG (M := M) (k := 3) (by norm_num)
  have h4 := mem_HG (M := M) (k := 4) (by norm_num)
  have h5 := mem_HG (M := M) (k := 5) (by norm_num)
  have h6 := mem_HG (M := M) (k := 6) (by norm_num)
  let f : adjointGroup .G2 K →* adjointGroup .G2 K := (MulAut.conj (gElt M 1)).toMonoidHom
  have hf : ∀ x, f x = gElt M 1 * x * (gElt M 1)⁻¹ := fun x => by
    simp [f, MulAut.conj_apply]
  have hle : (HG M).map f ≤ HG M := by
    unfold HG
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    show f (hElt M k) ∈ HG M
    rw [hf]
    fin_cases k
    · show gElt M 1 * hElt M 0 * (gElt M 1)⁻¹ ∈ HG M
      rw [hElt_zero, ← hElt_one]
      exact h1
    · have e : gElt M 1 * hElt M 1 * (gElt M 1)⁻¹ = hElt M 2 * hElt M 0 * (hElt M 2)⁻¹ := by
        rw [hElt_one, hElt_two, hElt_zero]
        group
      show gElt M 1 * hElt M 1 * (gElt M 1)⁻¹ ∈ HG M
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h0) (Subgroup.inv_mem _ h2)
    · have e : gElt M 1 * hElt M 2 * (gElt M 1)⁻¹ = hElt M 2 := by
        rw [hElt_two]
        group
      show gElt M 1 * hElt M 2 * (gElt M 1)⁻¹ ∈ HG M
      rw [e]
      exact h2
    · show gElt M 1 * hElt M 3 * (gElt M 1)⁻¹ ∈ HG M
      rw [hElt_three, ← hElt_four]
      exact h4
    · have e : gElt M 1 * hElt M 4 * (gElt M 1)⁻¹ = hElt M 2 * hElt M 3 * (hElt M 2)⁻¹ := by
        rw [hElt_four, hElt_two, hElt_three]
        group
      show gElt M 1 * hElt M 4 * (gElt M 1)⁻¹ ∈ HG M
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h3) (Subgroup.inv_mem _ h2)
    · have e : gElt M 1 * hElt M 5 * (gElt M 1)⁻¹ = hElt M 6 * (hElt M 2)⁻¹ := by
        rw [hElt_five, hElt_six, hElt_two]
        group
      show gElt M 1 * hElt M 5 * (gElt M 1)⁻¹ ∈ HG M
      rw [e]
      exact Subgroup.mul_mem _ h6 (Subgroup.inv_mem _ h2)
    · have e : gElt M 1 * hElt M 6 * (gElt M 1)⁻¹ = hElt M 2 * hElt M 5 := by
        rw [hElt_six, hElt_five, hElt_two]
        group
      show gElt M 1 * hElt M 6 * (gElt M 1)⁻¹ ∈ HG M
      rw [e]
      exact Subgroup.mul_mem _ h2 h5
  intro x hx
  rw [← hf]
  exact hle ⟨x, hx, rfl⟩

theorem g1_mem_normalizer_HG : gElt M 1 ∈ Subgroup.normalizer (HG M : Set (adjointGroup .G2 K)) :=
  mem_normalizer_of_conj_le (conj_g1_mem_HG M)

theorem key_cosets : ∀ s ∈ PX M, s ∈ HG M ∨ (gElt M 1)⁻¹ * s ∈ HG M := by
  have h0 := mem_HG (M := M) (k := 0) (by norm_num)
  have h2 := mem_HG (M := M) (k := 2) (by norm_num)
  have h3 := mem_HG (M := M) (k := 3) (by norm_num)
  have h6 := mem_HG (M := M) (k := 6) (by norm_num)
  have hn := g1_mem_normalizer_HG M
  have hn' : ∀ x ∈ HG M, (gElt M 1)⁻¹ * x * (gElt M 1)⁻¹⁻¹ ∈ HG M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
  have hn1 : ∀ x ∈ HG M, gElt M 1 * x * (gElt M 1)⁻¹ ∈ HG M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  intro s hs
  unfold PX at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    interval_cases j
    · left
      rw [← hElt_zero]
      exact h0
    · right
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    · left
      rw [← hElt_three]
      exact h3
    · right
      have e : (gElt M 1)⁻¹ * gElt M 3 = (hElt M 2)⁻¹ * hElt M 6 := by
        rw [hElt_two, hElt_six]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h6
  | one =>
    left
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rcases ihx with hx' | hx' <;> rcases ihy with hy' | hy'
    · left
      exact Subgroup.mul_mem _ hx' hy'
    · right
      have e : (gElt M 1)⁻¹ * (x * y) =
          ((gElt M 1)⁻¹ * x * (gElt M 1)⁻¹⁻¹) * ((gElt M 1)⁻¹ * y) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hn' x hx') hy'
    · right
      rw [← mul_assoc]
      exact Subgroup.mul_mem _ hx' hy'
    · left
      have e : x * y = (gElt M 1 * ((gElt M 1)⁻¹ * x) * (gElt M 1)⁻¹) * (hElt M 2) *
          ((gElt M 1)⁻¹ * y) := by
        rw [hElt_two]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hn1 _ hx') h2) hy'
  | inv x hx ih =>
    rcases ih with h | h
    · left
      exact Subgroup.inv_mem _ h
    · right
      have e : (gElt M 1)⁻¹ * x⁻¹ = ((gElt M 1)⁻¹ * ((gElt M 1)⁻¹ * x)⁻¹ * (gElt M 1)⁻¹⁻¹) *
          (hElt M 2)⁻¹ := by
        rw [hElt_two]
        group
      rw [e]
      exact Subgroup.mul_mem _ (hn' _ (Subgroup.inv_mem _ h)) (Subgroup.inv_mem _ h2)

theorem VX_le_HG (heps : epsOK tzc gW = true) (hPS : PX M = SX M) : VX M ≤ HG M := by
  intro x hx
  have hxS : x ∈ PX M := hPS ▸ VX_le_SX M hx
  rcases key_cosets M x hxS with h | h
  · exact h
  · exfalso
    have h1 : Cen M ((gElt M 1)⁻¹ * x) := (mem_VX_iff M).mp (HG_le_VX M heps h)
    have h2 : Cen M x := (mem_VX_iff M).mp hx
    have h3 : Cen M ((gElt M 1)⁻¹ * x * x⁻¹) := h1.mul h2.inv'
    rw [mul_inv_cancel_right] at h3
    exact not_cen_of_inv M (inv_g1 M heps).inv' h3

theorem VX_eq_HG (heps : epsOK tzc gW = true) (hPS : PX M = SX M) : VX M = HG M :=
  le_antisymm (VX_le_HG M heps hPS) (HG_le_VX M heps)

theorem suHyp (hK : Nat.card K = 8) : SUHyp M := by
  obtain ⟨hPS, hcard, -⟩ := omega_facts M hK
  obtain ⟨D, hD⟩ := Certificates.certificate9558
  have heps := epsOK_gW_of hD.eps
  have h2 := card_SX_eq M heps
  refine ⟨by omega, VX_eq_HG M heps hPS⟩

end VSub

end CFSG.AGLEmbedding.KFactProofs.G28
