module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutD
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutR

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

structure StdGrp (b c : F) (E : Subgroup (GL6 F)) : Prop where
  pel : ∀ g ∈ E, PEl b c g
  sq : ∀ g ∈ E, g * g = 1
  comm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g

@[expose] noncomputable def rhoHom {E : Subgroup (GL6 F)} (hE : StdGrp b c E) :
    ↥E →* Matrix (Fin 2) (Fin 2) F where
  toFun g := rho (g : GL6 F)
  map_one' := rho_one
  map_mul' g h := rho_mul (hE.pel _ g.2) (hE.pel _ h.2)

@[expose] noncomputable def tHom {E : Subgroup (GL6 F)} (hE : StdGrp b c E) :
    ↥E →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (tc (g : GL6 F))
  map_one' := by
    show Multiplicative.ofAdd (tc (1 : GL6 F)) = 1
    rw [tc_one]
    rfl
  map_mul' g h := by
    show Multiplicative.ofAdd (tc ((g : GL6 F) * (h : GL6 F))) =
      Multiplicative.ofAdd (tc (g : GL6 F)) * Multiplicative.ofAdd (tc (h : GL6 F))
    rw [tc_mul_eq (hE.pel _ g.2) (hE.pel _ h.2)]
    rfl

theorem rhoHom_apply {E : Subgroup (GL6 F)} (hE : StdGrp b c E) (g : ↥E) :
    rhoHom hE g = rho (g : GL6 F) := rfl

theorem PEl.rho_iso {g : GL6 F} (h : PEl b c g) (p q : F) :
    Nf b c (rho g 0 0 * p + rho g 0 1 * q) (rho g 1 0 * p + rho g 1 1 * q) = Nf b c p q := by
  have hy0 : gv g (nvec F p q) (Sum.inr (Sum.inl idx0)) = 0 := by rw [h.y0, nvec_inr_inl]
  have hy1 : gv g (nvec F p q) (Sum.inr (Sum.inl idx1)) = 0 := by
    rw [h.y1, nvec_inr_inl, nvec_inr_inl]
    ring
  have hn0 := h.coordN (nvec F p q) 0
  have hn1 := h.coordN (nvec F p q) 1
  rw [nvec_inr_inl, nvec_inr_inl, nvec_n0, nvec_n1] at hn0 hn1
  have hQ := h.iso (nvec F p q)
  rw [Q_coords, hy0, hy1, hn0, hn1, quad_nvec] at hQ
  simp only [Nf]
  linear_combination hQ

theorem mulVec_add_one (ρ : Matrix (Fin 2) (Fin 2) F) (m : Fin 2 → F) (k : Fin 2) :
    ((ρ + 1) *ᵥ m) k = ρ k 0 * m 0 + ρ k 1 * m 1 + m k := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem PEl.constraint_vec {g a : GL6 F} (hg : PEl b c g) (ha : PEl b c a) (hg0 : tc g = 0)
    (hg1 : rho g = 1) (hcomm : g * a = a * g) :
    (rho a + 1) *ᵥ (fun k => mcol g idx1 k) = 0 ∧
      (rho a + 1) *ᵥ (fun k => mcol g idx0 k) = tc a • (fun k => mcol g idx1 k) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  constructor
  · funext k
    obtain ⟨-, h⟩ := hg.comm_constraint ha hg0 hg1 hcomm k
    rw [mulVec_add_one, Pi.zero_apply]
    linear_combination h + mcol g idx1 k * h2
  · funext k
    obtain ⟨h, -⟩ := hg.comm_constraint ha hg0 hg1 hcomm k
    rw [mulVec_add_one, Pi.smul_apply, smul_eq_mul]
    linear_combination h + mcol g idx0 k * h2

theorem PEl.m1_zero {g h : GL6 F} (hg : PEl b c g) (hh : PEl b c h) (hg0 : tc g = 0)
    (hg1 : rho g = 1) (hh1 : rho h = 1) (hht : tc h ≠ 0) (hcomm : g * h = h * g) (k : Fin 2) :
    mcol g idx1 k = 0 := by
  obtain ⟨h0, -⟩ := hg.comm_constraint hh hg0 hg1 hcomm k
  have r00 : rho h 0 0 = 1 := by rw [hh1, Matrix.one_apply_eq]
  have r11 : rho h 1 1 = 1 := by rw [hh1, Matrix.one_apply_eq]
  have r01 : rho h 0 1 = 0 := by rw [hh1, Matrix.one_apply_ne (by decide)]
  have r10 : rho h 1 0 = 0 := by rw [hh1, Matrix.one_apply_ne (by decide)]
  have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases hk k with rfl | rfl
  · rw [r00, r01] at h0
    have : tc h * mcol g idx1 0 = 0 := by linear_combination -h0
    exact (mul_eq_zero.mp this).resolve_left hht
  · rw [r10, r11] at h0
    have : tc h * mcol g idx1 1 = 0 := by linear_combination -h0
    exact (mul_eq_zero.mp this).resolve_left hht

theorem card_le_of_std (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {E : Subgroup (GL6 F)}
    (hE : StdGrp b c E) (hout : ¬ E ≤ StatedOmega (StatedQuadMinus 3 F b c)) :
    Nat.card ↥E ≤ 2 * Nat.card F ^ 3 := by
  classical
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨a, ha⟩ : ∃ a : ↥E, rho (a : GL6 F) ≠ 1 := by
    by_contra hcon
    refine hout fun g hg => (hE.pel g hg).mem_omega_of_rho hirr ?_
    by_contra hne
    exact hcon ⟨⟨g, hg⟩, hne⟩
  have hsq : ∀ g : ↥E, rho (g : GL6 F) * rho (g : GL6 F) = 1 := fun g => by
    rw [← rho_mul (hE.pel _ g.2) (hE.pel _ g.2), hE.sq _ g.2, rho_one]
  have hcomm' : ∀ x y : ↥E,
      rho (x : GL6 F) * rho (y : GL6 F) = rho (y : GL6 F) * rho (x : GL6 F) := fun x y => by
    rw [← rho_mul (hE.pel _ x.2) (hE.pel _ y.2), ← rho_mul (hE.pel _ y.2) (hE.pel _ x.2),
      hE.comm _ x.2 _ y.2]
  set K₁ : Subgroup ↥E := (rhoHom hE).ker with hK₁
  have hmemK₁ : ∀ x : ↥E, x ∈ K₁ ↔ rho (x : GL6 F) = 1 := fun x => by
    rw [hK₁, MonoidHom.mem_ker, rhoHom_apply]
  have hidx : K₁.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨a, fun h => ha ((hmemK₁ a).1 h), fun x => ?_⟩
    by_cases hx : rho (x : GL6 F) = 1
    · exact Or.inr ((hmemK₁ x).2 hx)
    · left
      rw [hmemK₁]
      have hxa : rho ((x * a : ↥E) : GL6 F) = rho (x : GL6 F) * rho (a : GL6 F) :=
        rho_mul (hE.pel _ x.2) (hE.pel _ a.2)
      rcases commuting_involutions_eq hirr (hE.pel _ x.2).rho_iso (hE.pel _ a.2).rho_iso
        (hsq x) (hsq a) (hcomm' x a) with h | h | h
      · exact absurd h hx
      · exact absurd h ha
      · rw [hxa, h]
        exact hsq a
  have hE1 : Nat.card ↥K₁ * 2 = Nat.card ↥E := by
    have := Subgroup.card_mul_index K₁
    rwa [hidx] at this
  suffices hK : Nat.card ↥K₁ ≤ Nat.card F ^ 3 by omega
  let tK : ↥K₁ →* Multiplicative F := (tHom hE).comp K₁.subtype
  set K₂ : Subgroup ↥K₁ := tK.ker with hK₂
  have hcardK : Nat.card ↥K₂ * Nat.card ↥tK.range = Nat.card ↥K₁ :=
    Subgroup.card_ker_mul_card_range tK
  have hrange : Nat.card ↥tK.range ≤ Nat.card F := by
    calc Nat.card ↥tK.range ≤ Nat.card (Multiplicative F) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card F := Nat.card_congr Multiplicative.toAdd
  set ν : Matrix (Fin 2) (Fin 2) F := rho (a : GL6 F) + 1 with hν
  have hν0 : ν ≠ 0 := by
    intro h0
    apply ha
    ext i j
    have := congrFun (congrFun h0 i) j
    simp only [hν, Matrix.add_apply, Matrix.zero_apply] at this
    exact eq_of_add_eq_zero_char_two this
  let gx : ↥K₂ → GL6 F := fun x => (((x : ↥K₁) : ↥E) : GL6 F)
  have hgxE : ∀ x : ↥K₂, gx x ∈ E := fun x => ((x : ↥K₁) : ↥E).2
  have hgxrho : ∀ x : ↥K₂, rho (gx x) = 1 := fun x => (hmemK₁ _).1 (x : ↥K₁).2
  have hgxtc : ∀ x : ↥K₂, tc (gx x) = 0 := fun x => by
    have h1 : Multiplicative.ofAdd (tc (gx x)) = 1 := MonoidHom.mem_ker.mp x.2
    exact ofAdd_eq_one.mp h1
  have hrad : ∀ x : ↥K₂, RadHyp b c (gx x) := fun x =>
    (hE.pel _ (hgxE x)).radHyp (hgxtc x) (hgxrho x)
  let mm : ↥K₂ → (Fin 2 → F) × (Fin 2 → F) := fun x =>
    (fun k => mcol (gx x) idx0 k, fun k => mcol (gx x) idx1 k)
  let ss : ↥K₂ → F := fun x => gv (gx x) (fV F idx0) (Sum.inl idx1)
  have hinj : Function.Injective (fun x : ↥K₂ => (mm x, ss x)) := by
    intro x y hxy
    have hmm : mm x = mm y := congrArg Prod.fst hxy
    have hs : ss x = ss y := congrArg Prod.snd hxy
    have hm : ∀ (i : Fin (3 - 1)) (k : Fin 2),
        gv (gx x) (fV F i) (Sum.inr (Sum.inr k)) = gv (gx y) (fV F i) (Sum.inr (Sum.inr k)) := by
      intro i k
      have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
      rcases hi i with rfl | rfl
      · exact congrFun (congrArg Prod.fst hmm) k
      · exact congrFun (congrArg Prod.snd hmm) k
    exact Subtype.ext (Subtype.ext (Subtype.ext (RadHyp.ext_params (hrad x) (hrad y) hm hs)))
  have key : ∀ P : (Fin 2 → F) × (Fin 2 → F) → Prop, (∀ x : ↥K₂, P (mm x)) →
      Nat.card ↥K₂ ≤ Nat.card {m // P m} * Nat.card F := by
    intro P hP
    have hinj' : Function.Injective
        (fun x : ↥K₂ => ((⟨mm x, hP x⟩ : {m // P m}), ss x)) := by
      intro x y hxy
      apply hinj
      have h1 := congrArg Prod.fst hxy
      have h2 := congrArg Prod.snd hxy
      exact Prod.ext (congrArg Subtype.val h1) h2
    calc Nat.card ↥K₂ ≤ Nat.card ({m // P m} × F) := Nat.card_le_card_of_injective _ hinj'
      _ = Nat.card {m // P m} * Nat.card F := Nat.card_prod _ _
  have hcons : ∀ x : ↥K₂, ν *ᵥ (mm x).2 = 0 ∧ ν *ᵥ (mm x).1 = tc (a : GL6 F) • (mm x).2 := fun x =>
    PEl.constraint_vec (hE.pel _ (hgxE x)) (hE.pel _ a.2) (hgxtc x) (hgxrho x)
      (hE.comm _ (hgxE x) _ a.2)
  by_cases hall : ∀ y : ↥K₁, tc (((y : ↥E)) : GL6 F) = 0
  ·
    have hr1 : Nat.card ↥tK.range ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun x y => ?_⟩
      obtain ⟨x', hx'⟩ := x.2
      obtain ⟨y', hy'⟩ := y.2
      apply Subtype.ext
      rw [← hx', ← hy']
      have e : ∀ z : ↥K₁, tK z = 1 := fun z => by
        show Multiplicative.ofAdd (tc (((z : ↥E)) : GL6 F)) = 1
        rw [hall z]
        rfl
      rw [e x', e y']
    have hK2 : Nat.card ↥K₂ ≤ Nat.card F ^ 2 * Nat.card F :=
      (key (fun m => ν *ᵥ m.2 = 0 ∧ ν *ᵥ m.1 = tc (a : GL6 F) • m.2) hcons).trans
        (Nat.mul_le_mul_right _ (card_pair_le ν hν0 (tc (a : GL6 F))))
    calc Nat.card ↥K₁ = Nat.card ↥K₂ * Nat.card ↥tK.range := hcardK.symm
      _ ≤ Nat.card ↥K₂ * 1 := Nat.mul_le_mul_left _ hr1
      _ ≤ Nat.card F ^ 2 * Nat.card F := by omega
      _ = Nat.card F ^ 3 := by ring
  ·
    push Not at hall
    obtain ⟨h, hh⟩ := hall
    have hh1 : rho ((h : ↥E) : GL6 F) = 1 := (hmemK₁ _).1 h.2
    have hm1 : ∀ x : ↥K₂, (mm x).2 = 0 := fun x => by
      funext k
      exact PEl.m1_zero (hE.pel _ (hgxE x)) (hE.pel _ (h : ↥E).2) (hgxtc x) (hgxrho x) hh1 hh
        (hE.comm _ (hgxE x) _ (h : ↥E).2) k
    have hK2 : Nat.card ↥K₂ ≤ Nat.card F * Nat.card F :=
      (key (fun m => m.2 = 0 ∧ ν *ᵥ m.1 = 0) (fun x => by
        refine ⟨hm1 x, ?_⟩
        have := (hcons x).2
        rw [hm1 x, smul_zero] at this
        exact this)).trans
        (Nat.mul_le_mul_right _ (card_pair_le' ν hν0))
    calc Nat.card ↥K₁ = Nat.card ↥K₂ * Nat.card ↥tK.range := hcardK.symm
      _ ≤ (Nat.card F * Nat.card F) * Nat.card F := Nat.mul_le_mul hK2 hrange
      _ = Nat.card F ^ 3 := by ring

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
