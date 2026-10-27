module

public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SRed
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SShape
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open scoped MatrixGroups
open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.Sec66T
  CFSG.Timmesfeld.ExceptionalOrders CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem even_geomSum_six {q : ℕ} (hq : Odd q) : Even (geomSum 6 1 q) := by
  have h : geomSum 6 1 q = (1 + q) * (1 + q ^ 2 + q ^ 4) := by
    simp [geomSum, Finset.sum_range_succ]
    ring
  have h1 : Even (1 + q) := by simpa [add_comm] using hq.add_odd odd_one
  rw [h]
  exact h1.mul_right _

section Glue


theorem noPNorm_char_glue {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {n r f : ℕ} [Fact r.Prime]
    (hm : LieModel Y t n r f) (ht : t ≠ .Tits)
    (hpar : ∀ (S : Sylow r Y) (P : Subgroup Y), P ≠ ⊤ →
      Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ P →
      ∃ a m : ℕ, Nat.card ↥P ∣ a ∧ Nat.card Y = a * m ∧ 2 ∣ m)
    {u : Y} {k : ℕ} (hk : Odd k) (hY : Nat.card Y = Nat.card ↥(centralizer ({u} : Set Y)) * k)
    {X : Subgroup Y} (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥)
    (hN : centralizer ({u} : Set Y) ≤ normalizer (X : Set Y)) : False := by
  obtain ⟨S, P, hPtop, hNX, -, -, hNS, -⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion Y t n r f hm X hX1 hX
  obtain ⟨a, m, hPa, hYam, hm2⟩ := hpar S P hPtop (hNS ht)
  have hDP : Nat.card ↥(centralizer ({u} : Set Y)) ∣ Nat.card ↥P :=
    Subgroup.card_dvd_of_le (hN.trans hNX)
  obtain ⟨e, he⟩ := hDP.trans hPa
  have hDpos : 0 < Nat.card ↥(centralizer ({u} : Set Y)) := Nat.card_pos
  have hke : k = e * m := by
    apply Nat.eq_of_mul_eq_mul_left hDpos
    calc Nat.card ↥(centralizer ({u} : Set Y)) * k = Nat.card Y := hY.symm
      _ = a * m := hYam
      _ = Nat.card ↥(centralizer ({u} : Set Y)) * (e * m) := by rw [he]; ring
  have h2k : 2 ∣ k := hm2.trans ⟨e, by rw [hke, mul_comm]⟩
  exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h2k)

end Glue

section Native


theorem g2_native_parity {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {r : ℕ} [Fact r.Prime]
    [CharP F r] (S : Sylow r ↥(adjointGroup Tag.G2 F)) (P : Subgroup ↥(adjointGroup Tag.G2 F))
    (hP : P ≠ ⊤)
    (hS : Subgroup.normalizer ((S : Subgroup ↥(adjointGroup Tag.G2 F)) : Set ↥(adjointGroup Tag.G2 F)) ≤ P) :
    ∃ a m : ℕ, Nat.card ↥P ∣ a ∧ Nat.card ↥(adjointGroup Tag.G2 F) = a * m ∧ 2 ∣ m := by
  classical
  have hfin : Finite (ModGL Tag.G2 F) := finite_modGL
  have hBC : borelGroup Tag.G2 F ≤ adjointGroup Tag.G2 F := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 F ≤ adjointGroup Tag.G2 F := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index r hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := g2Sub_exists_conj_le (hUp.toSylow hUi) S
    ((borelGroup Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) P
    (by rw [hUc]; exact g2Sub_borel_le_normalizer) hS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hP
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := g2Sub_exists_parabolic _ hg hP₁top
  obtain ⟨j, hj⟩ := g2Sub_exists_subset_singleton hJ
  obtain ⟨-, -, -, hle, -, -, hcell⟩ := standard_parabolic_cells Tag.G2 F
  have hP1card : Nat.card ↥(P.comap (MulAut.conj g).toMonoidHom) = Nat.card ↥P := by
    have hcomap : P.comap (MulAut.conj g).toMonoidHom = P.map (MulAut.conj g⁻¹).toMonoidHom := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · intro h
        exact ⟨g * x * g⁻¹, h, by group⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
    rw [hcomap]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hAle : (P.comap (MulAut.conj g).toMonoidHom).map (adjointGroup Tag.G2 F).subtype ≤
      parabolicSubgroup Tag.G2 F {j} := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hle J {j}).2 hj (hJP y hy)
  have hmapcard : Nat.card ↥((P.comap (MulAut.conj g).toMonoidHom).map
      (adjointGroup Tag.G2 F).subtype) = Nat.card ↥(P.comap (MulAut.conj g).toMonoidHom) :=
    Subgroup.card_map_of_injective (adjointGroup Tag.G2 F).subtype_injective
  have hPdvd : Nat.card ↥P ∣ Nat.card (parabolicSubgroup Tag.G2 F {j}) := by
    rw [← hP1card, ← hmapcard]
    exact Subgroup.card_dvd_of_le hAle
  have : Fintype (WeylGroup Tag.G2) := Fintype.ofFinite _
  have hC : Nat.card (adjointGroup Tag.G2 F) = Nat.card (torusGroup Tag.G2 F) *
      Nat.card F ^ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}.ncard *
        (geomSum 2 1 (Nat.card F) * geomSum 6 1 (Nat.card F)) := by
    rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_G2]
  have ha := hcell {j}
  refine ⟨Nat.card (parabolicSubgroup Tag.G2 F {j}), ?_⟩
  rcases g2Sub_finsum_parabolicWeyl (Set.Subset.refl ({j} : Set (Fin Tag.G2.rank))) (Nat.card F) with hs | hs
  · rw [hs, mul_one] at ha
    refine ⟨geomSum 2 1 (Nat.card F) * geomSum 6 1 (Nat.card F), hPdvd, ?_, ?_⟩
    · rw [hC, ha]
    · exact even_iff_two_dvd.mp ((even_geomSum_six hodd).mul_left _)
  · rw [hs] at ha
    refine ⟨geomSum 6 1 (Nat.card F), hPdvd, ?_, ?_⟩
    · have h2 : geomSum 2 1 (Nat.card F) = 1 + Nat.card F := by simp [geomSum, add_comm]
      rw [hC, ha, h2]
      ring
    · exact even_iff_two_dvd.mp (even_geomSum_six hodd)

end Native

section Model


theorem g2_parity {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hm : LieModel Y .G2 0 r f) (S : Sylow r Y) (P : Subgroup Y) (hP : P ≠ ⊤)
    (hS : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ P) :
    ∃ a m : ℕ, Nat.card ↥P ∣ a ∧ Nat.card Y = a * m ∧ 2 ∣ m := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact (hr.odd_of_ne_two hr2).pow
  have : Fintype F := Fintype.ofFinite F
  have : CharP F r := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  let S' : Sylow r ↥(adjointGroup Tag.G2 F) := S.mapSurjective (f := φ.toMonoidHom) φ.surjective
  let P' : Subgroup ↥(adjointGroup Tag.G2 F) := P.map φ.toMonoidHom
  have hP' : P' ≠ ⊤ := by
    intro h
    apply hP
    rw [eq_top_iff]
    intro y _
    have : φ y ∈ P' := h ▸ Subgroup.mem_top _
    obtain ⟨y', hy', hyy⟩ := this
    have : y' = y := φ.injective hyy
    rwa [← this]
  have hS' : Subgroup.normalizer ((S' : Subgroup ↥(adjointGroup Tag.G2 F)) : Set _) ≤ P' := by
    have h1 : ((S' : Subgroup ↥(adjointGroup Tag.G2 F))) = (S : Subgroup Y).map φ.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    rw [h1, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hS
  obtain ⟨a, m, hdvd, hcardC, hm2⟩ := g2_native_parity hodd S' P' hP' hS'
  refine ⟨a, m, ?_, ?_, hm2⟩
  · have e : Nat.card ↥P' = Nat.card ↥P := Subgroup.card_map_of_injective φ.injective
    rw [← e]
    exact hdvd
  · rw [Nat.card_congr φ.toEquiv]; exact hcardC


theorem g2_index_odd {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hm : LieModel Y .G2 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ k : ℕ, Odd k ∧ Nat.card Y = Nat.card ↥(centralizer ({u} : Set Y)) * k := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, hF, hFin, S, hcard, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hr hr2 hm u (orderOf_eq_two_of_inv hu hu1)
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact (hr.odd_of_ne_two hr2).pow
  have hD : Nat.card ↥(centralizer ({u} : Set Y)) =
      Nat.card F * (Nat.card F ^ 2 - 1) * (Nat.card F * (Nat.card F ^ 2 - 1)) :=
    shape_card S hodd hodd
  obtain ⟨F', hF', hFin', hcard', ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  have hY : Nat.card Y = CFSG.Open.ordG2 (r ^ f) := by
    rw [Nat.card_congr e.toEquiv]
    have := card_adjointGroup_G2 (K := F')
    rw [hcard'] at this
    exact this
  refine ⟨(r ^ f) ^ 4 * ((r ^ f) ^ 4 + (r ^ f) ^ 2 + 1), ?_, ?_⟩
  · have hq : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
    have hq4 : Odd ((r ^ f) ^ 4) := hq.pow
    have hq2 : Odd ((r ^ f) ^ 2) := hq.pow
    exact hq4.mul (Even.add_one (hq4.add_odd hq2))
  · rw [hY, hD, hcard]
    set q := r ^ f with hq
    have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hr.pos
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    unfold CFSG.Open.ordG2
    zify [h2, h6]
    ring

theorem g2_noPNorm_char {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hm : LieModel Y .G2 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1) {X : Subgroup Y}
    (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥) (hN : centralizer ({u} : Set Y) ≤ normalizer (X : Set Y)) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk, hY⟩ := g2_index_odd hr hr2 hm hu hu1
  exact noPNorm_char_glue hm (by decide) (fun S P hP hS => g2_parity hr hr2 hm S P hP hS) hk hY hX hX1 hN

end Model

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
