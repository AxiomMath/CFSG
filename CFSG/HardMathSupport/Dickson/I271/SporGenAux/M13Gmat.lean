module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Pure
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Planes
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Conj
public import Certificates.Certificate17421
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenA
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.M13

open CFSG.Monster CFSG.Monster.Generated CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.Gen13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
open scoped commutatorElement

theorem m13_facts :
    gw genD13W3 * gw genD13W1 = gw genD13W1 ^ 6 * gw genD13W3 ∧
    gw genD13W4 * gw genD13W1 = gw genD13W1 * gw genD13W4 ∧
    gw censusGW * gw genD13W1 = gw thirteenZ ^ 12 * gw censusGW := by
  have h := Certificates.certificate17421
  unfold m13Check at h
  have hp := agreeAll_sound h
  have p0 := hp (genD13W1 ++ genD13W3, genD13W3 ++ powL 6 genD13W1) (by simp [m13Pairs])
  have p1 := hp (genD13W1 ++ genD13W4, genD13W4 ++ genD13W1) (by simp [m13Pairs])
  have p2 := hp (genD13W1 ++ censusGW, censusGW ++ powL 12 thirteenZ) (by simp [m13Pairs])
  simp only [gw_append, gw_powL13] at p0 p1 p2
  exact ⟨p0, p1, p2⟩

section Pure


theorem pureData_Gmat : PureData (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw genD13W3)
    (gw genD13W4) (gw genD13W5) (gw genD13W6) (gw genD13W7) := by
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, ht, hx1x, hx1y, hx2x, hx2y, hy1z, hy1y, hy2z, hy2y,
    hy4z, hy4y⟩ := d13_gw_facts
  obtain ⟨hx1c, hx2c, -⟩ := m13_facts
  refine ⟨PlaneData.of_heis hd13 hc13 hc1 hcg hcd hdg, hc1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact mul_inv_eq_iff_eq_mul.2 hcg.symm
  · exact gd_conj hcg hcd hdg hc13
  · exact mul_inv_eq_iff_eq_mul.2 hy1z
  · exact mul_inv_eq_iff_eq_mul.2 (by rw [hy1y]; simp only [mul_assoc])
  · exact mul_inv_eq_iff_eq_mul.2 hy2z
  · exact mul_inv_eq_iff_eq_mul.2 (by rw [hy2y]; simp)
  · exact mul_inv_eq_iff_eq_mul.2 hy4z
  · exact mul_inv_eq_iff_eq_mul.2 (by rw [hy4y]; simp only [mul_assoc])
  · exact mul_inv_eq_iff_eq_mul.2 hx1c
  · exact mul_inv_eq_iff_eq_mul.2 hx2c

theorem pure_top
    (hGenD : Subgroup.closure (Set.range fun i : Fin genD13Gens.size => gw genD13Gens[i]) = ⊤) :
    Subgroup.closure (centSet (Subgroup.closure ({gw genD13W2, gw genD13W1} : Set Gmat))) = ⊤ := by
  have D := pureData_Gmat
  obtain ⟨-, -, -, -, -, -, -, ht, -⟩ := d13_gw_facts
  have hsz : genD13Gens.size = 9 := rfl
  show Subgroup.closure (centSet (Subgroup.closure ({gw genD13W2, gw genD13W1} : Set Gmat))) =
    ⊤
  rw [eq_top_iff, ← hGenD, Subgroup.closure_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  rw [hsz] at hi
  interval_cases i
  · exact D.g_mem
  · exact D.c_mem
  · exact D.d_mem
  · exact D.x1_mem
  · exact D.x2_mem
  · exact D.y1_mem
  · exact D.y2_mem
  · exact D.y4_mem
  · show gw genD13W8 ∈ _
    rw [ht]
    exact Subgroup.pow_mem _ D.x2_mem 3

end Pure

section Mixed


theorem mixed_top
    (hGen13 : Subgroup.closure (Set.range fun i : Fin gen13Gens.size => gw gen13Gens[i]) = ⊤) :
    Subgroup.closure (centSet (Subgroup.zpowers (gw thirteenX) ⊔ Subgroup.zpowers (gw thirteenZ))) =
      ⊤ := by
  obtain ⟨hx, hy, hcomm, hz, hzx, hzy⟩ := thirteen_gw_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := thirteen_commute_facts
  have hsz : gen13Gens.size = 9 := rfl
  have hx1 : gw thirteenX ≠ 1 := fun h =>
    hz (by rw [← hcomm, h]; exact commutatorElement_one_left _)
  have hxB : gw thirteenX ∈ Subgroup.zpowers (gw thirteenX) ⊔ Subgroup.zpowers (gw thirteenZ) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hzB : gw thirteenZ ∈ Subgroup.zpowers (gw thirteenX) ⊔ Subgroup.zpowers (gw thirteenZ) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [eq_top_iff, ← hGen13, Subgroup.closure_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  rw [hsz] at hi
  interval_cases i
  · exact Subgroup.subset_closure ⟨_, hxB, hx1, c1.eq⟩
  · exact Subgroup.subset_closure ⟨_, hxB, hx1, c2.eq⟩
  · exact Subgroup.subset_closure ⟨_, hxB, hx1, rfl⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, hzy.symm.eq⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, c3.eq⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, c4.eq⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, c5.eq⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, c6.eq⟩
  · exact Subgroup.subset_closure ⟨_, hzB, hz, c7.eq⟩

end Mixed

section LineConj

variable {G : Type*} [Group G]

theorem conj_pow_of {a c u : G} (h : a * c = u * a) (α : ℕ) : a * c ^ α = u ^ α * a := by
  have h1 : a * c * a⁻¹ = u := mul_inv_eq_iff_eq_mul.2 h
  have h2 : a * c ^ α * a⁻¹ = u ^ α := by rw [← conj_pow, h1]
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem comp_c {T G' X c t : G} {δ m : ℕ} (hX : X * c = c ^ δ * X) (hG : G' * c = c * G')
    (hT : T * c = t ^ m * T) : (T * (G' * X)) * c = t ^ (m * δ) * (T * (G' * X)) := by
  have hGp : G' * c ^ δ = c ^ δ * G' := ((Commute.pow_right (show Commute G' c from hG) δ)).eq
  have hTp : T * c ^ δ = t ^ (m * δ) * T := by rw [conj_pow_of hT δ, ← pow_mul]
  calc (T * (G' * X)) * c = T * (G' * (X * c)) := by simp only [mul_assoc]
    _ = T * ((G' * c ^ δ) * X) := by rw [hX]; simp only [mul_assoc]
    _ = T * (c ^ δ * (G' * X)) := by rw [hGp]; simp only [mul_assoc]
    _ = (T * c ^ δ) * (G' * X) := by simp only [mul_assoc]
    _ = t ^ (m * δ) * (T * (G' * X)) := by rw [hTp]; simp only [mul_assoc]

end LineConj

section Lines


theorem xword_c (xw : List Bool) :
    ∃ δ : ℕ, δ % 13 ≠ 0 ∧
      gw (xw.map fun l => if l then genD13W3 else genD13W4).flatten * gw genD13W1 =
        gw genD13W1 ^ δ * gw (xw.map fun l => if l then genD13W3 else genD13W4).flatten := by
  obtain ⟨hx1c, hx2c, -⟩ := m13_facts
  induction xw with
  | nil => exact ⟨1, by norm_num, by simp [gw_nil]⟩
  | cons b xs ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    simp only [List.map_cons, List.flatten_cons, gw_append]
    cases b
    · refine ⟨δ, hδ, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      rw [mul_assoc, hx2c, ← mul_assoc, h, mul_assoc]
    · refine ⟨δ * 6, by omega, ?_⟩
      simp only [if_true]
      rw [mul_assoc, hx1c, ← mul_assoc, conj_pow_of h 6, ← pow_mul, mul_assoc]

theorem line_conj_c (e : CensusLine) :
    ∃ δ : ℕ, δ % 13 ≠ 0 ∧
      gw (lineConjW e) * gw genD13W1 =
        (if e.toC then gw genD13W2 else gw thirteenZ) ^ (12 * δ) * gw (lineConjW e) := by
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, ht, hx1x, hx1y, hx2x, hx2y, hy1z, hy1y, hy2z, hy2y,
    hy4z, hy4y⟩ := d13_gw_facts
  obtain ⟨-, -, hcen⟩ := m13_facts
  obtain ⟨δ, hδ, hX⟩ := xword_c e.xw
  refine ⟨δ, hδ, ?_⟩
  have hG : gw (powL e.j (if e.corrG then genD13W0 else genD13W2)) * gw genD13W1 =
      gw genD13W1 * gw (powL e.j (if e.corrG then genD13W0 else genD13W2)) := by
    rw [gw_powL13]
    cases e.corrG
    · exact ((show Commute (gw genD13W2) (gw genD13W1) from hcd.symm).pow_left e.j).eq
    · exact ((show Commute (gw genD13W0) (gw genD13W1) from hcg.symm).pow_left e.j).eq
  unfold lineConjW
  simp only [gw_append]
  cases hC : e.toC
  · simp only [Bool.false_eq_true, if_false]
    exact comp_c hX hG hcen
  · simp only [if_true]
    exact comp_c hX hG hy2z

end Lines

section Final


theorem line_plane_conj (e : CensusLine) (he : e ∈ censusLines) (μ : ℕ) (hμ : μ % 13 ≠ 0) :
    (Subgroup.zpowers ((gw genD13W0 ^ e.a * gw genD13W2 ^ e.b) ^ μ) ⊔
        Subgroup.zpowers (gw genD13W1)).map (MulAut.conj (gw (lineConjW e))).toMonoidHom =
      if e.toC then Subgroup.zpowers (gw genD13W1) ⊔ Subgroup.zpowers (gw genD13W2)
      else Subgroup.zpowers (gw thirteenX) ⊔ Subgroup.zpowers (gw thirteenZ) := by
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, -⟩ := d13_gw_facts
  have hplane := PlaneData.of_heis hd13 hc13 hc1 hcg hcd hdg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlines⟩ := thirteen_a_facts
  obtain ⟨hx, -, hcomm, hz, hzx, -⟩ := thirteen_gw_facts
  obtain ⟨δ, hδ, hWc⟩ := line_conj_c e
  have hWrep := hlines e he
  have hshape : e.lam % 13 ≠ 0 := by
    have h := lines_shape
    rw [List.all_eq_true] at h
    have h1 := h e he
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
    exact h1.2
  have hrep : gw (lineRepW e) = gw genD13W0 ^ e.a * gw genD13W2 ^ e.b := by
    rw [lineRepW, gw_append, gw_powL13, gw_powL13]
  have hco : orderOf (gw genD13W1) = 13 := orderOf_eq_prime hc13 hc1
  have hdo : orderOf (gw genD13W2) = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    refine orderOf_eq_prime hd13 fun h => ?_
    have := (hplane.ind 1 0 (by simp [h])).1
    omega
  have hx1 : gw thirteenX ≠ 1 := fun h =>
    hz (by rw [← hcomm, h]; exact commutatorElement_one_left _)
  have hxo : orderOf (gw thirteenX) = 13 := orderOf_eq_prime hx hx1
  have hz13 : gw thirteenZ ^ 13 = 1 := by
    have hzx' : Commute ⁅gw thirteenX, gw thirteenY⁆ (gw thirteenX) := by
      rw [hcomm]; exact hzx
    have h13 := CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx' 13
    rw [hcomm, hx, commutatorElement_one_left] at h13
    exact h13
  have hzo : orderOf (gw thirteenZ) = 13 := orderOf_eq_prime hz13 hz
  have hlamμ : (e.lam * μ) % 13 ≠ 0 := by
    intro h0
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 (Nat.dvd_of_mod_eq_zero h0) with h | h
    · exact hshape (Nat.mod_eq_zero_of_dvd h)
    · exact hμ (Nat.mod_eq_zero_of_dvd h)
  have hδ12 : (12 * δ) % 13 ≠ 0 := by omega
  have key : ∀ t : Gmat, gw (lineTargetW e) = t →
      gw (lineConjW e) * (gw genD13W0 ^ e.a * gw genD13W2 ^ e.b) ^ μ * (gw (lineConjW e))⁻¹ =
        t ^ (e.lam * μ) := by
    intro t ht
    have h1 : gw (lineConjW e) * (gw genD13W0 ^ e.a * gw genD13W2 ^ e.b) * (gw (lineConjW e))⁻¹ =
        t ^ e.lam := by
      apply mul_inv_eq_iff_eq_mul.2
      rw [← hrep, ← ht]
      exact hWrep
    rw [pow_mul, ← h1, conj_pow]
  cases hC : e.toC
  · rw [hC] at hWc
    simp only [Bool.false_eq_true, if_false] at hWc ⊢
    have ht : gw (lineTargetW e) = gw thirteenX := by
      unfold lineTargetW; simp [hC]
    exact conj_plane_eq hxo hzo hlamμ hδ12 (key _ ht) (mul_inv_eq_iff_eq_mul.2 hWc)
  · rw [hC] at hWc
    simp only [if_true] at hWc ⊢
    have ht : gw (lineTargetW e) = gw genD13W1 := by
      unfold lineTargetW; simp [hC]
    exact conj_plane_eq hco hdo hlamμ hδ12 (key _ ht) (mul_inv_eq_iff_eq_mul.2 hWc)

end Final

theorem hcov_lines : ∀ a b : ℕ, a < 13 → b < 13 → (a ≠ 0 ∨ b ≠ 0) →
    ∃ e ∈ (censusLines.map fun e => (e.a, e.b)), ∃ μ : ℕ, μ % 13 ≠ 0 ∧
      (μ * e.1) % 13 = a ∧ (μ * e.2) % 13 = b := by
  intro a b ha hb hab
  have hcov := lines_cover
  rw [List.all_eq_true] at hcov
  have h1 := hcov a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with ⟨rfl, rfl⟩ | h2
  · exact absurd hab (by simp)
  · unfold lineCovered at h2
    rw [List.any_eq_true] at h2
    obtain ⟨e, he, hμ⟩ := h2
    rw [List.any_eq_true] at hμ
    obtain ⟨μ, hμ13, hμe⟩ := hμ
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hμe
    obtain ⟨⟨hμ0, hae⟩, hbe⟩ := hμe
    refine ⟨(e.a, e.b), List.mem_map.2 ⟨e, he, rfl⟩, μ, ?_, hae, hbe⟩
    rw [Nat.mod_eq_of_lt (List.mem_range.1 hμ13)]
    exact hμ0

section Final2


theorem centGen_Gmat_thirteen (hG : (Nat.card Gmat).factorization 13 = 3)
    (hGenD : Subgroup.closure (Set.range fun i : Fin genD13Gens.size => gw genD13Gens[i]) = ⊤)
    (hGen13 : Subgroup.closure (Set.range fun i : Fin gen13Gens.size => gw gen13Gens[i]) = ⊤) :
    CentGen 13 Gmat := by
  haveI : Finite Gmat := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hG; simp at hG)
  intro P hPel hPcard
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, -⟩ := d13_gw_facts
  obtain ⟨h, e', he', μ, hμ, hPh⟩ := exists_conj_line hg13 hd13 hc13 hc1 hcg hcd hdg hG
    (censusLines.map fun e => (e.a, e.b)) hcov_lines hPel hPcard
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
  have hconj := line_plane_conj e he μ hμ
  have hQ : Subgroup.closure (centSet (if e.toC then Subgroup.zpowers (gw genD13W1) ⊔
      Subgroup.zpowers (gw genD13W2) else Subgroup.zpowers (gw thirteenX) ⊔
        Subgroup.zpowers (gw thirteenZ))) = ⊤ := by
    cases e.toC
    · simpa using mixed_top hGen13
    · have := pure_top hGenD
      rw [closure_pair_eq, sup_comm] at this
      simpa using this
  have h1 := closure_centSet_of_map_eq (MulAut.conj (gw (lineConjW e))) hconj hQ
  exact closure_centSet_of_map_eq (MulAut.conj h) hPh h1

end Final2

end CFSG.HardMathSupport.Dickson.I271.M13
