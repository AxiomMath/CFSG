module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ABGLocalTools CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section ChiefModelO

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_fixed_singular_O6 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEΩ : E ≤ StatedOmega (StatedQuadMinus 3 F b c)) (hE : IsPGroup 2 E) :
    ∃ w : OW F, w ≠ 0 ∧ quadMinus 3 F b c w = 0 ∧
      ∀ g ∈ E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.StandardType.OrthRestEnd.exists_fixed_singular (quadMinus 3 F b c) E hE
    (fun g hg v => quadMinus_mulVec_of_mem_statedOmega (hEΩ hg) v) ?_
  have hcard : (Nat.card {v : OW F // quadMinus 3 F b c v = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 2 hirr).1
  have hsucc : Nat.card {v : OW F // quadMinus 3 F b c v = 0} =
      Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} + 1 :=
    CFSG.StandardType.OrthRestEnd.card_singular_eq_succ (quadMinus 3 F b c)
  have hN : (Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} : ℤ) =
      ((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    have h := hcard
    rw [hsucc] at h
    push_cast at h
    linarith
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hevZ : Even (Nat.card F : ℤ) := (Int.even_coe_nat _).mpr hev
  have hodd : Odd (((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1)) :=
    Odd.mul ((hevZ.pow_of_ne_zero (by norm_num)).add_one)
      ((hevZ.pow_of_ne_zero (by norm_num)).sub_odd odd_one)
  intro hdvd
  have h2 : (2 : ℤ) ∣ (Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} : ℤ) := by
    exact_mod_cast hdvd
  rw [hN] at h2
  exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem polar_smul_fix {w : OW F} (g : ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (hg : g • w = w) (y : OW F) :
    polar (quadMinus 3 F b c) w (g • y) = polar (quadMinus 3 F b c) w y := by
  have h := polar_mulVec_of_mem_statedOmega g.2 w y
  have e : g • w = ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w := rfl
  rw [e] at hg
  rw [hg] at h
  exact h

def Qw (b c : F) (w : OW F) : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)) where
  carrier := {g | g • w = w ∧ ∀ y, polar (quadMinus 3 F b c) w y = 0 →
    g • y - y ∈ Submodule.span F {w}}
  mul_mem' := fun {g g'} hg hg' => by
    refine ⟨by rw [mul_smul, hg'.1, hg.1], fun y hy => ?_⟩
    have h1 := hg'.2 y hy
    have hy' : polar (quadMinus 3 F b c) w (g' • y) = 0 := by rw [polar_smul_fix g' hg'.1, hy]
    have h2 := hg.2 (g' • y) hy'
    rw [mul_smul]
    have : g • g' • y - y = (g • g' • y - g' • y) + (g' • y - y) := by abel
    rw [this]
    exact Submodule.add_mem _ h2 h1
  one_mem' := ⟨one_smul _ _, fun y _ => by simp⟩
  inv_mem' := fun {g} hg => by
    have hgw : g⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hg.1.symm
    refine ⟨hgw, fun y hy => ?_⟩
    have hy' : polar (quadMinus 3 F b c) w (g⁻¹ • y) = 0 := by rw [polar_smul_fix g⁻¹ hgw, hy]
    have h1 := hg.2 (g⁻¹ • y) hy'
    rw [smul_inv_smul] at h1
    have := Submodule.neg_mem _ h1
    simpa using this

theorem Qw_conj {w : OW F} {h : ↥(StatedOmega (StatedQuadMinus 3 F b c))} (hh : h • w = w)
    {q : ↥(StatedOmega (StatedQuadMinus 3 F b c))} (hq : q ∈ Qw b c w) :
    h * q * h⁻¹ ∈ Qw b c w := by
  have hhi : h⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hh.symm
  refine ⟨by rw [mul_smul, mul_smul, hhi, hq.1, hh], fun y hy => ?_⟩
  have hy' : polar (quadMinus 3 F b c) w (h⁻¹ • y) = 0 := by rw [polar_smul_fix h⁻¹ hhi, hy]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq.2 _ hy')
  have e : (h * q * h⁻¹) • y - y = h • (q • h⁻¹ • y - h⁻¹ • y) := by
    rw [smul_sub, smul_smul, smul_smul, smul_inv_smul h y, mul_smul]
  rw [e, ← hc, smul_comm, hh]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)

theorem omega_ext_smul {g : ↥(StatedOmega (StatedQuadMinus 3 F b c))} (h : ∀ x : OW F, g • x = x) :
    g = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  have e : g • (Pi.single j (1 : F) : OW F) = ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        Pi.single j (1 : F) := rfl
  rw [e, Matrix.mulVec_single_one] at this
  simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this

theorem Qw_pow_four (h2 : (2 : F) = 0) {w : OW F}
    {q : ↥(StatedOmega (StatedQuadMinus 3 F b c))} (hq : q ∈ Qw b c w) : q * q * q * q = 1 := by
  refine omega_ext_smul fun x => ?_
  have h4 : ∀ y : OW F, y + y = 0 := fun y => by rw [← two_smul F y, h2, zero_smul]
  set a := q • x - x with hadef
  have ha : polar (quadMinus 3 F b c) w a = 0 := by
    rw [hadef, polar_sub_right, polar_smul_fix q hq.1, sub_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq.2 a ha)
  have hqb : q • (c • w) = c • w := by rw [smul_comm, hq.1]
  have e1 : q • x = x + a := by rw [hadef]; abel
  have e2 : q • a = a + c • w := by rw [hc]; abel
  have e3 : q • q • x = x + c • w := by
    rw [e1, smul_add, e1, e2]
    calc x + a + (a + c • w) = x + (a + a) + c • w := by abel
      _ = x + c • w := by rw [h4 a, add_zero]
  have e4 : q • q • (x + c • w) = x := by
    rw [smul_add, smul_add, e3, hqb, hqb]
    calc x + c • w + c • w = x + (c • w + c • w) := by abel
      _ = x := by rw [h4, add_zero]
  calc (q * q * q * q) • x = q • q • (q • q • x) := by simp only [mul_smul]
    _ = x := by rw [e3, e4]

theorem exists_perp_not_span (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w : OW F} (hw0 : w ≠ 0) :
    ∃ z : OW F, polar (quadMinus 3 F b c) w z = 0 ∧ z ∉ Submodule.span F {w} := by
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.BilinForm.orthogonal (polarBilin (quadMinus 3 F b c))
      (Submodule.span F {w}) ≤ Submodule.span F {w} := by
    intro z hz
    apply hcon z
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
    have := hz w (Submodule.mem_span_singleton_self w)
    simpa [LinearMap.BilinForm.IsOrtho, polarBilin_apply_apply] using this
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQn, finrank_span_singleton hw0] at h1
  have h6 : Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

theorem fix_Qw_subset (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w : OW F} (hw0 : w ≠ 0)
    (hw : quadMinus 3 F b c w = 0) {y : OW F} (hy : ∀ s ∈ Qw b c w, s • y = y) :
    y ∈ Submodule.span F {w} := by
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hE : ∀ z, polar (quadMinus 3 F b c) w z = 0 → eichler (quadMinus 3 F b c) w z y = y := by
    intro z hz
    obtain ⟨A, hAΩ, hA⟩ := eichler_mem_statedOmega hirr w z
    let g : ↥(StatedOmega (StatedQuadMinus 3 F b c)) := ⟨A, hAΩ⟩
    have e : ∀ y' : OW F, g • y' = (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y' := fun y' => rfl
    have hgw : g • w = w := by
      rw [e, hA, eichler_apply_self]
    have hg : g ∈ Qw b c w := by
      refine ⟨hgw, fun y' hy' => ?_⟩
      have hy'' : polar (quadMinus 3 F b c) y' w = 0 := by rw [polar_comm]; exact hy'
      rw [e, hA, eichler_apply hw hz, hy'', zero_smul, add_zero, mul_zero, add_zero]
      have : y' - polar (quadMinus 3 F b c) y' z • w - y' =
          -(polar (quadMinus 3 F b c) y' z • w) := by abel
      rw [this]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
    have := hy g hg
    rw [e, hA] at this
    exact this
  have hyw : polar (quadMinus 3 F b c) y w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzn⟩ := exists_perp_not_span hirr hw0
    have h := hE z hz
    rw [eichler_apply hw hz] at h
    have h3 : polar (quadMinus 3 F b c) y w • z -
        (polar (quadMinus 3 F b c) y z + quadMinus 3 F b c z * polar (quadMinus 3 F b c) y w) • w
          = 0 := by
      have e0 : polar (quadMinus 3 F b c) y w • z -
          (polar (quadMinus 3 F b c) y z + quadMinus 3 F b c z * polar (quadMinus 3 F b c) y w) • w
          = (y + polar (quadMinus 3 F b c) y w • z -
          (polar (quadMinus 3 F b c) y z + quadMinus 3 F b c z * polar (quadMinus 3 F b c) y w) • w)
            - y := by abel
      rw [e0]
      exact sub_eq_zero.mpr h
    have h4 := sub_eq_zero.mp h3
    apply hzn
    have : z = (polar (quadMinus 3 F b c) y w)⁻¹ •
        ((polar (quadMinus 3 F b c) y z + quadMinus 3 F b c z * polar (quadMinus 3 F b c) y w) • w) := by
      rw [← h4, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
  by_contra hyn
  obtain ⟨z, hz, hzn⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_polar_ne_zero hQn
    (U₀ := Submodule.span F {w}) hyn
  have hz' : polar (quadMinus 3 F b c) w z = 0 := by
    have := hz w (Submodule.mem_span_singleton_self w)
    exact this
  have h := hE z hz'
  rw [eichler_apply hw hz', hyw, zero_smul, add_zero, mul_zero, add_zero] at h
  have h3 : polar (quadMinus 3 F b c) y z • w = 0 := sub_eq_self.mp h
  rcases smul_eq_zero.mp h3 with h5 | h5
  · exact hzn h5
  · exact hw0 h5

theorem pgroup_le_sylow_of_normal {G : Type*} [Group G] [Finite G] {T M N : Subgroup G}
    (hT : IsSylowOf 2 T M) (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hN : IsPGroup 2 ↥N) : N ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := hT.isPGroup.to_sup_of_normal_right' hN (hT.le.trans hMN)
  have h := hT.eq_of_le le_sup_left (sup_le hT.le hNM) hsup
  exact (le_sup_right : N ≤ T ⊔ N).trans h.le

theorem chief_model_O6 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n p : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c))} (hE : IsSylowOf 2 E ⊤) :
    ∃ Q : Subgroup ↥(StatedOmega (StatedQuadMinus 3 F b c)), Q ≤ E ∧
      ∃ x : ↥(StatedOmega (StatedQuadMinus 3 F b c)),
        x ∈ Subgroup.normalizer (Q : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) ∧
        x ≠ 1 ∧ x ^ p = 1 ∧ ∀ y : OW F, (∀ s ∈ Q, s • y = y) → x • y = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨w, hw0, hw, hwfix⟩ := exists_fixed_singular_O6 hirr hF hn
    (E := E.map (StatedOmega (StatedQuadMinus 3 F b c)).subtype)
    (Subgroup.map_subtype_le E) (hE.isPGroup.map _)
  have hst : ∀ g ∈ E, g ∈ MulAction.stabilizer ↥(StatedOmega (StatedQuadMinus 3 F b c)) w :=
    fun g hg => MulAction.mem_stabilizer_iff.mpr (hwfix _ ⟨g, hg, rfl⟩)
  have hE' : IsSylowOf 2 E (MulAction.stabilizer ↥(StatedOmega (StatedQuadMinus 3 F b c)) w) :=
    hE.of_le hst le_top
  have hQst : Qw b c w ≤ MulAction.stabilizer ↥(StatedOmega (StatedQuadMinus 3 F b c)) w :=
    fun q hq => MulAction.mem_stabilizer_iff.mpr hq.1
  have hnorm : MulAction.stabilizer ↥(StatedOmega (StatedQuadMinus 3 F b c)) w ≤
      Subgroup.normalizer (Qw b c w : Set ↥(StatedOmega (StatedQuadMinus 3 F b c))) := by
    intro h hh
    have hh' := MulAction.mem_stabilizer_iff.mp hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact Qw_conj hh' hk
    · intro hk
      have hhi : h⁻¹ • w = w := by rw [inv_smul_eq_iff]; exact hh'.symm
      have := Qw_conj hhi hk
      simpa [mul_assoc] using this
  have hQ2 : IsPGroup 2 ↥(Qw b c w) := fun q => ⟨2, Subtype.ext (by
    have h4 : (q : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ^ (2 ^ 2) = q * q * q * q := by
      norm_num [pow_succ, mul_assoc]
    show (q : ↥(StatedOmega (StatedQuadMinus 3 F b c))) ^ (2 ^ 2) = 1
    rw [h4]
    exact Qw_pow_four h2 q.2)⟩
  have hQE : Qw b c w ≤ E := pgroup_le_sylow_of_normal hE' hQst hnorm hQ2
  have hpq' : p ∣ Nat.card F + 1 := by
    rw [hF]
    exact hpq
  obtain ⟨M⟩ := nonempty_normModel hirr hF hn
  obtain ⟨k, Ep, hk, hEpΩ, hEpa, hEpc, hEpfix⟩ := exists_stab_ne_zero M hirr hp hpq' hw0
  have hnt : Nontrivial ↥Ep := by
    have : 1 < Nat.card ↥Ep := by
      rw [hEpc]
      exact Nat.one_lt_pow (by omega) hp.one_lt
    exact Finite.one_lt_card_iff_nontrivial.mp this
  obtain ⟨g, hg1⟩ := exists_ne (1 : ↥Ep)
  let x : ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    ⟨(g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F), hEpΩ g.2⟩
  have hxw : x • w = w := hEpfix g g.2
  refine ⟨Qw b c w, hQE, x, hnorm (MulAction.mem_stabilizer_iff.mpr hxw), ?_, ?_, ?_⟩
  · intro hx
    apply hg1
    exact Subtype.ext (congrArg (fun t : ↥(StatedOmega (StatedQuadMinus 3 F b c)) =>
      (t : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)) hx)
  · refine Subtype.ext ?_
    simpa using hEpa.2 (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) g.2
  · intro y hy
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp (fix_Qw_subset hirr hw0 hw hy)
    rw [smul_comm, hxw]

end ChiefModelO

end CFSG.LocalAnalysis.RankThreeUC
