module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPhiM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls2
public import Certificates.Certificate27822

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

section PhiZ

variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M}

theorem zeta_tab {c : ℕ} (hc : c < 128) : (repArrs[8]!)[c]! = ixP (zD (decD c)) (c % 32) := by
  have h := Certificates.certificate27822.2.1
  simp only [zetaCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h c hc

theorem twist_facts : b0Idx < 128 ∧ (repArrs[8]!)[b0Idx]! = b0Idx ∧ mulC b0Idx b0Idx = tC ∧
    ∀ i < 128, (repArrs[7]!)[i]! = (repArrs[8]!)[mulC (mulC b0Idx i) (invC b0Idx)]! := by
  have h := Certificates.certificate27822.2.2.1
  simp only [twistCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem fus_facts {j : ℕ} (hj : j = 4 ∨ j = 7 ∨ j = 8) :
    fusTab[j]! < 128 ∧ (repArrs[j]!)[fusTab[j]!]! = mulC fusTab[j]! tC := by
  have h := Certificates.certificate27822.2.2.2
  simp only [fusCheck, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  rcases hj with rfl | rfl | rfl
  · exact h 4 (Or.inl rfl)
  · exact h 7 (Or.inr (Or.inl rfl))
  · exact h 8 (Or.inr (Or.inr rfl))

@[expose] noncomputable def b0Elt {D : Subgroup M} (eD : D ≃* DihedralGroup 4) (eltE : ℕ → M) : M :=
  labD eD eltE b0Idx

namespace DECtx

variable (hctx : DECtx D E eD t eltE) [hW : (D ⊔ E).Normal]

include hctx

theorem lab_invC {x : ℕ} (hx : x < 128) : labD eD eltE (invC x) = (labD eD eltE x)⁻¹ := by
  have h := hctx.tabLab.mul x hx (invC x) (invC_lt hx)
  rw [mulC_invC hx, hctx.lab_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem z_act {z : M} (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4) {c : ℕ} (hc : c < 128) :
    z * labD eD eltE c * z⁻¹ = labD eD eltE (repArrs[8]!)[c]! := by
  have hD : ∀ i < 8, z * sElt eD i * z⁻¹ = sElt eD (zD i) := by
    apply conj_sElt z zD (by decide) (by decide +kernel) (by decide)
    · rw [show zD 1 = 3 by decide, sElt_three]
      exact hza
    · rw [show zD 4 = 5 by decide]
      have h5 : sElt eD 5 = sElt eD 3 * sElt eD 4 := by
        rw [sElt_mul eD (by norm_num) (by norm_num), show dMul 3 4 = 5 by decide]
      rw [h5, sElt_three]
      exact hzb
  have hE : ∀ k < 32, z * eltE k * z⁻¹ = eltE (id k) := by
    intro k hk
    have h1 := hzE _ (hctx.L.mem k hk)
    calc z * eltE k * z⁻¹ = eltE k * z * z⁻¹ := by rw [h1]
      _ = eltE (id k) := by simp
  rw [hctx.act_lab z zD id (by decide) (fun k hk => hk) hD hE hc, zeta_tab hc]
  rfl

theorem Phi_z {z : M} (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4) : hctx.Phi z = repPg 8 :=
  Subtype.ext (hctx.Phi_eq_of_table z repArrs[8]! (repPerm_rep (by norm_num))
    fun _ hc => hctx.z_act hzE hza hzb hc)

theorem b0_mem : b0Elt eD eltE ∈ D ⊔ E := hctx.lab_mem b0Idx twist_facts.1

theorem b0_sq : b0Elt eD eltE * b0Elt eD eltE = t := by
  have h := hctx.tabLab.mul b0Idx twist_facts.1 b0Idx twist_facts.1
  rw [twist_facts.2.2.1, hctx.lab_tC] at h
  exact h.symm

theorem z_b0 {z : M} (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4) : z * b0Elt eD eltE * z⁻¹ = b0Elt eD eltE := by
  have h := hctx.z_act hzE hza hzb twist_facts.1
  rw [twist_facts.2.1] at h
  exact h

theorem Phi_zb {z : M} (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4) :
    hctx.Phi (z * b0Elt eD eltE) = repPg 7 := by
  refine Subtype.ext (hctx.Phi_eq_of_table (z * b0Elt eD eltE) repArrs[7]! (repPerm_rep (by norm_num))
    fun c hc => ?_)
  obtain ⟨hb1, -, -, htw⟩ := twist_facts
  have hi : invC b0Idx < 128 := invC_lt hb1
  have hm1 : mulC b0Idx c < 128 := mulC_lt hb1 hc
  have hm2 : mulC (mulC b0Idx c) (invC b0Idx) < 128 := mulC_lt hm1 hi
  have h1 : b0Elt eD eltE * labD eD eltE c * (b0Elt eD eltE)⁻¹ =
      labD eD eltE (mulC (mulC b0Idx c) (invC b0Idx)) := by
    rw [hctx.tabLab.mul _ hm1 _ hi, hctx.tabLab.mul _ hb1 _ hc, hctx.lab_invC hb1]
    rfl
  calc z * b0Elt eD eltE * labD eD eltE c * (z * b0Elt eD eltE)⁻¹
      = z * (b0Elt eD eltE * labD eD eltE c * (b0Elt eD eltE)⁻¹) * z⁻¹ := by group
    _ = labD eD eltE (repArrs[8]!)[mulC (mulC b0Idx c) (invC b0Idx)]! := by
        rw [h1, hctx.z_act hzE hza hzb hm2]
    _ = labD eD eltE (repArrs[7]!)[c]! := by rw [htw c hc]

theorem fus_conj {j : ℕ} (hj : j = 4 ∨ j = 7 ∨ j = 8) (hj9 : j < 9) {y : M}
    (hy : ((hctx.Phi y : ↥Pg) : Equiv.Perm (Fin 128)) = repPerm j) :
    ∃ w ∈ D ⊔ E, y * w * y⁻¹ = w * t := by
  obtain ⟨hf1, hf2⟩ := fus_facts hj
  refine ⟨labD eD eltE fusTab[j]!, hctx.lab_mem _ hf1, ?_⟩
  have h1 := hctx.Phi_lab y ⟨fusTab[j]!, hf1⟩
  rw [hy, ← repPerm_rep hj9 ⟨fusTab[j]!, hf1⟩] at h1
  simp only at h1
  rw [← h1, hf2, hctx.tabLab.mul _ hf1 _ tC_lt, hctx.lab_tC]

end DECtx

end PhiZ

end CFSG.EvenSporadicStandard.Fin76b.W16
