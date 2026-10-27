module

public import CFSG.LieType.Ree.EndoRoots
public import CFSG.LieType.Chevalley.TwistUnipotent
public import CFSG.LieType.Chevalley.FixedCollection
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Commute

variable {τ : Tag}

theorem height_smul_zsmul_add_zsmul (w : WeylGroup τ) (a b : ℤ) (u v : Fin τ.rank → ℤ) :
    height (w • (a • u + b • v)) = a * height (w • u) + b * height (w • v) := by
  rw [smul_add, smul_comm w a u, smul_comm w b v]
  simp only [height, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem not_isRoot_nsmul_add_nsmul_of_weight (f : Fin τ.rank → ℤ) {θ θ' : Fin τ.rank → ℤ}
    (hθ : 0 < height θ) (hθ' : 0 < height θ')
    (hfθ : 0 ≤ ∑ k, f k * θ k) (hfθ' : 0 ≤ ∑ k, f k * θ' k)
    (hf : ∀ r, IsRoot τ r → 0 < height r →
      ∑ k, f k * r k < ∑ k, f k * θ k + ∑ k, f k * θ' k)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬IsRoot τ (a • θ + b • θ') := by
  intro hr
  have hheight : height (a • θ + b • θ') = a * height θ + b * height θ' := by
    simp only [height, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib]
    simp only [nsmul_eq_mul, Finset.mul_sum]
  have hsum : ∑ k, f k * (a • θ + b • θ') k = a * ∑ k, f k * θ k + b * ∑ k, f k * θ' k := by
    simp only [Pi.add_apply, Pi.smul_apply, mul_add, Finset.sum_add_distrib]
    simp only [nsmul_eq_mul, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h1 := hf _ hr (by rw [hheight]; nlinarith)
  rw [hsum] at h1
  nlinarith

variable (K : Type) [Field K]

theorem commute_of_forall_not_isRoot {α β : Root τ} (hα : 0 < height α.1)
    (hβ : 0 < height β.1) (hne : α ≠ β)
    (h : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬IsRoot τ (a • α.1 + b • β.1))
    {x y : adjointGroup τ K} (hx : x ∈ (nativeRootSubgroups τ K).X α)
    (hy : y ∈ (nativeRootSubgroups τ K).X β) : Commute x y := by
  have hc := commContained_pos K α β hα hβ hne x hx y hy
  have hbot : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α.1 + b • β.1),
      (rootOperatorFamily τ).rootSubgroup K γ) = ⊥ := by
    refine iSup_eq_bot.2 fun γ => iSup_eq_bot.2 fun ⟨a, b, ha, hb, hγ⟩ => ?_
    exact absurd (hγ ▸ γ.2) (h a b ha hb)
  rw [hbot, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact hc)

theorem nrep_conj_xElement_ne_one (v : WeylGroup τ) (j : Fin τ.rank) :
    nrep τ K v * xElement j 1 * (nrep τ K v)⁻¹ ≠ 1 := by
  rw [Ne, conj_eq_one_iff]
  exact xElement_ne_one one_ne_zero

variable [Finite K]

theorem nrep_conj_xElement_mem_X (v : WeylGroup τ) (j : Fin τ.rank) :
    nrep τ K v * xElement j 1 * (nrep τ K v)⁻¹ ∈
      (nativeRootSubgroups τ K).X (v • simpleRoot τ j) := by
  have h := (nativeRootSubgroups τ K).map_conj ⟨nrep τ K v, nrep_mem_monomialGroup τ K v⟩
    (simpleRoot τ j)
  rw [weylHom_nrep] at h
  rw [← h]
  exact ⟨xElement j 1, xElement_mem_X j 1, rfl⟩

end Commute

namespace ReeTag

variable {t : ReeTag}

theorem height_smul_single_perm_neg {w : WeylGroup t.tag} (hw : t.weylPerm w = w)
    {i : Fin t.tag.rank} (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    height (w • (Pi.single (t.perm i) 1 : Fin t.tag.rank → ℤ)) < 0 := by
  have h := dualRoot_smul w (isRoot_single t.tag i)
  rw [dualRoot_single, hw] at h
  rw [← h]
  exact (height_dualRoot_neg_iff (IsRoot.smul (isRoot_single t.tag i) w)).2 hi

@[expose] def reeRootWord : (t : ReeTag) → Fin t.tag.rank → List (Fin t.tag.rank)
  | .G2 => (![[0, 1], [0, 1]] : Fin 2 → List (Fin 2))
  | .F4 => (![[], [1], [1], []] : Fin 4 → List (Fin 4))

@[expose] def reeRootIndex : (t : ReeTag) → Fin t.tag.rank → Fin t.tag.rank
  | .G2 => (![0, 0] : Fin 2 → Fin 2)
  | .F4 => (![0, 2, 2, 0] : Fin 4 → Fin 4)

@[expose] def reeSepWord : (t : ReeTag) → Fin t.tag.rank → List (Fin t.tag.rank)
  | .G2 => (![[0, 1, 0], [0, 1, 0]] : Fin 2 → List (Fin 2))
  | .F4 => (![[0], [2, 1], [2, 1], [0]] : Fin 4 → List (Fin 4))

variable (t) in
@[expose] def reeTheta (i : Fin t.tag.rank) : Fin t.tag.rank → ℤ :=
  (reeRootWord t i).foldr (reflect t.tag) (Pi.single (reeRootIndex t i) 1)

variable (t) in
@[expose] def reeWeight (i k : Fin t.tag.rank) : ℤ :=
  if k = i ∨ k = t.perm i then 1 else -10

variable (t) in
theorem reeTheta_spec (i : Fin t.tag.rank) :
    reeTheta t i = reeTheta t i i • Pi.single i 1 +
        reeTheta t i (t.perm i) • Pi.single (t.perm i) 1 ∧
      0 ≤ reeTheta t i i ∧ 0 ≤ reeTheta t i (t.perm i) ∧
      0 < reeTheta t i i + reeTheta t i (t.perm i) ∧ 0 < height (reeTheta t i) ∧
      t.dualRoot (reeTheta t i) ≠ reeTheta t i := by
  revert i
  cases t <;> decide +kernel

variable (t) in
theorem reeWeight_spec (i : Fin t.tag.rank) :
    0 ≤ ∑ k, reeWeight t i k * reeTheta t i k ∧
      0 ≤ ∑ k, reeWeight t i k * t.dualRoot (reeTheta t i) k ∧
      ∀ n < t.tag.rootCertificate.roots.length, 0 < height (t.tag.rootCertificate.root n) →
        ∑ k, reeWeight t i k * t.tag.rootCertificate.root n k <
          ∑ k, reeWeight t i k * reeTheta t i k +
            ∑ k, reeWeight t i k * t.dualRoot (reeTheta t i) k := by
  revert i
  cases t <;> decide +kernel

variable (t) in
theorem reeSepWord_spec (i : Fin t.tag.rank) :
    height ((reeSepWord t i).foldr (reflect t.tag) (reeTheta t i)) < 0 ∧
      0 < height ((reeSepWord t i).foldr (reflect t.tag) (t.dualRoot (reeTheta t i))) := by
  revert i
  cases t <;> decide +kernel

variable {K : Type} [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

theorem reeAut_nrep_conj_xElement (v : WeylGroup t.tag) (j : Fin t.tag.rank) :
    t.reeAut K a (nrep t.tag K v * xElement j 1 * (nrep t.tag K v)⁻¹) =
      nrep t.tag K (t.weylPerm v) * xElement (t.perm j) 1 * (nrep t.tag K (t.weylPerm v))⁻¹ := by
  rw [map_mul, map_mul, map_inv, reeAut_nrep, reeAut_xElement, one_pow]

theorem reeAut_reeAut_nrep_conj_xElement (v : WeylGroup t.tag) (j : Fin t.tag.rank) :
    t.reeAut K a (t.reeAut K a (nrep t.tag K v * xElement j 1 * (nrep t.tag K v)⁻¹)) =
      nrep t.tag K v * xElement j 1 * (nrep t.tag K v)⁻¹ := by
  rw [reeAut_nrep_conj_xElement, reeAut_nrep_conj_xElement, weylPerm_weylPerm, perm_perm]

theorem exists_reeAut_fixed_conj_not_mem_U_of_index {w : WeylGroup t.tag}
    (hw : t.weylPerm w = w) {i : Fin t.tag.rank}
    (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    ∃ u ∈ (nativeData t.tag K).U, t.reeAut K a u = u ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  set v := (coxeterSystem t.tag).wordProd (reeRootWord t i)
  set j := reeRootIndex t i
  set θ : Root t.tag := v • simpleRoot t.tag j
  set θ' : Root t.tag := t.dualRootOf θ with hθ'
  have hθ1 : θ.1 = reeTheta t i := wordProd_smul _ _
  have hθ'1 : θ'.1 = t.dualRoot (reeTheta t i) := by
    change t.dualRoot θ.1 = _
    rw [hθ1]
  obtain ⟨hdec, hc1, hc2, hc3, hpos, hne⟩ := reeTheta_spec t i
  obtain ⟨hf1, hf2, hf3⟩ := reeWeight_spec t i
  obtain ⟨hs1, hs2⟩ := reeSepWord_spec t i
  have hθpos : 0 < height θ.1 := by rw [hθ1]; exact hpos
  have hθ'pos : 0 < height θ'.1 := (height_dualRoot_pos_iff θ.2).2 hθpos
  have hwθ : height (w • θ).1 < 0 := by
    have hi' := height_smul_single_perm_neg hw hi
    rw [coe_smul_root, hθ1, hdec, height_smul_zsmul_add_zsmul]
    nlinarith
  have hwθ' : height (w • θ').1 < 0 := by
    rw [hθ', ← hw, ← dualRootOf_smul]
    exact (height_dualRoot_neg_iff (w • θ).2).2 hwθ
  have hθne : θ ≠ θ' := fun h => hne (by rw [← hθ'1, ← h, hθ1])
  have hnot : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬IsRoot t.tag (a • θ.1 + b • θ'.1) := by
    intro a b ha hb
    rw [hθ1, hθ'1]
    refine not_isRoot_nsmul_add_nsmul_of_weight (reeWeight t i) hpos (hθ'1 ▸ hθ'pos) hf1 hf2
      (fun r hr hrpos => ?_) ha hb
    obtain ⟨n, hn, rfl⟩ := RootCertificate.exists_root_eq t.tag.rootCertificate_check hr
    exact hf3 n hn hrpos
  set y := nrep t.tag K v * xElement j 1 * (nrep t.tag K v)⁻¹
  have hyX : y ∈ (nativeRootSubgroups t.tag K).X θ := nrep_conj_xElement_mem_X K v j
  have hFyX : t.reeAut K a y ∈ (nativeRootSubgroups t.tag K).X θ' := reeAut_mem_X a hyX
  have hFFy : t.reeAut K a (t.reeAut K a y) = y := reeAut_reeAut_nrep_conj_xElement a v j
  have hcomm : Commute y (t.reeAut K a y) :=
    commute_of_forall_not_isRoot K hθpos hθ'pos hθne hnot hyX hFyX
  have hUm : y * t.reeAut K a y ∈ Uminus t.tag K w :=
    mul_mem (mem_Uminus_of_mem_X hθpos hwθ hyX) (mem_Uminus_of_mem_X hθ'pos hwθ' hFyX)
  refine ⟨y * t.reeAut K a y, Uminus_le_U t.tag K w hUm, ?_, fun hU => ?_⟩
  · rw [map_mul, hFFy]
    exact hcomm.eq.symm
  ·
    have hu := eq_one_of_mem_Uminus_of_nrep_conj_mem_U hUm hU
    set w' := (coxeterSystem t.tag).wordProd (reeSepWord t i) with hw'
    have hw'θ : height (w' • θ).1 < 0 := by
      rw [coe_smul_root, hw', wordProd_smul, hθ1]
      exact hs1
    have hw'θ' : 0 < height (w' • θ').1 := by
      rw [coe_smul_root, hw', wordProd_smul, hθ'1]
      exact hs2
    have hym : y ∈ Uminus t.tag K w' := mem_Uminus_of_mem_X hθpos hw'θ hyX
    have hyp : y ∈ Uplus t.tag K w' := by
      rw [eq_inv_of_mul_eq_one_left hu]
      exact inv_mem (mem_Uplus_of_mem_X hθ'pos hw'θ' hFyX)
    have h1 : y ∈ Uplus t.tag K w' ⊓ Uminus t.tag K w' := Subgroup.mem_inf.2 ⟨hyp, hym⟩
    rw [Uplus_inf_Uminus, Subgroup.mem_bot] at h1
    exact nrep_conj_xElement_ne_one K v j h1

end ReeTag

open ReeTag

theorem exists_reeAut_fixed_conj_not_mem_U (t : ReeTag) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (a : ℕ) {w : WeylGroup t.tag} (hw : t.weylPerm w = w) (hw1 : w ≠ 1) :
    ∃ u ∈ (nativeData t.tag K).U, t.reeAut K a u = u ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
  exact exists_reeAut_fixed_conj_not_mem_U_of_index a hw hi

end CFSG.LieType.Ree
