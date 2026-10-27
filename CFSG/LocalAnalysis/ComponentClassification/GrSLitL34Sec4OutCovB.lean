module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealNF
public import Certificates.Data.GrSLitL34Sec4OutCovCheck

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4.OutCov

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.CosetTable

noncomputable abbrev nfE {E : Type*} [Group E] (l : Cover →* E)
    (x : El) : E :=
  nf l x.1 x.2.1 x.2.2

theorem inKb_iff (κ : ZMod 4 × ZMod 4) (a b : ZMod 4) : inKb κ a b = true ↔ inK κ a b := by
  revert κ a b
  decide

theorem kGensB_eq : kGensB = kGens := rfl

theorem mem_z4 (a : ZMod 4) : a ∈ z4 := by
  revert a
  decide

theorem mem_els {x : El} (hx : x.1 < 64) : x ∈ els := by
  obtain ⟨k, a, b⟩ := x
  simp only [els, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨k, hx, a, mem_z4 a, b, mem_z4 b, rfl⟩

theorem lt_of_mem_els {x : El} (hx : x ∈ els) : x.1 < 64 := by
  simp only [els, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, a, -, b, -, rfl⟩ := hx
  exact hk

theorem invOKE_spec (hI : invOKE = true) {t : ℕ} (ht : t < 64) :
    invIdx t < 64 ∧ (t1Entry t (invIdx t)).1 = 0 := by
  simp only [invOKE, allBelow_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hI
  exact hI t ht

section Setting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem mulE_lt {x y : El} (hx : x.1 < 64) (hy : y.1 < 64) :
    (mulE x y).1 < 64 :=
  t1_lt hx hy

theorem alphaE_lt {i : ℕ} (hi : i < 36) {x : El}
    (hx : x.1 < 64) : (alphaE i x).1 < 64 :=
  alpha_lt hi hx

theorem nfE_mulE
    (h : IsQSetting q l) {x y : El}
    (hx : x.1 < 64) (hy : y.1 < 64) :
    nfE l (mulE x y) = nfE l x * nfE l y :=
  (nf_mul h hx hy _ _ _ _).symm

theorem eqE_iff
    (h : IsQSetting q l) {κ : ZMod 4 × ZMod 4}
    (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {x y : El} (hx : x.1 < 64) (hy : y.1 < 64) :
    eqE κ x y = true ↔ nfE l x = nfE l y := by
  rw [nf_eq_iff h hx hy, hκ]
  simp only [eqE, Bool.and_eq_true, beq_iff_eq, inKb_iff]

theorem q_nfE
    (h : IsQSetting q l) {x : El} (hx : x.1 < 64) :
    q (nfE l x) = wordPerm (tg x.1) :=
  q_nf h hx _ _

theorem nfE_oneE : nfE l oneE = 1 := nf_zero

theorem beta_nfE
    (h : IsQSetting q l) (hI : invOKE = true)
    {β : E ≃* E} {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hform : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)))
    {x : El} (hx : x.1 < 64) :
    β (nfE l x) = nfE l (betaE t i x) ∧ (betaE t i x).1 < 64 := by
  set β' : E ≃* E := β.trans (MulAut.conj (nf l t 0 0)⁻¹) with hβ'
  have hβ'l : ∀ w, β' (l (cv w)) = l (cv (substWord (aut i) w)) := fun w => by
    rw [← hform w, hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have e1 : β (nfE l x) = nf l t 0 0 * β' (nfE l x) * (nf l t 0 0)⁻¹ := by
    rw [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨hinv, hinv0⟩ := invOKE_spec hI ht
  have hα : β' (nfE l x) = nfE l (alphaE i x) := beta_nf h hi hx hβ'l _ _
  have hn : nf l t 0 0 = nfE l ((t, 0, 0) : El) := rfl
  have hi' : (nf l t 0 0)⁻¹ = nfE l (invE t) := nf_inv h ht hinv hinv0
  have hlt1 : (mulE ((t, 0, 0) : El) (alphaE i x)).1 < 64 := mulE_lt ht (alphaE_lt hi hx)
  refine ⟨?_, mulE_lt hlt1 hinv⟩
  rw [e1, hα, hi', hn, betaE, nfE_mulE h hlt1 hinv, nfE_mulE h ht (alphaE_lt hi hx)]

theorem invar_of_beta
    (h : IsQSetting q l)
    {κ : ZMod 4 × ZMod 4} (hκ : ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j) {β : E ≃* E}
    {t i : ℕ} (hi : i < 36)
    (hform : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w))) :
    invar κ i = true := by
  set β' : E ≃* E := β.trans (MulAut.conj (nf l t 0 0)⁻¹) with hβ'
  have hβ'l : ∀ w, β' (l (cv w)) = l (cv (substWord (aut i) w)) := fun w => by
    rw [← hform w, hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have h1 : zz l κ.1 κ.2 = 1 := (hκ _ _).2 ⟨1, one_mul _, one_mul _⟩
  have h2 := beta_zz h hi hβ'l κ.1 κ.2
  rw [h1, map_one] at h2
  rw [invar, inKb_iff, ← hκ]
  exact h2.symm

theorem is2_of_mem {Y : Subgroup (Equiv.Perm (Fin 42))}
    (hY : IsPGroup 2 ↥Y) (hYR : Y ≤ R)
    {g : Equiv.Perm (Fin 42)} (hg : g ∈ Y) {x : Tab} (hx : TabRep x g) : is2 x = true := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hY ⟨g, hg⟩
  have h1 : orderOf g ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf g ∣ 241920 := by
    rw [← card_R, ← Subgroup.orderOf_mk g (hYR hg)]
    exact orderOf_dvd_natCard _
  have hm8 : m ≤ 8 := by
    by_contra hm8
    push Not at hm8
    have h3 : 2 ^ 9 ∣ 241920 := (pow_dvd_pow 2 hm8).trans (hm ▸ h2)
    norm_num at h3
  have h4 : g ^ 2 ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.1 (hm ▸ pow_dvd_pow 2 hm8)
  exact ((tabRep_powTwoTab hx 8).beq_iff TabRep.idTab).2 h4

end Setting

end CFSG.ComponentClassification.GrSLit.GrS4.OutCov
