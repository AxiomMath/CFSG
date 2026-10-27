module

public import CFSG.ClassicalInvolution.SmallCases.NobqQuasi
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow
public import CFSG.ClassicalInvolution.SmallCases.NobqMcLInputs
public import Certificates.Certificate9307
public import Certificates.Certificate9314
public import Certificates.Certificate3170
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public meta import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Foundations.QuasisimpleMulEquiv
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.McL
public meta import CFSG.Sporadic.McL
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof

theorem noncentralInvOK_true : noncentralInvOK = true := by
  exact Certificates.certificate9307

theorem exists_noncentral_involution :
    ∃ u ∈ K, u * u = 1 ∧ u ≠ 1 ∧ u ≠ pa := by
  have h := noncentralInvOK_true
  simp only [noncentralInvOK, Array.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨k, hk, hT1, hT2⟩ := h
  obtain ⟨-, hrep, -, -⟩ := enumOK_spec hn sgens_perm sylow_check.1
  obtain ⟨hr, hmem⟩ := hrep k hk
  have hk' : (mulClosureH 275 sgens.toArray capK).1[k]! =
      (mulClosureH 275 sgens.toArray capK).1[k] := getElem!_pos _ k hk
  rw [hk'] at hr hmem
  have ho := orderOf_eq_two_of_involOK hn hr hT1
  refine ⟨_, S_le_K hmem, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one (tablePerm 275 (mulClosureH 275 sgens.toArray capK).1[k])
    rwa [ho, pow_two] at this
  · intro h1
    rw [h1, orderOf_one] at ho
    omega
  · intro h1
    have := (tblEq_iff_eq hr rep_pa).2 h1
    rw [this] at hT2
    exact absurd hT2 (by simp)

theorem noUniqueInvNormal_McLP
    (hP : Nat.card P = 898128000) : NoUniqueInvNormal P := by
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [card_S]; norm_num)
  refine noUniqueInvNormal_of_reps P [pa] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact pa_mem
  · intro u hu ho
    obtain ⟨c, hc, hcu⟩ := cover_of_sylow P S hS2 (S_index_odd hP) pa cover_S u hu ho
    exact ⟨pa, by simp, c, hc, hcu⟩
  · intro r hr hrP N
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨u, huK, hu2, hu1, hur⟩ := exists_noncentral_involution
    exact not_uniqueInvNormal_of_ambient_quasisimple P _ hrP K (centralizerIn_P hP)
      K_quasisimple.1 card_center_K u huK hu2 hu1 hur N

theorem noUniqueInvNormal_McL :
    NoUniqueInvNormal CFSG.Blueprint.NativeSporadic.McL :=
  NoUniqueInvNormal.of_mulEquiv mclEquivP (noUniqueInvNormal_McLP card_P)

end CFSG.ClassicalInvolution.Nobq
