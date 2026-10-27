
module

public import CFSG.Fischer.TransvectionPointsBase
import all CFSG.Fischer.TransvectionPointsBase

public import CFSG.Fischer.PolarCert
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix Blueprint.Fischer Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec tvTabs

theorem polar_parts : tvTabs.size = 693 ∧ commPerpOK tvTabs = true ∧ tvInjOK tvTabs = true ∧
    tvNontrivOK tvTabs = true ∧ tvConjOK tvTabs = true := by
  have h := polar_certificate
  unfold polarCertificate at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem tvP_comm_iff (p q : Fin 693) :
    tvP p * tvP q = tvP q * tvP p ↔ hermStd (uVec p) (uVec q) = 0 := by
  have h := allIn_eq_true.1 (allIn_eq_true.1 polar_parts.2.1 p.val (Nat.zero_le _) p.2) q.val
    (Nat.zero_le _) q.2
  simp only [Bool.beq_eq_decide_eq, decide_eq_decide] at h
  have h' := of_decide_eq_true h
  rw [← codeOf_uVec ptsFacts p.2, ← codeOf_uVec ptsFacts q.2, hermC_codeOf] at h'
  rw [← code_eq_zero_iff, ← h']
  constructor
  · intro hc
    have h1 := (rep_tvP p).compT (rep_tvP q)
    have h2 := (rep_tvP q).compT (rep_tvP p)
    rw [hc] at h1
    exact rep_unique_table (compT_size _ _) (compT_size _ _) h1 h2
  · intro ht
    have h2 := (rep_tvP q).compT (rep_tvP p)
    rw [← ht] at h2
    exact perm_eq_of_rep ((rep_tvP p).compT (rep_tvP q)) h2

theorem tvP_injective : Function.Injective tvP := by
  intro p q hpq
  by_contra hne
  have h := allIn_eq_true.1 (allIn_eq_true.1 polar_parts.2.2.1 p.val (Nat.zero_le _) p.2) q.val
    (Nat.zero_le _) q.2
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · exact hne (Fin.ext h)
  · exact h (rep_unique_table (tvTabs_size p) (tvTabs_size q) (rep_tvP p) (hpq ▸ rep_tvP q))

theorem tvP_ne_one (p : Fin 693) : tvP p ≠ 1 := by
  intro h1
  have h := allIn_eq_true.1 polar_parts.2.2.2.1 p.val (Nat.zero_le _) p.2
  simp only [bne_iff_ne, ne_eq] at h
  apply h
  apply rep_unique_table (tvTabs_size p) (by unfold idT; simp) (rep_tvP p)
  rw [h1]
  exact Rep.idT (by norm_num)

theorem tvP_conj (p q : Fin 693) : tvP p * tvP q * tvP p = tvP (tvP p q) := by
  have h := allIn_eq_true.1 (allIn_eq_true.1 polar_parts.2.2.2.2 p.val (Nat.zero_le _) p.2) q.val
    (Nat.zero_le _) q.2
  simp only [beq_iff_eq] at h
  have h1 := ((rep_tvP p).compT (rep_tvP q)).compT (rep_tvP p)
  rw [h] at h1
  have hq : ap tvTabs[p.val]! q.val = (tvP p q).val := by
    rw [rep_tvP p q.val q.2, idx_of_lt _ q.2]
    rfl
  have h2 := rep_tvP (tvP p q)
  rw [← hq] at h2
  exact perm_eq_of_rep h1 h2

theorem tvPsu_injective :
    Function.Injective tvPsu := by
  intro p q h
  apply tvP_injective
  rw [← psuT46_tvPsu, ← psuT46_tvPsu, h]

end CFSG.Fischer
