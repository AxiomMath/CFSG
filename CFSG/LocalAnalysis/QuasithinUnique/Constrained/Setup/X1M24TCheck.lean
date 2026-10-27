module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TChain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TUniq
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Check
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TData
public meta import CFSG.Sporadic.Schreier.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheckInputs
public import Certificates.Certificate4137
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

section Slp

theorem slpLetter_mem {G : Type*} [Group G] (H : Subgroup G) {regs : List G}
    (hr : ∀ g ∈ regs, g ∈ H) (z : Int) : slpLetter regs z ∈ H := by
  have hget : ∀ i : ℕ, regs.getD i 1 ∈ H := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : regs[i]? with
    | none => exact H.one_mem
    | some g => exact hr g (List.mem_of_getElem? h)
  unfold slpLetter
  split_ifs
  · exact H.one_mem
  · exact hget _
  · exact H.inv_mem (hget _)

theorem slpEval_mem {G : Type*} [Group G] (norm : G → G) (hnorm : ∀ x, norm x = x)
    (H : Subgroup G) :
    ∀ (prog : List (Int × Int)) (gens : List G), (∀ g ∈ gens, g ∈ H) →
      ∀ r ∈ slpEval norm gens prog, r ∈ H := by
  intro prog
  induction prog with
  | nil => intro gens hg r hr; exact hg r hr
  | cons pq prog ih =>
    intro gens hg r hr
    refine ih (gens ++ [norm (slpLetter gens pq.1 * slpLetter gens pq.2)]) ?_ r hr
    intro g hgm
    rcases List.mem_append.1 hgm with h | h
    · exact hg g h
    · rw [List.mem_singleton.1 h, hnorm]
      exact H.mul_mem (slpLetter_mem H hg _) (slpLetter_mem H hg _)

end Slp

section Checks

theorem m24_e1_check :
    m24E1l.length = 64 ∧ m24E1l.Nodup ∧ (1 : S24) ∈ m24E1l ∧
      (∀ x ∈ m24E1l, ∀ y ∈ m24E1l, x * y ∈ m24E1l) ∧ (∀ x ∈ m24E1l, x * x = 1) ∧
      (∀ x ∈ m24E1l, ∀ y ∈ m24E1l, x * y = y * x) ∧ (∀ b ∈ m24E1B, b ∈ m24E1l) :=
  Certificates.certificate4137.1

theorem m24_e2_check :
    m24E2l.length = 64 ∧ m24E2l.Nodup ∧ (1 : S24) ∈ m24E2l ∧
      (∀ x ∈ m24E2l, ∀ y ∈ m24E2l, x * y ∈ m24E2l) ∧ (∀ x ∈ m24E2l, x * x = 1) ∧
      (∀ x ∈ m24E2l, ∀ y ∈ m24E2l, x * y = y * x) ∧ (∀ b ∈ m24E2B, b ∈ m24E2l) :=
  Certificates.certificate4137.2.1

theorem m24_heavy_check :
    heavyList m24rl (m24E1l ++ m24E2l) 62 = [] :=
  Certificates.certificate4137.2.2.1

theorem adjCert_of_adjData {B : List S24} {g : S24} {p : ℕ × ℕ} (h : AdjData B g p) :
    AdjCert (m24Lst B) g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨m24Elt B p.1, ?_, m24Elt B p.2, ?_, h3, h4, h5, h6, h7⟩
  · exact List.mem_map.2 ⟨p.1, List.mem_range.2 h1, rfl⟩
  · exact List.mem_map.2 ⟨p.2, List.mem_range.2 h2, rfl⟩

theorem m24_e1_adj :
    AdjData m24E1B (m24Cj m24E1G2) m24E1A2 ∧ AdjData m24E1B (m24Cj m24E1G3) m24E1A3 :=
  Certificates.certificate4137.2.2.2.1

theorem m24_e2_adj :
    AdjData m24E2B (m24Cj m24E2G2) m24E2A2 ∧ AdjData m24E2B (m24Cj m24E2G3) m24E2A3 :=
  Certificates.certificate4137.2.2.2.2.1

theorem m24_e1_gen :
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.1 1 = m24a ∧
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.2 1 = m24b :=
  Certificates.certificate4137.2.2.2.2.2.1

theorem m24_e2_gen :
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.1 1 = m24a ∧
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.2 1 = m24b :=
  Certificates.certificate4137.2.2.2.2.2.2

end Checks

section Generation

theorem m24_closure_top_of_slp (B : List S24) (g₂ g₃ : S24) (prog : List (Int × Int))
    (ra rb : ℕ) (hB : ∀ b ∈ B, b ∈ m24Lst B)
    (ha : (slpEval (normH NativeSporadic.M24) (m24Gens18 B g₂ g₃) prog).getD ra 1 = m24a)
    (hb : (slpEval (normH NativeSporadic.M24) (m24Gens18 B g₂ g₃) prog).getD rb 1 = m24b) :
    Subgroup.closure (conjSet [1, g₂, g₃] {x : S24 | x ∈ m24Lst B}) = ⊤ := by
  set H := Subgroup.closure (conjSet [1, g₂, g₃] {x : S24 | x ∈ m24Lst B}) with hH
  have hgens : ∀ g ∈ m24Gens18 B g₂ g₃, g ∈ H := by
    intro g hg
    simp only [m24Gens18, List.mem_append, List.mem_map] at hg
    apply Subgroup.subset_closure
    rcases hg with (hg | ⟨b, hb', rfl⟩) | ⟨b, hb', rfl⟩
    · exact ⟨1, by simp, g, hB g hg, by simp⟩
    · exact ⟨g₂, by simp, b, hB b hb', rfl⟩
    · exact ⟨g₃, by simp, b, hB b hb', rfl⟩
  have hmem := slpEval_mem (normH NativeSporadic.M24) (normH_eq _) H prog _ hgens
  have hget : ∀ i : ℕ, (slpEval (normH NativeSporadic.M24) (m24Gens18 B g₂ g₃) prog).getD i 1
      ∈ H := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : (slpEval (normH NativeSporadic.M24) (m24Gens18 B g₂ g₃) prog)[i]? with
    | none => exact H.one_mem
    | some g => exact hmem g (List.mem_of_getElem? h)
  have ha' := hget ra
  have hb' := hget rb
  rw [ha] at ha'
  rw [hb] at hb'
  rw [eq_top_iff, ← closure_pair_eq_top m24_eq (m24a.2) (m24b.2)]
  rw [Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact ha'
  · exact hb'

end Generation

end CFSG.QuasithinUnique.Setup.X1
