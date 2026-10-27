module

public import Certificates.Certificate5183
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

theorem tabRep_of_comp_idTab {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (hs : t.size = n)
    (h : TabRep (comp n t (idTab n)) g) : TabRep t g := by
  refine ⟨hs, fun i => ?_⟩
  have := h.2 i
  rwa [TabRep.comp_getElem!, TabRep.idTab_getElem!] at this

theorem enumerates_center {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    (hP : Enumerates P T.toList) :
    Enumerates (Subgroup.centralizer (P : Set (Equiv.Perm (Fin n))) ⊓ P)
      (T.filter fun t => allBelow T.size fun j => comp n t T[j]! == comp n T[j]! t).toList := by
  rw [Array.toList_filter]
  refine hP.filter _ fun t g hg => ?_
  rw [Subgroup.mem_centralizer_iff, allBelow_eq_true]
  constructor
  · intro h x hx
    obtain ⟨j, hj, hxj⟩ := hP.exists_pos hx
    have := h j hj
    rw [(hg.comp hxj).beq_iff (hxj.comp hg)] at this
    exact this.symm
  · intro h j hj
    obtain ⟨x, hx, hxj⟩ := hP.exists_elt hj
    rw [(hg.comp hxj).beq_iff (hxj.comp hg)]
    exact (h x hx).symm

open CFSG.ComponentClassification.PSL3Four in
theorem exists_sylCfg_model :
    ∃ P E F : Subgroup (Equiv.Perm (Fin 42)),
      P ≤ S ∧ E ≤ P ∧ F ≤ P ∧ E ≤ F ∧
      Nat.card P = 64 ∧ Nat.card E = 4 ∧ Nat.card F = 16 ∧
      (∀ x ∈ P, x ^ 4 = 1) ∧
      (∀ x ∈ P, r₃ * x * r₃⁻¹ ∈ P) ∧
      (∀ e ∈ E, e * e = 1) ∧
      (∀ e ∈ E, ∀ x ∈ P, e * x = x * e) ∧
      (∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ E) ∧
      (∀ e ∈ E, r₃ * e = e * r₃) ∧
      (∀ e ∈ E, ∃ a ∈ P, ∃ b ∈ P, a * b * a⁻¹ * b⁻¹ = e) ∧
      (∀ f ∈ F, ∀ g ∈ F, f * g = g * f) ∧ (∀ f ∈ F, f * f = 1) ∧
      (∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
        ∃ n ∈ S, n ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 42))) ∧ n * e * n⁻¹ = e') := by
  have h : l34SylCheck enumS.tabs = true := Certificates.certificate5183
  unfold l34SylCheck at h
  extract_lets EP EPi idxP Et EF idxF nI at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ := h
  clear_value EP EPi idxP EF idxF nI
  have hr3r3 : r₃ * r₃ = 1 := Equiv.ext g6Fun_g6Fun
  have hr3i : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right hr3r3
  have hgensS : ∀ j < pGens.size, ∃ a ∈ S, TabRep pGens[j]! a := by
    intro j hj
    obtain ⟨k, hk, hkj⟩ := memTab_iff.1 ((allBelow_eq_true.1 c1) j hj)
    obtain ⟨a, haS, har⟩ := enumerates_S.exists_elt hk
    exact ⟨a, haS, by rw [← hkj]; exact har⟩
  set A : Set (Equiv.Perm (Fin 42)) := {a | ∃ j < pGens.size, TabRep pGens[j]! a}
  have hAS : A ⊆ S := by
    rintro a ⟨j, hj, har⟩
    obtain ⟨b, hbS, hbr⟩ := hgensS j hj
    rwa [har.perm_eq hbr]
  set P : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure A
  have hP : Enumerates P EP.tabs.toList :=
    enumerates_closure (fun a ha => ha) (fun j hj => by
      obtain ⟨a, -, har⟩ := hgensS j hj
      exact ⟨a, ⟨j, hj, har⟩, har⟩) c2
  have hPS : P ≤ S := (Subgroup.closure_le S).2 hAS
  have hcardP : Nat.card P = 64 := by
    rw [hP.card, Array.length_toList]
    exact beq_iff_eq.1 c3
  have hexp : ∀ x ∈ P, x ^ 4 = 1 := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hP.exists_pos hx
    exact ((hxk.pow 4).beq_iff TabRep.idTab).1 ((allBelow_eq_true.1 c5) k hk)
  have hr3P : ∀ x ∈ P, r₃ * x * r₃⁻¹ ∈ P := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hP.exists_pos hx
    obtain ⟨g, hgP, hg⟩ := hP.sound _ (mem_of_found ((allBelow_eq_true.1 c6) k hk))
    have hr : TabRep r₃T r₃⁻¹ := by rw [hr3i]; exact tabRep_r₃
    rw [(tabRep_r₃.conjTab hxk hr).perm_eq hg]
    exact hgP
  set E : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.centralizer (P : Set (Equiv.Perm (Fin 42))) ⊓ P
  have hE : Enumerates E Et.toList := enumerates_center hP
  have hcardE : Nat.card E = 4 := by
    rw [hE.card, Array.length_toList]
    exact beq_iff_eq.1 c7
  have hEdata : ∀ e ∈ E, e * e = 1 ∧ r₃ * e = e * r₃ ∧
      ∃ a ∈ P, ∃ b ∈ P, a * b * a⁻¹ * b⁻¹ = e := by
    intro e he
    obtain ⟨k, hk, hek⟩ := hE.exists_pos he
    have h8 := (allBelow_eq_true.1 c8) k hk
    simp only [Bool.and_eq_true, anyBelow_eq_true] at h8
    obtain ⟨⟨h1, h2⟩, a, ha, b, hb, h3⟩ := h8
    obtain ⟨x, hxP, hxa⟩ := hP.exists_elt ha
    obtain ⟨y, hyP, hyb⟩ := hP.exists_elt hb
    have hxi := invsOK_spec c4 ha hxa
    have hyi := invsOK_spec c4 hb hyb
    refine ⟨((hek.comp hek).beq_iff TabRep.idTab).1 h1,
      ((tabRep_r₃.comp hek).beq_iff (hek.comp tabRep_r₃)).1 h2, x, hxP, y, hyP, ?_⟩
    have := ((hxa.commTab hyb hxi hyi).beq_iff hek).1 h3
    rwa [commutatorElement_def] at this
  have hEFtab : ∀ k < EF.tabs.size, ∃ g ∈ P, TabRep EF.tabs[k]! g := by
    intro k hk
    have h11 := (allBelow_eq_true.1 c11) k hk
    simp only [Bool.and_eq_true] at h11
    exact hP.sound _ (mem_of_found h11.1.1)
  have hfsz : ∀ j < fGens.size, (fGens[j]!).size = 42 := by decide
  have hFgens : ∀ j < fGens.size, ∃ a : Equiv.Perm (Fin 42), TabRep fGens[j]! a := by
    intro j hj
    have c9' := c9
    unfold enumOK at c9'
    obtain ⟨hpos, h0, -, hclosed, -⟩ := treeOK_spec c9'
    have hmem := hclosed 0 hpos j hj
    rw [h0] at hmem
    obtain ⟨k, hk, hkeq⟩ := exists_getElem!_of_mem hmem
    obtain ⟨g, -, hg⟩ := hEFtab k hk
    rw [hkeq] at hg
    exact ⟨g, tabRep_of_comp_idTab (hfsz j hj) hg⟩
  set A' : Set (Equiv.Perm (Fin 42)) := {a | ∃ j < fGens.size, TabRep fGens[j]! a}
  set F : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure A'
  have hF : Enumerates F EF.tabs.toList :=
    enumerates_closure (fun a ha => ha) (fun j hj => by
      obtain ⟨a, har⟩ := hFgens j hj
      exact ⟨a, ⟨j, hj, har⟩, har⟩) c9
  have hcardF : Nat.card F = 16 := by
    rw [hF.card, Array.length_toList]
    exact beq_iff_eq.1 c10
  have hFP : F ≤ P := by
    intro f hf
    obtain ⟨k, hk, hfk⟩ := hF.exists_pos hf
    obtain ⟨g, hgP, hg⟩ := hEFtab k hk
    rw [hfk.perm_eq hg]
    exact hgP
  have hFdata : ∀ f ∈ F, f * f = 1 ∧ ∀ g ∈ F, f * g = g * f := by
    intro f hf
    obtain ⟨k, hk, hfk⟩ := hF.exists_pos hf
    have h11 := (allBelow_eq_true.1 c11) k hk
    simp only [Bool.and_eq_true] at h11
    obtain ⟨⟨-, h2⟩, h3⟩ := h11
    refine ⟨((hfk.comp hfk).beq_iff TabRep.idTab).1 h2, fun g hg => ?_⟩
    obtain ⟨l, hl, hgl⟩ := hF.exists_pos hg
    exact ((hfk.comp hgl).beq_iff (hgl.comp hfk)).1 ((allBelow_eq_true.1 h3) l hl)
  have hEF : E ≤ F := by
    intro e he
    obtain ⟨k, hk, hek⟩ := hE.exists_pos he
    obtain ⟨g, hgF, hg⟩ := hF.sound _ (mem_of_found ((allBelow_eq_true.1 c12) k hk))
    rw [hek.perm_eq hg]
    exact hgF
  obtain ⟨kn, hkn, hknT⟩ := memTab_iff.1 c13
  obtain ⟨n, hnS, hnk⟩ := enumerates_S.exists_elt hkn
  have hn : TabRep nT n := by rw [← hknT]; exact hnk
  have hni : TabRep nI n⁻¹ := invsOK_spec (T := #[nT]) c14 (k := 0) (by simp) hn
  have hni' : TabRep nT n⁻¹⁻¹ := by rw [inv_inv]; exact hn
  have hnorm : ∀ x ∈ P, n * x * n⁻¹ ∈ P ∧ n⁻¹ * x * n ∈ P := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hP.exists_pos hx
    have h15 := (allBelow_eq_true.1 c15) k hk
    rw [Bool.and_eq_true] at h15
    obtain ⟨g1, hg1P, hg1⟩ := hP.sound _ (mem_of_found h15.1)
    obtain ⟨g2, hg2P, hg2⟩ := hP.sound _ (mem_of_found h15.2)
    refine ⟨?_, ?_⟩
    · rw [(hn.conjTab hxk hni).perm_eq hg1]
      exact hg1P
    · have e := (hni.conjTab hxk hni').perm_eq hg2
      rw [inv_inv] at e
      rw [e]
      exact hg2P
  have hnN : n ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 42))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (hnorm x hx).1
    · intro hx
      have := (hnorm _ hx).2
      rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this
  have hniN : n⁻¹ ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 42))) :=
    Subgroup.inv_mem _ hnN
  have hfuse : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ m ∈ S, m ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 42))) ∧ m * e * m⁻¹ = e' := by
    intro e he he1 e' he' he1'
    obtain ⟨a, ha, hea⟩ := hE.exists_pos he
    obtain ⟨b, hb, heb⟩ := hE.exists_pos he'
    have h16 := (allBelow_eq_true.1 ((allBelow_eq_true.1 c16) a ha)) b hb
    simp only [Bool.or_eq_true] at h16
    rcases h16 with (((h | h) | h) | h) | h
    · exact absurd ((hea.beq_iff TabRep.idTab).1 h) he1
    · exact absurd ((heb.beq_iff TabRep.idTab).1 h) he1'
    · refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
      rw [← (hea.beq_iff heb).1 h]
      group
    · exact ⟨n, hnS, hnN, ((hn.conjTab hea hni).beq_iff heb).1 h⟩
    · exact ⟨n⁻¹, Subgroup.inv_mem _ hnS, hniN, ((hni.conjTab hea hni').beq_iff heb).1 h⟩
  refine ⟨P, E, F, hPS, inf_le_right, hFP, hEF, hcardP, hcardE, hcardF, hexp, hr3P,
    fun e he => (hEdata e he).1, fun e he x hx => ?_, fun x hx hc => ?_,
    fun e he => (hEdata e he).2.1, fun e he => (hEdata e he).2.2,
    fun f hf g hg => (hFdata f hf).2 g hg, fun f hf => (hFdata f hf).1, hfuse⟩
  · exact ((Subgroup.mem_centralizer_iff.1 he.1) x hx).symm
  · exact ⟨Subgroup.mem_centralizer_iff.2 fun y hy => (hc y hy).symm, hx⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
