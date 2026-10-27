module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

section Abstract

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

theorem card_ge_of_acts [Finite X] (D : ModuleSpec X p) (P : Subgroup X) (hEP : D.span ≤ P)
    {k : ℕ} (J : Fin k → Fin D.m) (hJ : ∀ a, D.g (J a) ∈ P)
    (hd : ∀ a b : Fin k, a ≠ b → D.M (J a) ≠ D.M (J b)) :
    k * Nat.card D.span ≤ Nat.card P := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : Fin k × D.span → P := fun x =>
    ⟨D.g (J x.1) * (x.2 : X), P.mul_mem (hJ x.1) (hEP x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, e⟩ ⟨b, e'⟩ h
    have h' : D.g (J a) * (e : X) = D.g (J b) * (e' : X) := congrArg Subtype.val h
    have hab : a = b := by
      by_contra hne
      apply hd a b hne
      ext r i
      have hcol : D.g (J a) * D.a i * (D.g (J a))⁻¹ = D.g (J b) * D.a i * (D.g (J b))⁻¹ := by
        have hga : D.g (J a) = D.g (J b) * ((e' : X) * (e : X)⁻¹) := by
          rw [← mul_assoc]
          exact eq_mul_inv_of_mul_eq h'
        have hc : ((e' : X) * (e : X)⁻¹) * D.a i = D.a i * ((e' : X) * (e : X)⁻¹) :=
          D.mul_comm_of_mem (D.span.mul_mem e'.2 (D.span.inv_mem e.2)) (D.a_mem_span i)
        calc D.g (J a) * D.a i * (D.g (J a))⁻¹
            = D.g (J b) * (((e' : X) * (e : X)⁻¹) * D.a i * ((e' : X) * (e : X)⁻¹)⁻¹) *
                (D.g (J b))⁻¹ := by rw [hga]; group
          _ = D.g (J b) * D.a i * (D.g (J b))⁻¹ := by rw [hc]; group
      have := D.elt_injective (show D.elt (fun r => D.M (J a) r i) = D.elt (fun r => D.M (J b) r i)
        from by rw [D.elt_col, D.elt_col, hcol])
      exact congrFun this r
    subst hab
    have : (e : X) = e' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext this)
  calc k * Nat.card D.span = Nat.card (Fin k × D.span) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    _ ≤ Nat.card P := Nat.card_le_card_of_injective f hf

end Abstract

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod} {tops : List Pc}
  {gs : List NGrp} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
  {ct : ℕ → ℕ → ℕ → ℕ → ℤ}

include Sp in
theorem moduleDatum_of_modCheckE [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] (hp : p.Prime)
    {N s : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N) (hs : p ^ s ≤ gs.length * p ^ m.basis.length)
    (h : modCheckE O sA sB nregs prog p m tops gs cf ci ct = true) :
    ModuleDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold modCheckE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, hpcwf⟩, hentries⟩, hacts⟩, hgrp⟩, hrank⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsE p tops gs⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsE p tops gs
    simp only [NMod.modFactsE, List.mem_append]
    exact Or.inl (Or.inl hf)
  have hpcf : ∀ q ∈ tops ++ m.basisPc p, ∀ f ∈ q.facts p, f ∈ C.facts := by
    intro q hq f hqf
    show f ∈ m.modFactsE p tops gs
    unfold NMod.modFactsE
    refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
    exact List.mem_flatMap.2 ⟨q, hq, hqf⟩
  have hgf : ∀ g ∈ gs, MFact.eq [((m.acts.getD g.idx default).reg, 1)] g.w ∈ C.facts := by
    intro g hg
    show _ ∈ m.modFactsE p tops gs
    unfold NMod.modFactsE
    refine List.mem_append.2 (Or.inr ?_)
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  let DS := NMod.spec Sp hC' m hf hw
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ tops ++ m.basisPc p, u = regUnit Sp hC' q.reg}
  have hPgrp : IsPGroup p P := chain_isPGroup Sp hC' (tops ++ m.basisPc p) hpcwf hpcf
  let qs : List (certMonoid c d sA sB)ˣ := tops.map fun q => regUnit Sp hC' q.reg
  let P' : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure ((DS.span : Set _) ∪ {x | x ∈ qs})
  have hspanP : DS.span ≤ P := by
    rw [ModuleSpec.span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨q, hq, hqreg⟩ : ∃ q ∈ m.basisPc p, q.reg = m.basis.getD i.val 0 :=
      ⟨_, List.mem_map.2 ⟨i.val, List.mem_range.2 i.2, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inr hq), by rw [hqreg]; rfl⟩
  have hqsP : ∀ x ∈ qs, x ∈ P := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inl hq), rfl⟩
  have hP'le : P' ≤ P := (Subgroup.closure_le P).2 (Set.union_subset hspanP hqsP)
  have hP'grp : IsPGroup p P' := IsPGroup.to_le hPgrp hP'le
  have hqsP' : ∀ x ∈ qs, x ∈ P' := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hspanP' : DS.span ≤ P' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hP'norm : P' ≤ Subgroup.normalizer (DS.span : Set _) := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.le_normalizer hx
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨g, hg, hgq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hacts q hq)
      have hgq' : g.reg = q.reg := beq_iff_eq.1 hgq
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
      have := DS.g_mem_normalizer j
      show regUnit Sp hC' q.reg ∈ _
      rw [← hgq']
      exact this
  unfold NMod.grpOK at hgrp
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hgrp
  obtain ⟨hgrp1, hgrp2⟩ := hgrp
  have hidx : ∀ a : Fin gs.length, (gs.get a).idx < m.acts.length := fun a =>
    (hgrp1 _ (List.get_mem _ _)).1
  let J : Fin gs.length → Fin DS.m := fun a => ⟨(gs.get a).idx, hidx a⟩
  have hget : ∀ a : Fin gs.length,
      m.acts.getD (gs.get a).idx default = m.acts.get (J a) := by
    intro a
    have hi := hidx a
    show m.acts.getD (gs.get a).idx default = m.acts.get ⟨(gs.get a).idx, hi⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rfl
  have hJ : ∀ a, DS.g (J a) ∈ P' := by
    intro a
    have hmem := List.get_mem gs a
    have hfact := hgf _ hmem
    have hwq := (hgrp1 _ hmem).2
    rw [hget a] at hfact
    have hu : HasOrd C [((m.acts.get (J a)).reg, 1)] := by
      intro x hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      have hord : MFact.ord (m.acts.get (J a)).reg (m.acts.get (J a)).ord ∈ C.facts := by
        apply hf
        simp only [NMod.facts, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨m.acts.get (J a), List.get_mem _ _, by simp⟩
      exact ⟨_, hord⟩
    have hwo : HasOrd C (gs.get a).w := by
      intro x hx
      obtain ⟨q, hq, hqx⟩ := List.any_eq_true.1 (hwq x hx)
      have : x.1 = q.reg := (beq_iff_eq.1 hqx).symm
      refine ⟨q.ord, ?_⟩
      rw [this]
      exact hpcf q (List.mem_append.2 (Or.inl hq)) _ (by simp [Pc.facts])
    have heq := regUnit_eq Sp hC' hfact hu hwo
    have hgreg : DS.g (J a) = regUnit Sp hC' (m.acts.get (J a)).reg := rfl
    rw [hgreg]
    have e : wordUnit Sp hC' [((m.acts.get (J a)).reg, 1)] =
        regUnit Sp hC' (m.acts.get (J a)).reg := by simp [wordUnit]
    rw [e] at heq
    rw [heq]
    refine CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC' P' _ fun x hx => ?_
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.1 (hwq x hx)
    have : x.1 = q.reg := (beq_iff_eq.1 hqx).symm
    rw [this]
    exact hqsP' _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  have hentries' : ∀ (g : NAct), g ∈ m.acts → ∀ i, g.mat.getD i 0 < p := by
    intro g hg i
    by_cases hi : i < g.mat.length
    · have := List.all_eq_true.1 (List.all_eq_true.1 hentries g hg) (g.mat.getD i 0)
        (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      simpa using this
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hi)]
      exact hp.pos
  have hdiff : ∀ a b : Fin gs.length, a.val < b.val → DS.M (J a) ≠ DS.M (J b) := by
    intro a b hab hM
    have h1 := hgrp2 a.val (List.mem_range.2 a.2) b.val (List.mem_range.2 b.2)
    have h1' : m.matDiffer (gs.getD a.val default).idx (gs.getD b.val default).idx = true := by
      simpa [not_le.2 hab] using h1
    have hga : gs.getD a.val default = gs.get a := by
      simp [List.getD_eq_getElem?_getD]
    have hgb : gs.getD b.val default = gs.get b := by
      simp [List.getD_eq_getElem?_getD]
    rw [hga, hgb] at h1'
    unfold NMod.matDiffer at h1'
    rw [hget a, hget b] at h1'
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne] at h1'
    obtain ⟨k, hk, l, hl, hkl⟩ := h1'
    apply hkl
    have hent := congrFun (congrFun hM ⟨k, hk⟩) ⟨l, hl⟩
    have ea := hentries' (m.acts.get (J a)) (List.get_mem _ _) (m.basis.length * k + l)
    have eb := hentries' (m.acts.get (J b)) (List.get_mem _ _) (m.basis.length * k + l)
    have hent' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hent
    rwa [Nat.mod_eq_of_lt ea, Nat.mod_eq_of_lt eb] at hent'
  have hdist : ∀ a b : Fin gs.length, a ≠ b → DS.M (J a) ≠ DS.M (J b) := by
    intro a b hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hdiff a b hlt
    · exact (hdiff b a hlt).symm
  have hlow : gs.length * p ^ m.basis.length ≤ Nat.card P' := by
    have h := card_ge_of_acts DS P' hspanP' J hJ hdist
    rw [DS.card_span hp] at h
    exact h
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := hP'grp.exists_card_eq
  have hdvd : Nat.card P' ∣ N := hN ▸ Subgroup.card_subgroup_dvd_card P'
  have hs1 : s ≤ k := by
    have : p ^ s ≤ p ^ k := by
      rw [← hk]
      exact hs.trans hlow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hs2 : k ≤ s := by
    by_contra hlt
    apply hv.2
    exact (Nat.pow_dvd_pow p (not_le.1 hlt)).trans (hk ▸ hdvd)
  have hkeq : k = s := le_antisymm hs2 hs1
  have hfact : N.factorization p = s := by
    have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
    have h2 : ¬ s + 1 ≤ N.factorization p :=
      fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
    omega
  have hcard : Nat.card P' = p ^ (Nat.card (certMonoid c d sA sB)ˣ).factorization p := by
    rw [hN, hfact, hk, hkeq]
  exact ⟨DS, hrank, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', Sylow.ofCard P' hcard, hP'norm⟩

end Main

end CFSG.AGLEmbedding.R3
