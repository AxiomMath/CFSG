module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem classOK_gens {gG : Array Table} {x : Table} {cap sizeG csz : ℕ}
    (h : classOK gG x cap sizeG csz = true) : ∀ g ∈ gG, permOK 820 g = true := by
  simp only [classOK, Bool.and_eq_true, Array.all_eq_true'] at h
  intro g hg
  have := h.1.1.1 g hg
  simp only [permInvOK, Bool.and_eq_true] at this
  exact this.1

theorem case_spec_norm
    (d : CaseData) (hd : caseCheck d = true) {G : Subgroup (Equiv.Perm (Fin 820))}
    (hG : ∀ x, x ∈ G ↔ ∃ g ∈ P, ∃ k ∈ d.ks, k < 8 ∧ x = g * tP k) (hsz : Nat.card G = d.sizeG)
    {T y c k : Equiv.Perm (Fin 820)} (hT : Rep 820 d.Tt T) (hT2 : T * T = 1)
    (hy : Rep 820 d.y0 y) (hs : SigRel T y c k) (hcG : c ∈ G) (hkG : k ∈ G) :
    ∃ s ∈ solList d, Nat.card ↥(G ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = d.ysz ∧
      Nat.card ↥(G ⊓ centralizer ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} :
        Set (Equiv.Perm (Fin 820)))) = cent5Of d s := by
  simp only [caseCheck, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hy0p⟩, hgens⟩, -⟩, -⟩, -⟩, -⟩, hyg⟩, heyg⟩, hcly⟩, -⟩, -⟩ := hd
  rw [Array.all_eq_true'] at hgens hyg
  simp only [Bool.and_eq_true] at hyg
  have hy0 : Rep 820 d.y0 (tp 820 d.y0) := rep_tp hy0p
  have hyeq : y = tp 820 d.y0 := CFSG.Sporadic.Schreier.rep_unique hy hy0
  subst hyeq
  have hgG : ∀ x ∈ d.gensG, tp 820 x ∈ G := fun x hx =>
    mem_G_of_memCos hG (classOK_gens hcly x hx) (hgens x hx)
  have hYbound := classOK_card_le hsz hgG hy0 hcly
  obtain ⟨hygperm, hyrep, hymem, hycov, hycard, hynodup, hysize⟩ := enumOK_spec heyg
  have hysize' : (yEnum d).size = d.ysz := hysize
  have hygle : closure (tp 820 '' {x | x ∈ d.yg}) ≤
      G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨mem_G_of_memCos hG (hygperm x hx).1 (hyg x hx).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff (rep_tp (hygperm x hx).1) hy0).1 (hyg x hx).2
  have hYeq : closure (tp 820 '' {x | x ∈ d.yg}) =
      G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820))) :=
    Subgroup.eq_of_le_of_card_ge hygle (by rw [hycard]; exact hYbound)
  have hYcard : Nat.card ↥(G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820)))) =
      d.ysz := by
    rw [← hYeq]
    exact hycard
  have hcY : c ∈ G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hcG, mem_centralizer_singleton_iff.2 hs.yc.symm⟩
  have hkY : k ∈ G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hkG, mem_centralizer_singleton_iff.2 hs.yk.symm⟩
  have hcov' : ∀ x ∈ G ⊓ centralizer ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820))),
      ∃ i < (yEnum d).size, Rep 820 (yEnum d)[i]! x := by
    intro x hx
    rw [← hYeq] at hx
    obtain ⟨i, hi, hr⟩ := hycov x hx
    exact ⟨i, hysize'.symm ▸ hi, hr⟩
  obtain ⟨i, hi, hrc⟩ := hcov' c hcY
  obtain ⟨j, hj, hrk⟩ := hcov' k hkY
  have hcand : candOK d.Tt d.y0 (yEnum d)[i]! = true :=
    candOK_of_sig hT hT2 hy0 hrc hs.y3 hs.c3 hs.yc hs.ycp hs.ccp hs.card27
  have hkok : kOK d.Tt (yEnum d)[i]! (yEnum d)[j]! = true :=
    kOK_of_sig hT hT2 hrc hrk hs.kk hs.k1 hs.kcp hs.kkp hs.kc
  have hmemsol : ((yEnum d)[i]!, (yEnum d)[j]!) ∈ solList d := by
    unfold solList
    rw [List.mem_flatMap]
    refine ⟨(yEnum d)[i]!,
      List.mem_filter.2 ⟨Array.mem_toList_iff.2 (getElem!_mem_array hi), hcand⟩, ?_⟩
    rw [List.mem_map]
    exact ⟨(yEnum d)[j]!,
      List.mem_filter.2 ⟨Array.mem_toList_iff.2 (getElem!_mem_array hj), hkok⟩, rfl⟩
  refine ⟨_, hmemsol, hYcard, ?_⟩
  have hTi : Rep 820 d.Tt T⁻¹ := by rw [inv_eq_of_mul_eq_one_right hT2]; exact hT
  have hcp : Rep 820 (cpOf d.Tt (yEnum d)[i]!) (T * c * T⁻¹) := rep_conjT hT hTi hrc
  have hkp : Rep 820 (cpOf d.Tt (yEnum d)[j]!) (T * k * T⁻¹) := rep_conjT hT hTi hrk
  exact cent5_spec (E := yEnum d) (fun i hi => hyrep i (hysize' ▸ hi))
    (fun i hi => hYeq ▸ hymem i (hysize' ▸ hi)) hcov' hynodup hrc hcp hrk hkp

theorem case_spec
    (d : CaseData) (hd : caseCheck d = true) {G : Subgroup (Equiv.Perm (Fin 820))}
    (hG : ∀ x, x ∈ G ↔ ∃ g ∈ P, ∃ k ∈ d.ks, k < 8 ∧ x = g * tP k) (hsz : Nat.card G = d.sizeG)
    {T y c k : Equiv.Perm (Fin 820)} (hT : Rep 820 d.Tt T) (hT2 : T * T = 1)
    (hs : SigRel T y c k) (hyG : y ∈ G) (hcG : c ∈ G) (hkG : k ∈ G) :
    ∃ s ∈ solList d, Nat.card ↥(G ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = d.ysz ∧
      Nat.card ↥(G ⊓ centralizer ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} :
        Set (Equiv.Perm (Fin 820)))) = cent5Of d s := by
  have hd' := hd
  simp only [caseCheck, Bool.and_eq_true, beq_iff_eq] at hd'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hy0p⟩, hgens⟩, hclT⟩, hcg⟩, hecg⟩, hcov⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hd'
  rw [Array.all_eq_true'] at hgens hcg
  simp only [Bool.and_eq_true] at hcg
  have hy0 : Rep 820 d.y0 (tp 820 d.y0) := rep_tp hy0p
  have hgG : ∀ x ∈ d.gensG, tp 820 x ∈ G := fun x hx =>
    mem_G_of_memCos hG (classOK_gens hclT x hx) (hgens x hx)
  have hCT := classOK_card_le hsz hgG hT hclT
  obtain ⟨hcgperm, -, -, -, hcgcard, -, -⟩ := enumOK_spec hecg
  have hcgle : closure (tp 820 '' {x | x ∈ d.cg}) ≤
      G ⊓ centralizer ({T} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨mem_G_of_memCos hG (hcgperm x hx).1 (hcg x hx).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff (rep_tp (hcgperm x hx).1) hT).1 (hcg x hx).2
  have hCeq : closure (tp 820 '' {x | x ∈ d.cg}) =
      G ⊓ centralizer ({T} : Set (Equiv.Perm (Fin 820))) :=
    Subgroup.eq_of_le_of_card_ge hcgle (by rw [hcgcard]; exact hCT)
  have hyC : y ∈ closure (tp 820 '' {x | x ∈ d.cg}) := by
    rw [hCeq]
    exact mem_inf.2 ⟨hyG, mem_centralizer_singleton_iff.2 hs.comm_Ty.symm⟩
  obtain ⟨c₀, hc₀, hyc₀⟩ := coverOK_spec hy0 hecg hcov y hyC hs.y3
  rw [hCeq] at hc₀
  obtain ⟨hc₀G, hc₀T⟩ := mem_inf.1 hc₀
  have hc₀T' : c₀ * T = T * c₀ := mem_centralizer_singleton_iff.1 hc₀T
  have hTfix : c₀⁻¹ * T * c₀ = T := by
    calc c₀⁻¹ * T * c₀ = c₀⁻¹ * (T * c₀) := by group
      _ = c₀⁻¹ * (c₀ * T) := by rw [hc₀T']
      _ = T := by group
  have hyfix : c₀⁻¹ * y * c₀ = tp 820 d.y0 := by rw [hyc₀]; group
  have hs' := hs.conj c₀⁻¹
  simp only [inv_inv] at hs'
  rw [hTfix, hyfix] at hs'
  obtain ⟨s, hsmem, hYcard, hcent⟩ := case_spec_norm d hd hG hsz hT hT2 hy0 hs'
    (G.mul_mem (G.mul_mem (G.inv_mem hc₀G) hcG) hc₀G)
    (G.mul_mem (G.mul_mem (G.inv_mem hc₀G) hkG) hc₀G)
  refine ⟨s, hsmem, ?_, ?_⟩
  · have := card_inf_centralizer_conj_set G hc₀G ({tp 820 d.y0} : Set (Equiv.Perm (Fin 820)))
    rw [Set.image_singleton] at this
    rw [show c₀ * tp 820 d.y0 * c₀⁻¹ = y from hyc₀.symm] at this
    rw [this, hYcard]
  · have hset : (fun x => c₀ * x * c₀⁻¹) ''
        ({tp 820 d.y0, c₀⁻¹ * c * c₀, T * (c₀⁻¹ * c * c₀) * T⁻¹, c₀⁻¹ * k * c₀,
          T * (c₀⁻¹ * k * c₀) * T⁻¹} : Set (Equiv.Perm (Fin 820))) =
        {y, c, T * c * T⁻¹, k, T * k * T⁻¹} := by
      have hcT : c₀ * T * c₀⁻¹ = T := by rw [hc₀T']; group
      simp only [Set.image_insert_eq, Set.image_singleton]
      have e1 : c₀ * tp 820 d.y0 * c₀⁻¹ = y := hyc₀.symm
      have e2 : c₀ * (c₀⁻¹ * c * c₀) * c₀⁻¹ = c := by group
      have e3 : c₀ * (T * (c₀⁻¹ * c * c₀) * T⁻¹) * c₀⁻¹ = T * c * T⁻¹ := by
        calc c₀ * (T * (c₀⁻¹ * c * c₀) * T⁻¹) * c₀⁻¹
            = (c₀ * T * c₀⁻¹) * c * (c₀ * T * c₀⁻¹)⁻¹ := by group
          _ = T * c * T⁻¹ := by rw [hcT]
      have e4 : c₀ * (c₀⁻¹ * k * c₀) * c₀⁻¹ = k := by group
      have e5 : c₀ * (T * (c₀⁻¹ * k * c₀) * T⁻¹) * c₀⁻¹ = T * k * T⁻¹ := by
        calc c₀ * (T * (c₀⁻¹ * k * c₀) * T⁻¹) * c₀⁻¹
            = (c₀ * T * c₀⁻¹) * k * (c₀ * T * c₀⁻¹)⁻¹ := by group
          _ = T * k * T⁻¹ := by rw [hcT]
      rw [e1, e2, e3, e4, e5]
    have := card_inf_centralizer_conj_set G hc₀G
      ({tp 820 d.y0, c₀⁻¹ * c * c₀, T * (c₀⁻¹ * c * c₀) * T⁻¹, c₀⁻¹ * k * c₀,
        T * (c₀⁻¹ * k * c₀) * T⁻¹} : Set (Equiv.Perm (Fin 820)))
    rw [hset] at this
    rw [this, hcent]

end CFSG.EvenSporadicStandard.HSStd.U43
