module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB2
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

theorem pglFactsCheck_all (h : pglFactsCheck () = true) :
    pglF1Of (pglData ()) = true ∧ pglF2Of (pglData ()) = true ∧
    pglF3Of (pglData ()) = true ∧ pglF4Of (pglData ()) = true ∧
    pglF5Of (pglData ()) = true ∧ pglF6Of (pglData ()) = true ∧
    pglF7Of (pglData ()) = true ∧ pglF8Of (pglData ()) = true ∧
    pglF9Of (pglData ()) = true ∧ pglF10Of (pglData ()) = true ∧
    pglF11Of (pglData ()) = true ∧ pglF12Of (pglData ()) = true ∧
    pglF13Of (pglData ()) = true := by
  simp only [pglFactsCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem pglF1Of_facts {D : PGLData} (h : pglF1Of D = true) :
    (D.invs.size = D.elems.size ∧ D.invs0.size = D.elems0.size) ∧
    (∀ i, i < D.elems.size → Code.mul (D.elems[i]!) (D.invs[i]!) = Code.one) ∧
    (∀ i, i < D.elems0.size → Code.mul (D.elems0[i]!) (D.invs0[i]!) = Code.one) := by
  simp only [pglF1Of, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hinvsize⟩, hinv⟩, hinv0size⟩, hinv0⟩ := h
  refine ⟨⟨hinvsize, hinv0size⟩, ?_, ?_⟩
  · intro i hi
    exact hinv i (List.mem_range.mpr hi)
  · intro i hi
    exact hinv0 i (List.mem_range.mpr hi)

theorem pglF3Of_facts {D : PGLData} (h : pglF3Of D = true) :
    D.elems.size = 336 ∧ D.elems0.size = 168 := by
  simpa only [pglF3Of, Bool.and_eq_true, beq_iff_eq] using h

theorem pglF5Of_singular {D : PGLData} (h : pglF5Of D = true) :
    (∀ n ∈ vPlusVecs, qB false n = false) ∧ (∀ n ∈ vStarVecs, qB false n = false) := by
  simp only [pglF5Of, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hplus, hstar⟩, -⟩, -⟩, -⟩ := h
  exact ⟨fun n hn => by simpa using hplus n hn, fun n hn => by simpa using hstar n hn⟩

theorem pglF5Of_inf {D : PGLData} (h : pglF5Of D = true) :
    ∀ n, n ∈ vPlusVecs → n ∈ vStarVecs → n = 0 := by
  simp only [pglF5Of, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, hinter⟩, -⟩, -⟩ := h
  have hinter' : vPlusVecs.filter (fun v => vStarVecs.contains v) = [0] := hinter
  intro n hn hn'
  have hmem : n ∈ vPlusVecs.filter (fun v => vStarVecs.contains v) := by
    rw [List.mem_filter]
    exact ⟨hn, by simpa using hn'⟩
  rw [hinter'] at hmem
  simpa using hmem

theorem pglF5Of_decomp {D : PGLData} (h : pglF5Of D = true) :
    ∀ n, n < 64 → ∃ p, p ∈ D.f5Wit.toList ∧
      p.1 ∈ vPlusVecs ∧ p.2 ∈ vStarVecs ∧ p.1 ^^^ p.2 = n := by
  simp only [pglF5Of, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hsize⟩, hwit⟩ := h
  intro n hn
  have hp := hwit n (List.mem_range.mpr hn)
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  refine ⟨D.f5Wit[n]!, ?_, by simpa using hp1, by simpa using hp2, hp3⟩
  have hn' : n < D.f5Wit.size := by rw [hsize]; exact hn
  rw [show D.f5Wit[n]! = D.f5Wit[n] from
    array_getElem!_eq_getElem_of_lt (A := D.f5Wit) (i := n) hn']
  exact Array.getElem_mem_toList hn' 

theorem vPlusVecs_lt : ∀ n ∈ vPlusVecs, n < 64 := by decide +kernel

theorem vStarVecs_lt : ∀ n ∈ vStarVecs, n < 64 := by decide +kernel

theorem vPlusVecs_nodup : vPlusVecs.Nodup := by decide +kernel

theorem vStarVecs_nodup : vStarVecs.Nodup := by decide +kernel

theorem VPlus_singular {D : PGLData} (h : pglF5Of D = true) {v : V₀} (hv : v ∈ VPlus) :
    qModel false v = 0 := by
  rw [mem_VPlus_iff] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  rw [qModel_vec, (pglF5Of_singular h).1 n hn]
  simp

theorem VStar_singular {D : PGLData} (h : pglF5Of D = true) {v : V₀} (hv : v ∈ VStar) :
    qModel false v = 0 := by
  rw [mem_VStar_iff] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  rw [qModel_vec, (pglF5Of_singular h).2 n hn]
  simp

theorem VPlus_inf_VStar {D : PGLData} (h : pglF5Of D = true) : VPlus ⊓ VStar = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [mem_VPlus_iff] at hv
  rw [mem_VStar_iff] at hv
  obtain ⟨⟨n, hn, rfl⟩, ⟨m, hm, hmn⟩⟩ := hv
  have hnm : n = m := by
    exact vec_injective_of_lt (vPlusVecs_lt n hn) (vStarVecs_lt m hm) hmn.symm
  have hn0 : n = 0 := pglF5Of_inf h n hn (hnm ▸ hm)
  rw [hn0, vec_zero]
  exact Submodule.zero_mem _

theorem VPlus_sup_VStar {D : PGLData} (h : pglF5Of D = true) : VPlus ⊔ VStar = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨n, hn, rfl⟩ := exists_vec v
  obtain ⟨p, hp, hp1, hp2, hpn⟩ := pglF5Of_decomp h n hn
  rw [← hpn, vec_xor]
  exact Submodule.add_mem_sup (mem_VPlus_iff.mpr ⟨p.1, hp1, rfl⟩)
    (mem_VStar_iff.mpr ⟨p.2, hp2, rfl⟩)

theorem finrank_VPlus {D : PGLData} (h : pglF5Of D = true) : finrank (ZMod 2) VPlus = 3 := by
  have hP : finrank (ZMod 2) VPlus ≤ 3 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := V₀)
      ({Code.vec 2, Code.vec 4, Code.vec 32} : Set V₀)
    have hc : ({Code.vec 2, Code.vec 4, Code.vec 32} : Set V₀).toFinset.card = 3 := by
      decide +kernel
    rw [hc] at h
    exact h
  have hS : finrank (ZMod 2) VStar ≤ 3 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := V₀)
      ({Code.vec 1, Code.vec 8, Code.vec 16} : Set V₀)
    have hc : ({Code.vec 1, Code.vec 8, Code.vec 16} : Set V₀).toFinset.card = 3 := by
      decide +kernel
    rw [hc] at h
    exact h
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq VPlus VStar
  rw [VPlus_sup_VStar h, VPlus_inf_VStar h, finrank_top] at hdim
  have htop : finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)
  simp only [finrank_bot, add_zero] at hdim
  rw [htop] at hdim
  omega

theorem finrank_VStar {D : PGLData} (h : pglF5Of D = true) : finrank (ZMod 2) VStar = 3 := by
  have hP : finrank (ZMod 2) VPlus ≤ 3 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := V₀)
      ({Code.vec 2, Code.vec 4, Code.vec 32} : Set V₀)
    have hc : ({Code.vec 2, Code.vec 4, Code.vec 32} : Set V₀).toFinset.card = 3 := by
      decide +kernel
    rw [hc] at h
    exact h
  have hS : finrank (ZMod 2) VStar ≤ 3 := by
    have h := finrank_span_le_card (R := ZMod 2) (M := V₀)
      ({Code.vec 1, Code.vec 8, Code.vec 16} : Set V₀)
    have hc : ({Code.vec 1, Code.vec 8, Code.vec 16} : Set V₀).toFinset.card = 3 := by
      decide +kernel
    rw [hc] at h
    exact h
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq VPlus VStar
  rw [VPlus_sup_VStar h, VPlus_inf_VStar h, finrank_top] at hdim
  have htop : finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)
  simp only [finrank_bot, add_zero] at hdim
  rw [htop] at hdim
  omega


end CFSG.GF2Type.Smith1979W3.Cert690
