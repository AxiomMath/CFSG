module

public import CFSG.ClassicalInvolution.AschTight.S1916Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjClosure (C Q : Subgroup G) : Subgroup G := ⨆ c ∈ C, conjSub c Q

theorem conjSub_le_conjClosure {C Q : Subgroup G} {c : G} (hc : c ∈ C) :
    conjSub c Q ≤ conjClosure C Q :=
  le_iSup₂ (f := fun d (_ : d ∈ C) => conjSub d Q) c hc

theorem le_conjClosure (C Q : Subgroup G) : Q ≤ conjClosure C Q := by
  have := conjSub_le_conjClosure (Q := Q) C.one_mem
  rwa [conjSub_one] at this

theorem conjClosure_le {C Q H : Subgroup G} (h : ∀ c ∈ C, conjSub c Q ≤ H) :
    conjClosure C Q ≤ H :=
  iSup₂_le h

theorem conjClosure_le_of_normalizes {C Q H : Subgroup G} (hQH : Q ≤ H)
    (hH : ∀ c ∈ C, conjSub c H = H) : conjClosure C Q ≤ H :=
  conjClosure_le fun c hc => (hH c hc) ▸ conjSub_mono hQH

theorem conjSub_conjClosure {C Q : Subgroup G} {c : G} (hc : c ∈ C) :
    conjSub c (conjClosure C Q) = conjClosure C Q := by
  have key : ∀ c ∈ C, conjSub c (conjClosure C Q) ≤ conjClosure C Q := by
    intro c hc
    rw [conjSub_le_iff]
    refine conjClosure_le fun d hd => ?_
    rw [← conjSub_le_iff, ← conjSub_mul]
    exact conjSub_le_conjClosure (C.mul_mem hc hd)
  refine le_antisymm (key c hc) ?_
  have h := key c⁻¹ (C.inv_mem hc)
  have h2 := (conjSub_le_iff c⁻¹).mp h
  rwa [inv_inv] at h2

theorem closure_twoElements_eq_conjClosure {C Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Subgroup.closure {x : G | x ∈ conjClosure C Q ∧ IsPGroup 2 (Subgroup.zpowers x)} =
      conjClosure C Q := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  refine conjClosure_le fun c hc x hx => Subgroup.subset_closure ⟨conjSub_le_conjClosure hc hx, ?_⟩
  exact (isPGroup_conjSub c hQ).to_le (Subgroup.zpowers_le.mpr hx)

theorem IsSylow2In.conj {P M : Subgroup G} (h : IsSylow2In P M) (g : G) :
    IsSylow2In (conjSub g P) (conjSub g M) := by
  refine ⟨conjSub_mono h.1, isPGroup_conjSub g h.2.1, fun V' hV'M hV'2 hle => ?_⟩
  have h1 : conjSub g⁻¹ V' ≤ M := by
    have := conjSub_mono (n := g⁻¹) hV'M
    rwa [conjSub_inv_conjSub] at this
  have h2 : P ≤ conjSub g⁻¹ V' := (conjSub_le_iff g).mp hle
  have h3 := h.2.2 _ h1 (isPGroup_conjSub g⁻¹ hV'2) h2
  calc V' = conjSub g (conjSub g⁻¹ V') := (conjSub_conjSub_inv g V').symm
    _ = conjSub g P := by rw [h3]

theorem IsSylow2In.exists_conj [Finite G] {P P' M : Subgroup G} (h : IsSylow2In P M)
    (h' : IsSylow2In P' M) : ∃ c ∈ M, conjSub c P = P' := by
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥M) (sylowOf h) (sylowOf h')
  rw [coe_sylowOf, coe_sylowOf] at hx
  refine ⟨x, x.2, ?_⟩
  have hPx : conjSub (x : G) P ≤ M := by
    have := conjSub_mono (n := (x : G)) h.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) P).subgroupOf M = P'.subgroupOf M := by
    have e : (conjSub (x : G) P).subgroupOf M = conjSub x (P.subgroupOf M) := by
      ext y
      rw [Subgroup.mem_subgroupOf, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_subgroupOf]
      simp
    rw [e]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hPx, inf_eq_left.mpr h'.1] at h2

theorem IsSylow2In.of_le {P M H : Subgroup G} (h : IsSylow2In P H) (hPM : P ≤ M) (hMH : M ≤ H) :
    IsSylow2In P M :=
  ⟨hPM, h.2.1, fun V' hV'M hV'2 hle => h.2.2 V' (hV'M.trans hMH) hV'2 hle⟩

theorem isUniqueInvolution_of_isSylow2In [Finite G] {Q M : Subgroup G} {z : G}
    (hQ : IsSylow2In Q M) (hz : IsUniqueInvolution Q z)
    (hMz : M ≤ Subgroup.centralizer ({z} : Set G)) : IsUniqueInvolution M z := by
  refine ⟨hQ.1 hz.mem, hz.ne_one, hz.sq, fun y hy hy2 => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  right
  have hy2' : IsPGroup 2 (Subgroup.zpowers y) := isPGroup_zpowers_of_mul_self_eq_one hy2 hy1
  obtain ⟨V, hV, hyV⟩ := IsSylow2In.exists_ge hy2' (Subgroup.zpowers_le.mpr hy)
  obtain ⟨c, hcM, hc⟩ := IsSylow2In.exists_conj hQ hV
  have hyQ : c⁻¹ * y * c ∈ Q := by
    have : y ∈ conjSub c Q := hc ▸ hyV (Subgroup.mem_zpowers y)
    rwa [mem_conjSub_iff] at this
  have hsq : c⁻¹ * y * c * (c⁻¹ * y * c) = 1 := by
    calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
      _ = 1 := by rw [hy2]; group
  have hne : c⁻¹ * y * c ≠ 1 := by
    intro h
    apply hy1
    calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have h1 : c⁻¹ * y * c = z := (hz.unique _ hyQ hsq).resolve_left hne
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hMz hcM)
  calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    _ = c * z * c⁻¹ := by rw [h1]
    _ = z := by rw [hcz]; group

theorem oddCoreOf_conjSub (g : G) (M : Subgroup G) :
    oddCoreOf (conjSub g M) = conjSub g (oddCoreOf M) := by
  let e : ↥M ≃* ↥(conjSub g M) :=
    Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hinv : (classicalInvolutionOddCore ↥M).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g M) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcoe : ∀ m : ↥M, ((e m : ↥(conjSub g M)) : G) = g * (m : G) * g⁻¹ := fun m => rfl
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hyO⟩ := mem_oddCoreOf_iff.mp hy
    rw [← hinv] at hyO
    obtain ⟨j, hj, hje⟩ := hyO
    have h1 : g * (j : G) * g⁻¹ = y := by
      have hje' : e j = ⟨y, hyC⟩ := hje
      have := congrArg Subtype.val hje'
      rw [hcoe] at this
      exact this
    rw [mem_conjSub_iff]
    have h2 : g⁻¹ * y * g = (j : G) := by rw [← h1]; group
    rw [h2]
    exact mem_oddCoreOf_iff.mpr ⟨j.2, hj⟩
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨hjJ, hjO⟩ := mem_oddCoreOf_iff.mp hy
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hyC : y ∈ conjSub g M := by
      rw [← h1]
      exact conj_mem_conjSub hjJ
    refine mem_oddCoreOf_iff.mpr ⟨hyC, ?_⟩
    rw [← hinv]
    refine ⟨⟨g⁻¹ * y * g, hjJ⟩, hjO, Subtype.ext ?_⟩
    show ((e ⟨g⁻¹ * y * g, hjJ⟩ : ↥(conjSub g M)) : G) = y
    rw [hcoe]
    exact h1

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
