module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native Certificates.L34Borel

theorem l34Borel_check :
    l34BorelCheck (enumBFS 42 gensS 20160).tabs = true :=
  Certificates.certificate41501

private theorem found_of_mem_treeOK {step : ℕ → Tab → Tab} {k : ℕ} {root : Tab} {E : Enum}
    (h : treeOK step k root E = true) {x : Tab} (hx : x ∈ E.tabs.toList) :
    found (indexOf E.tabs) E.tabs x = true := by
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hx
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨-, -⟩, hall⟩ := h
  have := (hall i hi).1.1
  simp only [found, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [this]
  exact ⟨hi, rfl⟩

private theorem es_get {j : ℕ} (hj : j < 6) :
    ((Array.range 6).map fun j => (sylEnum j).tabs)[j]! = (sylEnum j).tabs := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

private theorem idxs_get {j : ℕ} (hj : j < 6) :
    (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf)[j]! =
      indexOf (sylEnum j).tabs := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

private theorem exists_central_involution {V : Subgroup (Equiv.Perm (Fin 42))}
    (hV : IsPGroup 2 V) (hne : V ≠ ⊥) :
    ∃ z ∈ V, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ v ∈ V, z * v = v * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hne
  have hZ : Nontrivial (Subgroup.center V) := hV.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center V) := hV.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := Subgroup.center V)
    rw [hk, pow_zero] at this
    exact lt_irrefl 1 this
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center V) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((z : V) : Equiv.Perm (Fin 42)), (z : V).2, ?_, ?_, ?_⟩
  · intro h1
    have : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    omega
  · have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have := congrArg (fun w : Subgroup.center V => ((w : V) : Equiv.Perm (Fin 42))) h2
    simpa using this
  · intro v hv
    have := Subgroup.mem_center_iff.1 z.2 ⟨v, hv⟩
    exact (congrArg Subtype.val this).symm

theorem l34Borel_spec :
    ∃ (u₀ : Equiv.Perm (Fin 42)) (T : ℕ → Subgroup (Equiv.Perm (Fin 42))),
      u₀ ∈ S ∧ u₀ ≠ 1 ∧ u₀ ^ 3 = 1 ∧
      (∀ j < 6, T j ≤ S ∧ Nat.card (T j) = 64 ∧ ∀ t ∈ T j, u₀ * t * u₀⁻¹ ∈ T j) ∧
      (∀ V : Subgroup (Equiv.Perm (Fin 42)), V ≤ S → IsPGroup 2 V → V ≠ ⊥ →
          (∀ v ∈ V, u₀ * v * u₀⁻¹ ∈ V) → ∃ j < 6, V ≤ T j) ∧
      (∀ j < 6, ∀ s ∈ S, (∀ t ∈ T j, s * t * s⁻¹ ∈ T j) →
          s ∈ T j ∨ u₀⁻¹ * s ∈ T j ∨ u₀⁻¹ * (u₀⁻¹ * s) ∈ T j) := by
  have h := l34Borel_check
  simp only [l34BorelCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hu0, hinv, hisz, hne, hcube, -, hsyl, hcover, hnorm⟩ := h
  have hS := enumerates_S
  obtain ⟨u₀, hu₀S, hu₀⟩ := hS.sound _ (mem_of_found hu0)
  have hu₀i : TabRep u0iT u₀⁻¹ := hu₀.inv hisz hinv
  have hu₀ne : u₀ ≠ 1 := by
    intro h1
    rw [h1] at hu₀
    rw [hu₀.tab_eq TabRep.idTab] at hne
    simp at hne
  have hu₀3 : u₀ ^ 3 = 1 := by
    rw [pow_three]
    exact ((hu₀.comp (hu₀.comp hu₀)).eq_iff TabRep.idTab).1 hcube
  let T : ℕ → Subgroup (Equiv.Perm (Fin 42)) := fun j =>
    Subgroup.closure {a | ∃ i < (sylGens[j]!).size, TabRep (sylGens[j]!)[i]! a}
  have hsylj : ∀ j < 6, sylOK (indexOf (enumBFS 42 gensS 20160).tabs)
      (enumBFS 42 gensS 20160).tabs j = true := fun j hj => (allBelow_eq_true.1 hsyl) j hj
  have hparts : ∀ j < 6,
      (∀ i < (sylGens[j]!).size, ∃ g ∈ S, TabRep (sylGens[j]!)[i]! g) ∧
      enumOK 42 sylGens[j]! (sylEnum j) = true ∧ (sylEnum j).tabs.size = 64 ∧
      ∀ k < (sylEnum j).tabs.size,
        found (indexOf (sylEnum j).tabs) (sylEnum j).tabs (conjU (sylEnum j).tabs[k]!) = true := by
    intro j hj
    have h1 := hsylj j hj
    simp only [sylOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h1
    obtain ⟨⟨⟨hg, he⟩, hsz⟩, hc⟩ := h1
    exact ⟨fun i hi => hS.sound _ (mem_of_found (hg i hi)), he, hsz, hc⟩
  have hTenum : ∀ j < 6, Enumerates (T j) (sylEnum j).tabs.toList := by
    intro j hj
    obtain ⟨hg, he, -, -⟩ := hparts j hj
    refine enumerates_closure (gens := sylGens[j]!) (fun a ha => ha) (fun i hi => ?_) he
    obtain ⟨g, -, hgrep⟩ := hg i hi
    exact ⟨g, ⟨i, hi, hgrep⟩, hgrep⟩
  have hTS : ∀ j < 6, T j ≤ S := by
    intro j hj
    rw [Subgroup.closure_le]
    rintro a ⟨i, hi, harep⟩
    obtain ⟨g, hgS, hgrep⟩ := (hparts j hj).1 i hi
    rw [harep.perm_eq hgrep]
    exact hgS
  have hTmem : ∀ j < 6, ∀ {t : Tab} {g : Equiv.Perm (Fin 42)}, TabRep t g →
      (found (indexOf (sylEnum j).tabs) (sylEnum j).tabs t = true ↔ g ∈ T j) := by
    intro j hj t g htg
    constructor
    · intro hf
      obtain ⟨g', hg', hrep⟩ := (hTenum j hj).sound _ (mem_of_found hf)
      rw [htg.perm_eq hrep]
      exact hg'
    · intro hg
      obtain ⟨t', ht', hrep⟩ := (hTenum j hj).complete g hg
      rw [htg.tab_eq hrep]
      exact found_of_mem_treeOK (hparts j hj).2.1 ht'
  have hTinv : ∀ j < 6, ∀ t ∈ T j, u₀ * t * u₀⁻¹ ∈ T j := by
    intro j hj t ht
    obtain ⟨k, hk, hrep⟩ := (hTenum j hj).exists_pos ht
    exact (hTmem j hj (TabRep.conjTab hu₀ hrep hu₀i)).1 ((hparts j hj).2.2.2 k hk)
  refine ⟨u₀, T, hu₀S, hu₀ne, hu₀3, fun j hj => ⟨hTS j hj, ?_, hTinv j hj⟩, ?_, ?_⟩
  · rw [(hTenum j hj).card, Array.length_toList]
    exact (hparts j hj).2.2.1
  ·
    intro V hVS hV hVne hVu
    have hu₀inv : ∀ v ∈ V, u₀⁻¹ * v * u₀ ∈ V := by
      intro v hv
      have h1 := hVu _ (hVu v hv)
      have hsq : u₀ * u₀ = u₀⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_three']
        exact hu₀3
      have : u₀⁻¹ * v * u₀ = u₀ * (u₀ * v * u₀⁻¹) * u₀⁻¹ := by
        calc u₀⁻¹ * v * u₀ = (u₀ * u₀) * v * (u₀ * u₀)⁻¹ := by rw [hsq, inv_inv]
          _ = u₀ * (u₀ * v * u₀⁻¹) * u₀⁻¹ := by group
      rw [this]
      exact h1
    obtain ⟨z, hzV, hz1, hz2, hzc⟩ := exists_central_involution hV hVne
    have hcen : ∀ w ∈ V, (∀ v ∈ V, w * v = v * w) → ∀ v ∈ V,
        (u₀ * w * u₀⁻¹) * v = v * (u₀ * w * u₀⁻¹) := by
      intro w hw hwc v hv
      have := hwc _ (hu₀inv v hv)
      calc u₀ * w * u₀⁻¹ * v = u₀ * (w * (u₀⁻¹ * v * u₀)) * u₀⁻¹ := by group
        _ = u₀ * ((u₀⁻¹ * v * u₀) * w) * u₀⁻¹ := by rw [this]
        _ = v * (u₀ * w * u₀⁻¹) := by group
    set z₁ := u₀ * z * u₀⁻¹ with hz₁
    set z₂ := u₀ * z₁ * u₀⁻¹ with hz₂
    have hz₁V : z₁ ∈ V := hVu z hzV
    have hz₁c : ∀ v ∈ V, z₁ * v = v * z₁ := hcen z hzV hzc
    have hz₂c : ∀ v ∈ V, z₂ * v = v * z₂ := hcen z₁ hz₁V hz₁c
    obtain ⟨k, hk, hzrep⟩ := hS.exists_pos (hVS hzV)
    have hz₁rep : TabRep (conjU (enumBFS 42 gensS 20160).tabs[k]!) z₁ :=
      TabRep.conjTab hu₀ hzrep hu₀i
    have hz₂rep : TabRep (conjU (conjU (enumBFS 42 gensS 20160).tabs[k]!)) z₂ :=
      TabRep.conjTab hu₀ hz₁rep hu₀i
    unfold coverScan at hcover
    have hck := (allBelow_eq_true.1 hcover) k hk
    simp only [] at hck
    have hnid : ((enumBFS 42 gensS 20160).tabs[k]! == idTab 42) = false := by
      rw [Bool.eq_false_iff]
      intro h1
      exact hz1 ((hzrep.beq_iff TabRep.idTab).1 h1)
    have hinvl : (comp 42 (enumBFS 42 gensS 20160).tabs[k]! (enumBFS 42 gensS 20160).tabs[k]! ==
        idTab 42) = true :=
      ((hzrep.comp hzrep).beq_iff TabRep.idTab).2 (by rw [← pow_two]; exact hz2)
    have hcomm : (comp 42 (enumBFS 42 gensS 20160).tabs[k]!
        (conjU (enumBFS 42 gensS 20160).tabs[k]!) ==
        comp 42 (conjU (enumBFS 42 gensS 20160).tabs[k]!) (enumBFS 42 gensS 20160).tabs[k]!) =
        true := ((hzrep.comp hz₁rep).beq_iff (hz₁rep.comp hzrep)).2 ((hz₁c z hzV).symm)
    rw [hnid, hinvl, hcomm] at hck
    simp only [Bool.false_or, Bool.not_true] at hck
    have h1 := hck
    obtain ⟨j, hj, hall⟩ := anyBelow_eq_true.1 h1
    beta_reduce at hall
    refine ⟨j, hj, fun v hv => ?_⟩
    obtain ⟨m, hm, hvrep⟩ := hS.exists_pos (hVS hv)
    have hmemC : (enumBFS 42 gensS 20160).tabs[m]! ∈
        centTabs 42 (centTabs 42 (centTabs 42 (enumBFS 42 gensS 20160).tabs
          (enumBFS 42 gensS 20160).tabs[k]!) (conjU (enumBFS 42 gensS 20160).tabs[k]!))
          (conjU (conjU (enumBFS 42 gensS 20160).tabs[k]!)) := by
      simp only [centTabs, Array.mem_filter]
      refine ⟨⟨⟨by simpa using getElem!_mem hm, ?_⟩, ?_⟩, ?_⟩
      · exact ((hvrep.comp hzrep).beq_iff (hzrep.comp hvrep)).2 (hzc v hv).symm
      · exact ((hvrep.comp hz₁rep).beq_iff (hz₁rep.comp hvrep)).2 (hz₁c v hv).symm
      · exact ((hvrep.comp hz₂rep).beq_iff (hz₂rep.comp hvrep)).2 (hz₂c v hv).symm
    obtain ⟨i, hi, hieq⟩ := exists_getElem!_of_mem (by simpa using hmemC)
    have hf := (allBelow_eq_true.1 hall) i hi
    rw [hieq, es_get hj, idxs_get hj] at hf
    exact (hTmem j hj hvrep).1 hf
  ·
    intro j hj s hsS hsN
    obtain ⟨k, hk, hsrep⟩ := hS.exists_pos hsS
    unfold normScan at hnorm
    have hnk := (allBelow_eq_true.1 ((allBelow_eq_true.1 hnorm) j hj)) k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hnk
    obtain ⟨⟨hsi1, hsi2⟩, hrest⟩ := hnk
    have hsirep : TabRep (invTab 42 (enumBFS 42 gensS 20160).tabs[k]!) s⁻¹ :=
      hsrep.inv hsi1 hsi2
    rw [es_get hj, idxs_get hj] at hrest
    have hgens : (allBelow (sylGens[j]!).size fun i =>
        found (indexOf (sylEnum j).tabs) (sylEnum j).tabs
          (conjTab 42 (enumBFS 42 gensS 20160).tabs[k]!
            (invTab 42 (enumBFS 42 gensS 20160).tabs[k]!) (sylGens[j]!)[i]!)) = true := by
      rw [allBelow_eq_true]
      intro i hi
      obtain ⟨g, -, hgrep⟩ := (hparts j hj).1 i hi
      have hgT : g ∈ T j := Subgroup.subset_closure ⟨i, hi, hgrep⟩
      exact (hTmem j hj (TabRep.conjTab hsrep hgrep hsirep)).2 (hsN g hgT)
    rcases hrest with ((h1 | h1) | h1) | h1
    · rw [hgens] at h1
      exact absurd h1 (by decide)
    · exact Or.inl ((hTmem j hj hsrep).1 h1)
    · exact Or.inr (Or.inl ((hTmem j hj (hu₀i.comp hsrep)).1 h1))
    · exact Or.inr (Or.inr ((hTmem j hj (hu₀i.comp (hu₀i.comp hsrep))).1 h1))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel
