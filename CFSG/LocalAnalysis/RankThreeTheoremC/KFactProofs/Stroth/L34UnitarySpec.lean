module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate41501
public import Certificates.Certificate41503

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Unitary

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native Certificates.L34Borel
  Certificates.L34Unitary

theorem l34Unitary_check :
    l34UnitaryCheck (enumBFS 42 gensS 20160).tabs (enumBFS 42 gTabs 241920).tabs = true :=
  Certificates.certificate41503

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

private abbrev T (j : ℕ) : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {a | ∃ i < (sylGens[j]!).size, TabRep (sylGens[j]!)[i]! a}

private theorem borel_concrete :
    ∃ u₀ : Equiv.Perm (Fin 42), u₀ ∈ S ∧ TabRep u0T u₀ ∧ u₀ ≠ 1 ∧
      (∀ j < 6, ∀ i < (sylGens[j]!).size, ∃ g ∈ T j, TabRep (sylGens[j]!)[i]! g) ∧
      (∀ j < 6, T j ≤ S ∧ Nat.card (T j) = 64 ∧ ∀ t ∈ T j, u₀ * t * u₀⁻¹ ∈ T j) ∧
      (∀ V : Subgroup (Equiv.Perm (Fin 42)), V ≤ S → IsPGroup 2 V → V ≠ ⊥ →
          (∀ v ∈ V, u₀ * v * u₀⁻¹ ∈ V) → ∃ j < 6, V ≤ T j) := by
  have h := (Certificates.certificate41501 :
    l34BorelCheck (enumBFS 42 gensS 20160).tabs = true)
  simp only [l34BorelCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hu0, hinv, hisz, hne, hcube, -, hsyl, hcover, -⟩ := h
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
  refine ⟨u₀, hu₀S, hu₀, hu₀ne, fun j hj i hi => ?_,
    fun j hj => ⟨hTS j hj, ?_, hTinv j hj⟩, ?_⟩
  · obtain ⟨g, -, hgrep⟩ := (hparts j hj).1 i hi
    exact ⟨g, Subgroup.subset_closure ⟨i, hi, hgrep⟩, hgrep⟩
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

theorem l34Unitary_spec :
    ∃ (u₀ : Equiv.Perm (Fin 42)) (E₀ : Subgroup (Equiv.Perm (Fin 42))),
      u₀ ∈ E₀ ∧ E₀ ≤ S ∧ Nat.card E₀ = 9 ∧ u₀ ≠ 1 ∧
      ∀ β ∈ R, β ≠ 1 → β * β = 1 → (∀ e ∈ E₀, β * e = e * β) →
        ∀ V D : Subgroup (Equiv.Perm (Fin 42)), V ≤ S → Nat.card V = 64 →
          (∀ v ∈ V, u₀ * v * u₀⁻¹ ∈ V) → D ≤ S → u₀ ∈ D → V ≤ D →
          (∀ x ∈ D, β * x * β⁻¹ ∈ D) → D = S := by
  obtain ⟨u₀, hu₀S, hu₀, hu₀ne, hTgen, hT, hcover⟩ := borel_concrete
  have h := l34Unitary_check
  simp only [l34UnitaryCheck, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨⟨hfb, hen⟩, hsz⟩, hscan⟩ := h
  have hS := enumerates_S
  have hR := enumerates_R
  obtain ⟨b, hbS, hb⟩ := hS.sound _ (mem_of_found hfb)
  have hsz2 : e0Gens.size = 2 := rfl
  have hE : Enumerates (Subgroup.closure ({u₀, b} : Set (Equiv.Perm (Fin 42))))
      e0Enum.tabs.toList := by
    refine enumerates_closure (gens := e0Gens) (A := {u₀, b}) (fun x hx => ?_) (fun j hj => ?_) hen
    · rcases hx with rfl | rfl
      · exact ⟨0, by rw [hsz2]; omega, hu₀⟩
      · exact ⟨1, by rw [hsz2]; omega, hb⟩
    · rw [hsz2] at hj
      interval_cases j
      · exact ⟨u₀, Or.inl rfl, hu₀⟩
      · exact ⟨b, Or.inr rfl, hb⟩
  have hle : Subgroup.closure ({u₀, b} : Set (Equiv.Perm (Fin 42))) ≤ S := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hu₀S, hbS]
  refine ⟨u₀, _, Subgroup.subset_closure (Or.inl rfl), hle, ?_, hu₀ne, ?_⟩
  · rw [hE.card, Array.length_toList]
    exact hsz
  intro β hβR hβ1 hββ hβc V D hVS hV64 hVu hDS hu₀D hVD hβD
  obtain ⟨k, hk, hr⟩ := hR.exists_pos hβR
  have hk' := hscan k hk
  set r := (enumBFS 42 gTabs 241920).tabs[k]! with hrdef
  have hrr : comp 42 r r = idTab 42 := (hr.comp hr).tab_eq (by rw [hββ]; exact TabRep.idTab)
  have hr1 : TabRep r β⁻¹ := hr.inv hr.1 hrr
  have hA : (r == idTab 42) = false := by
    rw [Bool.eq_false_iff]
    intro h1
    exact hβ1 ((hr.beq_iff TabRep.idTab).1 h1)
  have hB : (comp 42 r r == idTab 42) = true := beq_iff_eq.2 hrr
  have hC : (comp 42 r u0T == comp 42 u0T r) = true :=
    ((hr.comp hu₀).beq_iff (hu₀.comp hr)).2 (hβc u₀ (Subgroup.subset_closure (Or.inl rfl)))
  have hD : (comp 42 r t3bT == comp 42 t3bT r) = true :=
    ((hr.comp hb).beq_iff (hb.comp hr)).2 (hβc b (Subgroup.subset_closure (Or.inr rfl)))
  rw [hA, hB, hC, hD] at hk'
  simp only [Bool.not_true, Bool.false_or] at hk'
  have hVne : V ≠ ⊥ := by
    rintro rfl
    simp at hV64
  obtain ⟨j, hj, hVj⟩ := hcover V hVS (IsPGroup.of_card (n := 6) (by rw [hV64]; norm_num)) hVne hVu
  have hVeq : V = T j := Subgroup.eq_of_le_of_card_ge hVj (by rw [hV64, (hT j hj).2.1])
  have hTD : T j ≤ D := hVeq ▸ hVD
  have hpj := (allBelow_eq_true.1 hk') j hj
  simp only [pairOK, Bool.and_eq_true, beq_iff_eq] at hpj
  obtain ⟨hok, hsize⟩ := hpj
  have hbor : ∀ g ∈ (borelGens j).toList, ∃ a ∈ D, TabRep g a := by
    intro g hg
    have hg' : g ∈ borelGens j := Array.mem_toList_iff.1 hg
    simp only [borelGens, Array.mem_append, Array.mem_singleton] at hg'
    rcases hg' with rfl | hg'
    · exact ⟨u₀, hu₀D, hu₀⟩
    · obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem (Array.mem_toList_iff.2 hg')
      obtain ⟨a, haT, harep⟩ := hTgen j hj i hi
      exact ⟨a, hTD haT, harep⟩
  have hall : ∀ g ∈ (pairGens r j).toList, ∃ a ∈ D, TabRep g a := by
    intro g hg
    have hg' : g ∈ pairGens r j := Array.mem_toList_iff.1 hg
    simp only [pairGens, Array.mem_append, Array.mem_map] at hg'
    rcases hg' with hg' | ⟨g', hg', rfl⟩
    · exact hbor g (Array.mem_toList_iff.2 hg')
    · obtain ⟨a', ha'D, ha'⟩ := hbor g' (Array.mem_toList_iff.2 hg')
      exact ⟨β * a' * β⁻¹, hβD a' ha'D, hr.conjTab ha' hr1⟩
  let A : Set (Equiv.Perm (Fin 42)) :=
    {a | ∃ i < (pairGens r j).size, TabRep (pairGens r j)[i]! a}
  have hgens : ∀ i < (pairGens r j).size, ∃ a ∈ A, TabRep (pairGens r j)[i]! a := by
    intro i hi
    obtain ⟨a, -, ha⟩ := hall _ (getElem!_mem hi)
    exact ⟨a, ⟨i, hi, ha⟩, ha⟩
  have hEnum : Enumerates (Subgroup.closure A)
      (enumBFS 42 (pairGens r j) 20160).tabs.toList :=
    enumerates_closure (fun a ha => ha) hgens hok
  have hAD : Subgroup.closure A ≤ D := by
    rw [Subgroup.closure_le]
    rintro a ⟨i, hi, ha⟩
    obtain ⟨a', ha'D, ha'⟩ := hall _ (getElem!_mem hi)
    rw [ha.perm_eq ha']
    exact ha'D
  have hcard : Nat.card (Subgroup.closure A) = 20160 := by
    rw [hEnum.card, Array.length_toList]
    exact hsize
  exact Subgroup.eq_of_le_of_card_ge hDS (by rw [card_S, ← hcard]; exact Subgroup.card_le_of_le hAD)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Unitary
