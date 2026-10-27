module

public import Certificates.Certificate21262
public import CFSG.LargeExtraspecial.SMod20CollCertBase

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [local irreducible] uaPts uPts uPos

theorem uaMem_get {j q : ℕ} (hj : j < 891) (hq : q < 693) :
    uaMem uaPts[j]! q = true ↔ (⟨q, hq⟩ : Fin 693) ∈ wPlane j := by
  unfold uaMem
  rw [anyIn_eq_true]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, Fin.ext (by rw [wPt_val hj hk]; exact beq_iff_eq.1 he)⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, by rw [beq_iff_eq, ← wPt_val hj hk, he]⟩

theorem uaFlags_get {j q : ℕ} (hj : j < 891) (hq : q < 693) :
    ((uaFlags uaPts)[j]!)[q]! = true ↔ (⟨q, hq⟩ : Fin 693) ∈ wPlane j := by
  unfold uaFlags
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn,
    getElem!_pos _ q (by rw [Array.size_ofFn]; exact hq), Array.getElem_ofFn]
  exact uaMem_get hj hq

theorem image_wPlane_eq {g : Equiv.Perm (Fin 693)} {j j' : ℕ}
    (hj : j < 891) (hj' : j' < 891) (h : ∀ k < 21, g (wPt j k) ∈ wPlane j') :
    ⇑g '' wPlane j = wPlane j' := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (wPlane_finite j')
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact h k hk
  · rw [Set.ncard_image_of_injective _ g.injective, ncard_wPlane hj, ncard_wPlane hj']

theorem ap_tvTabs (k x : Fin 693) :
    ap tvTabs[k.val]! x.val = (tvP k x).val := by
  rw [rep_tvP k x.val x.2, idx_of_lt _ x.2]
  rfl

theorem genPt_spec {g : ℕ} (hg : g < 46) :
    uPos[tvGens[g]!]! < 693 ∧ uPts[uPos[tvGens[g]!]!]! = tvGens[g]! := by
  have hc := tvGens_facts.2 g hg
  have hm : tvGens[g]! ∈ uPts.toList := Array.mem_toList_iff.2 hc
  have hlt := List.idxOf_lt_length_of_mem hm
  have hsz : uPts.toList.length = 693 := by rw [Array.length_toList, ptsFacts.size]
  have he := List.getElem_idxOf hlt
  rw [Array.getElem_toList] at he
  rw [uPos_get (mem_uPts.1 hc).1, getElem!_pos uPts _ (by rw [← Array.length_toList]; exact hlt)]
  exact ⟨hsz ▸ hlt, he⟩

theorem t46G_eq_gen {z : ℤ} (hz : z.natAbs - 1 < 46) :
    t46G z = tvP ⟨uPos[tvGens[z.natAbs - 1]!]!, (genPt_spec hz).1⟩ := by
  have e : CFSG.Sporadic.Fi22.Native.t46Gen z =
      tvTabs[(⟨_, (genPt_spec hz).1⟩ : Fin 693).val]! := by
    rw [tvTabs_get]
    exact congrArg tvTable (genPt_spec hz).2.symm
  have h := rep_t46G z
  rw [e] at h
  exact perm_eq_of_rep h (rep_tvP _)

section T46

theorem gen_image_wPlane {g : ℕ} (hg : g < 46) {j : ℕ} (hj : j < 891) :
    ∃ j' < 891, ⇑(tvP ⟨uPos[tvGens[g]!]!, (genPt_spec hg).1⟩) '' wPlane j = wPlane j' := by
  obtain ⟨j', hj', H⟩ := Certificates.certificate21262.2.2.2.1 g hg j hj
  refine ⟨j', hj', image_wPlane_eq hj hj' fun m hm => ?_⟩
  have hx := H m hm
  rw [← wPt_val hj hm, ap_tvTabs ⟨_, (genPt_spec hg).1⟩ (wPt j m)] at hx
  exact (uaMem_get hj' _).1 hx

theorem exists_image_wPlane {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) {j : ℕ} (hj : j < 891) :
    ∃ j' < 891, ⇑g '' wPlane j = wPlane j' := by
  have hcl : T46 ≤ Subgroup.closure (Set.range t46G) :=
    T46_le_closure.trans ((Subgroup.closure_le _).2 (by
      rintro _ (rfl | rfl)
      · exact Subgroup.pow_mem _
          (t46_wordG_mem (fun z => Subgroup.subset_closure (Set.mem_range_self z)) _) 3
      · exact Subgroup.pow_mem _
          (t46_wordG_mem (fun z => Subgroup.subset_closure (Set.mem_range_self z)) _) 2))
  have key : ∀ z : ℤ, (t46G z)⁻¹ = t46G z ∧
      ∀ j < 891, ∃ j' < 891, ⇑(t46G z) '' wPlane j = wPlane j' := by
    intro z
    by_cases hz : z.natAbs - 1 < 46
    · rw [t46G_eq_gen hz, tvP_inv]
      exact ⟨rfl, fun j hj => gen_image_wPlane hz hj⟩
    · rw [t46G_eq_one (by omega), inv_one]
      exact ⟨rfl, fun j hj => ⟨j, hj, by simp⟩⟩
  have hg' := hcl hg
  clear hg
  induction hg' using Subgroup.closure_induction'' generalizing j with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    exact (key z).2 j hj
  | inv_mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [(key z).1]
    exact (key z).2 j hj
  | one => exact ⟨j, hj, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨j₁, hj₁, h₁⟩ := hy hj
    obtain ⟨j₂, hj₂, h₂⟩ := hx hj₁
    exact ⟨j₂, hj₂, by rw [Equiv.Perm.coe_mul, Set.image_comp, h₁, h₂]⟩

theorem exists_image_wPlane_zero {j : ℕ} (hj : j < 891) :
    ∃ g ∈ T46, ⇑g '' wPlane 0 = wPlane j := by
  refine Certificates.certificate21262.2.2.2.2.2.1
    (fun j => ∃ g ∈ T46, ⇑g '' wPlane 0 = wPlane j) ?_ ?_ j hj
  · intro v _ hv
    rw [beq_iff_eq] at hv
    exact ⟨1, T46.one_mem, by rw [hv]; simp⟩
  · rintro k hk j' hj' v hv he ⟨g, hg, hgj⟩
    refine ⟨tvP ⟨_, (genPt_spec hk).1⟩ * g, T46.mul_mem (tvP_mem _) hg, ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, hgj]
    refine image_wPlane_eq hj' hv fun m hm => ?_
    have hx := (allIn_eq_true.1 he) m (Nat.zero_le _) hm
    rw [← wPt_val hj' hm, ap_tvTabs ⟨_, (genPt_spec hk).1⟩ (wPt j' m)] at hx
    exact (uaMem_get hv _).1 hx

end T46

@[expose] noncomputable def stabElt (g : ℕ) :
    Equiv.Perm (Fin 693) :=
  tvPn stabWords[g]!.1 * tvPn stabWords[g]!.2

theorem stabWords_lt {g : ℕ} (hg : g < stabWords.size) :
    stabWords[g]!.1 < 693 ∧ stabWords[g]!.2 < 693 := by
  have : stabWords.size = 34 := rfl
  rw [this] at hg
  revert g
  decide

theorem ap_tvTabs_n {p : ℕ} (hp : p < 693) (x : Fin 693) :
    ap tvTabs[p]! x.val = (tvPn p x).val := by
  rw [rep_tvPn hp x.val x.2, idx_of_lt _ x.2]
  rfl

theorem stabAp_eq {g : ℕ} (hg : g < stabWords.size)
    (x : Fin 693) : stabAp tvTabs stabWords[g]! x.val = (stabElt g x).val := by
  unfold stabAp
  rw [ap_tvTabs_n (stabWords_lt hg).2, ap_tvTabs_n (stabWords_lt hg).1]
  rfl

section Stab

theorem stabElt_image {g : ℕ} (hg : g < stabWords.size) : ⇑(stabElt g) '' wPlane 0 = wPlane 0 := by
  refine image_wPlane_eq (by norm_num) (by norm_num) fun k hk => ?_
  have hx := Certificates.certificate21262.1 g hg k hk
  rw [← wPt_val (by norm_num) hk, stabAp_eq hg] at hx
  exact (uaMem_get (by norm_num) _).1 hx

theorem stabElt_mem_PA {g : ℕ} (hg : g < stabWords.size) : stabElt g ∈ PA 0 := by
  refine ⟨T46.mul_mem ?_ ?_, mem_stabilizer_wPlane.2 (stabElt_image hg)⟩
  · rw [tvPn, dite_eq_left (stabWords_lt hg).1]
    exact tvP_mem _
  · rw [tvPn, dite_eq_left (stabWords_lt hg).2]
    exact tvP_mem _

theorem sArr_stabElt {g : ℕ} (hg : g < stabWords.size) :
    sArr 0 (stabElt g) = (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! := by
  rw [getElem!_pos _ g (by rw [Array.size_map]; exact hg), Array.getElem_map]
  refine Array.ext (by rw [sArr_size, stabSig, Array.size_ofFn]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem]
  simp only [stabSig, Array.getElem_ofFn]
  rw [← wPt_val (by norm_num) hk', ← getElem!_pos stabWords g hg, stabAp_eq hg]

theorem exists_conj_uaRoot {a : ℕ} (ha : a < 512) :
    ∃ g ∈ PA 0, uaPsi 0 a = g * uaPsi 0 (uaRoot (uaCls collS2 a)) * g⁻¹ := by
  refine Certificates.certificate21262.2.2.2.2.1
    (fun v => ∃ g ∈ PA 0, uaPsi 0 v = g * uaPsi 0 (uaRoot (uaCls collS2 v)) * g⁻¹) ?_ ?_ a ha
  · intro v _ hv
    rw [beq_iff_eq] at hv
    exact ⟨1, (PA 0).one_mem, by rw [← hv]; group⟩
  · rintro g hg u _ v _ he ⟨x, hx, hxu⟩
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← sArr_stabElt hg] at he
    obtain ⟨hcls, hv⟩ := he
    subst hv
    refine ⟨stabElt g * x, (PA 0).mul_mem (stabElt_mem_PA hg) hx, ?_⟩
    have hpa := isPolarAut_of_mem (stabElt_mem_PA hg).1
    rw [← hcls, ← conj_uaPsi (by norm_num) hpa (stabElt_image hg), hxu]
    group

theorem uaMeet_eq {j : ℕ} (hj : j < 891) :
    uaMeet uaPts[0]! uaPts[j]! = (wPlane 0 ∩ wPlane j).ncard := by
  unfold uaMeet
  rw [countP_range_eq_card]
  have hinj : Set.InjOn (fun k => wPt j k) ↑((Finset.range 21).filter fun k =>
      uaMem uaPts[0]! (uaPts[j]!)[k]! = true) := fun k hk l hl h =>
    wPt_inj hj (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hl).1) h
  rw [← Set.ncard_coe_finset, ← hinj.ncard_image]
  congr 1
  ext p
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨k, ⟨hk, hmem⟩, rfl⟩
    refine ⟨?_, wPt_mem j hk⟩
    obtain ⟨l, hl, he⟩ := anyIn_eq_true.1 hmem
    exact ⟨l, hl, Fin.ext (by rw [wPt_val (by norm_num) hl, wPt_val hj hk]; exact beq_iff_eq.1 he)⟩
  · rintro ⟨⟨l, hl, rfl⟩, ⟨k, hk, he⟩⟩
    refine ⟨k, ⟨hk, anyIn_eq_true.2 ⟨l, hl, ?_⟩⟩, he⟩
    rw [beq_iff_eq, ← wPt_val (by norm_num) hl, ← wPt_val hj hk, he]

theorem exists_PA_zero_image {j : ℕ} (hj : j < 891) :
    ∃ g ∈ PA 0, ⇑g '' wPlane (uaDRoot uaPts (uaMeet uaPts[0]! uaPts[j]!)) = wPlane j := by
  refine Certificates.certificate21262.2.2.2.2.2.2 (fun j => ∃ g ∈ PA 0,
    ⇑g '' wPlane (uaDRoot uaPts (uaMeet uaPts[0]! uaPts[j]!)) = wPlane j) ?_ ?_ j hj
  · intro v _ hv
    rw [beq_iff_eq] at hv
    exact ⟨1, (PA 0).one_mem, by rw [← hv]; simp⟩
  · rintro g hg j' hj' v hv he ⟨x, hx, hxj⟩
    rw [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨hmeet, he⟩ := he
    refine ⟨stabElt g * x, (PA 0).mul_mem (stabElt_mem_PA hg) hx, ?_⟩
    rw [Equiv.Perm.coe_mul, Set.image_comp, ← hmeet, hxj]
    refine image_wPlane_eq hj' hv fun m hm => ?_
    have hx' := (allIn_eq_true.1 he) m (Nat.zero_le _) hm
    rw [← wPt_val hj' hm, stabAp_eq hg] at hx'
    exact (uaMem_get hv _).1 hx'

end Stab

end CFSG.LargeExtraspecial.SMod20
