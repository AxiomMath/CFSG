module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def nodeOKT (n : ℕ) (ps : List ℕ) (inW : Array ℕ → Bool) (d : ConjData)
    (cN : Array ArrCert) (e0 : Array (Array ℕ)) (i : ℕ) : Bool :=
  enumOKK n d.nodes[i]!.basis ps cN[i]! &&
    (d.nodes[i]!.wit.isMono ||
      ((decide (cN[i]!.pts.size < 4) || excOKW n ps inW e0 cN d.excs i) &&
        d.ents[i]!.length == d.us.size &&
        (d.us.toList.zip d.ents[i]!).all fun ue => entOK n d.nodes cN d.cs d.ci i ue.1 ue.2))

@[expose] def conjTreeOKW (n : ℕ) (ps : List ℕ) (inW : Array ℕ → Bool) (d : ConjData)
    (e0 : Array (Array ℕ)) : Bool :=
  let cN := d.nodes.map fun nd => maskCert n nd.basis
  pcOK n d.xs d.rs d.cjs d.bs && invOK n d.xs d.us d.im d.wt && conjTabOK n d.xs d.cm d.cs d.ci &&
    d.roots.length == d.us.size &&
    (d.us.toList.zip d.roots).all (fun ur => rootOKC n d.nodes cN d.cs d.ci ur.1 ur.2) &&
    allLt d.nodes.size (nodeOKT n ps inW d cN e0)

variable {n : ℕ}

theorem pc_of_conjTreeOKW {ps : List ℕ} {d : ConjData} {e0 : Array (Array ℕ)}
    {inW : Array ℕ → Bool} (h : conjTreeOKW n ps inW d e0 = true) :
    (∀ a ∈ d.xs, validA n a = true) ∧ PcRel (d.xs.map (permOfArr n)) ∧
      PcSep (d.xs.map (permOfArr n)) := by
  simp only [conjTreeOKW, Bool.and_eq_true] at h
  exact pc_of_pcOK h.1.1.1.1.1

theorem mem_nodeSub_of_conjTreeOKW {ps : List ℕ} {d : ConjData} {e0 : Array (Array ℕ)}
    {inW : Array ℕ → Bool} (hps : ∀ p ∈ ps, p < n) (h : conjTreeOKW n ps inW d e0 = true)
    {i : ℕ} (hi : i < d.nodes.size) {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g)
    (hm : memA n (maskCert n d.nodes[i]!.basis) a = true) : g ∈ nodeSub n d.nodes i := by
  simp only [conjTreeOKW, Bool.and_eq_true] at h
  have hn := allLt_spec h.2 hi
  simp only [nodeOKT, Bool.and_eq_true] at hn
  have hc : (d.nodes.map fun nd => maskCert n nd.basis)[i]! = maskCert n d.nodes[i]!.basis := by
    rw [getElem!_pos _ i (by simpa using hi), getElem!_pos d.nodes i hi, Array.getElem_map]
  rw [hc] at hn
  exact enumOK_mem_of_any hps (enumOK_of_enumOKK hn.1) ha hm

theorem roots_of_conjTreeOKW {ps : List ℕ} {d : ConjData} {e0 : Array (Array ℕ)}
    {inW : Array ℕ → Bool} (h : conjTreeOKW n ps inW d e0 = true) :
    ∀ a ∈ pcSub n d.xs, a ^ 2 = 1 → a ≠ 1 → ∃ i < d.nodes.size, ∃ s ∈ pcSub n d.xs,
      ∀ l < d.nodes[i]!.basis.size, ∀ g, Rep n d.nodes[i]!.basis[l]! g →
        g = s * a * s⁻¹ ∨ g = 1 := by
  simp only [conjTreeOKW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpc, hinv⟩, htab⟩, hrlen⟩, hroot⟩, -⟩ := h
  replace hroot := List.all_eq_true.1 hroot
  obtain ⟨hxv, hrel, -⟩ := pc_of_pcOK hpc
  have hrep := rep_pcA hxv
  have hlen : (d.xs.map (permOfArr n)).length = d.xs.length := List.length_map _
  simp only [invOK, Bool.and_eq_true, beq_iff_eq] at hinv
  obtain ⟨⟨⟨himl, hus⟩, hwtl⟩, hwalk⟩ := hinv
  replace hus := List.all_eq_true.1 hus
  have husl : d.im.length = d.us.toList.length := by rw [himl, Array.length_toList]
  have hinvS : ∀ a ∈ pcSub n d.xs, a ^ 2 = 1 → a ≠ 1 → ∃ k < d.us.size, Rep n d.us[k]! a := by
    intro a ha ha2 ha1
    obtain ⟨m, hm, rfl⟩ := exists_pcG_of_pcRel hrel a ha
    rw [hlen] at hm
    have hw := invRest_spec hwalk m (hwtl ▸ hm)
    rw [Nat.zero_add] at hw
    rcases hw with hc | h0 | ⟨hx, hne⟩
    · obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hc
      have hk' : k < d.us.toList.length := husl ▸ hk
      have := hus _ (mem_zip_of_lt hk' hk)
      refine ⟨k, by simpa using hk', ?_⟩
      rw [hkm] at this
      have e : d.us[k]! = d.us.toList[k] := by
        rw [getElem!_pos d.us k (by simpa using hk'), Array.getElem_toList]
      rw [e]
      exact rep_of_eqA (hrep m) this
    · rw [h0, pcG_zero] at ha1
      exact absurd rfl ha1
    · exfalso
      have hr := hrep m
      rw [hr.apply hx, hr.apply (Fin.isLt _)] at hne
      have : (pcG (d.xs.map (permOfArr n)) m) ((pcG (d.xs.map (permOfArr n)) m) ⟨_, hx⟩) =
          ⟨_, hx⟩ := by
        rw [← Equiv.Perm.mul_apply, ← sq, ha2, Equiv.Perm.one_apply]
      rw [this] at hne
      simp at hne
  simp only [conjTabOK, Bool.and_eq_true, beq_iff_eq] at htab
  obtain ⟨⟨⟨hcml, hcil⟩, hcs⟩, hci⟩ := htab
  replace hcs := List.all_eq_true.1 hcs
  replace hci := List.all_eq_true.1 hci
  have hconjT : ∀ t < d.cs.size, ∃ s ∈ pcSub n d.xs, Rep n d.cs[t]! s ∧ Rep n d.ci[t]! s⁻¹ := by
    intro t ht
    have ht1 : t < d.cs.toList.length := by simpa using ht
    have ht2 : t < d.cm.length := hcml ▸ ht
    have ht3 : t < d.ci.toList.length := by simpa [hcil] using ht
    have e1 : d.cs[t]! = d.cs.toList[t] := by rw [getElem!_pos d.cs t ht, Array.getElem_toList]
    have e2 : d.ci[t]! = d.ci.toList[t] := by
      rw [getElem!_pos d.ci t (by simpa using ht3), Array.getElem_toList]
    have hs1 : eqA n (pcA n d.xs d.cm[t]) d.cs.toList[t] = true :=
      hcs (d.cs.toList[t], d.cm[t]) (mem_zip_of_lt ht1 ht2)
    have hs := rep_of_eqA (hrep d.cm[t]) hs1
    have hc : eqA n (compA n d.ci.toList[t] d.cs.toList[t]) (idA n) = true :=
      hci (d.ci.toList[t], d.cs.toList[t]) (mem_zip_of_lt ht3 ht1)
    refine ⟨_, pcG_mem _ _, by rw [e1]; exact hs, ?_⟩
    rw [e2]
    exact rep_inv_of_comp hs hc
  intro a ha ha2 ha1
  obtain ⟨k, hk, hua⟩ := hinvS a ha ha2 ha1
  have hk' : k < d.us.toList.length := by simpa using hk
  have huk : d.us[k]! = d.us.toList[k]'hk' := by rw [getElem!_pos d.us k hk, Array.getElem_toList]
  have hrk := hroot _ (mem_zip_of_lt hk' (hrlen ▸ hk))
  rw [← huk] at hrk
  simp only [rootOKC, Bool.and_eq_true, decide_eq_true_eq] at hrk
  obtain ⟨⟨⟨hj, ht⟩, hall⟩, -⟩ := hrk
  obtain ⟨s, hsS, hs, hsi⟩ := hconjT _ ht
  have hsr := rep_compA hs (rep_compA hua hsi)
  refine ⟨_, hj, s, hsS, fun l hl g hg => ?_⟩
  have h2 := allLt_spec hall hl
  simp only [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · left
    rw [eq_of_eqA hg hsr h2, mul_assoc]
  · right
    exact eq_of_eqA hg rep_idA h2

theorem tree_of_conjTreeOKW {ps : List ℕ} {d : ConjData} {e0 : Array (Array ℕ)}
    {Wg : Subgroup (Equiv.Perm (Fin n))} {inW : Array ℕ → Bool} (hps : ∀ p ∈ ps, p < n)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ Wg)
    (hSW : pcSub n d.xs ≤ Wg) (h : conjTreeOKW n ps inW d e0 = true) :
    Nat.card (pcSub n d.xs) = 2 ^ d.xs.length ∧
      ∀ E : Subgroup (Equiv.Perm (Fin n)), E ≤ pcSub n d.xs → IsElemAbelian 2 E →
        4 ≤ Nat.card E →
        (∃ i < d.nodes.size, d.nodes[i]!.wit.isMono = true ∧ ∃ s ∈ pcSub n d.xs,
          (nodeSub n d.nodes i).map (MulAut.conj s).toMonoidHom ≤ E) ∨
          ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom := by
  simp only [conjTreeOKW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpc, hinv⟩, htab⟩, hrlen⟩, hroot⟩, hnodes⟩ := h
  replace hroot := List.all_eq_true.1 hroot
  obtain ⟨hxv, hrel, hsep⟩ := pc_of_pcOK hpc
  set S := pcSub n d.xs
  set nodes := d.nodes
  set cN := nodes.map fun nd => maskCert n nd.basis
  have hrep := rep_pcA hxv
  have hlen : (d.xs.map (permOfArr n)).length = d.xs.length := List.length_map _
  refine ⟨by rw [← hlen]; exact card_closure_of_pc hrel hsep, fun E hES hE hE4 => ?_⟩
  simp only [invOK, Bool.and_eq_true, beq_iff_eq] at hinv
  obtain ⟨⟨⟨himl, hus⟩, hwtl⟩, hwalk⟩ := hinv
  replace hus := List.all_eq_true.1 hus
  have husl : d.im.length = d.us.toList.length := by rw [himl, Array.length_toList]
  have hinvS : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ k < d.us.size, Rep n d.us[k]! a := by
    intro a ha ha2 ha1
    obtain ⟨m, hm, rfl⟩ := exists_pcG_of_pcRel hrel a ha
    rw [hlen] at hm
    have hw := invRest_spec hwalk m (hwtl ▸ hm)
    rw [Nat.zero_add] at hw
    rcases hw with hc | h0 | ⟨hx, hne⟩
    · obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hc
      have hk' : k < d.us.toList.length := husl ▸ hk
      have := hus _ (mem_zip_of_lt hk' hk)
      refine ⟨k, by simpa using hk', ?_⟩
      rw [hkm] at this
      have e : d.us[k]! = d.us.toList[k] := by
        rw [getElem!_pos d.us k (by simpa using hk'), Array.getElem_toList]
      rw [e]
      exact rep_of_eqA (hrep m) this
    · rw [h0, pcG_zero] at ha1
      exact absurd rfl ha1
    · exfalso
      have hr := hrep m
      rw [hr.apply hx, hr.apply (Fin.isLt _)] at hne
      have : (pcG (d.xs.map (permOfArr n)) m) ((pcG (d.xs.map (permOfArr n)) m) ⟨_, hx⟩) =
          ⟨_, hx⟩ := by
        rw [← Equiv.Perm.mul_apply, ← sq, ha2, Equiv.Perm.one_apply]
      rw [this] at hne
      simp at hne
  simp only [conjTabOK, Bool.and_eq_true, beq_iff_eq] at htab
  obtain ⟨⟨⟨hcml, hcil⟩, hcs⟩, hci⟩ := htab
  replace hcs := List.all_eq_true.1 hcs
  replace hci := List.all_eq_true.1 hci
  have hconjT : ∀ t < d.cs.size, ∃ s ∈ S, Rep n d.cs[t]! s ∧ Rep n d.ci[t]! s⁻¹ := by
    intro t ht
    have ht1 : t < d.cs.toList.length := by simpa using ht
    have ht2 : t < d.cm.length := hcml ▸ ht
    have ht3 : t < d.ci.toList.length := by simpa [hcil] using ht
    have e1 : d.cs[t]! = d.cs.toList[t] := by rw [getElem!_pos d.cs t ht, Array.getElem_toList]
    have e2 : d.ci[t]! = d.ci.toList[t] := by
      rw [getElem!_pos d.ci t (by simpa using ht3), Array.getElem_toList]
    have hs1 : eqA n (pcA n d.xs d.cm[t]) d.cs.toList[t] = true :=
      hcs (d.cs.toList[t], d.cm[t]) (mem_zip_of_lt ht1 ht2)
    have hs := rep_of_eqA (hrep d.cm[t]) hs1
    have hc : eqA n (compA n d.ci.toList[t] d.cs.toList[t]) (idA n) = true :=
      hci (d.ci.toList[t], d.cs.toList[t]) (mem_zip_of_lt ht3 ht1)
    refine ⟨_, pcG_mem _ _, by rw [e1]; exact hs, ?_⟩
    rw [e2]
    exact rep_inv_of_comp hs hc
  have hnode : ∀ i < nodes.size, nodeOKT n ps inW d cN e0 i = true :=
    fun i hi => allLt_spec hnodes hi
  have hnodeE : ∀ i < nodes.size, enumOK n nodes[i]!.basis ps cN[i]! = true := by
    intro i hi
    have := hnode i hi
    simp only [nodeOKT, Bool.and_eq_true] at this
    exact enumOK_of_enumOKK this.1
  have hbasis : ∀ i < nodes.size, ∀ k < nodes[i]!.basis.size,
      validA n nodes[i]!.basis[k]! = true := fun i hi k hk => enumOK_gens_valid (hnodeE i hi) hk
  have hmemN : ∀ i < nodes.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cN[i]! a = true → g ∈ nodeSub n nodes i :=
    fun i hi a g ha hm => enumOK_mem_of_any hps (hnodeE i hi) ha hm
  have hcardN : ∀ i < nodes.size, Nat.card (nodeSub n nodes i) = cN[i]!.pts.size :=
    fun i hi => (enumOK_spec hps (hnodeE i hi)).2.1
  have huk : ∀ k (hk : k < d.us.size), d.us[k]! = d.us.toList[k]'(by simpa using hk) :=
    fun k hk => by rw [getElem!_pos d.us k hk, Array.getElem_toList]
  set Mono : Subgroup (Equiv.Perm (Fin n)) → Prop := fun F => ∃ i < nodes.size,
    nodes[i]!.wit.isMono = true ∧ ∃ s ∈ S, (nodeSub n nodes i).map (MulAut.conj s).toMonoidHom ≤ F
  refine forall_of_conjTree (S := S)
    (fun E => Mono E ∨ ∃ w ∈ Wg, E = (closure (permsA n e0)).map (MulAut.conj w).toMonoidHom)
    Mono ?_ (fun E₀ E hm hle _ _ _ => Or.inl ?_) (nodeSub n nodes) nodes.size ?_ ?_ ?_ hES hE hE4
  ·
    intro E s hs hw
    rcases hw with ⟨i, hi, hm, t, ht, hle⟩ | ⟨w, hw, heq⟩
    · refine Or.inl ⟨i, hi, hm, s⁻¹ * t, S.mul_mem (S.inv_mem hs) ht, ?_⟩
      have := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) hle
      rwa [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel,
        show (MulAut.conj (1 : Equiv.Perm (Fin n))).toMonoidHom = MonoidHom.id _ by ext; simp,
        map_id] at this
    · refine Or.inr ⟨s⁻¹ * w, Wg.mul_mem (Wg.inv_mem (hSW hs)) hw, ?_⟩
      rw [← map_conj_map_conj, ← heq, map_conj_map_conj, inv_mul_cancel]
      ext x
      simp
  ·
    obtain ⟨i, hi, hmi, s, hs, hsle⟩ := hm
    exact ⟨i, hi, hmi, s, hs, hsle.trans hle⟩
  ·
    intro a ha ha2 ha1
    obtain ⟨k, hk, hua⟩ := hinvS a ha ha2 ha1
    have hk' : k < d.us.toList.length := by simpa using hk
    have hrk := hroot _ (mem_zip_of_lt hk' (hrlen ▸ hk))
    rw [← huk k hk] at hrk
    simp only [rootOKC, Bool.and_eq_true, decide_eq_true_eq] at hrk
    obtain ⟨⟨⟨hj, ht⟩, hall⟩, hu⟩ := hrk
    obtain ⟨s, hsS, hs, hsi⟩ := hconjT _ ht
    have hsr := rep_compA hs (rep_compA hua hsi)
    refine ⟨_, hj, s, hsS, le_antisymm ?_ ?_⟩
    · rw [nodeSub, closure_le]
      rintro _ ⟨l, hl, rfl⟩
      dsimp only
      have hbl := rep_of_validA (hbasis _ hj l hl)
      have h2 := allLt_spec hall hl
      simp only [Bool.or_eq_true] at h2
      rw [SetLike.mem_coe, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases h2 with h2 | h2
      · rw [eq_of_eqA hbl hsr h2, ← mul_assoc]
        exact mem_zpowers _
      · rw [eq_of_eqA hbl rep_idA h2]
        exact one_mem _
    · rw [MonoidHom.map_zpowers, zpowers_le, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hmemN _ hj hsr hu
      rwa [← mul_assoc] at this
  ·
    intro i hi
    have hn := hnode i hi
    simp only [nodeOKT, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at hn
    obtain ⟨-, hm | ⟨⟨-, hel⟩, hch⟩⟩ := hn
    · refine Or.inl ⟨i, hi, hm, 1, S.one_mem, ?_⟩
      rw [show (MulAut.conj (1 : Equiv.Perm (Fin n))).toMonoidHom = MonoidHom.id _ by ext; simp,
        map_id]
    refine Or.inr fun u hu hu2 hui hcomm => ?_
    have hu1 : u ≠ 1 := fun h1 => hui (h1 ▸ one_mem _)
    obtain ⟨k, hk, hur⟩ := hinvS u hu hu2 hu1
    have hk' : k < d.us.toList.length := by simpa using hk
    have hck := hch _ (mem_zip_of_lt hk' (by rw [hel]; exact hk))
    rw [← huk k hk] at hck
    simp only [entOK] at hck
    split_ifs at hck with h0 h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
        at hck
      obtain ⟨⟨hl, hx⟩, hne⟩ := hck
      have hbl := rep_of_validA (hbasis i hi _ hl)
      have hc := hcomm _ (subset_closure (mem_permsA hl))
      exfalso
      apply hne
      have e1 := hbl ⟨_, hx⟩
      have e2 := hur ⟨_, hx⟩
      rw [e1, e2, hur, hbl]
      have := congrArg (fun g : Equiv.Perm (Fin n) => (g ⟨_, hx⟩ : ℕ)) hc
      simpa only [Equiv.Perm.mul_apply] using this.symm
    · exact absurd (hmemN i hi hur hck) hui
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hck
    obtain ⟨⟨⟨⟨hj, ht⟩, hcard⟩, hib⟩, hu'⟩ := hck
    obtain ⟨s, hsS, hs, hsi⟩ := hconjT _ ht
    refine ⟨_, hj, s, hsS, ?_⟩
    have hle : (nodeSub n nodes i ⊔ zpowers u).map (MulAut.conj s).toMonoidHom ≤
        nodeSub n nodes ((d.ents[i]!)[k]'(by rw [hel]; exact hk)).2.1 := by
      rw [map_le_iff_le_comap]
      refine sup_le ?_ ?_
      · rw [nodeSub, closure_le]
        rintro _ ⟨l, hl, rfl⟩
        dsimp only
        have hbl := rep_of_validA (hbasis i hi l hl)
        rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have := hmemN _ hj (rep_compA hs (rep_compA hbl hsi)) (allLt_spec hib hl)
        rwa [← mul_assoc] at this
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have := hmemN _ hj (rep_compA hs (rep_compA hur hsi)) hu'
        rwa [← mul_assoc] at this
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [card_map_of_injective (MulAut.conj s).injective, hcardN _ hj, hcard, ← hcardN i hi]
    exact two_mul_card_le_sup hui
  ·
    intro i hi h4
    have hn := hnode i hi
    simp only [nodeOKT, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hn
    obtain ⟨hEi, hm | ⟨⟨⟨hs | hx, -⟩, -⟩⟩⟩ := hn
    · refine Or.inl ⟨i, hi, hm, 1, S.one_mem, ?_⟩
      rw [show (MulAut.conj (1 : Equiv.Perm (Fin n))).toMonoidHom = MonoidHom.id _ by ext; simp,
        map_id]
    · rw [hcardN i hi] at h4
      omega
    · exact Or.inr (Or.inr (eq_map_of_excOKW hps hinW (enumOK_of_enumOKK hEi) hx))

end CFSG.ComponentClassification.RankTwoSporadic.Cert
