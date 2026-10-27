module

public import Certificates.Data.Kernel.Census.HeConj2
public import CFSG.Certificates.Kernel.Census.ToMain
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
import CFSG.Certificates.Kernel.Census.ConjProof

public section

namespace CFSG.KC.HeConj

open Subgroup CFSG.KC.Enum CFSG.KC.Census CFSG.KS CFSG.KS.SporSch
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier CFSG.ABGLocalTools CFSG.Open
open scoped commutatorElement

@[expose] noncomputable def pperm (n w P : Nat) : Equiv.Perm (Fin n) := permOfArr n (unpackP n w P)

@[expose] def nodeH {G : Type*} [Group G] (xs : List G) (bm : List Nat) : Subgroup G :=
  closure {g | ∃ m ∈ bm, g = pcG xs m}

@[expose] def HW.facts {G : Type*} [Group G] (xs : List G) (E : Subgroup G) : HW → Prop
  | .small => Nat.card E < 4
  | .order4 e gf _ _ => pcG xs e ∈ E ∧ ∀ f ∈ gf, pcG xs f.t ∈ E ∧ pcG xs f.t ≠ 1
  | .closing s t v .. => pcG xs s ∈ E ∧ pcG xs s ≠ 1 ∧ pcG xs t ∈ E ∧ pcG xs t ≠ 1 ∧
      pcG xs v ∈ E

@[expose] def HW.isMono : HW → Bool
  | .order4 .. => true
  | _ => false

@[expose] def HW.isClosing : HW → Bool
  | .closing .. => true
  | _ => false

namespace T32

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer

variable {n w : Nat}

@[expose] def nodesP (d : HeD) : Array NodeP := d.nb.map fun b => ⟨b, default, #[]⟩

theorem nodesP_get (d : HeD) (i : Nat) : (nodesP d)[i]! = ⟨d.nb[i]!, default, #[]⟩ :=
  CFSG.KC.Census.SP.map_get' (fun b : Array Nat => (⟨b, default, #[]⟩ : NodeP)) rfl d.nb i

theorem nodesP_basis (d : HeD) : (nodesP d).map NodeP.basis = d.nb := by
  rw [nodesP, Array.map_map]
  exact Array.map_id d.nb

theorem pcN_nodesP (d : HeD) : pcN n w (nodesP d) = cN2 n w d := by
  simp only [pcN, cN2, nodesP, Array.map_map]
  rfl

theorem eqA_of_rep {t u : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u g) : eqA n t u = true := by
  unfold eqA
  rw [allLt_iff]
  intro i hi
  rw [beq_iff_eq, ht.apply hi, hu.apply hi]

theorem conj_one_map {W : Type*} [Group W] (H : Subgroup W) :
    H.map (MulAut.conj (1 : W)).toMonoidHom = H := by
  rw [show (MulAut.conj (1 : W)).toMonoidHom = MonoidHom.id W by ext; simp, map_id]

end T32

open T32 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer in
theorem tree32_sound {n w : Nat} {d : HeD} (h24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w)
    (ht : tree32OK n w d = true) (hn : nodes32OK n w d (List.range d.nb.size) = true) :
    PcRel (d.xs.map (pperm n w)) ∧ PcSep (d.xs.map (pperm n w)) ∧
      (∀ i < d.nb.size, (d.wits[i]!).facts (d.xs.map (pperm n w))
          (nodeH (d.xs.map (pperm n w)) d.nm[i]!) ∧
        ((d.wits[i]!).isClosing = true → ∀ m ∈ d.nm[i]!, bpar d.fl m = 0)) ∧
      ∀ E ≤ closure {g | g ∈ d.xs.map (pperm n w)}, IsElemAbelian 2 E → 4 ≤ Nat.card E →
        ∃ i < d.nb.size, ∃ s ∈ closure {g | g ∈ d.xs.map (pperm n w)},
          (nodeH (d.xs.map (pperm n w)) d.nm[i]!).map (MulAut.conj s).toMonoidHom ≤ E ∧
          ((d.wits[i]!).isMono = true ∨ ((d.wits[i]!).isClosing = true ∧
            (nodeH (d.xs.map (pperm n w)) d.nm[i]!).map (MulAut.conj s).toMonoidHom = E)) := by
  classical
  obtain ⟨e1, e2, hid⟩ := CFSG.KC.Census.SP.pid_good24 hw h24
  have G : CFSG.KC.Census.SP.Good n w := ⟨by omega, hw, e1, e2⟩
  simp only [tree32OK, Bool.and_eq_true] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcan, hpc⟩, hinv⟩, htab⟩, hrl⟩, hR⟩, -⟩, -⟩, -⟩, hks⟩ := ht
  simp only [canonD, Bool.and_eq_true, List.all_eq_true] at hcan
  obtain ⟨⟨⟨⟨hcx, hcu⟩, hcs⟩, hci⟩, hcb⟩ := hcan
  have Cx : ∀ x ∈ d.xs, canon1 n w x = true := fun x hx => (hcx x hx).1
  have Cu : ∀ x ∈ d.us.toList, canon1 n w x = true := fun x hx => (hcu x hx).1
  have Cs : ∀ x ∈ d.cs.toList, canon1 n w x = true := fun x hx => (hcs x hx).1
  have Ci : ∀ x ∈ d.ci.toList, canon1 n w x = true := fun x hx => (hci x hx).1
  have hUV : ∀ x ∈ d.us.toList, pvalid n w x = true := fun x hx => (hcu x hx).2
  have hxcv : ∀ x ∈ d.xs, canon1 n w x = true ∧ pvalid n w x = true := fun x hx => hcx x hx
  have hks' : ∀ p ∈ d.ks, p < n := fun p hp => by
    have := List.all_eq_true.1 hks p hp
    rwa [Nat.blt_eq] at this
  obtain ⟨hpcM, -⟩ := CFSG.KC.Census.SP.pcOK_of G d.xs d.rs d.cjs d.bs Cx hpc
  obtain ⟨hxv, hrel, hsep⟩ := pc_of_pcOK hpcM
  obtain ⟨hinvM, -⟩ := CFSG.KC.Census.SP.invOK_of G hxcv Cu hinv
  obtain ⟨htabM, hsz⟩ := CFSG.KC.Census.SP.conjTabOK_of G Cx Cs Ci htab
  have hxsP : d.xs.map (pperm n w) = (d.xs.map (unpackP n w)).map (permOfArr n) := by
    rw [List.map_map]
    rfl
  rw [hxsP]
  set xsA := d.xs.map (unpackP n w) with hxsA
  set xsP := xsA.map (permOfArr n) with hxsPdef
  have hrep := rep_pcA hxv
  have hppc : ∀ m, unpackP n w (ppcA n w d.xs m) = pcA n xsA m ∧
      canon1 n w (ppcA n w d.xs m) = true := fun m => CFSG.KC.Census.SP.ppcA_eq G d.xs m Cx
  have hpg : ∀ m, Rep n (unpackP n w (ppcA n w d.xs m)) (pcG xsP m) := fun m => by
    rw [(hppc m).1]
    exact hrep m
  set nodesM := (nodesP d).map (NodeP.toMain n w) with hnodesM
  set cNM := nodesM.map fun nd => maskCert n nd.basis with hcNM
  have hsize : nodesM.size = d.nb.size := by simp [nodesM, nodesP]
  have Cb : ∀ i : Nat, ∀ x ∈ ((nodesP d)[i]!).basis.toList, canon1 n w x = true := by
    intro i x hx
    rw [nodesP_get] at hx
    by_cases hi : i < d.nb.size
    · rw [getElem!_pos d.nb i hi] at hx
      exact (hcb _ (Array.getElem_mem_toList hi) x hx).1
    · rw [getElem!_neg d.nb i hi] at hx
      exact absurd hx List.not_mem_nil
  have Cv : ∀ i < (nodesP d).size, ∀ k < ((nodesP d)[i]!).basis.size,
      pvalid n w ((nodesP d)[i]!).basis[k]! = true := by
    intro i hi k hk
    have hi' : i < d.nb.size := by simpa [nodesP] using hi
    rw [nodesP_get] at hk ⊢
    dsimp only at hk ⊢
    rw [getElem!_pos d.nb i hi'] at hk ⊢
    rw [getElem!_pos _ k hk]
    exact (hcb _ (Array.getElem_mem_toList hi') _ (Array.getElem_mem_toList hk)).2
  have hcNget : ∀ i : Nat, cNM[i]! = ((cN2 n w d)[i]!).toMain n w := fun i => by
    rw [hcNM, hnodesM, CFSG.KC.Census.SP.cN_get G Cb i, pcN_nodesP]
  have hcNc : ∀ i : Nat, ∀ x ∈ ((cN2 n w d)[i]!).pts.toList, canon1 n w x = true := fun i => by
    rw [← pcN_nodesP]
    exact CFSG.KC.Census.SP.cN_canon G Cb i
  have hbM : ∀ i < d.nb.size, nodesM[i]!.basis = d.nb[i]!.map (unpackP n w) := fun i hi => by
    rw [hnodesM, CFSG.KC.Census.SP.map_get _ _ (by simpa [nodesP] using hi), nodesP_get]
    rfl
  have hnode : ∀ i < d.nb.size, node32OK n w d (cN2 n w d) i = true :=
    fun i hi => List.all_eq_true.1 hn i (List.mem_range.2 hi)
  have hE : ∀ i < d.nb.size, enumOK n nodesM[i]!.basis d.ks cNM[i]! = true := by
    intro i hi
    have h := hnode i hi
    unfold node32OK at h
    simp only [Bool.and_eq_true] at h
    have hcb' : ∀ x ∈ d.nb[i]!.toList, canon1 n w x = true := by
      intro x hx
      rw [getElem!_pos d.nb i hi] at hx
      exact (hcb _ (Array.getElem_mem_toList hi) x hx).1
    rw [hbM i hi, hcNget]
    exact enumOK_of_enumOKK (CFSG.KC.Census.SP.enumOKK_of_penumOK G hcb' (hcNc i) h.1.1.1.1)
  have hmemN : ∀ i < nodesM.size, ∀ {a : Array ℕ} {g : Equiv.Perm (Fin n)}, Rep n a g →
      memA n cNM[i]! a = true → g ∈ nodeSub n nodesM i :=
    fun i hi a g ha hm => enumOK_mem_of_any hks' (hE i (by omega)) ha hm
  have hcardN : ∀ i < nodesM.size, Nat.card (nodeSub n nodesM i) = cNM[i]!.pts.size :=
    fun i hi => (enumOK_spec hks' (hE i (by omega))).2.1
  have hcardN' : ∀ i < d.nb.size,
      Nat.card (nodeSub n nodesM i) = ((cN2 n w d)[i]!).pts.size := fun i hi => by
    rw [hcardN i (by omega), hcNget]
    simp [ArrCertP.toMain]
  have hbasis : ∀ i < nodesM.size, ∀ k < nodesM[i]!.basis.size,
      validA n nodesM[i]!.basis[k]! = true :=
    fun i hi k hk => enumOK_gens_valid (hE i (by omega)) hk
  have hinN : ∀ i < d.nb.size, ∀ m, inNode n w d.xs (cN2 n w d)[i]! m = true →
      pcG xsP m ∈ nodeSub n nodesM i := by
    intro i hi m h
    refine hmemN i (by omega) (hpg m) ?_
    rw [hcNget, CFSG.KC.Census.SP.memA_eq (hcNc i) (hppc m).2]
    exact h
  have hne : ∀ m, notOne n w d.xs m = true → pcG xsP m ≠ 1 := by
    intro m h he
    have h1 : Nat.beq (ppcA n w d.xs m) (pid n w) = false := by
      unfold notOne at h
      revert h
      cases Nat.beq (ppcA n w d.xs m) (pid n w) <;> simp
    have h2 := CFSG.KC.Census.SP.eqA_pid G (hppc m).2
    rw [h1, eqA_of_rep (hpg m) (by rw [he]; exact rep_idA)] at h2
    exact Bool.noConfusion h2
  have hnodeEq : ∀ i < d.nb.size, nodeSub n nodesM i = nodeH xsP d.nm[i]! := by
    intro i hi
    have h := hnode i hi
    unfold node32OK at h
    simp only [Bool.and_eq_true] at h
    have hlen : (d.nm[i]!).length = d.nb[i]!.size := Nat.eq_of_beq_eq_true h.1.1.1.2
    have hz := List.all_eq_true.1 h.1.1.2
    have hk : ∀ k (hk : k < (d.nm[i]!).length),
        (d.nb[i]!)[k]! = ppcA n w d.xs (d.nm[i]!)[k] := by
      intro k hk
      have hk' : k < d.nb[i]!.toList.length := by simpa [hlen] using hk
      have := hz _ (mem_zip_of_lt hk hk')
      rw [getElem!_pos _ k (by simpa [hlen] using hk), ← Array.getElem_toList]
      exact (Nat.eq_of_beq_eq_true this).symm
    have hperm : ∀ k (hk : k < (d.nm[i]!).length),
        permOfArr n (nodesM[i]!.basis[k]!) = pcG xsP (d.nm[i]!)[k] := by
      intro k hk'
      have hkb : k < nodesM[i]!.basis.size := by
        rw [hbM i hi, Array.size_map, ← hlen]
        exact hk'
      have e : nodesM[i]!.basis[k]! = unpackP n w (ppcA n w d.xs (d.nm[i]!)[k]) := by
        rw [hbM i hi, CFSG.KC.Census.SP.map_get _ _ (by rw [← hlen]; exact hk'), hk k hk']
      exact Rep.unique (rep_of_validA (hbasis i (by omega) k hkb)) (by rw [e]; exact hpg _)
    unfold nodeSub nodeH
    congr 1
    ext g
    constructor
    · rintro ⟨k, hkb, rfl⟩
      have hkb' : k < (d.nm[i]!).length := by
        have : k < nodesM[i]!.basis.size := hkb
        rw [hbM i hi, Array.size_map, ← hlen] at this
        exact this
      exact ⟨_, List.getElem_mem hkb', hperm k hkb'⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hm
      refine ⟨k, ?_, hperm k hk'⟩
      change k < nodesM[i]!.basis.size
      rw [hbM i hi, Array.size_map, ← hlen]
      exact hk'
  refine ⟨hrel, hsep, fun i hi => ?_, ?_⟩
  ·
    have h := hnode i hi
    unfold node32OK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hw32⟩, hm⟩ := h
    rw [← hnodeEq i hi]
    have hin := hinN i hi
    have hcd := hcardN' i hi
    generalize d.wits[i]! = W at hw32 hm ⊢
    cases W with
    | small =>
      refine ⟨?_, fun h => by simp [HW.isClosing] at h⟩
      simp only [HW.facts]
      simp only [wit32OK, Nat.blt_eq] at hw32
      omega
    | order4 e gf _ _ =>
      refine ⟨?_, fun h => by simp [HW.isClosing] at h⟩
      simp only [wit32OK, Bool.and_eq_true, List.all_eq_true] at hw32
      exact ⟨hin e hw32.1.1, fun f hf => ⟨hin _ (hw32.2 f hf).1, hne _ (hw32.2 f hf).2⟩⟩
    | closing s t v _ _ _ _ _ _ _ _ =>
      simp only [wit32OK, Bool.and_eq_true] at hw32
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩ := hw32
      refine ⟨⟨hin s h1, hne s h2, hin t h3, hne t h4, hin v h5⟩, fun _ m hm' => ?_⟩
      simp only [Bool.and_eq_true] at hm
      exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 hm.1 m hm')
  intro E hES hE' hE4
  set S := closure {g | g ∈ xsP} with hSdef
  have hlen : xsP.length = xsA.length := List.length_map _
  set usA := d.us.map (unpackP n w) with husA
  set csA := d.cs.map (unpackP n w) with hcsA
  set ciA := d.ci.map (unpackP n w) with hciA
  have huk : ∀ k (hk : k < d.us.size), usA[k]! = unpackP n w (d.us.toList[k]'(by simpa using hk)) :=
    fun k hk => by rw [husA, CFSG.KC.Census.SP.map_get _ _ hk, getElem!_pos d.us k hk,
      Array.getElem_toList]
  simp only [invOK, Bool.and_eq_true, beq_iff_eq] at hinvM
  obtain ⟨⟨⟨himl, hus⟩, hwtl⟩, hwalk⟩ := hinvM
  replace hus := List.all_eq_true.1 hus
  have husl : d.im.length = usA.toList.length := by rw [himl, Array.length_toList]
  have hinvS : ∀ a ∈ S, a ^ 2 = 1 → a ≠ 1 → ∃ k < usA.size, Rep n usA[k]! a := by
    intro a ha ha2 ha1
    obtain ⟨m, hm, rfl⟩ := exists_pcG_of_pcRel hrel a ha
    rw [hlen] at hm
    have hw := invRest_spec hwalk m (hwtl ▸ hm)
    rw [Nat.zero_add] at hw
    rcases hw with hc | h0 | ⟨hx, hne'⟩
    · obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hc
      have hk' : k < usA.toList.length := husl ▸ hk
      have := hus _ (mem_zip_of_lt hk' hk)
      refine ⟨k, by simpa using hk', ?_⟩
      rw [hkm] at this
      have e : usA[k]! = usA.toList[k] := by
        rw [getElem!_pos usA k (by simpa using hk'), Array.getElem_toList]
      rw [e]
      exact rep_of_eqA (hrep m) this
    · rw [h0, pcG_zero] at ha1
      exact absurd rfl ha1
    · exfalso
      have hr := hrep m
      rw [hr.apply hx, hr.apply (Fin.isLt _)] at hne'
      have : (pcG xsP m) ((pcG xsP m) ⟨_, hx⟩) = ⟨_, hx⟩ := by
        rw [← Equiv.Perm.mul_apply, ← sq, ha2, Equiv.Perm.one_apply]
      rw [this] at hne'
      simp at hne'
  simp only [conjTabOK, Bool.and_eq_true, beq_iff_eq] at htabM
  obtain ⟨⟨⟨hcml, hcil⟩, hcs'⟩, hci'⟩ := htabM
  replace hcs' := List.all_eq_true.1 hcs'
  replace hci' := List.all_eq_true.1 hci'
  have hconjT : ∀ t < csA.size, ∃ s ∈ S, Rep n csA[t]! s ∧ Rep n ciA[t]! s⁻¹ := by
    intro t ht
    have ht1 : t < csA.toList.length := by simpa using ht
    have ht2 : t < d.cm.length := hcml ▸ ht
    have ht3 : t < ciA.toList.length := by simpa [hcil] using ht
    have e1 : csA[t]! = csA.toList[t] := by rw [getElem!_pos csA t ht, Array.getElem_toList]
    have e2 : ciA[t]! = ciA.toList[t] := by
      rw [getElem!_pos ciA t (by simpa using ht3), Array.getElem_toList]
    have hs1 : eqA n (pcA n xsA d.cm[t]) csA.toList[t] = true :=
      hcs' (csA.toList[t], d.cm[t]) (mem_zip_of_lt ht1 ht2)
    have hs := rep_of_eqA (hrep d.cm[t]) hs1
    have hc : eqA n (compA n ciA.toList[t] csA.toList[t]) (idA n) = true :=
      hci' (ciA.toList[t], csA.toList[t]) (mem_zip_of_lt ht3 ht1)
    refine ⟨_, pcG_mem _ _, by rw [e1]; exact hs, ?_⟩
    rw [e2]
    exact rep_inv_of_comp hs hc
  have hrl' : d.roots.length = d.us.size := Nat.eq_of_beq_eq_true hrl
  have hrootK : ∀ k (hk : k < d.us.size), rootOKC n nodesM cNM csA ciA usA[k]!
      (d.roots[k]'(by rw [hrl']; exact hk)) = true := by
    intro k hk
    have hk' : k < d.us.toList.length := by simpa using hk
    have h1 := List.all_eq_true.1 hR _ (mem_zip_of_lt hk' (by rw [hrl']; exact hk))
    dsimp only at h1
    have h1' : prootOKC n w ((nodesP d).map NodeP.basis) (pcN n w (nodesP d)) d.cs d.ci
        d.us.toList[k] (d.roots[k]'(by rw [hrl']; exact hk)) = true := by
      rw [nodesP_basis, pcN_nodesP]
      exact h1
    have hu := List.getElem_mem hk'
    rw [huk k hk]
    exact CFSG.KC.Census.SP.rootOKC_of G hid Cb Cs hsz (Cu _ hu) (inj_of_pvalid (hUV _ hu)).1 h1'
  have hents : ∀ i < d.nb.size, (d.wits[i]!).isMono = false →
      (d.ents[i]!).length = usA.size ∧ ∀ k (hk : k < d.us.size) (hk2 : k < (d.ents[i]!).length),
        entOK n nodesM cNM csA ciA i usA[k]! (d.ents[i]!)[k] = true := by
    intro i hi hmono
    have h := hnode i hi
    unfold node32OK at h
    simp only [Bool.and_eq_true] at h
    have hm := h.2
    have hp : pentsOK n w d.nb (cN2 n w d) d.us d.cs d.ci d.ents[i]! i = true := by
      generalize d.wits[i]! = W at hm hmono
      cases W with
      | small => exact hm
      | order4 _ _ _ _ => simp [HW.isMono] at hmono
      | closing _ _ _ _ _ _ _ _ _ _ _ =>
        simp only [Bool.and_eq_true] at hm
        exact hm.2
    unfold pentsOK at hp
    simp only [Bool.and_eq_true] at hp
    obtain ⟨hl, hall⟩ := hp
    refine ⟨by rw [husA, Array.size_map]; exact Nat.eq_of_beq_eq_true hl, fun k hk hk2 => ?_⟩
    have hk' : k < d.us.toList.length := by simpa using hk
    have h1 := List.all_eq_true.1 hall _ (mem_zip_of_lt hk' hk2)
    dsimp only at h1
    have h1' : pentOK n w ((nodesP d).map NodeP.basis) (pcN n w (nodesP d)) d.cs d.ci i
        d.us.toList[k] (d.ents[i]!)[k] = true := by
      rw [nodesP_basis, pcN_nodesP]
      exact h1
    have hu := List.getElem_mem hk'
    rw [huk k hk]
    exact CFSG.KC.Census.SP.entOK_of G hid Cb Cv Cs hsz (by simpa [nodesP] using hi) (Cu _ hu)
      (inj_of_pvalid (hUV _ hu)).1 h1'
  suffices hWE : ∃ i < nodesM.size, ∃ s ∈ S,
      (nodeSub n nodesM i).map (MulAut.conj s).toMonoidHom ≤ E ∧
      ((d.wits[i]!).isMono = true ∨ ((d.wits[i]!).isClosing = true ∧
        (nodeSub n nodesM i).map (MulAut.conj s).toMonoidHom = E)) by
    obtain ⟨i, hi, s, hs, hle, halt⟩ := hWE
    rw [hnodeEq i (by omega)] at hle halt
    exact ⟨i, by omega, s, hs, hle, halt⟩
  refine forall_of_conjTree (S := S)
    (fun E => ∃ i < nodesM.size, ∃ s ∈ S, (nodeSub n nodesM i).map (MulAut.conj s).toMonoidHom ≤ E ∧
      ((d.wits[i]!).isMono = true ∨ ((d.wits[i]!).isClosing = true ∧
        (nodeSub n nodesM i).map (MulAut.conj s).toMonoidHom = E)))
    (fun N => ∃ i < nodesM.size, nodeSub n nodesM i = N ∧ (d.wits[i]!).isMono = true) ?_
    (fun E₀ E ⟨i, hi, hEq, hm⟩ hle _ _ _ =>
      ⟨i, hi, 1, one_mem _, by rw [conj_one_map, hEq]; exact hle, Or.inl hm⟩)
    (nodeSub n nodesM) nodesM.size ?_ ?_ ?_ hES hE' hE4
  ·
    rintro E s hs ⟨i, hi, s', hs', hle, halt⟩
    refine ⟨i, hi, s⁻¹ * s', mul_mem (inv_mem hs) hs', ?_, ?_⟩
    · have := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) hle
      rwa [CFSG.ComponentClassification.RankTwoSporadic.map_conj_map_conj,
        CFSG.ComponentClassification.RankTwoSporadic.map_conj_map_conj, inv_mul_cancel,
        conj_one_map] at this
    · rcases halt with hm | ⟨hc, heq⟩
      · exact Or.inl hm
      · refine Or.inr ⟨hc, ?_⟩
        rw [← CFSG.ComponentClassification.RankTwoSporadic.map_conj_map_conj, heq,
          CFSG.ComponentClassification.RankTwoSporadic.map_conj_map_conj, inv_mul_cancel,
          conj_one_map]
  ·
    intro a ha ha2 ha1
    obtain ⟨k, hk, hua⟩ := hinvS a ha ha2 ha1
    have hk' : k < d.us.size := by simpa [usA] using hk
    have hrk := hrootK k hk'
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
    by_cases hmono : (d.wits[i]!).isMono = true
    · exact Or.inl ⟨i, hi, rfl, hmono⟩
    obtain ⟨hel, hch⟩ := hents i (by omega) (by simpa using hmono)
    refine Or.inr fun u hu hu2 hui hcomm => ?_
    have hu1 : u ≠ 1 := fun h1 => hui (h1 ▸ one_mem _)
    obtain ⟨k, hk, hur⟩ := hinvS u hu hu2 hu1
    have hk' : k < d.us.size := by simpa [usA] using hk
    have hck := hch k hk' (by rw [hel]; exact hk)
    simp only [entOK] at hck
    split_ifs at hck with h0 h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
        at hck
      obtain ⟨⟨hl, hx⟩, hne'⟩ := hck
      have hbl := rep_of_validA (hbasis i hi _ hl)
      have hc := hcomm _ (subset_closure (mem_permsA hl))
      exfalso
      apply hne'
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
    have hle : (nodeSub n nodesM i ⊔ zpowers u).map (MulAut.conj s).toMonoidHom ≤
        nodeSub n nodesM ((d.ents[i]!)[k]'(by rw [hel]; exact hk)).2.1 := by
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
    have h := hnode i (by omega)
    unfold node32OK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hw32⟩, -⟩ := h
    have hc1 := hcardN' i (by omega)
    generalize hW : d.wits[i]! = W at hw32
    cases W with
    | small =>
      simp only [wit32OK, Nat.blt_eq] at hw32
      omega
    | order4 _ _ _ _ => exact Or.inl ⟨i, hi, rfl, by rw [hW]; rfl⟩
    | closing _ _ _ _ _ _ _ _ _ _ _ =>
      exact Or.inr ⟨i, hi, 1, one_mem _, (conj_one_map _).le,
        Or.inr ⟨by rw [hW]; rfl, conj_one_map _⟩⟩

namespace HWS

variable {n : Nat}

theorem nbeqT {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [Nat.beq_eq]
  exact h

theorem nbeqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem eq_of_eqOnL' {X : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat} (hX : BaseFaithful X bs)
    {f g : Nat → Nat} {u v : Equiv.Perm (Fin n)} (hf : RepF n f u) (hg : RepF n g v)
    (huv : v⁻¹ * u ∈ X) (h : eqOnL bs f g = true) : u = v := by
  have h1 := hX (v⁻¹ * u) huv fun x hx => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    refine Fin.ext ?_
    rw [← hf x x.2, ← hg x x.2]
    exact (eqOnL_iff bs f g).1 h x hx
  exact (inv_mul_eq_one.1 h1).symm

theorem repF_bpcAt {nfp : Nat → Nat → Nat} {uf : Nat → Nat} :
    ∀ {fl xf : List Nat} {xs : List (Equiv.Perm (Fin n))}, fl.length = xs.length →
      xf.length = xs.length → (∀ k < xs.length, RepF n (xp nfp uf fl[k]! xf[k]!) xs[k]!) →
      ∀ m, RepF n (bpcAt nfp uf fl xf m) (pcG xs m)
  | [], [], [], _, _, _, m => by
    intro x hx
    simp [bpcAt, pcG]
  | f :: fl, F :: xf, x :: xs, hl, hl', hr, m => by
    have ih := repF_bpcAt (fl := fl) (xf := xf) (xs := xs) (by simpa using hl) (by simpa using hl')
      (fun k hk => by simpa using hr (k + 1) (by simpa using hk)) (m / 2)
    have hx : RepF n (xp nfp uf f F) x := by simpa using hr 0 (by simp)
    intro y hy
    change strictN (bpcAt nfp uf fl xf (m / 2) y) (fun z => nIf(Nat.beq (m % 2) 1,
      xp nfp uf f F z, z)) = _
    rw [strictN_val, pcG]
    by_cases hm : m % 2 = 1
    · rw [nbeqT hm, if_pos hm]
      exact (hx.comp ih) y hy
    · rw [nbeqF hm, if_neg hm, one_mul]
      exact ih y hy
  | [], _ :: _, _, h1, h2, _, _ | _ :: _, [], _, h1, h2, _, _ | _ :: _, _, [], h1, h2, _, _
  | [], [], _ :: _, h1, h2, _, _ => by
    simp only [List.length_cons, List.length_nil] at h1 h2
    omega

theorem repF_prodP {α : Type*} (φ : α → Nat → Nat) (ψ : α → Equiv.Perm (Fin n)) :
    ∀ L : List α, (∀ a ∈ L, RepF n (φ a) (ψ a)) → RepF n (prodP (L.map φ)) (L.map ψ).prod
  | [], _ => fun _ _ => rfl
  | a :: L, h => by
    have ih := repF_prodP φ ψ L fun b hb => h b (List.mem_cons_of_mem a hb)
    intro x hx
    change strictN (prodP (L.map φ) x) (φ a) = _
    rw [strictN_val, List.map_cons, List.prod_cons]
    exact ((h a List.mem_cons_self).comp ih) x hx

theorem repF_cmp {a ai b bi : Nat → Nat} {A A' B B' : Equiv.Perm (Fin n)} (ha : RepF n a A)
    (hai : RepF n ai A') (hb : RepF n b B) (hbi : RepF n bi B') :
    RepF n (cmp a ai b bi) (A * B * A' * B') := by
  intro x hx
  simp only [cmp, strictN_val]
  have := (ha.comp (hb.comp (hai.comp hbi))) x hx
  simpa only [mul_assoc] using this

theorem mem_cent_closure {G : Type*} [Group G] {S : Set G} {x : G}
    (h : ∀ s ∈ S, s * x = x * s) : x ∈ centralizer (closure S : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  induction hy using closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]

theorem mem_normalizer_of_conj_le {X : Subgroup (Equiv.Perm (Fin n))} {y : Equiv.Perm (Fin n)}
    (h : ∀ x ∈ X, y * x * y⁻¹ ∈ X) : y ∈ normalizer (X : Set (Equiv.Perm (Fin n))) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hle : X.map (MulAut.conj y).toMonoidHom ≤ X := by
    rintro _ ⟨z, hz, rfl⟩
    exact h z hz
  have heq : X.map (MulAut.conj y).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  rw [← heq] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have : z = x := by
    simpa using hzx
  rwa [← this]

theorem xor_one_div (j : Nat) : Nat.xor j 1 / 2 = j / 2 := by
  change (j ^^^ 1) / 2 = j / 2
  rw [← Nat.shiftRight_one, ← Nat.shiftRight_one, Nat.shiftRight_xor_distrib]
  simp

theorem xor_one_mod (j : Nat) : Nat.xor j 1 % 2 = 1 - j % 2 := by
  change (j ^^^ 1) % 2 = 1 - j % 2
  rw [Nat.xor_mod_two_eq]
  omega

end HWS

open HWS in
theorem hwOK_sound {n : Nat} {bs : List Nat} {X : Subgroup (Equiv.Perm (Fin n))}
    (hX : BaseFaithful X bs) (hbs : ∀ b ∈ bs, b < n) {nfv : Nat → Bool} {nfp : Nat → Nat → Nat}
    (hnf : ∀ F, nfv F = true → ∃ g ∈ X, RepF n (nfp F) g) {uf : Nat → Nat} {fl xf : List Nat}
    {xs : List (Equiv.Perm (Fin n))} (hfl : fl.length = xs.length) (hxf : xf.length = xs.length)
    (hxr : ∀ k < xs.length, RepF n (xp nfp uf fl[k]! xf[k]!) xs[k]!)
    (hxX : ∀ y ∈ xs, ∀ x ∈ X, y * x * y⁻¹ ∈ X) {bm : List Nat} {wit : HW}
    (h : hwOK nfv nfp uf bs fl xf bm wit = true) (hE : IsElemAbelian 2 (nodeH xs bm))
    (hf : wit.facts xs (nodeH xs bm)) :
    (wit.isMono = true → ∃ y ∈ nE X (nodeH xs bm), 4 ∣ orderOf y) ∧
      (wit.isClosing = true → nodeH xs bm ≤ X → UWitness X (nodeH xs bm)) := by
  classical
  choose! g hgX hgR using hnf
  have hSN : closure {a | a ∈ xs} ≤ normalizer (X : Set (Equiv.Perm (Fin n))) :=
    (closure_le _).2 fun y hy => mem_normalizer_of_conj_le (hxX y hy)
  have hS : ∀ m, pcG xs m ∈ normalizer (X : Set (Equiv.Perm (Fin n))) :=
    fun m => hSN (pcG_mem xs m)
  have hep : ∀ m, RepF n (ep nfp uf fl xf m) (pcG xs m) := repF_bpcAt hfl hxf hxr
  have hconjX : ∀ m, ∀ x ∈ X, (pcG xs m)⁻¹ * x * pcG xs m ∈ X := fun m x hx => by
    have := (mem_normalizer_iff.1 (inv_mem (hS m)) x).1 hx
    simpa using this
  have hpair : ∀ F FI, pairOK nfv nfp bs F FI = true →
      nfv F = true ∧ nfv FI = true ∧ g FI = (g F)⁻¹ := by
    intro F FI hp
    simp only [pairOK, Bool.and_eq_true] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨h1, h2, ?_⟩
    have h3' : eqOnL bs (fun x => nfp F (nfp FI x)) (fun x => x) = true := by
      simpa only [idB, strictN_val] using h3
    exact eq_inv_of_mul_eq_one_right
      ((fixL_iff hX hbs ((hgR F h1).comp (hgR FI h2)) (mul_mem (hgX F h1) (hgX FI h2))).1 h3')
  have hcomm : ∀ F m, nfv F = true → commB nfp bs F (ep nfp uf fl xf m) = true →
      g F * pcG xs m = pcG xs m * g F := by
    intro F m hF hc
    have hc' : eqOnL bs (fun x => nfp F (ep nfp uf fl xf m x))
        (fun x => ep nfp uf fl xf m (nfp F x)) = true := by
      simpa only [commB, eqB, strictN_val] using hc
    refine eq_of_eqOnL' hX ((hgR F hF).comp (hep m)) ((hep m).comp (hgR F hF)) ?_ hc'
    have := mul_mem (inv_mem (hgX F hF)) (hconjX m _ (hgX F hF))
    simpa only [mul_inv_rev, mul_assoc] using this
  have hεi : ∀ a ∈ nodeH xs bm, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 a ha)
  have hcent : ∀ t, t ∈ nodeH xs bm → t ≠ 1 →
      centDer X t ≤ gammaE X (nodeH xs bm) := fun t ht ht1 =>
    le_iSup₂_of_le (f := fun t (_ : t ∈ nodeH xs bm) => ⨆ (_ : t ≠ 1), centDer X t) t ht
      (le_iSup_of_le (f := fun (_ : t ≠ 1) => centDer X t) ht1 le_rfl)
  cases wit with
  | small => exact ⟨fun h => by simp [HW.isMono] at h, fun h => by simp [HW.isClosing] at h⟩
  | order4 e gf m Y =>
    refine ⟨fun _ => ?_, fun h => by simp [HW.isClosing] at h⟩
    simp only [HW.facts] at hf
    obtain ⟨heE, hgf⟩ := hf
    simp only [hwOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hall, hY⟩, hYeq⟩, hY4⟩, hY2⟩ := h
    have hgfF : ∀ f ∈ gf, RepF n (GF.val nfp f) ⁅g f.c₁, g f.c₂⁆ ∧
        RepF n (GF.inv nfp f) ⁅g f.c₁, g f.c₂⁆⁻¹ ∧ ⁅g f.c₁, g f.c₂⁆ ∈ X ∧
        ⁅g f.c₁, g f.c₂⁆ ∈ gammaE X (nodeH xs bm) := by
      intro f hfm
      have hk := List.all_eq_true.1 hall f hfm
      simp only [GF.ok, Bool.and_eq_true] at hk
      obtain ⟨⟨⟨hp1, hp2⟩, hc1⟩, hc2⟩ := hk
      obtain ⟨v1, v1i, e1⟩ := hpair _ _ hp1
      obtain ⟨v2, v2i, e2⟩ := hpair _ _ hp2
      have r1i := hgR _ v1i
      have r2i := hgR _ v2i
      rw [e1] at r1i
      rw [e2] at r2i
      have hT := (hgf f hfm).1
      have hT1 := (hgf f hfm).2
      have m1 : g f.c₁ ∈ X ⊓ centralizer ({pcG xs f.t} : Set _) :=
        ⟨hgX _ v1, mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact (hcomm _ _ v1 hc1).symm⟩
      have m2 : g f.c₂ ∈ X ⊓ centralizer ({pcG xs f.t} : Set _) :=
        ⟨hgX _ v2, mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact (hcomm _ _ v2 hc2).symm⟩
      refine ⟨?_, ?_, ?_, hcent _ hT hT1 (commutator_mem_commutator m1 m2)⟩
      · rw [commutatorElement_def]
        exact repF_cmp (hgR _ v1) r1i (hgR _ v2) r2i
      · rw [commutatorElement_inv, commutatorElement_def]
        exact repF_cmp (hgR _ v2) r2i (hgR _ v1) r1i
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem m1.1 m2.1) (inv_mem m1.1)) (inv_mem m2.1)
    set γ := (gf.map fun f => ⁅g f.c₁, g f.c₂⁆).prod with hγ
    have hγR : RepF n (prodP (gf.map (GF.val nfp))) γ :=
      repF_prodP _ _ gf fun f hf => (hgfF f hf).1
    have hγiR : RepF n (prodP (gf.reverse.map (GF.inv nfp))) γ⁻¹ := by
      have := repF_prodP (GF.inv nfp) (fun f => ⁅g f.c₁, g f.c₂⁆⁻¹) gf.reverse
        fun f hf => (hgfF f (List.mem_reverse.1 hf)).2.1
      rw [hγ, List.prod_inv_reverse, List.map_map, ← List.map_reverse]
      exact this
    have hγX : γ ∈ X := Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
      exact (hgfF f hf).2.2.1
    have hγΓ : γ ∈ gammaE X (nodeH xs bm) := Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
      exact (hgfF f hf).2.2.2
    have hε := hεi _ heE
    have hyR : RepF n (fun x => strictN (strictN (prodP (gf.reverse.map (GF.inv nfp)) x)
        (ep nfp uf fl xf e)) fun z => ep nfp uf fl xf e (prodP (gf.map (GF.val nfp)) z))
        (pcG xs e * γ * pcG xs e * γ⁻¹) := by
      intro x hx
      simp only [strictN_val]
      have := ((hep e).comp (hγR.comp ((hep e).comp hγiR))) x hx
      simpa only [mul_assoc] using this
    have hyeq : pcG xs e * γ * pcG xs e * γ⁻¹ = ⁅pcG xs e, γ⁆ := by
      rw [commutatorElement_def, hε]
    have hyX : pcG xs e * γ * pcG xs e * γ⁻¹ ∈ X := by
      have h1 := (mem_normalizer_iff.1 (hS e) γ).1 hγX
      rw [hε] at h1
      exact mul_mem h1 (inv_mem hγX)
    have hYe : g Y = (pcG xs e * γ * pcG xs e * γ⁻¹) ^ m :=
      eq_of_eqOnL hX (hgR Y hY) (hyR.powF m) (hgX Y hY) (pow_mem hyX m) hYeq
    have h4 : g Y ^ 2 ^ (1 + 1) = 1 :=
      (fixL_iff hX hbs ((hgR Y hY).powF 4) (pow_mem (hgX Y hY) 4)).1 hY4
    have h2 : ¬ g Y ^ 2 ^ 1 = 1 := by
      intro he
      have := (fixL_iff hX hbs ((hgR Y hY).powF 2) (pow_mem (hgX Y hY) 2)).2 he
      unfold idB at hY2
      rw [this] at hY2
      exact Bool.noConfusion hY2
    have hord : orderOf (g Y) = 2 ^ (1 + 1) := orderOf_eq_prime_pow h2 h4
    refine ⟨(pcG xs e * γ * pcG xs e * γ⁻¹) ^ m, ?_, ?_⟩
    · rw [hyeq]
      exact pow_mem (commutator_mem_commutator heE hγΓ) m
    · rw [← hYe, hord]
      norm_num
  | closing s t v c ci kc gens G GI perf sw =>
    refine ⟨fun h => by simp [HW.isMono] at h, fun _ hEX => ?_⟩
    simp only [HW.facts] at hf
    obtain ⟨hsE, hs1, htE, ht1, hvE⟩ := hf
    simp only [hwOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, hct⟩, hpow⟩, hvc⟩, hGl⟩, hGIl⟩, hpl⟩, hall⟩, hsw⟩, hsG⟩ := h
    obtain ⟨vc, vci, eci⟩ := hpair _ _ hpc
    have hcX := hgX c vc
    have hctc := hcomm c t vc hct
    have hpow' : g c ^ 2 ^ kc = 1 :=
      (fixL_iff hX hbs ((hgR c vc).powF _) (pow_mem hcX _)).1 hpow
    have hpg : IsPGroup 2 (zpowers (g c)) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow')
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hvs : ⁅pcG xs v, g c⁆ = pcG xs s := by
      have rci := hgR ci vci
      rw [eci] at rci
      have hrep : RepF n (fun x => strictN (strictN (nfp ci x) (ep nfp uf fl xf v)) fun z =>
          ep nfp uf fl xf v (nfp c z)) (pcG xs v * g c * pcG xs v * (g c)⁻¹) := by
        intro x hx
        simp only [strictN_val]
        have := ((hep v).comp ((hgR c vc).comp ((hep v).comp rci))) x hx
        simpa only [mul_assoc] using this
      have hvX := hEX hvE
      rw [commutatorElement_def, hεi _ hvE]
      exact eq_of_eqOnL hX hrep (hep s)
        (mul_mem (mul_mem (mul_mem hvX hcX) hvX) (inv_mem hcX)) (hEX hsE) hvc
    have hGl' : G.length = gens.length := Nat.eq_of_beq_eq_true hGl
    have hj := fun j (hj : j < gens.length) => List.all_eq_true.1 hall j (List.mem_range.2 hj)
    have hGv : ∀ j < gens.length, nfv (G.getD j 0) = true ∧ nfv (GI.getD j 0) = true ∧
        g (GI.getD j 0) = (g (G.getD j 0))⁻¹ := fun j hj' => by
      have := hj j hj'
      simp only [Bool.and_eq_true] at this
      exact hpair _ _ this.1.1.1.1
    let lE : Nat → Equiv.Perm (Fin n) := fun j =>
      if j % 2 = 0 then g (G.getD (j / 2) 0) else (g (G.getD (j / 2) 0))⁻¹
    have hlR : ∀ j, j / 2 < gens.length → RepF n (nfp (bif Nat.beq (Nat.mod j 2) 0 then
        G.getD (Nat.div j 2) 0 else GI.getD (Nat.div j 2) 0)) (lE j) ∧ lE j ∈ X := by
      intro j hj'
      obtain ⟨v1, v2, e2⟩ := hGv _ hj'
      by_cases hm : j % 2 = 0
      · have hb : Nat.beq (Nat.mod j 2) 0 = true := nbeqT hm
        simp only [hb, cond_true, lE, if_pos hm]
        exact ⟨hgR _ v1, hgX _ v1⟩
      · have hb : Nat.beq (Nat.mod j 2) 0 = false := nbeqF hm
        simp only [hb, cond_false, lE, if_neg hm]
        have := hgR _ v2
        rw [e2] at this
        exact ⟨this, inv_mem (hgX _ v1)⟩
    let P : Subgroup (Equiv.Perm (Fin n)) := closure {x | ∃ j < gens.length, x = g (G.getD j 0)}
    have hlP : ∀ j, j / 2 < gens.length → lE j ∈ P := by
      intro j hj'
      have hm : g (G.getD (j / 2) 0) ∈ P := subset_closure ⟨j / 2, hj', rfl⟩
      by_cases h0 : j % 2 = 0
      · simp only [lE, if_pos h0]
        exact hm
      · simp only [lE, if_neg h0]
        exact inv_mem hm
    have hlt : ∀ wd, lettersLt (2 * G.length) wd = true → ∀ j ∈ wd, j / 2 < gens.length := by
      intro wd hw j hjw
      have := List.all_eq_true.1 hw j hjw
      rw [Nat.blt_eq] at this
      omega
    have hgw : ∀ wd, lettersLt (2 * G.length) wd = true →
        RepF n (gw nfp G GI wd) (wd.map lE).prod ∧ (wd.map lE).prod ∈ X ∧
          (wd.map lE).prod ∈ P := by
      intro wd hw
      refine ⟨repF_prodP _ lE wd fun j hjw => (hlR j (hlt wd hw j hjw)).1, ?_, ?_⟩
      · exact Subgroup.list_prod_mem _ fun x hx => by
          obtain ⟨j, hjw, rfl⟩ := List.mem_map.1 hx
          exact (hlR j (hlt wd hw j hjw)).2
      · exact Subgroup.list_prod_mem _ fun x hx => by
          obtain ⟨j, hjw, rfl⟩ := List.mem_map.1 hx
          exact hlP j (hlt wd hw j hjw)
    have hinv : ∀ wd, lettersLt (2 * G.length) wd = true →
        lettersLt (2 * G.length) (invW wd) = true ∧
          RepF n (gw nfp G GI (invW wd)) ((wd.map lE).prod)⁻¹ := by
      intro wd hw
      have hw' : lettersLt (2 * G.length) (invW wd) = true := by
        refine List.all_eq_true.2 fun j hj' => ?_
        simp only [invW, List.mem_reverse, List.mem_map] at hj'
        obtain ⟨i, hi, rfl⟩ := hj'
        have h1 := hlt wd hw i hi
        have h2 := xor_one_div i
        rw [Nat.blt_eq]
        omega
      refine ⟨hw', ?_⟩
      have := (hgw _ hw').1
      have he : ((invW wd).map lE).prod = ((wd.map lE).prod)⁻¹ := by
        rw [List.prod_inv_reverse, invW, List.map_reverse, List.map_map, List.map_map]
        congr 2
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, lE, xor_one_div, xor_one_mod]
        by_cases h0 : i % 2 = 0
        · rw [if_pos h0, if_neg (by omega)]
        · rw [if_neg h0, if_pos (by omega), inv_inv]
      rwa [he] at this
    have hPP : P ≤ ⁅P, P⁆ := by
      refine (closure_le _).2 ?_
      rintro _ ⟨j, hj', rfl⟩
      have := hj j hj'
      simp only [Bool.and_eq_true] at this
      obtain ⟨⟨⟨⟨-, -⟩, -⟩, hlet⟩, hpe⟩ := this
      have v1 := (hGv j hj').1
      let ψ : List Nat × List Nat → Equiv.Perm (Fin n) := fun ab =>
        ⁅(ab.1.map lE).prod, (ab.2.map lE).prod⁆
      have hab : ∀ ab ∈ perf.getD j [], lettersLt (2 * G.length) ab.1 = true ∧
          lettersLt (2 * G.length) ab.2 = true := fun ab hab => by
        have := List.all_eq_true.1 hlet ab hab
        simpa only [Bool.and_eq_true] using this
      have hR : RepF n (prodP ((perf.getD j []).map fun ab =>
          cmp (gw nfp G GI ab.1) (gw nfp G GI (invW ab.1)) (gw nfp G GI ab.2)
            (gw nfp G GI (invW ab.2)))) ((perf.getD j []).map ψ).prod := by
        refine repF_prodP _ ψ _ fun ab hab' => ?_
        obtain ⟨ha, hb⟩ := hab ab hab'
        have := repF_cmp (hgw _ ha).1 (hinv _ ha).2 (hgw _ hb).1 (hinv _ hb).2
        simp only [ψ, commutatorElement_def]
        exact this
      have hψ : ∀ ab ∈ perf.getD j [], ψ ab ∈ X ∧ ψ ab ∈ ⁅P, P⁆ := fun ab hab' => by
        obtain ⟨ha, hb⟩ := hab ab hab'
        refine ⟨?_, commutator_mem_commutator (hgw _ ha).2.2 (hgw _ hb).2.2⟩
        simp only [ψ, commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hgw _ ha).2.1 (hgw _ hb).2.1) (inv_mem (hgw _ ha).2.1))
          (inv_mem (hgw _ hb).2.1)
      have hpX : ((perf.getD j []).map ψ).prod ∈ X := Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨ab, hab', rfl⟩ := List.mem_map.1 hx
        exact (hψ ab hab').1
      rw [eq_of_eqOnL hX (hgR _ v1) hR (hgX _ v1) hpX hpe]
      exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨ab, hab', rfl⟩ := List.mem_map.1 hx
        exact (hψ ab hab').2
    have hPC : P ≤ ⁅X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n))),
        X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n)))⁆ := by
      refine (closure_le _).2 ?_
      rintro _ ⟨j, hj', rfl⟩
      have := hj j hj'
      simp only [Bool.and_eq_true] at this
      obtain ⟨⟨⟨⟨-, hcf⟩, hpe⟩, -⟩, -⟩ := this
      have v1 := (hGv j hj').1
      have hcfF : ∀ f ∈ (gens.getD j ([], 0)).1, RepF n (CF.val nfp f) ⁅g f.x₁, g f.x₂⁆ ∧
          ⁅g f.x₁, g f.x₂⁆ ∈ ⁅X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n))),
            X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n)))⁆ := by
        intro f hfm
        have hk := List.all_eq_true.1 hcf f hfm
        simp only [CF.ok, Bool.and_eq_true] at hk
        obtain ⟨⟨hp1, hp2⟩, hbm⟩ := hk
        obtain ⟨w1, w1i, e1⟩ := hpair _ _ hp1
        obtain ⟨w2, w2i, e2⟩ := hpair _ _ hp2
        have r1i := hgR _ w1i
        have r2i := hgR _ w2i
        rw [e1] at r1i
        rw [e2] at r2i
        have hc : ∀ F, nfv F = true → (∀ m ∈ bm, commB nfp bs F (ep nfp uf fl xf m) = true) →
            g F ∈ X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n))) := by
          intro F hF hb
          refine ⟨hgX F hF, mem_cent_closure ?_⟩
          rintro _ ⟨m, hm, rfl⟩
          exact (hcomm F m hF (hb m hm)).symm
        have m1 := hc _ w1 fun m hm => by
          have := List.all_eq_true.1 hbm m hm
          simp only [Bool.and_eq_true] at this
          exact this.1
        have m2 := hc _ w2 fun m hm => by
          have := List.all_eq_true.1 hbm m hm
          simp only [Bool.and_eq_true] at this
          exact this.2
        refine ⟨?_, commutator_mem_commutator m1 m2⟩
        rw [commutatorElement_def]
        exact repF_cmp (hgR _ w1) r1i (hgR _ w2) r2i
      have hR := (repF_prodP (CF.val nfp) (fun f => ⁅g f.x₁, g f.x₂⁆) _
        fun f hf => (hcfF f hf).1).powF (gens.getD j ([], 0)).2
      have hmem : ((gens.getD j ([], 0)).1.map fun f => ⁅g f.x₁, g f.x₂⁆).prod ∈
          ⁅X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n))),
            X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n)))⁆ :=
        Subgroup.list_prod_mem _ fun x hx => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
          exact (hcfF f hf).2
      have hle : ⁅X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n))),
          X ⊓ centralizer (nodeH xs bm : Set (Equiv.Perm (Fin n)))⁆ ≤ X :=
        commutator_le.2 fun a ha b hb => by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
      rw [eq_of_eqOnL hX (hgR _ v1) hR (hgX _ v1) (pow_mem (hle hmem) _) hpe]
      exact pow_mem hmem _
    have hsP : pcG xs s ∈ P := by
      have hw := hgw sw hsw
      rw [eq_of_eqOnL hX (hep s) hw.1 (hEX hsE) hw.2.1 hsG]
      exact hw.2.2
    exact ⟨pcG xs s, hsE, hs1, ⟨pcG xs t, htE, ht1, g c, hcX, hctc, hpg, pcG xs v, hvE, hvs⟩,
      P, hPC, le_antisymm (commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hPP, hsP⟩

end CFSG.KC.HeConj

end
