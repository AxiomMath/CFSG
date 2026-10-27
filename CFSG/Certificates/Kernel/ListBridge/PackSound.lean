module

public import CFSG.Certificates.Kernel.ListBridge.Sound
public import Certificates.Data.Kernel.ListBridge
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge CFSG.Sporadic.Schreier

variable {n w : Nat}

theorem eq_of_prep {P Q : Nat} {g : Equiv.Perm (Fin n)}
    (hP : canonK n w (mask w) (n * w) P = true) (hQ : canonK n w (mask w) (n * w) Q = true)
    (gP : PRep n w P g) (gQ : PRep n w Q g) : P = Q := by
  obtain ⟨-, hw, hP1, -⟩ := CFSG.KS.PF.canon_facts hP
  obtain ⟨-, -, hQ1, -⟩ := CFSG.KS.PF.canon_facts hQ
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hP1 hQ1 fun i hi => by
    rw [gP ⟨i, hi⟩, gQ ⟨i, hi⟩]

theorem bfsK_sz {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true) :
    n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  exact szOK_facts' hk.1

theorem bfsK_canonG {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true) :
    ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := by
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  exact allN_spec hk.2.1

theorem getD_mem {gens : List (Equiv.Perm (Fin n))} {k : Nat} (hk : k < gens.length) :
    gens.getD k 1 ∈ gens := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem enum_closure {ng N : Nat} {G T E S : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}
    (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) :
    (∀ g, g ∈ Subgroup.closure {s | s ∈ gens} ↔ ∃ i < N, PRep n w (T i) g) ∧
      Nat.card (Subgroup.closure {s | s ∈ gens}) = N := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  have hn32 : n < 2 ^ 32 := by omega
  set H := Subgroup.closure {s | s ∈ gens} with hH
  obtain ⟨hN, hT0, -, hcl⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hQ := (bfsK_points (fun y => ∃ g ∈ H, PRep n w y g)
    ⟨1, H.one_mem, prep_pidn hn hw⟩ (fun y ⟨g, hg, hy⟩ k hk1 =>
      ⟨gens.getD k 1 * g, H.mul_mem (Subgroup.subset_closure (getD_mem (hl ▸ hk1))) hg,
        prep_pcomp hn32 (hG k hk1) hy⟩) hk).2.2.1
  have hsub : (H : Set (Equiv.Perm (Fin n))) ⊆ {g | ∃ i < N, PRep n w (T i) g} := by
    refine closure_subset_of_left_closed _ _ ⟨0, hN, by rw [hT0]; exact prep_pidn hn hw⟩ ?_
    rintro s hs z ⟨i, hi, hz⟩
    obtain ⟨k, hk1, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨j, hj, e⟩ := hcl i hi k (hl ▸ hk1)
    refine ⟨j, hj, ?_⟩
    rw [e]
    have := hG k (hl ▸ hk1)
    rw [List.getD_eq_getElem _ _ hk1] at this
    exact prep_pcomp hn32 this hz
  have hmem : ∀ g, g ∈ H ↔ ∃ i < N, PRep n w (T i) g := by
    intro g
    refine ⟨fun h => hsub h, ?_⟩
    rintro ⟨i, hi, hg⟩
    obtain ⟨g', hg', h'⟩ := hQ i hi
    rw [prep_unique hg h']
    exact hg'
  refine ⟨hmem, ?_⟩
  have hcan := bfsK_canon hk
  have hdist : ∀ a < N, ∀ b < N, T a = T b → a = b := by
    have hk' := hk
    unfold bfsK at hk'
    simp only [bAnd_iff] at hk'
    exact distinctK_inj hk'.2.2.2.2.1
  let f : Fin N → H := fun i => ⟨Classical.choose (hQ i.1 i.2),
    (Classical.choose_spec (hQ i.1 i.2)).1⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b e => Fin.ext ?_, fun g => ?_⟩
    · have e' : Classical.choose (hQ a.1 a.2) = Classical.choose (hQ b.1 b.2) :=
        congrArg Subtype.val e
      have ha := (Classical.choose_spec (hQ a.1 a.2)).2
      have hb := (Classical.choose_spec (hQ b.1 b.2)).2
      rw [e'] at ha
      exact hdist a.1 a.2 b.1 b.2 (eq_of_prep (hcan a.1 a.2) (hcan b.1 b.2) ha hb)
    · obtain ⟨i, hi, hg⟩ := (hmem g.1).1 g.2
      refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
      exact prep_unique (Classical.choose_spec (hQ i hi)).2 hg
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem prep_pwordK {ng : Nat} {P : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hG : ∀ k < ng, PRep n w (P k) (gens.getD k 1)) :
    ∀ wd : List Int, posW ng wd = true → PRep n w (pwordK n w P wd) (evalCodes gens wd)
  | [] , _ => prep_pidn hn hw
  | z :: wd, h => by
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hz, hzn⟩, hwd⟩ := h
    have ih := prep_pwordK hn hw hG wd (by simpa [posW] using hwd)
    change PRep n w (pcomp n w (mask w) (P (Nat.sub (Int.toNat z) 1)) (pwordK n w P wd)) _
    rw [evalCodes, if_pos hz]
    exact prep_pcomp (by omega) (hG (z.toNat - 1) (by omega)) ih

theorem inK_spec {N : Nat} {T : Nat → Nat} {x : Nat} (h : inK N T x = true) :
    ∃ j < N, T j = x := by
  unfold inK at h
  rw [anyN_eq, List.any_eq_true] at h
  obtain ⟨j, hj, e⟩ := h
  exact ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true e⟩

theorem prep_psqK {x : Nat} {g : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) (hx : PRep n w x g) :
    ∀ k, PRep n w (psqK n w k x) (g ^ 2 ^ k)
  | 0 => by
    change PRep n w x (g ^ 2 ^ 0)
    simpa using hx
  | k + 1 => by
    change PRep n w (strictN (psqK n w k x) fun a => pcomp n w (mask w) a a) _
    have e : g ^ 2 ^ (k + 1) = g ^ 2 ^ k * g ^ 2 ^ k := by rw [Nat.pow_succ, pow_mul, sq]
    rw [strictN_eq, e]
    exact prep_pcomp hn (prep_psqK hn hx k) (prep_psqK hn hx k)

theorem twoConstrainedCheck_of_K {gK gU KL UL : List (Equiv.Perm (Fin n))}
    {ngK NK ngU NU k : Nat} {GK TK EK SK GU TU EU SU : Nat → Nat}
    (hKL : ∀ g, g ∈ KL ↔ g ∈ Subgroup.closure {s | s ∈ gK})
    (hUL : ∀ u, u ∈ UL ↔ u ∈ Subgroup.closure {s | s ∈ gU})
    (hkK : bfsK n w ngK GK NK TK EK SK = true) (hlK : gK.length = ngK)
    (hGK : ∀ j < ngK, PRep n w (GK j) (gK.getD j 1))
    (hkU : bfsK n w ngU GU NU TU EU SU = true) (hlU : gU.length = ngU)
    (hGU : ∀ j < ngU, PRep n w (GU j) (gU.getD j 1))
    (hUK : ∀ u ∈ gU, u ∈ Subgroup.closure {s | s ∈ gK})
    (hpow : powK n w k NU TU = true)
    (hnorm : allN ngK (fun j => normK n w NU TU (GK j)) = true)
    (hself : selfK n w NK TK ngU GU NU TU = true) :
    twoConstrainedCheck KL UL k = true := by
  obtain ⟨hn, hw⟩ := bfsK_sz hkK
  have hn32 : n < 2 ^ 32 := by omega
  have hnw : n < 2 ^ w := by omega
  obtain ⟨hK, -⟩ := enum_closure hkK hlK hGK
  obtain ⟨hU, -⟩ := enum_closure hkU hlU hGU
  set K := Subgroup.closure {s | s ∈ gK}
  set U := Subgroup.closure {s | s ∈ gU}
  have hcanK := bfsK_canon hkK
  have hcanGU := bfsK_canonG hkU
  refine twoConstrainedCheck_of K U hKL hUL ((Subgroup.closure_le K).2 fun u hu => hUK u hu)
    ?_ ?_ ?_
  · intro u hu
    obtain ⟨i, hi, hr⟩ := (hU u).1 hu
    have e := Nat.eq_of_beq_eq_true (allN_spec hpow i hi)
    have h1 := prep_psqK hn32 hr k
    rw [e] at h1
    exact prep_unique h1 (prep_pidn hn hw)
  · refine normalizes_of_gens _ U fun s hs u hu => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hGj := hGK j (hlK ▸ hj)
    rw [List.getD_eq_getElem _ _ hj] at hGj
    obtain ⟨i, hi, hr⟩ := (hU u).1 hu
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec hnorm j (hlK ▸ hj)) i hi)
    have hinv := (CFSG.KS.SporSch.MOC.prep_pinvS hnw hGj).1
    obtain ⟨a, ha, ea⟩ := inK_spec h1
    obtain ⟨b, hb, eb⟩ := inK_spec h2
    refine ⟨(hU _).2 ⟨a, ha, ?_⟩, (hU _).2 ⟨b, hb, ?_⟩⟩
    · rw [ea]
      exact prep_pcomp hn32 (prep_pcomp hn32 hGj hr) hinv
    · rw [eb]
      exact prep_pcomp hn32 (prep_pcomp hn32 hinv hr) hGj
  · intro g hg hcomm
    obtain ⟨i, hi, hr⟩ := (hK g).1 hg
    have h := allN_spec hself i hi
    rw [Orb.strictB_eq] at h
    have hall : allN ngU (fun k => Nat.beq (pcomp n w (mask w) (TK i) (GU k))
        (pcomp n w (mask w) (GU k) (TK i))) = true := by
      refine allN_intro fun j hj => ?_
      have hu : gU.getD j 1 ∈ U := Subgroup.subset_closure (getD_mem (hlU ▸ hj))
      have e : pcomp n w (mask w) (TK i) (GU j) = pcomp n w (mask w) (GU j) (TK i) := by
        refine eq_of_prep (canonK_pcomp (hcanK i hi) (hcanGU j hj))
          (canonK_pcomp (hcanGU j hj) (hcanK i hi)) (prep_pcomp hn32 hr (hGU j hj)) ?_
        rw [hcomm _ hu]
        exact prep_pcomp hn32 (hGU j hj) hr
      rw [e]
      exact Nat.beq_refl _
    rw [hall] at h
    have h2 : inK NU TU (TK i) = true := h
    obtain ⟨j, hj, e⟩ := inK_spec h2
    exact (hU g).2 ⟨j, hj, by rw [e]; exact hr⟩

end CFSG.ClassicalInvolution.ListBridge

end
