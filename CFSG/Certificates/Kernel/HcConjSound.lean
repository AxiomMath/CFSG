module

public import Certificates.Data.Kernel.HcConj
public import CFSG.Certificates.Kernel.HcPackSound
public import Certificates.Data.G23RecogHCharInputs
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.Kernel.HcConj
import all Certificates.Data.G23RecogGlueInputs
import all Certificates.Data.G23RecogHFactsInputs
import all Certificates.Data.G23RecogHCharInputs
import all CFSG.Certificates.Kernel.HcPackSound

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData
  CFSG.GH74.QTGen4.Recog.G23.HCharData

section Map

variable {α β γ δ : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (F : α → β) (S : α → Prop)
  (f h : γ → α → α) (f' h' : δ → β → β) (φ : γ → δ)
  (hfS : ∀ kb x, S x → S (f kb x)) (hhS : ∀ kb x, S x → S (h kb x))
  (hf : ∀ kb x, S x → F (f kb x) = f' (φ kb) (F x))
  (hh : ∀ kb x, S x → F (h kb x) = h' (φ kb) (F x))
  (hi : ∀ x y, S x → S y → F x = F y → x = y)

@[expose] def F2 (p : α × α) : β × β := (F p.1, F p.2)

@[expose] def S2 (p : α × α) : Prop := S p.1 ∧ S p.2

def mapSt2 (a : List (α × α) × List (α × α)) : List (β × β) × List (β × β) :=
  (a.1.map (F2 F), a.2.map (F2 F))

def InvS (a : List (α × α) × List (α × α)) : Prop :=
  (∀ q ∈ a.1, S2 S q) ∧ ∀ q ∈ a.2, S2 S q

include hi in
theorem any_map (L : List (α × α)) (hL : ∀ q ∈ L, S2 S q) (x : α) (hx : S x) :
    (L.map (F2 F)).any (fun q => q.1 == F x) = L.any (fun q => q.1 == x) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨q', hq', he⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hq'
    refine ⟨q, hq, ?_⟩
    rw [beq_iff_eq] at he ⊢
    exact hi _ _ (hL q hq).1 hx he
  · rintro ⟨q, hq, he⟩
    refine ⟨F2 F q, List.mem_map_of_mem hq, ?_⟩
    rw [beq_iff_eq] at he ⊢
    rw [← he]
    rfl

include hfS hhS in
theorem cjAdd_inv (p : α × α) (hp : S2 S p) (acc : List (α × α) × List (α × α))
    (ha : InvS S acc) (kb : γ) : InvS S (cjAdd f h p acc kb) := by
  unfold cjAdd
  dsimp only
  split
  · exact ha
  · have hq : S2 S (f kb p.1, h kb p.2) := ⟨hfS kb p.1 hp.1, hhS kb p.2 hp.2⟩
    refine ⟨fun q hq' => ?_, fun q hq' => ?_⟩
    · rcases List.mem_append.1 hq' with hq' | hq'
      · exact ha.1 q hq'
      · rw [List.mem_singleton.1 hq']
        exact hq
    · rcases List.mem_append.1 hq' with hq' | hq'
      · exact ha.2 q hq'
      · rw [List.mem_singleton.1 hq']
        exact hq

include hfS hhS in
theorem frFold_inv (gs : List γ) :
    ∀ (fr : List (α × α)), (∀ q ∈ fr, S2 S q) → ∀ (acc : List (α × α) × List (α × α)),
      InvS S acc → InvS S (fr.foldl (fun acc p => gs.foldl (cjAdd f h p) acc) acc)
  | [], _, _, ha => ha
  | p :: fr, hfr, acc, ha => by
    have hp := hfr p List.mem_cons_self
    have hg : ∀ (gs' : List γ) (a : List (α × α) × List (α × α)), InvS S a →
        InvS S (gs'.foldl (cjAdd f h p) a) := by
      intro gs'
      induction gs' with
      | nil => exact fun _ ha => ha
      | cons kb gs' ih => exact fun a ha => ih _ (cjAdd_inv S f h hfS hhS p hp a ha kb)
    rw [List.foldl_cons]
    exact frFold_inv gs fr (fun q hq => hfr q (List.mem_cons_of_mem _ hq)) _ (hg gs acc ha)

include hfS hhS in
theorem cjAuxG_inv (gs : List γ) :
    ∀ (n : ℕ) (seen fr : List (α × α)), (∀ q ∈ seen, S2 S q) → (∀ q ∈ fr, S2 S q) →
      ∀ q ∈ cjAuxG f h gs n seen fr, S2 S q
  | 0, _, _, hs, _ => hs
  | n + 1, seen, fr, hs, hfr => by
    simp only [cjAuxG]
    split
    · exact hs
    · have hst := frFold_inv S f h hfS hhS gs fr hfr (seen, [])
        ⟨hs, fun q hq => absurd hq List.not_mem_nil⟩
      exact cjAuxG_inv gs n _ _ hst.1 hst.2

include hfS hf hh hi in
theorem cjAdd_map (p : α × α) (hp : S2 S p) (acc : List (α × α) × List (α × α))
    (ha : InvS S acc) (kb : γ) :
    mapSt2 F (cjAdd f h p acc kb) = cjAdd f' h' (F2 F p) (mapSt2 F acc) (φ kb) := by
  have hc := any_map F S hi acc.1 ha.1 (f kb p.1) (hfS kb p.1 hp.1)
  unfold cjAdd mapSt2
  dsimp only
  have e1 : (F2 F p).1 = F p.1 := rfl
  have e2 : (F2 F p).2 = F p.2 := rfl
  rw [e1, e2, ← hf kb p.1 hp.1, ← hh kb p.2 hp.2, hc]
  split
  · rfl
  · simp [F2]

include hfS hhS hf hh hi in
theorem gensFold_map2 (p : α × α) (hp : S2 S p) :
    ∀ (gs : List γ) (acc : List (α × α) × List (α × α)), InvS S acc →
      mapSt2 F (gs.foldl (cjAdd f h p) acc) =
        (gs.map φ).foldl (cjAdd f' h' (F2 F p)) (mapSt2 F acc) ∧
      InvS S (gs.foldl (cjAdd f h p) acc)
  | [], _, ha => ⟨rfl, ha⟩
  | kb :: gs, acc, ha => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      ← cjAdd_map F S f h f' h' φ hfS hf hh hi p hp acc ha kb]
    exact gensFold_map2 p hp gs _ (cjAdd_inv S f h hfS hhS p hp acc ha kb)

include hfS hhS hf hh hi in
theorem frFold_map2 (gs : List γ) :
    ∀ (fr : List (α × α)), (∀ q ∈ fr, S2 S q) → ∀ (acc : List (α × α) × List (α × α)),
      InvS S acc →
      mapSt2 F (fr.foldl (fun acc p => gs.foldl (cjAdd f h p) acc) acc) =
        (fr.map (F2 F)).foldl (fun acc p => (gs.map φ).foldl (cjAdd f' h' p) acc)
          (mapSt2 F acc) ∧
      InvS S (fr.foldl (fun acc p => gs.foldl (cjAdd f h p) acc) acc)
  | [], _, _, ha => ⟨rfl, ha⟩
  | p :: fr, hfr, acc, ha => by
    have hp := hfr p List.mem_cons_self
    obtain ⟨e, ha'⟩ := gensFold_map2 F S f h f' h' φ hfS hhS hf hh hi p hp gs acc ha
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← e]
    exact frFold_map2 gs fr (fun q hq => hfr q (List.mem_cons_of_mem _ hq)) _ ha'

include hfS hhS hf hh hi in
theorem cjAuxG_map (gs : List γ) :
    ∀ (n : ℕ) (seen fr : List (α × α)), (∀ q ∈ seen, S2 S q) → (∀ q ∈ fr, S2 S q) →
      (cjAuxG f h gs n seen fr).map (F2 F) =
        cjAuxG f' h' (gs.map φ) n (seen.map (F2 F)) (fr.map (F2 F))
  | 0, _, _, _, _ => rfl
  | n + 1, seen, fr, hs, hfr => by
    have hst := frFold_map2 F S f h f' h' φ hfS hhS hf hh hi gs fr hfr (seen, [])
      ⟨hs, fun q hq => absurd hq List.not_mem_nil⟩
    simp only [cjAuxG, List.isEmpty_map]
    split
    · rfl
    · have e0 : mapSt2 F (seen, []) = (seen.map (F2 F), []) := rfl
      have e1 : (cjStepG f' h' (gs.map φ) (seen.map (F2 F)) (fr.map (F2 F))).1 =
          (cjStepG f h gs seen fr).1.map (F2 F) := by
        unfold cjStepG
        rw [← e0, ← hst.1]
        rfl
      have e2 : (cjStepG f' h' (gs.map φ) (seen.map (F2 F)) (fr.map (F2 F))).2 =
          (cjStepG f h gs seen fr).2.map (F2 F) := by
        unfold cjStepG
        rw [← e0, ← hst.1]
        rfl
      rw [e1, e2]
      exact cjAuxG_map gs n _ _ hst.2.1 hst.2.2

end Map

theorem cjAux_eq : ∀ (n : ℕ) (seen fr : List (List ℕ × List ℕ)),
    cjAux n seen fr = cjAuxG (fun kb x => conjG kb.1 kb.2 x) (fun kb c => conjC kb.1 kb.2 c)
      cjGens n seen fr
  | 0, _, _ => rfl
  | n + 1, seen, fr => by
    simp only [cjAux, cjAuxG]
    split
    · rfl
    · have e : cjStep seen fr = cjStepG (fun kb x => conjG kb.1 kb.2 x)
          (fun kb c => conjC kb.1 kb.2 c) cjGens seen fr := rfl
      rw [e]
      exact cjAux_eq n _ _

def cjA (kb : Fin 5 × Bool) : List ℕ := if kb.2 then Lst (gen kb.1) else Lst (gen kb.1)⁻¹

def cjB (kb : Fin 5 × Bool) : List ℕ := if kb.2 then Lst (gen kb.1)⁻¹ else Lst (gen kb.1)

theorem VL_cjA (kb : Fin 5 × Bool) : VL (cjA kb) := by
  unfold cjA
  split
  · exact VL_Lst _
  · exact VL_Lst _

theorem VL_cjB (kb : Fin 5 × Bool) : VL (cjB kb) := by
  unfold cjB
  split
  · exact VL_Lst _
  · exact VL_Lst _

theorem conjG_eq (kb : Fin 5 × Bool) (x : List ℕ) :
    conjG kb.1 kb.2 x = mulL (mulL (cjA kb) x) (cjB kb) := by
  unfold conjG cjA cjB
  split <;> rfl

theorem conjC_eq (kb : Fin 5 × Bool) (c : List ℕ) : conjC kb.1 kb.2 c = mulL (cjA kb) c := by
  unfold conjC cjA
  split <;> rfl

def cjPk (kb : Fin 5 × Bool) : ℕ × ℕ := (pk (cjA kb), pk (cjB kb))

theorem cjGens_map_pk : cjGens.map cjPk = cjGP := by decide +kernel

theorem cjClass_map_pk (r : List ℕ) (hr : VL r) :
    (cjClass r).map (F2 pk) = cjClassP (pk r) := by
  have hs : ∀ q ∈ [(r, idL)], S2 VL q := by
    intro q hq
    rw [List.mem_singleton.1 hq]
    exact ⟨hr, VL_idL⟩
  rw [cjClass, cjAux_eq, cjAuxG_map pk VL _ _ conjP conjCP cjPk
    (fun kb x hx => by rw [conjG_eq]; exact VL_mulL (VL_mulL (VL_cjA kb) hx) (VL_cjB kb))
    (fun kb c hc => by rw [conjC_eq]; exact VL_mulL (VL_cjA kb) hc)
    (fun kb x hx => by
      rw [conjG_eq, pk_mulL (VL_mulL (VL_cjA kb) hx) (VL_cjB kb), pk_mulL (VL_cjA kb) hx]
      rfl)
    (fun kb c hc => by rw [conjC_eq, pk_mulL (VL_cjA kb) hc]; rfl)
    (fun _ _ => VL_inj) cjGens 100 _ _ hs hs, cjGens_map_pk]
  simp [F2, pk_idL, cjClassP]

theorem VL_cjClass (r : List ℕ) (hr : VL r) : ∀ q ∈ cjClass r, VL q.1 ∧ VL q.2 := by
  have hs : ∀ q ∈ [(r, idL)], S2 VL q := by
    intro q hq
    rw [List.mem_singleton.1 hq]
    exact ⟨hr, VL_idL⟩
  rw [cjClass, cjAux_eq]
  exact cjAuxG_inv VL _ _
    (fun kb x hx => by rw [conjG_eq]; exact VL_mulL (VL_mulL (VL_cjA kb) hx) (VL_cjB kb))
    (fun kb c hc => by rw [conjC_eq]; exact VL_mulL (VL_cjA kb) hc) cjGens 100 _ _ hs hs

theorem idxC_pk : ∀ (l : List ℕ), (∀ a ∈ l, a < 32) → ∀ i, idxC (pk l) i l.length = l.idxOf i
  | [], _, _ => rfl
  | a :: l, hl, i => by
    have ha := hl a List.mem_cons_self
    have e : idxC (pk (a :: l)) i (l.length + 1) = Bool.rec (motive := fun _ => ℕ)
        (Nat.succ (idxC (pk (a :: l) / 32) i l.length)) 0 (Nat.beq (pk (a :: l) % 32) i) := rfl
    rw [List.length_cons, e, pk_cons_mod ha, pk_cons_div ha,
      idxC_pk l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) i, List.idxOf_cons]
    by_cases h : a = i
    · subst h
      simp
    · have hb : Nat.beq a i = false := by
        rw [Bool.eq_false_iff]
        exact fun e => h (Nat.eq_of_beq_eq_true e)
      rw [hb]
      simp [h]

theorem pk_invL {l : List ℕ} (hl : VL l) : pk (invL l) = invP (pk l) := by
  unfold invL invP
  refine congrArg pk (List.map_congr_left fun i _ => ?_)
  rw [← hl.1, idxC_pk l hl.2]

theorem invL_Lst (σ : Equiv.Perm (Fin 32)) : invL (Lst σ) = Lst σ⁻¹ := by
  have hnd : (Lst σ).Nodup := by
    unfold Lst
    rw [List.nodup_ofFn]
    intro a b h
    exact σ.injective (Fin.ext h)
  have hl : (Lst σ).length = 32 := (VL_Lst σ).1
  apply List.ext_getElem
  · rw [(VL_Lst σ⁻¹).1]
    simp [invL]
  · intro i h1 h2
    have hi : i < 32 := by simpa [invL] using h1
    have hk : ((σ⁻¹ ⟨i, hi⟩ : Fin 32) : ℕ) < (Lst σ).length := by
      rw [hl]
      exact (σ⁻¹ ⟨i, hi⟩).2
    have he : (Lst σ)[((σ⁻¹ ⟨i, hi⟩ : Fin 32) : ℕ)] = i := by
      simp only [Lst, List.getElem_ofFn, Fin.eta]
      simp
    have hx : (Lst σ).idxOf i = ((σ⁻¹ ⟨i, hi⟩ : Fin 32) : ℕ) := by
      conv_lhs => rw [← he]
      exact hnd.idxOf_getElem _ hk
    simp only [invL, List.getElem_map, List.getElem_range]
    rw [hx]
    simp only [Lst, List.getElem_ofFn]

theorem VL_invL_Lst (σ : Equiv.Perm (Fin 32)) : VL (invL (Lst σ)) := by
  rw [invL_Lst]
  exact VL_Lst _

theorem pk_powL {l : List ℕ} (hl : VL l) : ∀ n, pk (powL l n) = powP (pk l) n ∧ VL (powL l n)
  | 0 => ⟨pk_idL, VL_idL⟩
  | n + 1 => by
    obtain ⟨e, hv⟩ := pk_powL hl n
    refine ⟨?_, VL_mulL hl hv⟩
    change pk (mulL l (powL l n)) = mulP (pk l) (powP (pk l) n)
    rw [pk_mulL hl hv, e]

end CFSG.KC.HcPack

end
