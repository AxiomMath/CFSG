module

public import Certificates.Data.Kernel.F48Small.Sp43c
public import CFSG.Certificates.Kernel.F48Small.PackSound
public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
import all CFSG.Certificates.Kernel.F48Small.PackSound

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.Quasithin CFSG.ASVolI

theorem nodupT_sound : ∀ (L : List ℕ) (t : NT), OrdN t → nodupT L t = true →
    (∀ x ∈ L, ¬ memN t x) ∧ L.Nodup
  | [], _, _, _ => ⟨by simp, List.nodup_nil⟩
  | x :: L, t, ho, h => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memT t x)) (nodupT L (insT t x)) = true at h
    rw [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hL⟩ := h
    have hx' : ¬ memN t x := fun hm => by
      rw [(memT_iff ho x).2 hm] at hx
      exact Bool.noConfusion hx
    obtain ⟨h1, h2⟩ := nodupT_sound L (insT t x) (ord_insT x ho) hL
    refine ⟨fun y hy => ?_, List.nodup_cons.2 ⟨fun hm => h1 x hm ((mem_insT x x t).2 (Or.inl rfl)), h2⟩⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx'
    · exact fun hm => h1 y hy ((mem_insT x y t).2 (Or.inr hm))

theorem evL_eq {m : ℕ} (gl gli : Fin m → List ℕ) (LS LSi : List (List ℕ))
    (hgl : ∀ k, gl k = LS.getD k []) (hgli : ∀ k, gli k = LSi.getD k []) :
    burnsideF48s_sp43c_evL gl gli = burnsideF48s_eEvL 45 LS LSi := by
  funext w
  simp only [burnsideF48s_sp43c_evL, burnsideF48s_eEvL]
  congr 1
  funext acc l
  congr 1
  obtain ⟨k, b⟩ := l
  cases b <;> simp [burnsideF48s_sp43c_letL, burnsideF48s_eLetL, hgl, hgli]

theorem groupB_of {m : ℕ} {gl gli : Fin m → List ℕ} {LS LSi : List (List ℕ)}
    (h : LetOK 45 m LS LSi) (hgl : ∀ k, gl k = LS.getD k []) (hgli : ∀ k, gli k = LSi.getD k [])
    {W : List (List (Fin m × Bool))} {n : ℕ} (hn : W.length = n) (h0 : [] ∈ W) {gs : List ℕ}
    (hgs : (List.finRange m).map Fin.val = gs)
    (hk : groupK 45 (W.map (evK 45 (LS.map encL) (LSi.map encL))) (gs.map (getK (LS.map encL)))
      = true) :
    burnsideF48s_sp43c_groupB gl gli W n = true := by
  change CFSG.KC.Ord.andB _ _ = true at hk
  rw [andB_eq, Bool.and_eq_true] at hk
  obtain ⟨hnd, hcl⟩ := hk
  have hev : (fun w => encL (burnsideF48s_eEvL 45 LS LSi w)) =
      evK 45 (LS.map encL) (LSi.map encL) := funext (encL_ev h)
  have hcl' := (eClosed_ev h W gs (by rw [← hgs]; simp)).trans hcl
  rw [burnsideF48s_sp43c_groupB, evL_eq gl gli LS LSi hgl hgli]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hn, h0⟩, ?_⟩, ?_⟩
  · refine List.Nodup.of_map encL ?_
    rw [List.map_map, Function.comp_def, hev]
    exact (nodupT_sound _ NT.lf trivial hnd).2
  · rw [← hgs] at hcl'
    simpa only [burnsideF48s_eClosed, List.all_map, Function.comp_def, hgl] using hcl'

theorem decide_eq_encL {a b : List ℕ} (ha : Val 45 a) (hb : Val 45 b) :
    decide (a = b) = Nat.beq (encL a) (encL b) := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, Nat.beq_eq]
  exact ⟨fun e => e ▸ rfl, encL_inj (ha.1.trans hb.1.symm) ha.2 hb.2⟩

theorem val_compL45 {a b : List ℕ} (ha : Val 45 a) (hb : Val 45 b) : Val 45 (compL a b) :=
  ⟨by simp [compL, hb.1], small_compL ha.2 b⟩

theorem encL_compL45 {a b : List ℕ} (ha : Val 45 a) (hb : Val 45 b) :
    encL (compL a b) = pcomp (encL a) 45 (encL b) := by
  rw [encL_compL ha.2 hb.2, hb.1]

theorem codesLt10_sound : ∀ (L : List (List ℕ)), codesLt10 L = true → ∀ w ∈ L, ∀ c ∈ w, c < 10
  | [], _ => by simp
  | w :: L, h => by
    have hw : ∀ v : List ℕ, List.rec (motive := fun _ => Bool) true
        (fun c _ ih' => CFSG.KC.Ord.andB (Nat.blt c 10) ih') v = true → ∀ c ∈ v, c < 10 := by
      intro v
      induction v with
      | nil => simp
      | cons c v ih =>
        intro hv
        change CFSG.KC.Ord.andB (Nat.blt c 10) _ = true at hv
        rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at hv
        intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hv.1
        · exact ih hv.2 d hd
    change CFSG.KC.Ord.andB _ (codesLt10 L) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hw _ h.1
    · exact codesLt10_sound L h.2 v hv

theorem lt10_getD {L : List (List ℕ)} (h : codesLt10 L = true) (i : ℕ) :
    ∀ c ∈ L.getD i [], c < 10 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => simp
  | some v => exact codesLt10_sound L h v (List.mem_of_getElem? hi)

theorem val_of_letOK {n : ℕ} {LS LSi : List (List ℕ)} (h : LetOK 45 n LS LSi) {l : List ℕ}
    (hl : l ∈ LS ++ LSi) : Val 45 l :=
  ⟨(h.hv l hl).1, (h.hv l hl).2⟩

end CFSG.KC.F48S
