module

public import Certificates.Data.Kernel.EvenSporM22.HS08DDefs
public import CFSG.Certificates.Kernel.EvenSporM22.HS08ConjSound

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.HS08Check

theorem hs08tabV_tabF (f : Fin 22 → Fin 22) : hs08TabV (hs08TabF f) = true := by
  simp only [hs08TabV, hs08length_tabF, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    decide_eq_true_eq]
  intro e he
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 he
  have hn' : n < 22 := by rwa [hs08length_tabF] at hn
  have h := hs08getD_tabF f ⟨n, hn'⟩
  rw [List.getD_eq_getElem _ _ hn] at h
  rw [h]
  exact (f _).isLt

theorem hs08tmul_valid {a b : Tab} (ha : hs08TabV a = true) (hb : hs08TabV b = true) :
    hs08TabV (tmul a b) = true := by
  obtain ⟨A, rfl⟩ := hs08exists_tabF ha
  obtain ⟨B, rfl⟩ := hs08exists_tabF hb
  rw [← hs08TabF_comp]
  exact hs08tabV_tabF _

theorem hs08tmul_assoc {a b c : Tab} (ha : hs08TabV a = true) (hb : hs08TabV b = true)
    (hc : hs08TabV c = true) : tmul (tmul a b) c = tmul a (tmul b c) := by
  obtain ⟨A, rfl⟩ := hs08exists_tabF ha
  obtain ⟨B, rfl⟩ := hs08exists_tabF hb
  obtain ⟨C, rfl⟩ := hs08exists_tabF hc
  simp only [← hs08TabF_comp]
  rfl

theorem hs08tmul_idTab {a : Tab} (ha : hs08TabV a = true) : tmul a idTab = a := by
  obtain ⟨A, rfl⟩ := hs08exists_tabF ha
  rw [← hs08TabF_id, ← hs08TabF_comp]
  rfl

theorem hs08span_valid : ∀ {gs : List Tab}, (∀ g ∈ gs, hs08TabV g = true) →
    ∀ t ∈ span gs, hs08TabV t = true
  | [], _, t, ht => by
    rw [span, List.mem_singleton] at ht
    rw [ht]
    decide
  | g :: gs, hg, t, ht => by
    have hgs : ∀ g' ∈ gs, hs08TabV g' = true := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    rw [span, ext, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨t', ht', rfl⟩
    · exact hs08span_valid hgs t ht
    · exact hs08tmul_valid (hg g List.mem_cons_self) (hs08span_valid hgs t' ht')

theorem hs08mul_span {S : List Tab} (hSv : ∀ s ∈ S, hs08TabV s = true) :
    ∀ {gs : List Tab}, (∀ g ∈ gs, hs08TabV g = true ∧ ∀ s ∈ S, tmul s g ∈ S) →
      ∀ s ∈ S, ∀ t ∈ span gs, tmul s t ∈ S
  | [], _, s, hs, t, ht => by
    rw [span, List.mem_singleton] at ht
    rw [ht, hs08tmul_idTab (hSv s hs)]
    exact hs
  | g :: gs, hg, s, hs, t, ht => by
    have hgs : ∀ g' ∈ gs, hs08TabV g' = true ∧ ∀ s ∈ S, tmul s g' ∈ S :=
      fun g' h => hg g' (List.mem_cons_of_mem _ h)
    rw [span, ext, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨t', ht', rfl⟩
    · exact hs08mul_span hSv hgs s hs t ht
    · have hg0 := hg g List.mem_cons_self
      rw [← hs08tmul_assoc (hSv s hs) hg0.1 (hs08span_valid (fun g' h => (hgs g' h).1) t' ht')]
      exact hs08mul_span hSv hgs _ (hg0.2 s hs) t' ht'

theorem hs08dTabs_closed (hS : ∀ l ∈ s0Tabs, ∀ g ∈ s0Gens, tmul l g ∈ s0Tabs)
    (hs0 : s0Tabs.length = 256) (hgv : ∀ g ∈ dGens, hs08TabV g = true)
    (hrv : ∀ r ∈ dReps, hs08TabV r = true) (hlen : dReps.length = 15 ∧ dGens.length = 9)
    (hR : HS08DRecOK hs08DRecs) : ∀ l ∈ dTabs, ∀ g ∈ dGens, tmul l g ∈ dTabs := by
  have hs0v : ∀ g ∈ s0Gens, hs08TabV g = true :=
    fun g hg => hgv g (List.mem_append_left _ hg)
  have hSv : ∀ s ∈ s0Tabs, hs08TabV s = true := hs08span_valid hs0v
  have hmul : ∀ s ∈ s0Tabs, ∀ t ∈ s0Tabs, tmul s t ∈ s0Tabs :=
    hs08mul_span hSv fun g hg => ⟨hs0v g hg, fun s hs => hS s hs g hg⟩
  intro l hl g hg
  rw [dTabs, List.mem_flatMap] at hl ⊢
  obtain ⟨r, hr, hl⟩ := hl
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  obtain ⟨ha, hj, he⟩ := hR ⟨i, by omega⟩ ⟨k, by omega⟩
  dsimp only [Fin.val_mk] at ha hj he
  generalize hs08DRecs.getD (9 * i + k) (0, 0) = p at ha hj he
  obtain ⟨a, j⟩ := p
  dsimp only at ha hj he
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hk,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
  have hs' := List.getElem_mem (l := s0Tabs) (n := a) (by omega)
  have hr' := List.getElem_mem (l := dReps) (n := j) (by omega)
  refine ⟨_, hr', List.mem_map.2 ⟨_, hmul s hs _ hs', ?_⟩⟩
  rw [hs08tmul_assoc (hSv s hs) (hrv _ hr) (hgv _ hg), he,
    hs08tmul_assoc (hSv s hs) (hSv _ hs') (hrv _ hr')]

end CFSG.KC.EvenSporM22
