module

public import CFSG.Certificates.Kernel.LocalQTChainGSound
public import CFSG.Certificates.Kernel.LocalQTBfsMSound
import all CFSG.Certificates.Kernel.LocalQTBfsKSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem fc_rnc (hn : n ≤ 32) (r : RN n) : FC n (rnc r) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [P.ofFn_eq, rnc]
    refine P.E_congr fun i hi => ?_
    have := img_rnc hn r ⟨i, hi⟩
    rw [rdig_of_lt r hi]
    exact this
  · have := img_rnc hn r ⟨i, hi⟩
    rw [this]
    exact (r.val[(⟨i, hi⟩ : Fin n)]).isLt

theorem idxInjN (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (F : ℕ) : IdxInj (rnc : RN n → ℕ) n C F := fun a b hlt he =>
  rnc_inj hn (idxM_inj hn hok hI (fc_rnc hn a) (fc_rnc hn b) hlt he)

theorem repN (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true) (hI : chainInj n C = true)
    {F : ℕ} (L : List (Perm (Fin n))) (d : ℕ) (hb : (bfsM n C F (L.map P.code) d).ok = true) :
    RepM rnc n C F (bfsM n C F (L.map P.code) d) (bfsSet (L.map RN.enc) d) := by
  rw [← map_rnc_enc] at hb ⊢
  exact rep_bfsM (idxInjN hn hok hI F) (rnc_mul hn) rnc_one _ d hb

theorem memN (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true) (hI : chainInj n C = true)
    {F : ℕ} {S : SetM} {H : Std.HashSet (RN n)} (h : RepM rnc n C F S H) (σ : Perm (Fin n)) :
    memM n C F S (P.code σ) = true ↔ RN.enc σ ∈ H := by
  rw [← rnc_enc]
  exact repM_mem (idxInjN hn hok hI F) h _

theorem closedH_of_grp (G : List (Perm (Fin n))) (d : ℕ) (Q : Perm (Fin n) → Prop)
    (hmem : ∀ r, r ∈ bfsSet (G.map RN.enc) d ↔ ∃ σ, Q σ ∧ RN.enc σ = r) (h1 : Q 1)
    (hmul : ∀ σ, Q σ → ∀ g ∈ G, Q (σ * g)) :
    closedH (G.map RN.enc) (bfsSet (G.map RN.enc) d) = true := by
  unfold closedH
  rw [Bool.and_eq_true, Std.HashSet.contains_iff_mem, toList_all_iff]
  refine ⟨(hmem 1).2 ⟨1, h1, RN.enc_one⟩, fun x hx => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := (hmem x).1 hx
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
  rw [Std.HashSet.contains_iff_mem, ← RN.enc_mul]
  exact (hmem _).2 ⟨_, hmul σ hσ γ hγ, rfl⟩

theorem ok_addM_of {C : List Lvl} {F : ℕ} {S : SetM × List ℕ} {y : ℕ} (hS : S.1.ok = true)
    (hy : idxM n C F y < F) : (addM n C F S y).1.ok = true := by
  rw [addM_eq]
  split_ifs
  · exact hS
  · exact P.andB_iff.2 ⟨hS, P.blt_iff.2 hy⟩

theorem front_addM {C : List Lvl} {F : ℕ} {S : SetM × List ℕ} {y x : ℕ}
    (hx : x ∈ (addM n C F S y).2) : x ∈ S.2 ∨ x = y := by
  rw [addM_eq] at hx
  split_ifs at hx
  · exact Or.inl hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr rfl
    · exact Or.inl hx

theorem ok_bfsM {C : List Lvl} {F : ℕ} (G : List ℕ) (Q : ℕ → Prop) (h1 : Q (P.one n))
    (hmul : ∀ x, Q x → ∀ g ∈ G, Q (P.mul n x g)) (hlt : ∀ x, Q x → idxM n C F x < F) (d : ℕ) :
    (bfsM n C F G d).ok = true := by
  have inner : ∀ x, Q x → ∀ (gs : List ℕ), (∀ g ∈ gs, g ∈ G) → ∀ st : SetM × List ℕ,
      st.1.ok = true → (∀ y ∈ st.2, Q y) →
      (gs.foldl (fun st g => addM n C F st (P.mul n x g)) st).1.ok = true ∧
        ∀ y ∈ (gs.foldl (fun st g => addM n C F st (P.mul n x g)) st).2, Q y := by
    intro x hx gs
    induction gs with
    | nil => intro _ st h1 h2; exact ⟨h1, h2⟩
    | cons g gs ih =>
      intro hgs st hs hf
      rw [List.foldl_cons]
      have hg := hmul x hx g (hgs g (List.mem_cons_self ..))
      refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
        (ok_addM_of hs (hlt _ hg)) fun y hy => ?_
      rcases front_addM hy with hy | rfl
      · exact hf y hy
      · exact hg
  have outer : ∀ (Fr : List ℕ), (∀ x ∈ Fr, Q x) → ∀ st : SetM × List ℕ,
      st.1.ok = true → (∀ y ∈ st.2, Q y) →
      (Fr.foldl (fun st x => G.foldl (fun st g => addM n C F st (P.mul n x g)) st) st).1.ok =
        true ∧ ∀ y ∈ (Fr.foldl (fun st x => G.foldl
          (fun st g => addM n C F st (P.mul n x g)) st) st).2, Q y := by
    intro Fr
    induction Fr with
    | nil => intro _ st h1 h2; exact ⟨h1, h2⟩
    | cons x Fr ih =>
      intro hFr st hs hf
      rw [List.foldl_cons]
      obtain ⟨a, b⟩ := inner x (hFr x (List.mem_cons_self ..)) G (fun g hg => hg) st hs hf
      exact ih (fun y hy => hFr y (List.mem_cons_of_mem _ hy)) _ a b
  have key : ∀ d, (stM n C F G d).1.ok = true ∧ ∀ y ∈ (stM n C F G d).2, Q y := by
    intro d
    induction d with
    | zero =>
      refine ⟨ok_addM_of rfl (hlt _ h1), fun y hy => ?_⟩
      rcases front_addM hy with hy | rfl
      · exact absurd hy List.not_mem_nil
      · exact h1
    | succ d ih =>
      change (roundM n C F G (stM n C F G d).1 (stM n C F G d).2).1.ok = true ∧
        ∀ y ∈ (roundM n C F G (stM n C F G d).1 (stM n C F G d).2).2, Q y
      rw [roundM_eq]
      exact outer _ ih.2 _ ih.1 fun y hy => absurd hy List.not_mem_nil
  rw [bfsM_eq]
  exact (key d).1

theorem inC_closure {C : List Lvl} {MG : List (Perm (Fin n))}
    (hM : ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ MG}) {σ τ : Perm (Fin n)}
    (hσ : InC n C σ) (hτ : InC n C τ) : InC n C (σ * τ) :=
  (hM _).2 (Subgroup.mul_mem _ ((hM σ).1 hσ) ((hM τ).1 hτ))

theorem member_spec (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {d : ℕ} (L : List (Perm (Fin n))) (full : Bool)
    (W : List (List (List ℕ)))
    (hc : closedX n C (chainF C) d (L.map P.code, full, W)
      (mkX n C (chainF C) d (L.map P.code, full, W)) = true) :
    (∀ σ, memX n C (chainF C) (mkX n C (chainF C) d (L.map P.code, full, W)) (P.code σ) = true ↔
      RN.enc σ ∈ bfsSet (L.map RN.enc) d) ∧
    sizeX (chainF C) (mkX n C (chainF C) d (L.map P.code, full, W)) =
      (bfsSet (L.map RN.enc) d).size ∧
    closedH (L.map RN.enc) (bfsSet (L.map RN.enc) d) = true := by
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  cases full with
  | false =>
    change closedM n C (chainF C) (L.map P.code) (bfsM n C (chainF C) (L.map P.code) d) = true at hc
    have hb : (bfsM n C (chainF C) (L.map P.code) d).ok = true := (P.andB_iff.1 hc).1
    have hR := repN hn hok hI L d hb
    refine ⟨fun σ => memN hn hok hI hR σ, repM_size hR, ?_⟩
    have := closedM_iff (idxInjN hn hok hI (chainF C)) (rnc_mul hn) rnc_one (L.map RN.enc) hR hb
    rw [map_rnc_enc] at this
    exact this.1 hc
  | true =>
    change grpC n C (chainF C) (L.map P.code) W d = true at hc
    have hmem := mem_bfsSet_iff hn hok hI L hc
    obtain ⟨h1, -⟩ := grpC_sound hn hok hI L hc
    refine ⟨fun σ => ?_, (size_bfsSet hn hok hI L hc).symm, ?_⟩
    · change inC n C (chainF C) (P.code σ) = true ↔ _
      rw [inC_iff hn hC, hmem]
      exact ⟨fun h => ⟨σ, h, rfl⟩, fun ⟨τ, hτ, e⟩ => (RN.enc_inj e) ▸ hτ⟩
    · refine closedH_of_grp L d (InC n C) hmem ((h1 1).2 (Subgroup.one_mem _)) fun σ hσ g hg => ?_
      exact (h1 _).2 (Subgroup.mul_mem _ ((h1 σ).1 hσ) (Subgroup.subset_closure hg))

end CFSG.KC.LQT.CM

end
