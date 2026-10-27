module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SDefs
public import CFSG.ClassicalInvolution.Q3.Q3VChain3Row
public import CFSG.ClassicalInvolution.Q3.Q3VFrameLayer
public import CFSG.ClassicalInvolution.Q3.Q3VFrameComm
public import CFSG.ClassicalInvolution.Q3.Q3VLiftMain
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternModel
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Q3.Q3V
open CFSG.ClassicalInvolution.Models.SymplecticPairs

local notation "F₃" => GaloisField 3 1

variable {G : Type} [Group G]

theorem layerSub_comm_ab (Ω : Set (Subgroup G)) {m : ℕ} (K : Fin (m + 1) → Subgroup G)
    (a b : Fin (m + 1)) : layerSub Ω K a b = layerSub Ω K b a := by
  have key : ∀ a b : Fin (m + 1), layerSub Ω K a b ≤ layerSub Ω K b a := by
    intro a b
    unfold layerSub
    refine iSup₂_le fun M hM => ?_
    exact le_iSup₂_of_le M ⟨hM.1, fun c hb ha => hM.2 c ha hb⟩ le_rfl
  exact le_antisymm (key a b) (key b a)

theorem layerSub_comp_perm (Ω : Set (Subgroup G)) {m : ℕ} (K : Fin (m + 1) → Subgroup G)
    (σ : Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1)) :
    layerSub Ω (K ∘ σ) a b = layerSub Ω K (σ a) (σ b) := by
  apply le_antisymm
  · unfold layerSub
    refine iSup₂_le fun M hM => ?_
    refine le_iSup₂_of_le M ⟨hM.1, fun c hca hcb => ?_⟩ le_rfl
    have := hM.2 (σ.symm c) (fun e => hca (by rw [← e]; simp))
      (fun e => hcb (by rw [← e]; simp))
    simpa using this
  · unfold layerSub
    refine iSup₂_le fun M hM => ?_
    refine le_iSup₂_of_le M ⟨hM.1, fun c hca hcb => ?_⟩ le_rfl
    exact hM.2 (σ c) (fun e => hca (σ.injective e)) (fun e => hcb (σ.injective e))

theorem isMemberFrame_comp {Ω : Set (Subgroup G)} {m : ℕ} {K : Fin (m + 1) → Subgroup G}
    (h : IsMemberFrame Ω K) (σ : Equiv.Perm (Fin (m + 1))) : IsMemberFrame Ω (K ∘ σ) :=
  ⟨fun i => h.mem (σ i), fun i j hij => h.comm (σ i) (σ j) (fun e => hij (σ.injective e))⟩

theorem exists_frame_not_r1' {Ω : Set (Subgroup G)} {Kf : Fin 4 → Subgroup G}
    (hKf : IsMemberFrame Ω Kf) (hnc : ¬ Chain3.LayersCommute4 Ω Kf) :
    ∃ Kf' : Fin 4 → Subgroup G, IsMemberFrame Ω Kf' ∧ Kf' 0 = Kf 0 ∧
      ¬ Commutes (layerSub Ω Kf' 0 3) (layerSub Ω Kf' 1 2) := by
  by_cases h2 : Commutes (layerSub Ω Kf 0 3) (layerSub Ω Kf 1 2)
  · have h1 : ¬ Commutes (layerSub Ω Kf 0 1) (layerSub Ω Kf 2 3) := fun h1 => hnc ⟨h1, h2⟩
    have e0 : (Equiv.swap (1 : Fin 4) 3) 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e1 : (Equiv.swap (1 : Fin 4) 3) 1 = 3 := Equiv.swap_apply_left _ _
    have e2 : (Equiv.swap (1 : Fin 4) 3) 2 = 2 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e3 : (Equiv.swap (1 : Fin 4) 3) 3 = 1 := Equiv.swap_apply_right _ _
    refine ⟨Kf ∘ (Equiv.swap (1 : Fin 4) 3), isMemberFrame_comp hKf _, ?_, ?_⟩
    · show Kf ((Equiv.swap (1 : Fin 4) 3) 0) = Kf 0
      rw [e0]
    · rw [layerSub_comp_perm, layerSub_comp_perm, e0, e1, e2, e3, layerSub_comm_ab Ω Kf 3 2]
      exact h1
  · exact ⟨Kf, hKf, rfl, h2⟩

theorem layerSub_le_of_forall {Ω : Set (Subgroup G)} {m : ℕ} {K : Fin (m + 1) → Subgroup G}
    {a b : Fin (m + 1)} {H : Subgroup G}
    (h : ∀ M ∈ Ω, (∀ c, c ≠ a → c ≠ b → Commutes M (K c)) → M ≤ H) :
    layerSub Ω K a b ≤ H := by
  unfold layerSub
  exact iSup₂_le fun M hM => h M hM.1 hM.2

theorem le_layerSub {Ω : Set (Subgroup G)} {m : ℕ} {K : Fin (m + 1) → Subgroup G}
    {a b : Fin (m + 1)} {M : Subgroup G} (hM : M ∈ Ω)
    (h : ∀ c, c ≠ a → c ≠ b → Commutes M (K c)) : M ≤ layerSub Ω K a b := by
  unfold layerSub
  exact le_iSup₂_of_le M ⟨hM, h⟩ le_rfl

theorem commutes_layerSub_of_gen {Ω : Set (Subgroup G)} {m : ℕ} {K K' : Fin (m + 1) → Subgroup G}
    {a b a' b' : Fin (m + 1)}
    (h : ∀ M ∈ Ω, (∀ c, c ≠ a → c ≠ b → Commutes M (K c)) → ∀ N ∈ Ω,
      (∀ c, c ≠ a' → c ≠ b' → Commutes N (K' c)) → Commutes M N) :
    Commutes (layerSub Ω K a b) (layerSub Ω K' a' b') := by
  have hL2 : ∀ M ∈ Ω, (∀ c, c ≠ a → c ≠ b → Commutes M (K c)) →
      layerSub Ω K' a' b' ≤ Subgroup.centralizer (M : Set G) := fun M hM hMc =>
    layerSub_le_of_forall fun N hN hNc y hy =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => h M hM hMc N hN hNc x hx y hy
  have hL1 : layerSub Ω K a b ≤ Subgroup.centralizer (layerSub Ω K' a' b' : Set G) :=
    layerSub_le_of_forall fun M hM hMc x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hL2 M hM hMc hy) x hx).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hL1 hx) y hy).symm

theorem exists_gen_pair {Ω : Set (Subgroup G)} {Kf : Fin 4 → Subgroup G}
    (hnc : ¬ Commutes (layerSub Ω Kf 0 3) (layerSub Ω Kf 1 2)) :
    ∃ M ∈ Ω, Commutes M (Kf 1) ∧ Commutes M (Kf 2) ∧ ∃ N ∈ Ω, Commutes N (Kf 0) ∧
      Commutes N (Kf 3) ∧ ¬ Commutes M N := by
  by_contra hcon
  apply hnc
  refine commutes_layerSub_of_gen fun M hM hMc N hN hNc => ?_
  by_contra hMN
  exact hcon ⟨M, hM, hMc 1 (by decide) (by decide), hMc 2 (by decide) (by decide), N, hN,
    hNc 0 (by decide) (by decide), hNc 3 (by decide) (by decide), hMN⟩

theorem exists_labGamma {m : ℕ} (hm : 3 ≤ m) {Ω : Set (Subgroup G)}
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G} (hK : IsMemberFrame Ω K)
    {l : Fin (m + 1)} {Θ' : StatedSp m F₃ →* G} (h : IsLocLift m Ω (K l) Θ') :
    ∃ γ : StatedSp m F₃, IsLabLift m Ω K l (Θ'.comp (MulAut.conj γ).toMonoidHom) := by
  have hex : ∀ c : Fin (m + 1), ∃ P : Submodule F₃ (Fin m ⊕ Fin m → F₃),
      c ≠ l → IsHyperbolicPlane P ∧ K c = (planeGroup P).map Θ' := by
    intro c
    by_cases hc : c = l
    · exact ⟨⊥, fun h' => absurd hc h'⟩
    · have hne : K c ≠ K l := by
        intro heq
        apply hnonab (K l) (hK.mem l)
        have := hK.comm c l hc
        rwa [heq] at this
      obtain ⟨P, hP, hKP⟩ := h.members (K c) (hK.mem c) hne (hK.comm c l hc)
      exact ⟨P, fun _ => ⟨hP, hKP⟩⟩
  choose Pl hPl using hex
  have hhyp : ∀ j : Fin m, IsHyperbolicPlane (Pl (l.succAbove j)) := fun j =>
    (hPl _ (Fin.succAbove_ne l j)).1
  have horth : ∀ j j' : Fin m, j ≠ j' → ∀ x ∈ Pl (l.succAbove j), ∀ y ∈ Pl (l.succAbove j'),
      form x y = 0 := by
    intro j j' hjj'
    refine (Frame.commutes_map_planeGroup_iff hm h.ker_le (hhyp j) (hhyp j')).1 ?_
    rw [← (hPl _ (Fin.succAbove_ne l j)).2, ← (hPl _ (Fin.succAbove_ne l j')).2]
    exact hK.comm _ _ (fun h' => hjj' (Fin.succAbove_right_injective h'))
  obtain ⟨γ, hγ⟩ := exists_conj_planeGroup (P := fun j => Pl (l.succAbove j)) hhyp horth
  refine ⟨γ, Frame.IsLocLift.relabel h γ, fun j => ?_⟩
  rw [← Subgroup.map_map, planeGroup_stdPlane]
  have h2 : planeGroup (Pl (l.succAbove j)) =
      (longBlock F₃ m j).range.map (MulAut.conj γ).toMonoidHom := (hγ j).2
  have h1 : ((longBlock F₃ m j).range.map (MulAut.conj γ).toMonoidHom).map Θ' =
      K (l.succAbove j) := by
    rw [← h2, ← (hPl _ (Fin.succAbove_ne l j)).2]
  exact h1

theorem le_stdPlane_of_orth_single {n : ℕ} {a : Fin n} {P : Submodule F₃ (Fin n ⊕ Fin n → F₃)}
    (h : ∀ q, q ≠ a → ∀ u ∈ P, ∀ v ∈ stdPlane F₃ n q, form u v = 0) : P ≤ stdPlane F₃ n a := by
  intro v hv
  rw [mem_stdPlane_iff]
  intro t ht
  obtain ⟨q, htq, hqa⟩ : ∃ q, t ∈ coords q ∧ q ≠ a := by
    rcases t with q | q
    · exact ⟨q, inl_mem_coords q, fun e => ht (e ▸ inl_mem_coords q)⟩
    · exact ⟨q, inr_mem_coords q, fun e => ht (e ▸ inr_mem_coords q)⟩
  have hs : (Pi.single (par t) 1 : Fin n ⊕ Fin n → F₃) ∈ stdPlane F₃ n q := by
    rw [mem_stdPlane_iff]
    intro s hs
    have : s ≠ par t := fun e => hs (e ▸ parClosed_coords q t htq)
    simp [this]
  have h1 := h q hqa v hv _ hs
  rw [form_single_right, par_par] at h1
  exact (mul_eq_zero.1 h1).resolve_right (sgn_ne_zero _)

theorem eq_fourth_of_commutes {m : ℕ} (hm : 3 ≤ m) {Ω : Set (Subgroup G)}
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G} (hK : IsMemberFrame Ω K)
    {l : Fin (m + 1)} {Θ : StatedSp m F₃ →* G} (hΘ : IsLabLift m Ω K l Θ) {c : Fin (m + 1)}
    (hcl : c ≠ l) {M : Subgroup G} (hM : M ∈ Ω) (hMl : Commutes M (K l))
    (hMc : ∀ d, d ≠ c → d ≠ l → Commutes M (K d)) : M = K c := by
  obtain ⟨jc, hjc⟩ := Fin.exists_succAbove_eq hcl
  have hMne : M ≠ K l := by
    intro e
    rw [e] at hMl
    exact hnonab (K l) (hK.mem l) hMl
  obtain ⟨Q, hQ, hMQ⟩ := hΘ.loc.members M hM hMne hMl
  have horth : ∀ q, q ≠ jc → ∀ u ∈ Q, ∀ v ∈ stdPlane F₃ m q, form u v = 0 := by
    intro q hq
    have hd : l.succAbove q ≠ c := fun e => hq (Fin.succAbove_right_injective (e.trans hjc.symm))
    have hcomm := hMc (l.succAbove q) hd (Fin.succAbove_ne l q)
    rw [hMQ, ← hΘ.lab q] at hcomm
    exact (Frame.commutes_map_planeGroup_iff hm hΘ.loc.ker_le hQ
      (isHyperbolicPlane_stdPlane q)).1 hcomm
  have hle : Q ≤ stdPlane F₃ m jc := le_stdPlane_of_orth_single horth
  have hQeq : Q = stdPlane F₃ m jc := by
    obtain ⟨u, w, huw, rfl⟩ := hQ
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_pair huw]
    exact (finrank_span_pair (form_single_inl_inr (K := F₃) jc)).symm
  rw [hMQ, hQeq, hΘ.lab jc, hjc]

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
