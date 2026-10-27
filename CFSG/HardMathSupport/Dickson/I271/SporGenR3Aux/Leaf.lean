module

public import CFSG.HardMathSupport.Dickson.I271.ChevPBalOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltDiv

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4 GL83 GL83.CompFam

structure CompHyp (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  core : GLAPPrimeCore p X = ⊥
  comp : GLAPComponent p ⊤ K
  scp : IsSCp p ⊤ B
  norm : B ≤ Subgroup.normalizer (K : Set X)

theorem CompHyp.of_i271Hyp {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : I271Hyp p K B) (hN : B ≤ Subgroup.normalizer (K : Set X)) : CompHyp p K B :=
  ⟨h.prime, h.odd, h.core, h.comp, h.scp, hN⟩

theorem CompHyp.quasi {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : CompHyp p K B) : CFSG.Open.IsQuasisimple ↥K :=
  i116e_isQuasisimple h.core h.comp

theorem CompHyp.primeCore {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : CompHyp p K B) : GLAPPrimeCore p ↥K = ⊥ :=
  i271h_primeCore_eq_bot h.core h.comp

theorem CompHyp.elem {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : CompHyp p K B) : IsElemAbelian p B :=
  h.scp.2.1

theorem CompHyp.dvd {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : CompHyp p K B) : p ∣ Nat.card K :=
  i116e_dvd_card h.prime h.core h.comp

theorem CompHyp.sc {p : ℕ} {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : CompHyp p K B) : IsSCp p (K ⊔ B) B :=
  ⟨le_sup_right, h.elem, fun E _ hEel hBE => h.scp.2.2 E le_top hEel hBE⟩

section Alt

variable {X : Type} [Group X] [Finite X]

open GL83.PiGen in
theorem strong_alt {p : ℕ} {K B : Subgroup X} (h : CompHyp p K B)
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) (hpn : p ∣ n)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) : IsStronglyBalancedIn p B K := by
  have hp : p.Prime := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := h.odd
  have hq : CFSG.Open.IsQuasisimple ↥K := h.quasi
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore p ↥K = ⊥ := h.primeCore
  have h73 : ¬ (p = 3 ∧ n = 7) := by
    rintro ⟨rfl, rfl⟩
    omega
  have hZ : Subgroup.center ↥K = ⊥ := i271h_center_eq_bot_of_ne_six hp hpodd hOK hn e hn6 h73
  have hAsc := i271h_map_permHom_isSCp hp hpodd h.scp h.norm hZ hn hn6 e
  set N := Subgroup.normalizer (K : Set X) with hN
  set π := permHom (le_refl N) hn hn6 e with hπ
  have hdvdn : p ∣ Fintype.card (Fin n) := by simpa using hpn
  intro S hSN hcop hBS
  have hBNB : B ⊓ N = B := inf_of_le_left h.norm
  rw [hBNB] at hBS
  set T : Subgroup (Perm (Fin n)) := (S.subgroupOf N).map π with hT
  set A : Subgroup (Perm (Fin n)) := (B.subgroupOf N).map π with hA
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hcard : Nat.card (S.subgroupOf N) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  have hAT : A ≤ Subgroup.normalizer (T : Set (Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hx)) (h : X)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hxn)
  have hTbot : T = ⊥ := i271h_perm_coprime_normalized_eq_bot hAsc hdvdn hTcop hAT
  intro s hs
  have hsN : s ∈ N := hSN hs
  have h1 : π ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hs)
  rw [hTbot, Subgroup.mem_bot] at h1
  have h2 := (permHom_eq_one_iff (le_refl N) hn hn6 e ⟨s, hsN⟩).1 h1
  exact Subgroup.mem_centralizer_iff.2 fun x hx => (h2 ⟨x, hx⟩).symm

end Alt

@[expose] def ChevStrong (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X), Chev204Hyp p K B → ¬ ChevExc p K B →
    IsStronglyBalancedIn p B K

theorem chevStrong_of_residuals {p : ℕ} (hDC : DefCharInnerCoreFree) (hOut : DefCharOuterCoreFree)
    (hK65 : KD65 p) (hKD : KDChevInner p) (hCent : ChevCentralizerStep) (hCyc : ChevCyclicCase)
    (hAmb : ChevAmbCase) : ChevStrong p :=
  fun X _ _ K B h1 h2 =>
    chev204_induction hDC hOut hK65 hKD hCent hCyc hAmb (Nat.card X) X rfl K B h1 h2

@[expose] def LeafType (p : ℕ) (T : Type) [Group T] : Prop :=
  (IsChevSimple p T ∧ ¬ IsLTwoTwentySeven T ∧ ¬ Nonempty (T ≃* ↥(alternatingGroup (Fin 6)))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ n ≠ 6 ∧ p ∣ n ∧ Nonempty (T ≃* ↥(alternatingGroup (Fin n))))

theorem LeafType.of_equiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : LeafType p T) : LeafType p T' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨n, hn, hn6, hpn, ⟨f⟩⟩
  · refine Or.inl ⟨isChevSimple_of_mulEquiv e h1, fun h => h2 ?_, fun ⟨f⟩ => h3 ⟨e.trans f⟩⟩
    exact isLTwoTwentySeven_of_mulEquiv e.symm h
  · exact Or.inr ⟨n, hn, hn6, hpn, ⟨e.symm.trans f⟩⟩

theorem strong_leaf {p : ℕ} (hChev : ChevStrong p) {Y : Type}
    [Group Y] [Finite Y] {J B : Subgroup Y} (h : CompHyp p J B)
    (hT : LeafType p (↥J ⧸ Subgroup.center ↥J)) : IsStronglyBalancedIn p B J := by
  rcases hT with ⟨hC, hL27, hA6⟩ | ⟨n, hn, hn6, hpn, ⟨e⟩⟩
  · refine hChev Y J B ⟨h.prime, h.odd, h.core, h.comp, h.scp, h.norm, hC⟩ ?_
    rintro ⟨-, hb | hc⟩
    · exact hL27 hb.1
    · exact hA6 hc.1.2.2
  · exact strong_alt h hn hn6 hpn e

end CFSG.HardMathSupport.Dickson.I271
