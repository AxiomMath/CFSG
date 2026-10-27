module

public import CFSG.ClassicalInvolution.Q3.TL3T12
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

structure AEIdentOn (P : Set (Subgroup G)) (n : ℕ) (𝒜 : Set (Finset (Fin n)))
    (H : Subgroup (AE.AEQ n)) where
  φ : ↥(pSpan P) →* AE.AEQ n
  range_eq : φ.range = H
  ker_le : φ.ker ≤ Subgroup.center ↥(pSpan P)
  label : ∀ L ∈ P, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b
  label_surj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ P,
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b

section Phi

variable [Finite G] {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n)

theorem phi_injOn (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b) {l₁ l₂ : G} (h₁ : l₁ ∈ L)
    (h₂ : l₂ ∈ L) (he : φ ⟨l₁, le_pSpan hL h₁⟩ = φ ⟨l₂, le_pSpan hL h₂⟩) : l₁ = l₂ := by
  let f : ↥(L.subgroupOf (pSpan P)) → ↥(AE.memBar α h b) := fun x =>
    ⟨φ x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥(L.subgroupOf (pSpan P)) ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar hn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).toEquiv,
      h8]
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  have := @hinj ⟨⟨l₁, le_pSpan hL h₁⟩, Subgroup.mem_subgroupOf.mpr h₁⟩
    ⟨⟨l₂, le_pSpan hL h₂⟩, Subgroup.mem_subgroupOf.mpr h₂⟩ (Subtype.ext he)
  exact congrArg (fun x : ↥(L.subgroupOf (pSpan P)) => ((x : ↥(pSpan P)) : G)) this

theorem phi_map_eq_zBar (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b) {u : G}
    (hu : IsUniqueInvolution L u) : φ ⟨u, le_pSpan hL hu.mem⟩ = AE.zBar α h := by
  have hmem : φ ⟨u, le_pSpan hL hu.mem⟩ ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨⟨u, le_pSpan hL hu.mem⟩, Subgroup.mem_subgroupOf.mpr hu.mem, rfl⟩
  have hsq : φ ⟨u, le_pSpan hL hu.mem⟩ * φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext hu.sq
  rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
  · exfalso
    apply hu.ne_one
    have : φ ⟨u, le_pSpan hL hu.mem⟩ = φ ⟨1, le_pSpan hL L.one_mem⟩ := by
      rw [h1]
      exact (map_one φ).symm
    exact phi_injOn φ hn hL h8 hlab hu.mem L.one_mem this
  · exact h1

theorem phi_twins (hn : 5 ≤ n) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (h8 : Nat.card L = 8) (h8' : Nat.card L' = 8) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan P)).map φ = AE.memBar α h (!b)) :
    L ≠ L' ∧ ∀ u u' : G, ∀ (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u'),
      (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ : ↥(pSpan P)) ∈ φ.ker := by
  refine ⟨fun heq => ?_, fun u u' hu hu' => ?_⟩
  · subst heq
    rw [hlab] at hlab'
    cases b
    · exact AE.memBar_true_ne_false hn α h hlab'.symm
    · exact AE.memBar_true_ne_false hn α h hlab'
  · rw [MonoidHom.mem_ker, map_mul, phi_map_eq_zBar φ hn hL h8 hlab hu,
      phi_map_eq_zBar φ hn hL' h8' hlab' hu']
    exact AE.zBar_mul_self α h

end Phi

@[expose] def TightThmD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 8) →
    (∀ J ∈ Ω, ∀ u : G, IsUniqueInvolution J u →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) →
    (∀ J ∈ Ω, AEmpty Ω J) →
    (∀ J ∈ Ω, ∀ J' ∈ Ω, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u → J = J') →
    ∀ P : Set (Subgroup G), P ⊆ Ω →
    (∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') →
    (∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) →
    classicalInvolutionOddCore ↥(pSpan P) = ⊥ →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∀ Q : Subgroup G, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q →
        x = 1 ∨ x = u) →
    (∀ L ∈ P, ∀ L' ∈ P, L ≠ L' → ¬ nbrAdj Ω L L') ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent P n)) ∨
      Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
      Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

theorem twins_of_phi {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥(pSpan P) →* AE.AEQ n) (hker : φ.ker ≤ Subgroup.center ↥(pSpan P))
    (h8 : ∀ L ∈ P, Nat.card L = 8) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan P)).map φ = AE.memBar α h (!b))
    (huniq : ∀ L ∈ P, ∃ u : G, IsUniqueInvolution L u) :
    ∃ L ∈ P, ∃ L' ∈ P, L ≠ L' ∧ ∃ u u' : G, IsUniqueInvolution L u ∧
      IsUniqueInvolution L' u' ∧ ∀ I ∈ P, ∀ x ∈ I, (u * u') * x = x * (u * u') := by
  obtain ⟨hne, hk⟩ := phi_twins φ hn hL hL' (h8 L hL) (h8 L' hL') hlab hlab'
  obtain ⟨u, hu⟩ := huniq L hL
  obtain ⟨u', hu'⟩ := huniq L' hL'
  refine ⟨L, hL, L', hL', hne, u, u', hu, hu', fun I hI x hx => ?_⟩
  have := Subgroup.mem_center_iff.mp (hker (hk u u' hu hu')) ⟨x, le_pSpan hI hx⟩
  exact (congrArg Subtype.val this).symm

theorem tightThmD2_of_thmD3 (h : TightThmD3) : TightThmD2 := by
  intro G _ _ Ω hΩ h2 h8 htight hA htw P hPΩ htr hinv hodd hE2 hthin
  have h8P : ∀ L ∈ P, Nat.card L = 8 := fun L hL => h8 L (hPΩ hL)
  have huniq : ∀ L ∈ P, ∃ u : G, IsUniqueInvolution L u := fun L hL =>
    (hΩ.omega1 L (hPΩ hL)).1
  rcases h G Ω hΩ h2 h8 htight hA htw P hPΩ htr hinv hodd hE2 hthin with
    hind | ⟨n, hn, ⟨I⟩⟩ | hI | hI
  · exact Or.inl hind
  · by_cases hP : ∃ L, L ∈ P
    · obtain ⟨L, hL⟩ := hP
      obtain ⟨α, hα, b, hlab⟩ := I.label L hL
      obtain ⟨L', hL', hlab'⟩ := I.label_surj α hα (!b)
      exact Or.inr (twins_of_phi hn I.φ I.ker_le h8P hL hL' hlab hlab' huniq)
    · exact Or.inl fun L hL => absurd ⟨L, hL⟩ hP
  · obtain ⟨I⟩ := hI
    by_cases hP : ∃ L, L ∈ P
    · obtain ⟨L, hL⟩ := hP
      obtain ⟨α, hα𝒜, hα, b, hlab⟩ := I.label L hL
      obtain ⟨L', hL', hlab'⟩ := I.label_surj α hα𝒜 hα (!b)
      exact Or.inr (twins_of_phi (by norm_num) I.φ I.ker_le h8P hL hL' hlab hlab' huniq)
    · exact Or.inl fun L hL => absurd ⟨L, hL⟩ hP
  · obtain ⟨I⟩ := hI
    by_cases hP : ∃ L, L ∈ P
    · obtain ⟨L, hL⟩ := hP
      obtain ⟨α, hα𝒜, hα, b, hlab⟩ := I.label L hL
      obtain ⟨L', hL', hlab'⟩ := I.label_surj α hα𝒜 hα (!b)
      exact Or.inr (twins_of_phi (by norm_num) I.φ I.ker_le h8P hL hL' hlab hlab' huniq)
    · exact Or.inl fun L hL => absurd ⟨L, hL⟩ hP

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


@[expose] def TightCaseE64Leaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      Nonempty (TC.Thin.AEIdentOn {L : Subgroup Y |
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) L} 7
          AE.e64Sets AE.e64Sub) → False

@[expose] def TightCase29Leaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      Nonempty (TC.Thin.AEIdentOn {L : Subgroup Y |
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) L} 8
          AE.e29Sets AE.e29Sub) → False

variable {n : ℕ}

theorem tightIndepLeaf_of_thmD3 (hD : TC.Thin.TightThmD3) (hE64 : TightCaseE64Leaf n)
    (h29 : TightCase29Leaf n) : TightIndepLeaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall M hM
  obtain ⟨g, rfl⟩ := hM
  have hS := hL.thinStd hO hconn hsep
  refine hS.indep_conj ?_ g
  have huniq := hL.datum.isUniqueInvolution_core
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K₀ := tightCore R with hK₀
  have hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := ⟨x, hx, rfl⟩
    unfold TightOddCent at hO
    rw [hO, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hthM : TC.Thin.ThinAtM Ω K₀ := fun N h => hall K₀ N h
  set P : Set (Subgroup Y) := {L : Subgroup Y | MaxAdj (TC.nbrAdj Ω) K₀ L} with hPdef
  have hPΩ : P ⊆ Ω := fun L hL => (show MaxAdj (TC.nbrAdj Ω) K₀ L from hL).1.2.1
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ TC.Thin.pSpan P, conjSub x L = L' :=
    fun L hL L' hL' => hS.exists_conj_maxOrb hL hL'
  have hinv : ∀ L ∈ P, ∀ x ∈ TC.Thin.pSpan P, conjSub x L ∈ P := fun L hL x hx =>
    hS.maxAdj_conj_of_mem hL huniq (hS.pSpan_le_centralizer huniq hx)
  have hodd := hS.oddCore_pSpan_eq_bot huniq hOC
  have hE2 : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∃ Q : Subgroup Y,
      Q ≤ TC.Thin.pSpan P ∧ (∀ x ∈ TC.Thin.pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
        IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    refine ⟨TC.Thin.Qz t ⊓ TC.Thin.pSpan P, inf_le_right, ?_, ?_, ?_⟩
    · intro x hx q hq
      refine ⟨(TC.Thin.isNormalTwoIn_Qz t).2.2 x (hS.pSpan_le_centralizer huniq hx) q hq.1, ?_⟩
      exact (TC.Thin.pSpan P).mul_mem ((TC.Thin.pSpan P).mul_mem hx hq.2)
        ((TC.Thin.pSpan P).inv_mem hx)
    · exact (TC.Thin.isNormalTwoIn_Qz t).2.1.to_le inf_le_left
    · exact ⟨TC.Thin.mem_Qz_of_maxAdj hthM hL huniq hu,
        TC.Thin.le_pSpan hL hu.mem⟩
  have hthin : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∀ Q : Subgroup Y,
      Q ≤ TC.Thin.pSpan P → (∀ x ∈ TC.Thin.pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) →
        IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = u := by
    intro L hL u hu Q hQX hQn hQ2 x hxL hxQ
    exact hS.eq_of_mem_Qz (show MaxAdj (TC.nbrAdj Ω) K₀ L from hL).1 (hthM L hL) huniq hu hxL
      (hS.le_Qz_of_normal huniq hQX hQn hQ2 hxQ)
  rcases hD Y Ω hS.hyp hS.two hS.card hS.tight hS.aEmpty
      (fun J hJ J' hJ' u hu hu' => hS.eq_of_uniqueInvolution hJ hJ' hu hu') P hPΩ htrans hinv
      hodd hE2 hthin with hind | ⟨m, hm, ⟨I⟩⟩ | hI | hI
  · exact fun N N' hN hN' hne => hind N hN N' hN' hne
  · intro N N' hN _ _ _
    exact hS.false_of_aeIdent hL.center hall hN hm I hodd fun L hL => hS.trans L hL
  · exact absurd hI (hE64 Y R S t hL hO hconn hsep hall)
  · exact absurd hI (h29 Y R S t hL hO hconn hsep hall)

end Cit3

end CFSG.ClassicalInvolution.Q3
