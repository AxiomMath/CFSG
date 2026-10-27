module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F] {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

namespace FieldNeighbourParam

variable {X : Subgroup G} {N : Finset (Fin n)}

theorem pieceCore_eq_map_of_notMem [Finite G] [Finite F] (P : FieldNeighbourParam e t ι σ X N)
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hI : 2 ≤ I.card) {k : Fin n} (hk : k ∉ N) {κ : Kˣ}
    (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F) (hXI : X ≤ modelToG e (blockTorus (K := K) I)) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
  pieceCore_eq_map_of_conjDiag_of_notMem e ι hIN hk hκ
    (commutator_blockSpecialLinear_eq_of_two_le hI hF) hXI P.Φ P.ker_le P.range_eq
    (fun c _ x => P.N2 c x)

theorem pieceCore_index_eq_range [Finite G] [Finite F] (P : FieldNeighbourParam e t ι σ X N)
    (hN : 2 ≤ N.card) (hF : 4 ≤ Nat.card F) (hXN : X ≤ modelToG e (blockTorus (K := K) N)) :
    pieceCore e N = centralizerPerfectCore X := by
  rw [pieceCore_eq_range_of_conjDiag e ι (commutator_blockSpecialLinear_eq_of_two_le hN hF) hXN
    P.Φ P.ker_le P.range_eq (fun c _ x => P.N2 c x), P.range_eq]

theorem nonempty_mulEquiv_pieceCore_of_notMem [Finite G] [Finite F]
    (P : FieldNeighbourParam e t ι σ X N) {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N)
    (hI : 2 ≤ I.card) {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I)) :
    Nonempty (Matrix.SpecialLinearGroup (Fin I.card) F ≃* pieceCore e I) :=
  nonempty_mulEquiv_pieceCore_of_conjDiag e ι hIN hne
    (fun _ hi _ hj hij hIJ => exists_mem_blockTorusParam_ne_of_notMem hIN hk hκ hi hj hij hIJ)
    (commutator_blockSpecialLinear_eq_of_two_le hI hF) hXI P.Φ P.ker_le P.range_eq
    (fun c _ x => P.N2 c x)

theorem map_eq_map_of_notMem [Finite G] [Finite F] {X' : Subgroup G} {N' : Finset (Fin n)}
    (P : FieldNeighbourParam e t ι σ X N) (P' : FieldNeighbourParam e t ι σ X' N')
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N') (hI : 2 ≤ I.card) {k k' : Fin n}
    (hk : k ∉ N) (hk' : k' ∉ N') {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (hXI' : X' ≤ modelToG e (blockTorus (K := K) I)) :
    ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map P.Φ =
      ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N')).map P'.Φ := by
  rw [← P.pieceCore_eq_map_of_notMem hIN hI hk hκ hF hXI,
    ← P'.pieceCore_eq_map_of_notMem hIN' hI hk' hκ hF hXI']

theorem pieceCore_le_centralizer_of_notMem [Finite G] [Finite F]
    (P : FieldNeighbourParam e t ι σ X N) {I J : Finset (Fin n)} (hIN : I ⊆ N) (hJN : J ⊆ N)
    (hIJ : Disjoint I J) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) {k : Fin n} (hk : k ∉ N) {κ : Kˣ}
    (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F) (hXI : X ≤ modelToG e (blockTorus (K := K) I))
    (hXJ : X ≤ modelToG e (blockTorus (K := K) J)) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  rw [P.pieceCore_eq_map_of_notMem hIN hI hk hκ hF hXI,
    P.pieceCore_eq_map_of_notMem hJN hJ hk hκ hF hXJ]
  exact map_subgroupOf_le_centralizer_of_disjoint hIJ P.Φ

end FieldNeighbourParam

theorem Neighbour.exists_notMem_index (Nb : Neighbour n) : ∃ k, k ∉ Nb.index := by
  cases Nb with
  | root a b hab => exact ⟨a, by rw [Neighbour.index_root]; simp⟩
  | levi a => exact ⟨a, by rw [Neighbour.index_levi]; simp⟩

namespace FieldNeighbourParam

theorem pieceCore_eq_map_neighbour [Finite G] [Finite F] (Nb : Neighbour n)
    (P : FieldNeighbourParam e t ι σ (modelToG e (Nb.torus K)) Nb.index) {I : Finset (Fin n)}
    (hI : I ⊆ Nb.index) (hI2 : 2 ≤ I.card) {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F) :
    pieceCore e I =
      ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear Nb.index)).map P.Φ := by
  obtain ⟨k, hk⟩ := Nb.exists_notMem_index
  exact P.pieceCore_eq_map_of_notMem hI hI2 hk hκ hF (modelToG_torus_le_blockTorus e Nb hI)

theorem map_eq_map_neighbour [Finite G] [Finite F] (Nb Nb' : Neighbour n)
    (P : FieldNeighbourParam e t ι σ (modelToG e (Nb.torus K)) Nb.index)
    (P' : FieldNeighbourParam e t ι σ (modelToG e (Nb'.torus K)) Nb'.index) {I : Finset (Fin n)}
    (hI : I ⊆ Nb.index) (hI' : I ⊆ Nb'.index) (hI2 : 2 ≤ I.card) {κ : Kˣ} (hκ : κ ≠ 1)
    (hF : 4 ≤ Nat.card F) :
    ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear Nb.index)).map P.Φ =
      ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear Nb'.index)).map P'.Φ := by
  rw [← P.pieceCore_eq_map_neighbour Nb hI hI2 hκ hF,
    ← P'.pieceCore_eq_map_neighbour Nb' hI' hI2 hκ hF]

theorem pieceCore_eq_map_rootTorus [Finite G] [Finite F] {a b : Fin n} (hab : a ≠ b)
    (P : FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
      (({a, b} : Finset (Fin n))ᶜ)) {I : Finset (Fin n)} (hI : I ⊆ ({a, b} : Finset (Fin n))ᶜ)
    (hI2 : 2 ≤ I.card) {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F) :
    pieceCore e I = ((blockSpecialLinear (K := F) I).subgroupOf
      (blockSpecialLinear (({a, b} : Finset (Fin n))ᶜ))).map P.Φ :=
  P.pieceCore_eq_map_neighbour (.root a b hab) hI hI2 hκ hF

theorem pieceCore_eq_map_levTorus [Finite G] [Finite F] (a : Fin n)
    (P : FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ))
    {I : Finset (Fin n)} (hI : I ⊆ {a}ᶜ) (hI2 : 2 ≤ I.card) {κ : Kˣ} (hκ : κ ≠ 1)
    (hF : 4 ≤ Nat.card F) :
    pieceCore e I =
      ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear {a}ᶜ)).map P.Φ :=
  P.pieceCore_eq_map_neighbour (.levi a) hI hI2 hκ hF

end FieldNeighbourParam

@[expose] def FieldNeighbourCover (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F)
    (σ : F ≃+* F) (s : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ s → ∃ (X : Subgroup G) (N : Finset (Fin n)), S ⊆ N ∧
    (∃ k, k ∉ N) ∧ X ≤ modelToG e (blockTorus (K := K) S) ∧
      Nonempty (FieldNeighbourParam e t ι σ X N)

theorem FieldNeighbourCover.mono {s s' : ℕ} (h : FieldNeighbourCover e t ι σ s) (hs : s' ≤ s) :
    FieldNeighbourCover e t ι σ s' :=
  fun S hS => h S (hS.trans hs)

theorem exists_two_index_notMem {S : Finset (Fin n)} (hS : S.card + 2 ≤ n) :
    ∃ a b : Fin n, a ≠ b ∧ a ∉ S ∧ b ∉ S := by
  have hc : 1 < Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
  exact ⟨a, b, hab, Finset.mem_compl.1 ha, Finset.mem_compl.1 hb⟩

theorem exists_index_notMem_of_card_lt {S : Finset (Fin n)} (hS : S.card < n) :
    ∃ a : Fin n, a ∉ S := by
  have hc : 0 < Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hc
  exact ⟨a, Finset.mem_compl.1 ha⟩

theorem fieldNeighbourCover_rootTorus
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ)))
    {s : ℕ} (hs : s + 2 ≤ n) : FieldNeighbourCover e t ι σ s := by
  intro S hS
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_index_notMem (S := S) (by omega)
  refine ⟨modelToG e (rootTorus (K := K) hab), ({a, b} : Finset (Fin n))ᶜ, fun x hx => ?_,
    ⟨a, by simp⟩, modelToG_rootTorus_le e hab ha hb, hparam a b hab⟩
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun h => ha (h ▸ hx), fun h => hb (h ▸ hx)⟩

theorem fieldNeighbourCover_levTorus
    (hparam : ∀ a : Fin n,
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    {s : ℕ} (hs : s + 1 ≤ n) : FieldNeighbourCover e t ι σ s := by
  intro S hS
  obtain ⟨a, ha⟩ := exists_index_notMem_of_card_lt (S := S) (by omega)
  refine ⟨modelToG e (levTorus (K := K) a), {a}ᶜ, fun x hx => ?_, ⟨a, by simp⟩,
    modelToG_levTorus_le e ha, hparam a⟩
  simp only [Finset.mem_compl, Finset.mem_singleton]
  exact fun h => ha (h ▸ hx)

theorem pieceCore_le_centralizer_of_fieldNeighbourCover [Finite G] [Finite F] {s : ℕ}
    (hcov : FieldNeighbourCover e t ι σ s) {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hs : (I ∪ J).card ≤ s) {κ : Kˣ} (hκ : κ ≠ 1)
    (hF : 4 ≤ Nat.card F) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  obtain ⟨X, N, hSN, ⟨k, hk⟩, hX, ⟨P⟩⟩ := hcov (I ∪ J) hs
  exact P.pieceCore_le_centralizer_of_notMem (Finset.subset_union_left.trans hSN)
    (Finset.subset_union_right.trans hSN) hIJ hI hJ hk hκ hF
    (hX.trans (modelToG_mono e (blockTorus_anti Finset.subset_union_left)))
    (hX.trans (modelToG_mono e (blockTorus_anti Finset.subset_union_right)))

theorem exists_pieceCore_eq_map_of_fieldNeighbourCover [Finite G] [Finite F] {s : ℕ}
    (hcov : FieldNeighbourCover e t ι σ s) {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (hs : I.card ≤ s) {κ : Kˣ} (hκ : κ ≠ 1) (hF : 4 ≤ Nat.card F) :
    ∃ (X : Subgroup G) (N : Finset (Fin n)) (P : FieldNeighbourParam e t ι σ X N), I ⊆ N ∧
      pieceCore e I =
        ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  obtain ⟨X, N, hIN, ⟨k, hk⟩, hX, ⟨P⟩⟩ := hcov I hs
  exact ⟨X, N, P, hIN, P.pieceCore_eq_map_of_notMem hIN hI hk hκ hF hX⟩

end CFSG.SeitzReduction.LinearPilot
