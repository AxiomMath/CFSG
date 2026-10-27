module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrRoute
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Tri
public import CFSG.ClassicalInvolution.Q3.TL4OddSecEdge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

section Sylow

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_isSylow2In_core_le_centralizer (hd : TightDatum R S t) {a b : Y} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a)
    (haR : a ∈ centralizerModOdd ⊤ R) (hbR : b ∈ centralizerModOdd ⊤ R) :
    ∃ P : Subgroup Y, IsSylow2In P (tightCore R) ∧ P ≤ Subgroup.centralizer ({a} : Set Y) ∧
      P ≤ Subgroup.centralizer ({b} : Set Y) ∧ P ≤ Subgroup.centralizer ({t} : Set Y) := by
  have hB2 : IsPGroup 2 ↥(Subgroup.closure ({a, b} : Set Y)) :=
    IsPGroup.of_card (n := 2) (by
      rw [Bootstrap.card_closure_pair_eq_four ha hb ha1 hb1 hab hc]
      norm_num)
  have hBR : Subgroup.closure ({a, b} : Set Y) ≤ centralizerModOdd ⊤ R := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact haR
    · exact hbR
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer hB2 hBR
  refine ⟨_, (hd.ofSylow S').sylow_core, hS'.trans (Subgroup.centralizer_le ?_),
    hS'.trans (Subgroup.centralizer_le ?_), (Subgroup.map_subtype_le _).trans hd.cent⟩
  · exact Set.singleton_subset_iff.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  · exact Set.singleton_subset_iff.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

end Sylow

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_isSylow2In_member_le_centralizer (hL : TightLargeHypR r n Y R S t)
    {M : Subgroup Y} (hM : M ∈ CoreAssembly.conjClass (tightCore R)) {x : Y}
    (hx : IsUniqueInvolution M x) {N₁ N₂ : Subgroup Y}
    (h₁ : N₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M)
    (h₂ : N₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) {y₁ y₂ : Y}
    (hy₁ : IsUniqueInvolution N₁ y₁) (hy₂ : IsUniqueInvolution N₂ y₂) (hne : y₁ ≠ y₂)
    (hc : y₁ * y₂ = y₂ * y₁) :
    ∃ P : Subgroup Y, IsSylow2In P M ∧ P ≤ Subgroup.centralizer ({x} : Set Y) ∧
      P ≤ Subgroup.centralizer ({y₁} : Set Y) ∧ P ≤ Subgroup.centralizer ({y₂} : Set Y) := by
  have hd := hL.datum
  obtain ⟨g, hgM'⟩ := hM
  have hgM : conjSub g (tightCore R) = M := hgM'
  obtain ⟨SJ, hdg, -⟩ := hd.conj g
  have hcore : tightCore (conjSub g R) = M := by rw [← conjSub_tightCore, hgM]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hgx : g * t * g⁻¹ = x := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgM] at h1
    exact h1.eq hx
  have hN : ∀ {N : Subgroup Y}, N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M →
      N ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R))) (tightCore (conjSub g R)) :=
    fun h => by rw [hfam, hcore]; exact h
  obtain ⟨-, -, hut₁, -, huK₁, -⟩ := hdg.edge_involution (hN h₁) hy₁
  obtain ⟨-, -, hut₂, -, huK₂, -⟩ := hdg.edge_involution (hN h₂) hy₂
  obtain ⟨P, hP, hP₁, hP₂, hPx⟩ := exists_isSylow2In_core_le_centralizer hdg hy₁.sq hy₂.sq
    hy₁.ne_one hy₂.ne_one hne hc (mem_centralizerModOdd_of_act hdg hut₁ huK₁)
    (mem_centralizerModOdd_of_act hdg hut₂ huK₂)
  rw [hcore] at hP
  rw [hgx] at hPx
  exact ⟨P, hP, hPx, hP₁, hP₂⟩

theorem exists_triFrame_of_commonNbr (hL : TightLargeHypR r n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'K : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u z' : Y}
    (hu : IsUniqueInvolution J u) (hz' : IsUniqueInvolution K' z') :
    ∃ P : Fin 3 → Subgroup Y,
      TriFrame (CoreAssembly.conjClass (tightCore R)) ![tightCore R, J, K'] ![t, u, z'] P := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ht := hd.isUniqueInvolution_core
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) L, L' = L := fun L hL' =>
    T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
      rw [hd.twinSet_eq] at hK'
      exact hK') hL'
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have hKK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hK'K.1 hK'K
  have hJK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK'K.1 hK'J
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have ctz : t * z' = z' * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hK'K hz'
  have cuz : u * z' = z' * u := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hu hK'J hz'
  have ntu : t ≠ u := fun h => hJ.2.1 (hnt _ hK J ⟨hJ.1, t, ht, h ▸ hu⟩)
  have ntz : t ≠ z' := fun h => hK'K.2.1 (hnt _ hK K' ⟨hK'K.1, t, ht, h ▸ hz'⟩)
  have nuz : u ≠ z' := fun h => hK'J.2.1 (hnt _ hJ.1 K' ⟨hK'K.1, u, hu, h ▸ hz'⟩)
  obtain ⟨P₀, hP₀, hP₀t, hP₀u, hP₀z⟩ :=
    exists_isSylow2In_member_le_centralizer hL hK ht hJ hK'K hu hz' nuz cuz
  obtain ⟨P₁, hP₁, hP₁u, hP₁t, hP₁z⟩ :=
    exists_isSylow2In_member_le_centralizer hL hJ.1 hu hKJ hK'J ht hz' ntz ctz
  obtain ⟨P₂, hP₂, hP₂z, hP₂t, hP₂u⟩ :=
    exists_isSylow2In_member_le_centralizer hL hK'K.1 hz' hKK' hJK' ht hu ntu ctu
  refine ⟨![P₀, P₁, P₂], ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_,
    fun i j => ?_⟩⟩
  · fin_cases i
    · exact hK
    · exact hJ.1
    · exact hK'K.1
  · fin_cases i
    · exact ht
    · exact hu
    · exact hz'
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hJ
    · exact hK'K
    · exact hKJ
    · exact absurd rfl hij
    · exact hK'J
    · exact hKK'
    · exact hJK'
    · exact absurd rfl hij
  · fin_cases i
    · exact hP₀
    · exact hP₁
    · exact hP₂
  · fin_cases i <;> fin_cases j
    · exact hP₀t
    · exact hP₀u
    · exact hP₀z
    · exact hP₁t
    · exact hP₁u
    · exact hP₁z
    · exact hP₂t
    · exact hP₂u
    · exact hP₂z

theorem framesAtEdges_tri_of_commonNbr (hL : TightLargeHypR r n Y R S t)
    (h : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u →
        ∃ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ∧
            ∃ z' : Y, IsUniqueInvolution K' z' ∧ z' ≠ t * u) :
    FramesAtEdges (CoreAssembly.conjClass (tightCore R)) (tightCore R) t
      (triFrameSet (CoreAssembly.conjClass (tightCore R))) := by
  intro J hJ u hu
  obtain ⟨K', hK'K, hK'J, z', hz', hne⟩ := h J hJ u hu
  obtain ⟨P, hF⟩ := exists_triFrame_of_commonNbr hL hJ hK'K hK'J hu hz'
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) L, L' = L := fun L hL' =>
    T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
      rw [hd.twinSet_eq] at hK'
      exact hK') hL'
  have hx : z' ∉ Subgroup.closure ({t, u} : Set Y) :=
    not_mem_closure_pair_of_triangle hΩ hnt (CoreAssembly.mem_conjClass_self _)
      hd.isUniqueInvolution_core hu hz' hJ hK'K hK'J hne
  exact ⟨_, ⟨_, _, _, hF, hx, rfl⟩, closure_pair_le_closure_triangle⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
