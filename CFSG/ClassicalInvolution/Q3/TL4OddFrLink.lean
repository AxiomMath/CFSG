module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrNbr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (ShareFour rankTwoSpan)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

section Vertices

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def triVert (Ω : Set (Subgroup G)) (B : Subgroup G) : Set G :=
  {a | ∃ (M : Fin 3 → Subgroup G) (x : Fin 3 → G) (P : Fin 3 → Subgroup G),
    TriFrame Ω M x P ∧ x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G) ∧
      B = Subgroup.closure ({x 0, x 1, x 2} : Set G) ∧ ∃ i, x i = a}

theorem mem_triFrameSet_of_mem_triVert {B : Subgroup G} {a : G} (h : a ∈ triVert Ω B) :
    B ∈ triFrameSet Ω := by
  obtain ⟨M, x, P, hF, hx, hB, -⟩ := h
  exact ⟨M, x, P, hF, hx, hB⟩

theorem triVert_conj (hΩ : ConjInvariant Ω) {B : Subgroup G} {a : G} (h : a ∈ triVert Ω B)
    (g : G) : g * a * g⁻¹ ∈ triVert Ω (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨M, x, P, hF, hx2, rfl, i, rfl⟩ := h
  refine ⟨_, _, _, triFrame_conj hΩ hF g, fun h => hx2 ?_, map_conj_closure_three g _ _ _, i, rfl⟩
  have h' : g * x 2 * g⁻¹ ∈
      (Subgroup.closure ({x 0, x 1} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_closure_two]
    exact h
  obtain ⟨y, hy, hyx⟩ := h'
  have hyx' : y = x 2 := by
    have h1 : g * y * g⁻¹ = g * x 2 * g⁻¹ := hyx
    simpa using h1
  rwa [← hyx']

@[expose] def VtxAdjFn (V : Set G) (𝒯 : Set (Subgroup G)) (cl : Subgroup G → Set G)
    (a b : G) : Prop :=
  a ∈ V ∧ b ∈ V ∧ ∃ A ∈ 𝒯, a ∈ cl A ∧ b ∈ cl A

theorem reflTransGen_shareFour_of_vertexFn {V : Set G} {𝒯 : Set (Subgroup G)}
    (cl : Subgroup G → Set G)
    (hvert : ∀ a ∈ V, ∀ a' ∈ V, Relation.ReflTransGen (VtxAdjFn V 𝒯 cl) a a')
    (hlink : ∀ a ∈ V, ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X') A A')
    {A A' : Subgroup G} (hA : A ∈ 𝒯) (hA' : A' ∈ 𝒯) {a a' : G} (ha : a ∈ V) (haA : a ∈ cl A)
    (ha' : a' ∈ V) (haA' : a' ∈ cl A') :
    Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X') A A' := by
  have key : ∀ b, Relation.ReflTransGen (VtxAdjFn V 𝒯 cl) a b → b ∈ V → ∀ B ∈ 𝒯, b ∈ cl B →
      Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X') A B := by
    intro b hb
    induction hb with
    | refl => exact fun _ B hB hbB => hlink a ha A hA B hB haA hbB
    | @tail b c _ hstep ih =>
      obtain ⟨hbV, hcV, C, hC, hbC, hcC⟩ := hstep
      exact fun _ B hB hcB => (ih hbV C hC hbC).trans (hlink c hcV C hC B hB hcC hcB)
  exact key a' (hvert a ha a' ha') ha' A' hA' haA'

theorem reflTransGen_shareFour_map {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) {X X' : Subgroup G}
    (h : Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X') X X') (g : G) :
    Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X')
      (X.map (MulAut.conj g).toMonoidHom) (X'.map (MulAut.conj g).toMonoidHom) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ⟨hinv _ hbc.1 g, hinv _ hbc.2.1 g, Theorem5.shareFour_map hbc.2.2 g⟩

theorem map_conj_map_conj_inv (g : G) (B : Subgroup G) :
    (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
  rw [Subgroup.map_map]
  ext y
  simp [Subgroup.mem_map, mul_assoc]

variable [Finite G] in
theorem vtxAdjFn_of_dConnected (hΩ : HypOmegaGen Ω) (hconn : Disconnected.DConnected Ω)
    {𝒯 : Set (Subgroup G)} {cl : Subgroup G → Set G}
    (hfr : ∀ M ∈ Ω, ∀ a : G, IsUniqueInvolution M a → ∀ N ∈ omegaNbr Ω M, ∀ b : G,
      IsUniqueInvolution N b → ∃ A ∈ 𝒯, a ∈ cl A ∧ b ∈ cl A) :
    ∀ a ∈ memberInvSet Ω, ∀ a' ∈ memberInvSet Ω,
      Relation.ReflTransGen (VtxAdjFn (memberInvSet Ω) 𝒯 cl) a a' := by
  rintro a ⟨M, hM, ha⟩ a' ⟨M', hM', ha'⟩
  have key : ∀ N, Relation.ReflTransGen
      (fun X Y : Subgroup G => Y ∈ Ω ∧ Disconnected.dAdj Ω X Y) M N →
      ∀ b, IsUniqueInvolution N b →
        Relation.ReflTransGen (VtxAdjFn (memberInvSet Ω) 𝒯 cl) a b := by
    intro N hN
    induction hN with
    | refl =>
      intro b hb
      obtain rfl := ha.eq hb
      exact Relation.ReflTransGen.refl
    | @tail N N' hMN hstep ih =>
      intro b' hb'
      have hNΩ : N ∈ Ω := mem_of_reflTransGen_dAdj hM hMN
      obtain ⟨b, hb⟩ := Sec6Gen.exists_uniqueInvolution hΩ hNΩ
      have hnbr : N' ∈ omegaNbr Ω N := by
        rcases hstep.2 with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hstep.1 hNΩ h
      obtain ⟨A, hA, hbA, hb'A⟩ := hfr N hNΩ b hb N' hnbr b' hb'
      exact (ih b hb).tail ⟨⟨N, hNΩ, hb⟩, ⟨N', hstep.1, hb'⟩, A, hA, hbA, hb'A⟩
  exact key M' (hconn M hM M' hM') a' ha'

end Vertices

section Graph

variable {Y : Type} [Group Y]

@[expose] def GAdj (R : Subgroup Y) (t : Y) (J L : Subgroup Y) : Prop :=
  J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
    L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
    L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ∧
    ∃ u z' : Y, IsUniqueInvolution J u ∧ IsUniqueInvolution L z' ∧ z' ≠ t * u

@[expose] def TriNbrAll (R : Subgroup Y) (t : Y) : Prop :=
  ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
    IsUniqueInvolution J u →
      ∃ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J ∧
          ∃ z' : Y, IsUniqueInvolution K' z' ∧ z' ≠ t * u

@[expose] def GLinkStep (R : Subgroup Y) (t : Y) (J J' : Subgroup Y) : Prop :=
  GAdj R t J J' ∨ ∃ L : Subgroup Y, GAdj R t J L ∧ ∃ u z' : Y, IsUniqueInvolution J u ∧
    IsUniqueInvolution L z' ∧ ∃ g ∈ Subgroup.centralizer ({t} : Set Y),
      g ∈ rankTwoSpan (Subgroup.closure ({t, u, z'} : Set Y)) ∧ J' = conjSub g J

end Graph

section Cit3

@[expose] def TightGraphLinkR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TriNbrAll R t →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (GLinkStep R t) J J'

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem noTwins_of_large (hL : TightLargeHypR r n Y R S t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) L, L' = L := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  exact fun L hL' => T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
    rw [hd.twinSet_eq] at hK'
    exact hK') hL'

theorem eq_core_of_isUniqueInvolution (hL : TightLargeHypR r n Y R S t) {M : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (htM : IsUniqueInvolution M t) :
    M = tightCore R :=
  noTwins_of_large hL _ (CoreAssembly.mem_conjClass_self _) M
    ⟨hM, t, hL.datum.isUniqueInvolution_core, htM⟩

theorem tFrame_mem (hL : TightLargeHypR r n Y R S t) {J L : Subgroup Y} (hG : GAdj R t J L)
    {u z' : Y} (hu : IsUniqueInvolution J u) (hz' : IsUniqueInvolution L z') :
    t ∈ triVert (CoreAssembly.conjClass (tightCore R)) (Subgroup.closure ({t, u, z'} : Set Y)) ∧
      u ∈ triVert (CoreAssembly.conjClass (tightCore R))
        (Subgroup.closure ({t, u, z'} : Set Y)) := by
  obtain ⟨hJ, hLK, hLJ, u₀, z₀, hu₀, hz₀, hne⟩ := hG
  have e1 : u = u₀ := hu.eq hu₀
  have e2 : z' = z₀ := hz'.eq hz₀
  subst e1
  subst e2
  have hd := hL.datum
  obtain ⟨P, hF⟩ := exists_triFrame_of_commonNbr hL hJ hLK hLJ hu hz'
  have hx : z' ∉ Subgroup.closure ({t, u} : Set Y) :=
    not_mem_closure_pair_of_triangle hd.hypOmegaGen (noTwins_of_large hL)
      (CoreAssembly.mem_conjClass_self _) hd.isUniqueInvolution_core hu hz' hJ hLK hLJ hne
  exact ⟨⟨_, _, _, hF, hx, rfl, 0, rfl⟩, ⟨_, _, _, hF, hx, rfl, 1, rfl⟩⟩

theorem shareFour_of_mem_pair (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {A A' : Subgroup Y} (htA : t ∈ A) (huA : u ∈ A)
    (htA' : t ∈ A') (huA' : u ∈ A') : ShareFour A A' := by
  have hd := hL.datum
  obtain ⟨hne, hu2, hut, -, -, -⟩ := hd.edge_involution hJ hu
  have hc : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp hut).symm
  have h4 : Nat.card ↥(Subgroup.closure ({t, u} : Set Y)) = 4 :=
    Bootstrap.card_closure_pair_eq_four hd.isUniqueInvolution_core.sq hu2
      hd.isUniqueInvolution_core.ne_one hu.ne_one (Ne.symm hne) hc
  have hle : ∀ {B : Subgroup Y}, t ∈ B → u ∈ B → Subgroup.closure ({t, u} : Set Y) ≤ B := by
    intro B htB huB
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact htB
    · exact huB
  refine ⟨Subgroup.closure ({t, u} : Set Y), ⟨hle htA huA, ?_⟩, ⟨hle htA' huA', ?_⟩⟩
  · rw [h4]
    norm_num
  · rw [h4]
    norm_num

theorem tFrame_cases (hL : TightLargeHypR r n Y R S t) {A : Subgroup Y}
    (hA : t ∈ triVert (CoreAssembly.conjClass (tightCore R)) A) :
    ∃ (J L : Subgroup Y) (u z' : Y), GAdj R t J L ∧ IsUniqueInvolution J u ∧
      IsUniqueInvolution L z' ∧ A = Subgroup.closure ({t, u, z'} : Set Y) := by
  obtain ⟨M, x, P, hF, hx2, rfl, i, hi⟩ := hA
  have hΩ := hL.datum.hypOmegaGen
  have hcl : ∀ a b : Y, a ∈ ({x 0, x 1} : Set Y) → b ∈ ({x 0, x 1} : Set Y) →
      a * b ∈ Subgroup.closure ({x 0, x 1} : Set Y) := fun a b ha hb =>
    Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)
  have h3 : x 0 = t ∨ x 1 = t ∨ x 2 = t := by
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  rcases h3 with h0 | h1 | h2
  · have hM : M 0 = tightCore R := eq_core_of_isUniqueInvolution hL (hF.mem 0) (h0 ▸ hF.inv 0)
    have n01 := hF.nbr 0 1 (by decide)
    have n02 := hF.nbr 0 2 (by decide)
    rw [hM] at n01 n02
    refine ⟨M 1, M 2, x 1, x 2, ⟨n01, n02, hF.nbr 1 2 (by decide), x 1, x 2, hF.inv 1,
      hF.inv 2, fun h => hx2 ?_⟩, hF.inv 1, hF.inv 2, by rw [h0]⟩
    rw [h, ← h0]
    exact hcl _ _ (by simp) (by simp)
  · have hM : M 1 = tightCore R := eq_core_of_isUniqueInvolution hL (hF.mem 1) (h1 ▸ hF.inv 1)
    have n10 := hF.nbr 1 0 (by decide)
    have n12 := hF.nbr 1 2 (by decide)
    rw [hM] at n10 n12
    refine ⟨M 0, M 2, x 0, x 2, ⟨n10, n12, hF.nbr 0 2 (by decide), x 0, x 2, hF.inv 0,
      hF.inv 2, fun h => hx2 ?_⟩, hF.inv 0, hF.inv 2, ?_⟩
    · rw [h, ← h1]
      exact hcl _ _ (by simp) (by simp)
    · rw [h1, Set.insert_comm]
  · have hM : M 2 = tightCore R := eq_core_of_isUniqueInvolution hL (hF.mem 2) (h2 ▸ hF.inv 2)
    have n20 := hF.nbr 2 0 (by decide)
    have n21 := hF.nbr 2 1 (by decide)
    rw [hM] at n20 n21
    refine ⟨M 0, M 1, x 0, x 1, ⟨n20, n21, hF.nbr 0 1 (by decide), x 0, x 1, hF.inv 0,
      hF.inv 1, fun h => hx2 ?_⟩, hF.inv 0, hF.inv 1, ?_⟩
    · have hx0 : x 0 * x 0 = 1 := hF.sq 0
      have e : x 2 = x 1 * x 0 := by
        rw [h, ← h2, mul_assoc, hx0, mul_one]
      rw [e]
      exact hcl _ _ (by simp) (by simp)
    · rw [h2]
      congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

theorem link_at_core (hL : TightLargeHypR r n Y R S t)
    (hgl : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (GLinkStep R t) J J')
    {A A' : Subgroup Y} (hA : t ∈ triVert (CoreAssembly.conjClass (tightCore R)) A)
    (hA' : t ∈ triVert (CoreAssembly.conjClass (tightCore R)) A') :
    Relation.ReflTransGen (fun X X' => X ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧
      X' ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧ ShareFour X X') A A' := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hinv : ∀ B ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)), ∀ g : Y,
      B.map (MulAut.conj g).toMonoidHom ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) :=
    fun B hB g => triFrameSet_conj hΩ.conjInvariant hB g
  have hAm := mem_triFrameSet_of_mem_triVert hA
  obtain ⟨J₁, L₁, u₁, z₁, hG₁, hu₁, hz₁, rfl⟩ := tFrame_cases hL hA
  obtain ⟨J₂, L₂, u₂, z₂, hG₂, hu₂, hz₂, rfl⟩ := tFrame_cases hL hA'
  have hA'm := mem_triFrameSet_of_mem_triVert hA'
  have hmem3 : ∀ a b c : Y, a ∈ Subgroup.closure ({a, b, c} : Set Y) ∧
      b ∈ Subgroup.closure ({a, b, c} : Set Y) ∧ c ∈ Subgroup.closure ({a, b, c} : Set Y) :=
    fun a b c => ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
      Subgroup.subset_closure (by simp)⟩
  have key : ∀ J, Relation.ReflTransGen (GLinkStep R t) J₁ J →
      J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
        ∀ u : Y, IsUniqueInvolution J u →
          ∀ A'' ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)), t ∈ A'' → u ∈ A'' →
            Relation.ReflTransGen
              (fun X X' => X ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧
                X' ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧ ShareFour X X')
              (Subgroup.closure ({t, u₁, z₁} : Set Y)) A'' := by
    intro J hJ
    induction hJ with
    | refl =>
      refine ⟨hG₁.1, fun u hu A'' hA'' htA'' huA'' => ?_⟩
      obtain rfl := hu.eq hu₁
      exact Relation.ReflTransGen.single ⟨hAm, hA'', shareFour_of_mem_pair hL hG₁.1 hu
        (hmem3 _ _ _).1 (hmem3 _ _ _).2.1 htA'' huA''⟩
    | @tail J J'' _ hstep ih =>
      obtain ⟨hJΩ, hJlink⟩ := ih
      rcases hstep with hG | ⟨L, hG, u, z', hu, hz', g, hgt, hg, rfl⟩
      · obtain ⟨u, z', hu, hz', -⟩ := hG.2.2.2
        obtain ⟨htB, huB⟩ := tFrame_mem hL hG hu hz'
        have hB := mem_triFrameSet_of_mem_triVert htB
        have hAB := hJlink u hu _ hB (hmem3 _ _ _).1 (hmem3 _ _ _).2.1
        refine ⟨hG.2.1, fun u'' hu'' A'' hA'' htA'' huA'' => hAB.tail ⟨hB, hA'', ?_⟩⟩
        obtain rfl := hu''.eq hz'
        exact shareFour_of_mem_pair hL hG.2.1 hu'' (hmem3 _ _ _).1 (hmem3 _ _ _).2.2 htA'' huA''
      · obtain ⟨htB, huB⟩ := tFrame_mem hL hG hu hz'
        have hB := mem_triFrameSet_of_mem_triVert htB
        have hAB := hJlink u hu _ hB (hmem3 _ _ _).1 (hmem3 _ _ _).2.1
        have hBg := Theorem5.reflTransGen_shareFour_map_of_mem_rankTwoSpan hinv hB hg
        have hgt' : g * t * g⁻¹ = t := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
        have hcore : conjSub g (tightCore R) = tightCore R := by
          refine eq_core_of_isUniqueInvolution hL (hΩ.conjInvariant g _
            (CoreAssembly.mem_conjClass_self _)) ?_
          have h1 := hd.isUniqueInvolution_core.conj g
          rwa [hgt'] at h1
        have hJ'' :
            conjSub g J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
          have h1 := omegaNbr_conj hΩ.conjInvariant hJΩ g
          rwa [hcore] at h1
        refine ⟨hJ'', fun u'' hu'' A'' hA'' htA'' huA'' => (hAB.trans hBg).tail
          ⟨hinv _ hB g, hA'', ?_⟩⟩
        have e : u'' = g * u * g⁻¹ := hu''.eq (hu.conj g)
        refine shareFour_of_mem_pair hL hJ'' hu'' ?_ ?_ htA'' huA''
        · exact ⟨t, (hmem3 _ _ _).1, by simp [hgt']⟩
        · exact ⟨u, (hmem3 _ _ _).2.1, by rw [e]; simp⟩
  exact (key J₂ (hgl J₁ hG₁.1 J₂ hG₂.1)).2 u₂ hu₂ _ hA'm (hmem3 _ _ _).1 (hmem3 _ _ _).2.1

theorem link_at_vertex (hL : TightLargeHypR r n Y R S t)
    (hgl : ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        Relation.ReflTransGen (GLinkStep R t) J J') :
    ∀ a ∈ memberInvSet (CoreAssembly.conjClass (tightCore R)),
      ∀ A ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)),
      ∀ A' ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)),
        a ∈ triVert (CoreAssembly.conjClass (tightCore R)) A →
        a ∈ triVert (CoreAssembly.conjClass (tightCore R)) A' →
        Relation.ReflTransGen
          (fun X X' => X ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧
            X' ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)) ∧ ShareFour X X') A A' := by
  rintro a ⟨M, hM, ha⟩ A - A' - haA haA'
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  obtain ⟨g, hgM'⟩ := hM
  have hgM : conjSub g (tightCore R) = M := hgM'
  have hga : g * t * g⁻¹ = a := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgM] at h1
    exact h1.eq ha
  have hta : g⁻¹ * a * g⁻¹⁻¹ = t := by
    rw [← hga]
    group
  have h1 := triVert_conj hΩ.conjInvariant haA g⁻¹
  have h2 := triVert_conj hΩ.conjInvariant haA' g⁻¹
  rw [hta] at h1 h2
  have hc := reflTransGen_shareFour_map (fun B hB g => triFrameSet_conj hΩ.conjInvariant hB g)
    (link_at_core hL hgl h1 h2) g
  rwa [map_conj_map_conj_inv, map_conj_map_conj_inv] at hc

theorem framesV_of_triNbrAll (hL : TightLargeHypR r n Y R S t) (hA : TriNbrAll R t) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ a : Y, IsUniqueInvolution M a →
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M, ∀ b : Y, IsUniqueInvolution N b →
        ∃ B ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)),
          a ∈ triVert (CoreAssembly.conjClass (tightCore R)) B ∧
            b ∈ triVert (CoreAssembly.conjClass (tightCore R)) B := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hcore : ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ b : Y,
      IsUniqueInvolution N b → ∃ B ∈ triFrameSet (CoreAssembly.conjClass (tightCore R)),
        t ∈ triVert (CoreAssembly.conjClass (tightCore R)) B ∧
          b ∈ triVert (CoreAssembly.conjClass (tightCore R)) B := by
    intro N hN b hb
    obtain ⟨K', hK'K, hK'N, z', hz', hne⟩ := hA N hN b hb
    have hG : GAdj R t N K' := ⟨hN, hK'K, hK'N, b, z', hb, hz', hne⟩
    obtain ⟨htB, hbB⟩ := tFrame_mem hL hG hb hz'
    exact ⟨_, mem_triFrameSet_of_mem_triVert htB, htB, hbB⟩
  intro M hM a ha N hN b hb
  obtain ⟨g, hgM'⟩ := hM
  have hgM : conjSub g (tightCore R) = M := hgM'
  have hga : g * t * g⁻¹ = a := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgM] at h1
    exact h1.eq ha
  have hN' : conjSub g⁻¹ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hN g⁻¹
    rwa [← hgM, conjSub_inv_conjSub] at h1
  obtain ⟨B, hB, htB, hbB⟩ := hcore _ hN' _ (hb.conj g⁻¹)
  refine ⟨B.map (MulAut.conj g).toMonoidHom, triFrameSet_conj hΩ.conjInvariant hB g, ?_, ?_⟩
  · rw [← hga]
    exact triVert_conj hΩ.conjInvariant htB g
  · have h1 := triVert_conj hΩ.conjInvariant hbB g
    have e : g * (g⁻¹ * b * g⁻¹⁻¹) * g⁻¹ = b := by group
    rwa [e] at h1

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
