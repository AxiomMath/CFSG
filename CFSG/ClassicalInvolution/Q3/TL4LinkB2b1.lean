module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Pair

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def layerQ (Ω : Set (Subgroup G)) (x : G) : Subgroup G :=
  oddCoreOf (layerY Ω x)

@[expose] def RigidEdge (K J : Subgroup G) (k j : G) : Prop :=
  ∀ P T : Subgroup G, IsSylow2In P K → IsSylow2In T J → Commutes P T →
    ∀ e ∈ Subgroup.centralizer (P : Set G) ⊓ Subgroup.centralizer (T : Set G),
      e * e = 1 → e ∈ Subgroup.closure ({k, j} : Set G)

structure Tri (r : ℕ) (Ω : Set (Subgroup G)) (K J M : Subgroup G) (t u : G) : Prop where
  fam : TypeRFam r Ω
  trans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L'
  mem : K ∈ Ω
  inv_K : IsUniqueInvolution K t
  adj_J : J ∈ omegaNbr Ω K
  inv_J : IsUniqueInvolution J u
  adj_M : M ∈ omegaNbr Ω K
  adj_MJ : M ∈ omegaNbr Ω J
  h2 : ∀ J' ∈ omegaNbr Ω K, ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J' → ∀ u' z' : G,
    IsUniqueInvolution J' u' → IsUniqueInvolution K' z' → z' = t * u'
  h7 : ∀ L ∈ omegaNbr Ω K, ∃ ν ∈ layerQ Ω t, L = conjSub ν J ∨ L = conjSub ν M

omit [Finite G] in
private theorem conjSub_coreAt_conj (g x : G) (L : Subgroup G) :
    conjSub g (coreAt x L) = coreAt (g * x * g⁻¹) (conjSub g L) := by
  unfold coreAt
  rw [conjSub_tightCore]
  congr 1
  show (L ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  show conjSub g L ⊓ conjSub g (Subgroup.centralizer ({x} : Set G)) = _
  rw [Balance.conjSub_centralizer_singleton]

omit [Finite G] in
private theorem xMem_conjSub (hΩ : ConjInvariant Ω) {x : G} {L : Subgroup G} (hL : XMem Ω x L)
    (g : G) : XMem Ω (g * x * g⁻¹) (conjSub g L) := by
  obtain ⟨hLΩ, hN, R, hR, hRx⟩ := hL
  refine ⟨hΩ g L hLΩ, ?_, conjSub g R, hR.conj g, ?_⟩
  · rw [mem_normalizer_conjSub_iff]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hN
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := hRx _ hy
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group

omit [Finite G] in
private theorem conjSub_layerY_le (hΩ : ConjInvariant Ω) (g x : G) :
    conjSub g (layerY Ω x) ≤ layerY Ω (g * x * g⁻¹) := by
  unfold layerY
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun C hC => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨L, hL, rfl⟩ := hC
  exact le_layerY ⟨conjSub g L, xMem_conjSub hΩ hL g, conjSub_coreAt_conj g x L⟩

theorem layerY_conj (hΩ : ConjInvariant Ω) (g x : G) :
    layerY Ω (g * x * g⁻¹) = conjSub g (layerY Ω x) := by
  refine le_antisymm ?_ (conjSub_layerY_le hΩ g x)
  have h := conjSub_mono (n := g) (conjSub_layerY_le hΩ g⁻¹ (g * x * g⁻¹))
  rw [conjSub_conjSub_inv] at h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem layerQ_conj (hΩ : ConjInvariant Ω) (g x : G) :
    layerQ Ω (g * x * g⁻¹) = conjSub g (layerQ Ω x) := by
  unfold layerQ
  rw [layerY_conj hΩ g x]
  exact Thompson.oddCoreOf_conjSub_eq g (layerY Ω x)

theorem RigidEdge.symm {K J : Subgroup G} {k j : G} (h : RigidEdge K J k j) :
    RigidEdge J K j k := by
  intro P T hP hT hPT e he he2
  rw [Set.pair_comm]
  exact h T P hT hP hPT.symm e (by rw [inf_comm]; exact he) he2

theorem RigidEdge.conj {K J : Subgroup G} {k j : G} (h : RigidEdge K J k j) (g : G) :
    RigidEdge (conjSub g K) (conjSub g J) (g * k * g⁻¹) (g * j * g⁻¹) := by
  intro P T hP hT hPT e he he2
  have back : ∀ {A B : Subgroup G}, IsSylow2In A (conjSub g B) → IsSylow2In (conjSub g⁻¹ A) B := by
    intro A B hA
    have h1 := hA.conj g⁻¹
    rwa [conjSub_inv_conjSub] at h1
  have hcent : ∀ {A : Subgroup G}, e ∈ Subgroup.centralizer (A : Set G) →
      g⁻¹ * e * g ∈ Subgroup.centralizer (conjSub g⁻¹ A : Set G) := by
    intro A hA
    rw [Subgroup.mem_centralizer_iff] at hA ⊢
    intro a ha
    rw [SetLike.mem_coe, mem_conjSub_iff, inv_inv] at ha
    have h1 := hA _ ha
    calc a * (g⁻¹ * e * g) = g⁻¹ * ((g * a * g⁻¹) * e) * g := by group
      _ = g⁻¹ * (e * (g * a * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * e * g * a := by group
  have he' := h _ _ (back hP) (back hT) (hPT.conjSub g⁻¹) (g⁻¹ * e * g)
    (Subgroup.mem_inf.mpr ⟨hcent (Subgroup.mem_inf.mp he).1, hcent (Subgroup.mem_inf.mp he).2⟩)
    (by
      calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
        _ = 1 := by rw [he2]; group)
  have hcl : conjSub g (Subgroup.closure ({k, j} : Set G)) =
      Subgroup.closure ({g * k * g⁻¹, g * j * g⁻¹} : Set G) := by
    rw [conjSub, MonoidHom.map_closure, Set.image_pair]
    rfl
  have h1 := conj_mem_conjSub (n := g) he'
  rwa [hcl, show g * (g⁻¹ * e * g) * g⁻¹ = e by group] at h1

namespace Tri

variable {K J M : Subgroup G} {t u : G}

theorem inv_M (h : Tri r Ω K J M t u) : IsUniqueInvolution M (t * u) := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.fam.hyp h.adj_M.1
  have e := h.h2 J h.adj_J M h.adj_M h.adj_MJ u z h.inv_J hz
  rw [e] at hz
  exact hz

theorem comm_tu (h : Tri r Ω K J M t u) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr h.fam.hyp h.inv_K h.adj_J h.inv_J

theorem ne_tu (h : Tri r Ω K J M t u) : t ≠ u := by
  intro htu
  exact h.adj_J.2.1 (h.fam.noTwins K h.mem J ⟨h.adj_J.1, t, h.inv_K, htu ▸ h.inv_J⟩)

theorem conj (h : Tri r Ω K J M t u) (g : G) :
    Tri r Ω (conjSub g K) (conjSub g J) (conjSub g M) (g * t * g⁻¹) (g * u * g⁻¹) := by
  have hΩ : ConjInvariant Ω := h.fam.hyp.conjInvariant
  have back : ∀ {A B : Subgroup G}, B ∈ omegaNbr Ω (conjSub g A) →
      conjSub g⁻¹ B ∈ omegaNbr Ω A := by
    intro A B hB
    have h1 := omegaNbr_conj hΩ hB g⁻¹
    rwa [conjSub_inv_conjSub] at h1
  refine
    { fam := h.fam
      trans := h.trans
      mem := hΩ g K h.mem
      inv_K := h.inv_K.conj g
      adj_J := omegaNbr_conj hΩ h.adj_J g
      inv_J := h.inv_J.conj g
      adj_M := omegaNbr_conj hΩ h.adj_M g
      adj_MJ := omegaNbr_conj hΩ h.adj_MJ g
      h2 := ?_
      h7 := ?_ }
  · intro J' hJ' K' hK' hK'J' u' z' hu' hz'
    have e := h.h2 _ (back hJ') _ (back hK') (omegaNbr_conj hΩ hK'J' g⁻¹) _ _ (hu'.conj g⁻¹)
      (hz'.conj g⁻¹)
    rw [inv_inv] at e
    calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * u' * g)) * g⁻¹ := by rw [e]
      _ = g * t * g⁻¹ * u' := by group
  · intro L hL
    obtain ⟨ν, hν, hLν⟩ := h.h7 _ (back hL)
    refine ⟨g * ν * g⁻¹, ?_, ?_⟩
    · rw [layerQ_conj hΩ g t]
      exact conj_mem_conjSub hν
    · have e : ∀ X : Subgroup G, conjSub g (conjSub ν X) = conjSub (g * ν * g⁻¹) (conjSub g X) := by
        intro X
        rw [← conjSub_mul g ν, ← conjSub_mul (g * ν * g⁻¹) g, inv_mul_cancel_right]
      rw [← e, ← e, ← conjSub_conjSub_inv g L]
      rcases hLν with hLν | hLν
      · exact Or.inl (by rw [hLν])
      · exact Or.inr (by rw [hLν])

theorem swap (h : Tri r Ω K J M t u) : Tri r Ω K M J t (t * u) where
  fam := h.fam
  trans := h.trans
  mem := h.mem
  inv_K := h.inv_K
  adj_J := h.adj_M
  inv_J := h.inv_M
  adj_M := h.adj_J
  adj_MJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.fam.hyp h.adj_J.1 h.adj_M.1 h.adj_MJ
  h2 := h.h2
  h7 := fun L hL => by
    obtain ⟨ν, hν, hLν⟩ := h.h7 L hL
    exact ⟨ν, hν, hLν.symm⟩

theorem exists_perm (h : Tri r Ω K J M t u) :
    ∃ g : G, conjSub g K = J ∧ g * t * g⁻¹ = u ∧
      ((conjSub g J = K ∧ conjSub g M = M) ∨ (conjSub g J = M ∧ conjSub g M = K)) := by
  have hΩ : ConjInvariant Ω := h.fam.hyp.conjInvariant
  have hKJ : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.fam.hyp h.mem h.adj_J.1 h.adj_J
  have hJM : J ∈ omegaNbr Ω M :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.fam.hyp h.adj_J.1 h.adj_M.1 h.adj_MJ
  obtain ⟨g₀, hg₀⟩ := h.trans K h.mem J h.adj_J.1
  have hK0 : conjSub g₀⁻¹ K ∈ omegaNbr Ω K := by
    have h1 := omegaNbr_conj hΩ hKJ g₀⁻¹
    rwa [← hg₀, conjSub_inv_conjSub] at h1
  obtain ⟨ν, hν, hc⟩ := h.h7 _ hK0
  have hνC : ν ∈ Subgroup.centralizer ({t} : Set G) :=
    layerY_le_centralizer (oddCoreOf_le_self _ hν)
  have hνK : conjSub ν K = K :=
    mem_normalizer_iff_conjSub_eq.mp (h.fam.tight K h.mem t h.inv_K hνC)
  have hgK : conjSub (g₀ * ν) K = J := by rw [conjSub_mul, hνK, hg₀]
  have hgt : g₀ * ν * t * (g₀ * ν)⁻¹ = u := by
    have h1 := h.inv_K.conj (g₀ * ν)
    rw [hgK] at h1
    exact (h.inv_J.eq h1).symm
  have twin : ∀ {L : Subgroup G}, L ∈ Ω → IsUniqueInvolution L (t * u) → L = M :=
    fun hL hLz => h.fam.noTwins M h.adj_M.1 _ ⟨hL, t * u, h.inv_M, hLz⟩
  refine ⟨g₀ * ν, hgK, hgt, ?_⟩
  rcases hc with hc | hc
  · have hgJ : conjSub (g₀ * ν) J = K := by rw [conjSub_mul, ← hc, conjSub_conjSub_inv]
    refine Or.inl ⟨hgJ, twin (hΩ _ M h.adj_M.1) ?_⟩
    have h1 : conjSub (g₀ * ν) M ∈ omegaNbr Ω K := by
      have h1 := omegaNbr_conj hΩ h.adj_MJ (g₀ * ν)
      rwa [hgJ] at h1
    have h2 : conjSub (g₀ * ν) M ∈ omegaNbr Ω J := by
      have h2 := omegaNbr_conj hΩ h.adj_M (g₀ * ν)
      rwa [hgK] at h2
    have hz := h.inv_M.conj (g₀ * ν)
    rwa [h.h2 J h.adj_J _ h1 h2 u _ h.inv_J hz] at hz
  · have hgM : conjSub (g₀ * ν) M = K := by rw [conjSub_mul, ← hc, conjSub_conjSub_inv]
    refine Or.inr ⟨twin (hΩ _ J h.adj_J.1) ?_, hgM⟩
    have h1 : conjSub (g₀ * ν) J ∈ omegaNbr Ω K := by
      have h1 := omegaNbr_conj hΩ hJM (g₀ * ν)
      rwa [hgM] at h1
    have h2 : conjSub (g₀ * ν) J ∈ omegaNbr Ω J := by
      have h2 := omegaNbr_conj hΩ h.adj_J (g₀ * ν)
      rwa [hgK] at h2
    have hz := h.inv_J.conj (g₀ * ν)
    rwa [h.h2 J h.adj_J _ h1 h2 u _ h.inv_J hz] at hz

theorem rot (h : Tri r Ω K J M t u) : Tri r Ω J M K u (t * u) := by
  obtain ⟨g, hKg, htg, ⟨hJg, hMg⟩ | ⟨hJg, hMg⟩⟩ := h.exists_perm
  · have hc := h.conj g
    rw [hKg, htg, hJg, hMg] at hc
    have hgu : g * u * g⁻¹ = t := by
      have := h.inv_J.conj g
      rw [hJg] at this
      exact (h.inv_K.eq this).symm
    rw [hgu] at hc
    have hs := hc.swap
    rwa [← h.comm_tu] at hs
  · have hc := h.conj g
    rw [hKg, htg, hJg, hMg] at hc
    have hgu : g * u * g⁻¹ = t * u := by
      have := h.inv_J.conj g
      rw [hJg] at this
      exact (h.inv_M.eq this).symm
    rwa [hgu] at hc

theorem edge_conj (h : Tri r Ω K J M t u) :
    ∀ x ∈ ({t, u, t * u} : Set G), ∃ c : G, x = c * t * c⁻¹ := by
  have key : ∀ {L : Subgroup G} {z : G}, L ∈ Ω → IsUniqueInvolution L z →
      ∃ c : G, z = c * t * c⁻¹ := by
    intro L z hL hz
    obtain ⟨c, hc⟩ := h.trans K h.mem L hL
    exact ⟨c, hz.eq (hc ▸ h.inv_K.conj c)⟩
  intro x hx
  rcases hx with hx | hx | hx
  · exact ⟨1, by rw [hx]; simp⟩
  · rw [hx]
    exact key h.adj_J.1 h.inv_J
  · rw [hx]
    exact key h.adj_M.1 h.inv_M

theorem rigid_of_adj (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u) {A B : Subgroup G}
    (hA : A ∈ Ω) (hB : B ∈ omegaNbr Ω A) {a b : G} (ha : IsUniqueInvolution A a)
    (hb : IsUniqueInvolution B b) : RigidEdge A B a b := by
  have hΩ : ConjInvariant Ω := h.fam.hyp.conjInvariant
  have hrM : RigidEdge K M t (t * u) := by
    obtain ⟨g, hJg, hug, ⟨hMg, hKg⟩ | ⟨hMg, hKg⟩⟩ := h.rot.exists_perm
    · have hc := hr.conj g
      rw [hKg, hJg, hug, h.inv_K.conj_eq hKg] at hc
      exact hc
    · have hgt : g * t * g⁻¹ = u := by
        have h1 := h.inv_K.conj g
        rw [hKg] at h1
        exact (h.inv_J.eq h1).symm
      have hgtu : g * (t * u) * g⁻¹ = t := by
        have h1 := h.inv_M.conj g
        rw [hMg] at h1
        exact (h.inv_K.eq h1).symm
      have hc := (hr.conj g).conj g
      rw [hKg, hJg, hgt, hug, hMg, hgtu] at hc
      exact hc.symm
  obtain ⟨g₀, hg₀⟩ := h.trans K h.mem A hA
  have hB0 : conjSub g₀⁻¹ B ∈ omegaNbr Ω K := by
    have h1 := omegaNbr_conj hΩ hB g₀⁻¹
    rwa [← hg₀, conjSub_inv_conjSub] at h1
  obtain ⟨ν, hν, hc⟩ := h.h7 _ hB0
  have hνC : ν ∈ Subgroup.centralizer ({t} : Set G) :=
    layerY_le_centralizer (oddCoreOf_le_self _ hν)
  have hνK : conjSub ν K = K :=
    mem_normalizer_iff_conjSub_eq.mp (h.fam.tight K h.mem t h.inv_K hνC)
  have hgK : conjSub (g₀ * ν) K = A := by rw [conjSub_mul, hνK, hg₀]
  have hga : g₀ * ν * t * (g₀ * ν)⁻¹ = a := by
    have h1 := h.inv_K.conj (g₀ * ν)
    rw [hgK] at h1
    exact (ha.eq h1).symm
  rcases hc with hc | hc
  · have hgJ : conjSub (g₀ * ν) J = B := by rw [conjSub_mul, ← hc, conjSub_conjSub_inv]
    have hgb : g₀ * ν * u * (g₀ * ν)⁻¹ = b := by
      have h1 := h.inv_J.conj (g₀ * ν)
      rw [hgJ] at h1
      exact (hb.eq h1).symm
    have hc' := hr.conj (g₀ * ν)
    rwa [hgK, hgJ, hga, hgb] at hc'
  · have hgM : conjSub (g₀ * ν) M = B := by rw [conjSub_mul, ← hc, conjSub_conjSub_inv]
    have hgb : g₀ * ν * (t * u) * (g₀ * ν)⁻¹ = b := by
      have h1 := h.inv_M.conj (g₀ * ν)
      rw [hgM] at h1
      exact (hb.eq h1).symm
    have hc' := hrM.conj (g₀ * ν)
    rwa [hgK, hgM, hga, hgb] at hc'

end Tri

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
