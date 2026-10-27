module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def omegaNbrGen {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Subgroup G :=
  ⨆ M ∈ omegaNbr Ω K, M

@[expose] def sigmaNorm {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Subgroup G where
  carrier := {g | ∀ M : Subgroup G, M ∈ dComp Ω K ↔ conjSub g M ∈ dComp Ω K}
  one_mem' := fun M => by rw [conjSub_one]
  mul_mem' := by
    intro g h hg hh M
    show M ∈ dComp Ω K ↔ conjSub (g * h) M ∈ dComp Ω K
    rw [conjSub_mul]
    exact (hh M).trans (hg _)
  inv_mem' := by
    intro g hg M
    have h := hg (conjSub g⁻¹ M)
    rw [conjSub_conjSub_inv] at h
    exact h.symm

@[expose] def DstarConnected {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (dstarAdj Ω) K J

@[expose] def LFiveType {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  if piSign p f then HasLieType p f Ω .PSU 5 else HasLieType p f Ω .PSL 5

structure Std8 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : AscStand p f Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def C26_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)

@[expose] def C26_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoS4 Ω W

@[expose] def C26_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoWylD4 Ω W

@[expose] def C26_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      MuIsoE4 Ω W → ¬ LFiveType p f Ω →
        (⨆ M ∈ KPerp Ω K, M) ⊔ (⨆ M ∈ KPerp Ω J, M) = ⊤

@[expose] def C26_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      MuIsoE4 Ω W → ¬ LFiveType p f Ω → DConnected Ω

@[expose] def C26_L5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      LFiveType p f Ω → DConnected Ω

@[expose] def CF26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W

variable {p f}

theorem cf26_of_steps (h7 : C26_7 p f) (hL5 : C26_L5 p f) : CF26 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  by_cases h5 : LFiveType p f Ω
  · exact hdisc (hL5 G Ω K J S R T W z t hs h5)
  · exact hdisc (h7 G Ω K J S R T W z t hs hE4 h5)

variable (p f)

@[expose] def C27_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ (MuIsoE4 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W)

@[expose] def C27_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → dComp Ω K = dstarComp Ω K

@[expose] def C27_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω →
        sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
          Subgroup.centralizer ({z * s} : Set G)) = ⊤

@[expose] def C27_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω →
        rLayer Ω (z * t) ≤ oddCoreOf (rLayer Ω (z * t)) ⊔ (rLayer Ω (z * t) ⊓ sigmaNorm Ω K) ∧
          ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x

@[expose] def C27_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → alphaOf (Subgroup.closure {t, z}) = ⊥

@[expose] def C27_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

@[expose] def C27_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → ∀ z : G,
      IsUniqueInvolution K z → ∀ J ∈ omegaNbr Ω K, ∀ t : G, IsUniqueInvolution J t →
        ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8 p f Ω K J S R T W z t

@[expose] def C27_nbr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → ¬ DEdgeless Ω → ∃ J ∈ omegaNbr Ω K, True

variable {p f}

theorem c27_1_of_steps (hF : CF26 p f) (h2 : C26_2 p f) (h13 : C26_13 p f) : C27_1 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc h
  rcases h with h | h | h
  · exact hF G Ω K J S R T W z t hs hdisc h
  · exact h2 G Ω K J S R T W z t hs hdisc h
  · exact h13 G Ω K J S R T W z t hs hdisc h

theorem reflTransGen_dAdj_symm {G : Type} [Group G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    (hK : K ∈ Ω)
    (h : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K J) :
    Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) J K := by
  have hmem : ∀ N, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K N →
      N ∈ Ω := by
    intro N hN
    induction hN with
    | refl => exact hK
    | tail _ hbc _ => exact hbc.1
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    exact Relation.ReflTransGen.head ⟨hmem b hab, dAdj_symm hbc.2⟩ ih

theorem dConnected_of_sigmaNorm_eq_top {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (htop : sigmaNorm Ω K = ⊤) : DConnected Ω := by
  have hall : ∀ J ∈ Ω, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K J := by
    intro J hJ
    obtain ⟨g, rfl⟩ := htrans J hJ
    exact (show g ∈ sigmaNorm Ω K by rw [htop]; exact Subgroup.mem_top g) K |>.mp
      Relation.ReflTransGen.refl
  intro K₁ h₁ J₁ hJ₁
  exact (reflTransGen_dAdj_symm hK (hall K₁ h₁)).trans (hall J₁ hJ₁)

theorem thm8A_of_steps (hnbr : C27_nbr p f) (hsetup : C27_setup p f) (h274 : C27_4 p f)
    (h278 : C27_8 p f) : Thm8A p f := by
  intro G _ _ _ Ω K hs hedge hnt hdisc
  obtain ⟨J, hJ, -⟩ := hnbr G Ω K hs hedge
  obtain ⟨z, hzcl⟩ := hs.hyp.classical K hs.mem
  have hz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hs.odd hs.five hzcl
  obtain ⟨t, htcl⟩ := hs.hyp.classical J hJ.1
  have ht := ConnectedA2.isUniqueInvolution_of_isClassicalMember hs.odd hs.five htcl
  obtain ⟨S, R, T, W, hstd⟩ := hsetup G Ω K hs hnt hdisc z hz J hJ t ht
  have h4 := h274 G Ω K J S R T W z t hstd hdisc
  have hle : sigmaNorm Ω K ⊔ (⨆ M ∈ omegaNbr Ω K, ⨆ (s : G) (_ : IsUniqueInvolution M s),
      Subgroup.centralizer ({z * s} : Set G)) ≤ sigmaNorm Ω K := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ := hsetup G Ω K hs hnt hdisc z hz M hM s hs'
    exact h278 G Ω K M S' R' T' W' z s hstd' hdisc
  rw [h4] at hle
  have htop : sigmaNorm Ω K = ⊤ := top_le_iff.mp hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans htop)

end CFSG.ClassicalInvolution.Asc77
