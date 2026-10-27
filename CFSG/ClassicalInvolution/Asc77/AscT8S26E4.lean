module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire
public import CFSG.ClassicalInvolution.Asc77.AscT8Four

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

theorem s26_perm3_not_comm : ¬ ∀ x y : Equiv.Perm (Fin 3), x * y = y * x := by decide

theorem s26_perm4_not_comm : ¬ ∀ x y : Equiv.Perm (Fin 4), x * y = y * x := by decide

theorem s26_coxeterD4_not_comm : ¬ ∀ x y : coxeterD4.Group, x * y = y * x := by
  intro hcomm
  let cs := coxeterD4.toCoxeterSystem
  let g : Fin 4 → Equiv.Perm (Fin 4) :=
    ![Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 0 1]
  have hg : coxeterD4.IsLiftable g := by
    unfold CoxeterMatrix.IsLiftable
    decide
  let φ : coxeterD4.Group →* Equiv.Perm (Fin 4) := cs.lift ⟨g, hg⟩
  have h0 : φ (cs.simple 0) = g 0 := cs.lift_apply_simple hg 0
  have h1 : φ (cs.simple 1) = g 1 := cs.lift_apply_simple hg 1
  have := congrArg φ (hcomm (cs.simple 0) (cs.simple 1))
  rw [map_mul, map_mul, h0, h1] at this
  revert this
  decide

theorem s26_not_comm_of_muIso {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
    (h : MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W) :
    ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
  intro hc
  have key : ∀ {X : Type} [Group X], (↥(muGroup Ω W) ≃* X) → ∀ x y : X, x * y = y * x := by
    intro X _ e x y
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hc _ _
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact s26_perm3_not_comm (key e)
  · obtain ⟨e⟩ := h
    exact s26_perm4_not_comm (key e)
  · obtain ⟨e⟩ := h
    exact s26_coxeterD4_not_comm (key e)

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem s26_comm_of_muIsoE4 (h : MuIsoE4 Ω W) : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
  obtain ⟨e⟩ := h
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem s26_dComp_eq_of_e4 {K J : Subgroup G} {S : Sylow 2 G} {R T : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hE4 : MuIsoE4 Ω W) : dComp Ω K = dstarComp Ω K := by
  by_contra hne
  have hP : PartIHyp p f Ω := ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hs.stand.mem hne hW
  exact s26_not_comm_of_muIso (l7_10_proved G Ω hP W hW hnc) (s26_comm_of_muIsoE4 hE4)

end Main

variable {p f : ℕ} [Fact p.Prime]

theorem s26_H274_eq_top (h4a : C27_4a p f) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hcomp : dComp Ω K = dstarComp Ω K) : T8.H274 Ω K z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact h4a G Ω K (conjSub g⁻¹ K) S' R' T' W' z (g⁻¹ * z * g) hstd hdisc
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
    exact hKs inferInstance
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact CFSG.StronglyEmbedded.UniqueCoset.false_of_uniqueCoset_of_not_isSolvable hH hz2 h1 h2'
    hTs hTnab hTc (CFSG.StronglyEmbedded.UniqueCoset.le_centralizer_of_isUniqueInvolution hz) hKs

variable (p f)

@[expose] def C27_4c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → dComp Ω K = dstarComp Ω K → T8.H274 Ω K z = ⊤

@[expose] def C27_8E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoE4 Ω W → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

@[expose] def C27_8nE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

variable {p f}

theorem c27_4c_of_c27_4 (h : C27_4 p f) : C27_4c p f :=
  fun G _ _ _ Ω K J S R T W z t hs hdisc _ => h G Ω K J S R T W z t hs hdisc

theorem c27_4c_of_c27_4a (h : C27_4a p f) : C27_4c p f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hs hdisc hcomp => s26_H274_eq_top h hs hdisc hcomp

theorem c26_7_of_c27_8E4 (h752 : L7_5_2 p f) (h4 : C27_4c p f) (h8 : C27_8E4 p f) :
    C26_7 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hE4 _
  by_contra hdisc
  have hcomp := s26_dComp_eq_of_e4 hs hE4
  have h4' : T8.H274 Ω K z = ⊤ := h4 G Ω K J S R T W z t hs hdisc hcomp
  have hz := hs.hz
  have hle : T8.H274 Ω K z ≤ sigmaNorm Ω K := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz M hM s
      hs'
    obtain ⟨φ⟩ := hE4
    obtain ⟨ψ⟩ := h752 hs.stand.odd hs.stand.five G Ω hs.stand.hyp W' hstd'.hW.1 W hs.hW.1
    exact h8 G Ω K M S' R' T' W' z s hstd' hdisc ⟨ψ.trans φ⟩
  rw [h4'] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.stand.mem hs.stand.trans (top_le_iff.mp hle))

theorem c26_7_of_c27_8E4_a (h752 : L7_5_2 p f) (h4a : C27_4a p f) (h8 : C27_8E4 p f) :
    C26_7 p f :=
  c26_7_of_c27_8E4 h752 (c27_4c_of_c27_4a h4a) h8

theorem c27_8_of_split (h1 : C27_8E4 p f) (h2 : C27_8nE4 p f) : C27_8 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_cases hE4 : MuIsoE4 Ω W
  · exact h1 G Ω K J S R T W z t hs hdisc hE4
  · exact h2 G Ω K J S R T W z t hs hdisc hE4

theorem c26_7_of_c27_8 (h752 : L7_5_2 p f) (h4 : C27_4 p f) (h8 : C27_8 p f) : C26_7 p f :=
  c26_7_of_c27_8E4 h752 (c27_4c_of_c27_4 h4) fun G _ _ _ Ω K J S R T W z t hs hdisc _ =>
    h8 G Ω K J S R T W z t hs hdisc

end CFSG.ClassicalInvolution.Asc77
