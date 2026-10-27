module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26B01
public import CFSG.ClassicalInvolution.Q3.Q3T8AFFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77.Thompson

section Defs


structure BadStd8 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  std : Std8 Ω K J S R T W z t
  conn : DConnected Ω
  bad : alphaOf (Subgroup.closure ({t, z} : Set G)) ≠ ⊥



@[expose] def C26_2B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), BadStd8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → ¬ MuIsoS4 Ω W


@[expose] def CFB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), BadStd8 Ω K J S R T W z t →
      omegaNbrGen Ω K ≠ ⊤ → ¬ MuIsoE4 Ω W

end Defs

section Route


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem c27_setupB (hs : AscStand Ω K) (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G}
    (hz : IsUniqueInvolution K z) {J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) {t : G}
    (ht : IsUniqueInvolution J t) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8 Ω K J S R T W z t := by
  have hΩ : HypOmegaMod Ω := hs.hyp
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved G Ω hΩ S).1
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { stand := hs
      noTwins := hnt
      hz := hz
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hs.mem hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

theorem sigmaNorm_eq_top_of_dConnected (hΩ : ConjInvariant Ω) (hK : K ∈ Ω)
    (hconn : DConnected Ω) : sigmaNorm Ω K = ⊤ := by
  refine top_unique fun g _ => ?_
  rw [T8.mem_sigmaNorm_iff hΩ hK]
  exact hconn K hK (conjSub g K) (hΩ g K hK)

theorem alphaOf_odd_of_triangle [IsSimpleGroup G] {K₀ : Subgroup G}
    (hs : Q3.Disc3.AscStand3 Ω K₀) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K J A : Subgroup G} {z t u : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hu : IsUniqueInvolution A u) (hKJ : J ∈ omegaNbr Ω K)
    (hKA : A ∈ omegaNbr Ω K) (hJA : A ∈ omegaNbr Ω J)
    (hind : u ∉ Subgroup.closure ({z, t} : Set G)) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) := by
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hs.hyp
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩu
  have hfr := fuzzyFrame3_of_adj hΩ hΩu hnt hK hz ht hu hKJ hKA hJA hind
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp
      (isClassicalMember3_of_uniqueInvolution hΩu hK hz).not_le_center
    rw [Subgroup.mem_center_iff] at hac
    push Not at hac
    obtain ⟨b, hb⟩ := hac
    exact ⟨b, a, hb⟩
  have hHyp : Hyp51 (Subgroup.closure ({z, t, u} : Set G)) :=
    Q3NH.hyp51_of_fuzzyFrame (Q3T7.inClass3_of_stand3 hs) (Q3T7.cit3Below_of_stand3 hs) hnab hfr
  have hc01 : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hKJ ht
  have hzt' : t ≠ z := fun h => by
    have : IsUniqueInvolution J z := h ▸ ht
    exact hKJ.2.1 (hnt K hK J ⟨hKJ.1, z, hz, this⟩)
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, u} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht.sq hz.sq ht.ne_one hz.ne_one hzt' hc01.symm
  exact (lemma54_odd_and_eq hHyp hDB hD).1

theorem alphaOf_eq_bot_of_fuzzyFrame [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hconn : DConnected Ω) (hframe : ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀) :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have : Fact AlphaFrame3 := ⟨alphaFrame3_proved⟩
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hN := T8YY.sigmaNorm_le_normalizer_alpha hs hframe
  rw [sigmaNorm_eq_top_of_dConnected hΩ.conjInvariant hs.stand.mem hconn, top_le_iff] at hN
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hN
  obtain ⟨A, B, tA, tB, hA, hB, hBA, htA, htB, hind⟩ :=
    exists_triangle hs.stand.toStand3 hs.hz hframe
  have hodd := alphaOf_odd_of_triangle hs.stand.toStand3 hnt hs.stand.mem hs.hz htA htB hA hB hBA
    hind
  have hconst : alphaOf (Subgroup.closure ({t, z} : Set G)) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) :=
    T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz htA hs.ht hA hs.hJ
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hz := hs.hz
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    have hodd' : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) := hconst ▸ hodd
    rw [h, Subgroup.card_top] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hdvd)

theorem BadStd8.not_fuzzyFrame [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t) :
    ¬ ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀ := fun hframe =>
  h.bad (alphaOf_eq_bot_of_fuzzyFrame h.std h.conn hframe)

theorem BadStd8.eq_mul_of_nbr_nbr [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {K' : Subgroup G} {u : G} (hKK' : K' ∈ omegaNbr Ω K) (hJK' : K' ∈ omegaNbr Ω J)
    (hu : IsUniqueInvolution K' u) : u = z * t := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  by_contra hne
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hind : u ∉ Subgroup.closure ({z, t} : Set G) := fun hmem => by
    rcases Thompson.eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hcomm hmem with h1 | h1 | h1 | h1
    · exact hu.ne_one h1
    · have : IsUniqueInvolution K' z := h1 ▸ hu
      exact hKK'.2.1 (hnt K hs.stand.mem K' ⟨hKK'.1, z, hs.hz, this⟩)
    · have : IsUniqueInvolution K' t := h1 ▸ hu
      exact hJK'.2.1 (hnt J hs.hJ.1 K' ⟨hJK'.1, t, hs.ht, this⟩)
    · exact hne h1
  have hfr := fuzzyFrame3_of_adj hΩ hs.stand.modU hnt hs.stand.mem hs.hz hs.ht hu hs.hJ hKK' hJK'
    hind
  exact h.not_fuzzyFrame ⟨_, hfr⟩

end Route

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
