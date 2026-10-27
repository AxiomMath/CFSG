module

public import CFSG.ClassicalInvolution.Asc77.AscT8U3
public import CFSG.ClassicalInvolution.Asc77.AscT8T12
public import CFSG.ClassicalInvolution.Asc77.AscT8YB3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

namespace FrameData

theorem exists_triFrame (hs : Std8 p f Ω K J S R T W z t) (F : FrameData Ω W K J z t) :
    ∃ R₃ : Fin 3 → Subgroup G, T8T.TriFrame Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃ ∧
      F.zz 2 ∉ Subgroup.closure ({z, t} : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz2 : IsUniqueInvolution (F.ρ 2).K (F.zz 2) := F.hz 2
  have h02 : (F.ρ 2).K ∈ omegaNbr Ω K := by
    have := F.hadj 0 2 (by decide)
    rwa [F.h0] at this
  have h12 : (F.ρ 2).K ∈ omegaNbr Ω J := by
    have := F.hadj 1 2 (by decide)
    rwa [F.h1] at this
  obtain ⟨R₃, hF⟩ := T8T.exists_triFrame_of_nbrs hp hq hΩ hK hs.hz hs.ht hz2 hs.hJ h02 h12
  refine ⟨R₃, hF, ?_⟩
  intro hmem
  have hcomm : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  rcases Thompson.eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hcomm hmem with h | h | h | h
  · exact (F.hz 2).ne_one h
  · exact F.hinj 2 0 (by decide) (h.trans F.hz0.symm)
  · exact F.hinj 2 1 (by decide) (h.trans F.hz1.symm)
  · have h2 : F.zz 2 = F.zz 0 * F.zz 1 := by rw [h, F.hz0, F.hz1]
    have h3 : F.zz 3 = 1 := by
      have hp3 := F.hprod
      rw [← h2] at hp3
      have : F.zz 2 * F.zz 2 = 1 := (F.hz 2).sq
      calc F.zz 3 = (F.zz 2 * F.zz 2) * F.zz 3 := by rw [this, one_mul]
        _ = 1 := by rw [mul_assoc]; rw [← mul_assoc (F.zz 2)]; simpa [mul_assoc] using hp3
    exact (F.hz 3).ne_one h3

end FrameData

theorem exists_fuzzyFrame (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : ∃ A₀, FuzzyFrameOn p f Ω A₀ := by
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact ⟨_, T8U.fuzzyFrameOn_of_triFrame hs.stand.odd hs.stand.five hΩ hnt hF
    (by simpa using hind)⟩

theorem alphaOf_eq_of_mem_dComp [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀) {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y → IsUniqueInvolution L' y' →
      alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  induction hL with
  | refl =>
    refine ⟨hs.stand.mem, fun L' hL' y y' hy hy' => ?_⟩
    have hyz : y = z := hy.eq hs.hz
    subst hyz
    exact T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs.ht hy' hs.hJ hL'
  | @tail b c hbk hbc ih =>
    obtain ⟨hbΩ, hPb⟩ := ih
    obtain ⟨hcΩ, hadj⟩ := hbc
    have hcb : c ∈ omegaNbr Ω b ∧ b ∈ omegaNbr Ω c := by
      rcases hadj with h | h
      · exact ⟨h, T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hbΩ hcΩ h⟩
      · exact ⟨T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hcΩ hbΩ h, h⟩
    refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' => ?_⟩
    obtain ⟨yb, hyb⟩ := hΩ.exists_uniqueInvolution hp hq hbΩ
    have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
        alphaOf (Subgroup.closure ({yb, y₂} : Set G)) :=
      T8U.alphaOf_eq_of_omegaNbr_frame (hs.stand.of_mem hcΩ) (hnt c hcΩ) hframe hy₂ hyb hy''
        hcb.2 hL''
    have h2 : alphaOf (Subgroup.closure ({y₂, yb} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := hPb c hcb.1 yb y₂ hyb hy₂
    rw [h1, Set.pair_comm]
    exact h2

theorem sigmaNorm_le_normalizer_alpha [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀) :
    sigmaNorm Ω K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  intro n hn
  have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hs.stand.mem).1 hn
  obtain ⟨-, hP⟩ := alphaOf_eq_of_mem_dComp hs hframe hKn
  have h := hP (conjSub n J) (omegaNbr_conj hΩ.conjInvariant hs.hJ n) (n * z * n⁻¹)
    (n * t * n⁻¹) (hs.hz.conj n) (hs.ht.conj n)
  rw [← conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

theorem centralizer_le_normalizer_alpha_of_nbr [IsSimpleGroup G]
    (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hdisc : ¬ DConnected Ω) (hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s)
    (hconn : DConnected (T8.layerFamQ Ω (z * s))) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  have hμ' := muIsoWylD4_transfer hp hq hΩ hs.hW.1 hstd.hW.1 hμ
  have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
  obtain ⟨F⟩ := exists_frameData hstd hμ' hnc'
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hstd
  have hHyp : Hyp51 (Subgroup.closure ({z, s, F.zz 2} : Set G)) :=
    T8T.hyp51Tri_proved p f G Ω ![K, M, (F.ρ 2).K] ![z, s, F.zz 2] R₃ hstd.stand hnt hF
      (by simpa using hind)
  have hc01 : z * s = s * z := hF.comm hp hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hp hΩ 0 2
  have hc12 : s * F.zz 2 = F.zz 2 * s := hF.comm hp hΩ 1 2
  have hz2 : z * z = 1 := hF.sq 0
  have hs2 : s * s = 1 := hF.sq 1
  have hz''2 : F.zz 2 * F.zz 2 = 1 := hF.sq 2
  have hz1 : z ≠ 1 := hF.ne_one 0
  have hs1 : s ≠ 1 := hF.ne_one 1
  have hz''1 : F.zz 2 ≠ 1 := hF.ne_one 2
  have hzs : z ≠ s := hF.x_ne hnt (i := 0) (j := 1) (by decide)
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, s, F.zz 2} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 hs2 hz''2 hc01 hc02 hc12
  have hB8 : Nat.card ↥(Subgroup.closure ({z, s, F.zz 2} : Set G)) = 8 :=
    T8T.natCard_closure_three hz2 hs2 hz''2 hc01 hc02 hc12 hz1 hs1 hzs hz''1 (by simpa using hind)
  have hDB : Subgroup.closure ({s, z} : Set G) ≤ Subgroup.closure ({z, s, F.zz 2} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hs2 hz2 hs1 hz1 hzs.symm hc01.symm
  have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, s, F.zz 2} : Set G) →
      IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({s, z} : Set G)) :=
    (lemma54_odd_and_eq hHyp hDB hD).2
  have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
      alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    (T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM hs.hJ).symm
  intro c hc
  have hx : z * s * (z * s) = 1 := T8.mul_self_zt hp hΩ hs.hz hM hs'
  have hKx : T8.XMem Ω (z * s) K := T8.xMem_zt hstd
  have hcz : c ∈ T8.cenZ (z * s) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω (z * s) (conjSub c K) := hKx.conj hΩ hcz
  obtain ⟨ν, hν, hνK⟩ := T8.exists_oddCore_conj_mem_dComp hp hq hΩ hx hKx hconn hKc
  have hνc : ν * c ∈ sigmaNorm Ω K := by
    rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK, conjSub_mul]
    exact hνK
  have hzsB : z * s ∈ Subgroup.closure ({z, s, F.zz 2} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hν' : ν ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({s, z} : Set G)) : Set G) :=
    T8T.oddCoreOf_centralizer_le_normalizer hB hB8 hzsB h3
      (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) hν)
  rw [hα] at hν'
  have hc' : c = ν⁻¹ * (ν * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)

end T8YY

end CFSG.ClassicalInvolution.Asc77
