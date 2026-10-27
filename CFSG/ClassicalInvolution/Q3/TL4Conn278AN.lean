module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

section Gen

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem alphaConst_conj (hcl : ConjInvariant Ω) {K : Subgroup G} {z : G}
    (hA : ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K, ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ →
      IsUniqueInvolution J₂ t₂ → alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
        alphaOf (Subgroup.closure ({t₂, z} : Set G)))
    (g : G) : ∀ J₁ ∈ omegaNbr Ω (conjSub g K), ∀ J₂ ∈ omegaNbr Ω (conjSub g K), ∀ t₁ t₂ : G,
      IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
        alphaOf (Subgroup.closure ({t₁, g * z * g⁻¹} : Set G)) =
          alphaOf (Subgroup.closure ({t₂, g * z * g⁻¹} : Set G)) := by
  intro J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2
  have hJ₁' := omegaNbr_conj hcl hJ₁ g⁻¹
  have hJ₂' := omegaNbr_conj hcl hJ₂ g⁻¹
  rw [conjSub_inv_conjSub] at hJ₁' hJ₂'
  have key := hA _ hJ₁' _ hJ₂' _ _ (h1.conj g⁻¹) (h2.conj g⁻¹)
  have e : ∀ u : G, Subgroup.closure ({u, g * z * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({g⁻¹ * u * g⁻¹⁻¹, z} : Set G)) := by
    intro u
    rw [T7A.conjSub_closure_pair, show g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u by group]
  rw [e t₁, e t₂, alphaOf_conjSub, alphaOf_conjSub, key]

variable [Finite G]

theorem alphaOf_eq_of_mem_dComp_gen (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {z t : G}
    (hK : K ∈ Ω) (htrans : ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t)
    (hA : ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K, ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ →
      IsUniqueInvolution J₂ t₂ → alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
        alphaOf (Subgroup.closure ({t₂, z} : Set G)))
    {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y →
      IsUniqueInvolution L' y' → alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  induction hL with
  | refl =>
    refine ⟨hK, fun L' hL' y y' hy hy' => ?_⟩
    rw [hy.eq hz]
    exact hA L' hL' J hJ y' t hy' ht
  | @tail b c _ hbc ih =>
    obtain ⟨hbΩ, hPb⟩ := ih
    obtain ⟨hcΩ, hadj⟩ := hbc
    have hbc' : b ∈ omegaNbr Ω c := by
      rcases hadj with h | h
      · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hbΩ hcΩ h
      · exact h
    have hcb : c ∈ omegaNbr Ω b := by
      rcases hadj with h | h
      · exact h
      · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
    refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' => ?_⟩
    obtain ⟨g, hg⟩ := htrans c hcΩ
    obtain ⟨yb, hyb⟩ := Sec6Gen.exists_uniqueInvolution hΩ hbΩ
    have hzg : IsUniqueInvolution c (g * z * g⁻¹) := hg ▸ hz.conj g
    have hy₂e : y₂ = g * z * g⁻¹ := hy₂.eq hzg
    have hA' := alphaConst_conj hΩ.conjInvariant hA g
    rw [hg] at hA'
    have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
        alphaOf (Subgroup.closure ({yb, y₂} : Set G)) := by
      rw [hy₂e]
      exact hA' L'' hL'' b hbc' y'' yb hy'' hyb
    rw [h1, Set.pair_comm]
    exact hPb c hcb yb y₂ hyb hy₂

end Gen

section Cit3


@[expose] def TightAlphaConstR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y),
    TightLargeHypR r n Y Rd Sd z → ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
      (∃ W ∈ WSet (CoreAssembly.conjClass (tightCore Rd)),
        (∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
          ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) ∧
        ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) →
      ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y))

@[expose] def TightAlphaFrameR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y),
    TightLargeHypR r n Y Rd Sd z → ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
      (∃ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
        TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P ∧
          x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y)) →
      ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y))

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.exists_mul_mem_sigmaNorm_of_centralizer
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hconn : T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    {c : Y} (hc : c ∈ Subgroup.centralizer ({z * t} : Set Y)) :
    ∃ ν ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)),
      ν * c ∈ sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hcl := hs.hyp.conjInvariant
  have hK := hs.xMem_K
  obtain ⟨ν, hν, hνK⟩ := exists_conj_mem_dstarComp_of_conn h hK hconn (XMem.conj' hcl hK hc)
  refine ⟨ν, ⟨ν, hν, rfl⟩, ?_⟩
  rw [mem_sigmaNorm_iff hcl hs.mem, conjSub_mul, hcomp]
  exact hνK

theorem TightStd8R.centralizer_le_sigmaNorm_of_zt (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hconn : T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    {K' : Subgroup Y} (hK' : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hz' : IsUniqueInvolution K' (z * t)) :
    Subgroup.centralizer ({z * t} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have hO := hs.oddCoreOf_layerY_le_of_zt hK' hz'
  intro c hc
  obtain ⟨ν, hν, hνc⟩ := hs.exists_mul_mem_sigmaNorm_of_centralizer hcomp hconn hc
  have := (sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)).mul_mem
    ((sigmaNorm _ _).inv_mem (hO hν)) hνc
  simpa using this

theorem TightStd8R.sigmaNorm_le_normalizer_alpha (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hA : ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y))) :
    sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  intro m hm
  have hKm := (mem_sigmaNorm_iff hΩ.conjInvariant hs.mem).1 hm
  obtain ⟨-, hP⟩ := alphaOf_eq_of_mem_dComp_gen hΩ hs.mem hs.trans hs.hz hs.hJ hs.ht hA hKm
  have h := hP (conjSub m J) (omegaNbr_conj hΩ.conjInvariant hs.hJ m) (m * z * m⁻¹)
    (m * t * m⁻¹) (hs.hz.conj m) (hs.ht.conj m)
  rw [← T7A.conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

theorem TightStd8R.centralizer_le_normalizer_alpha_of_nbr (h2 : TightC27_2R r n)
    (hTri : TightSecTriangleR r n) (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hab : ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
      ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x)
    (hE4 : ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hA : ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y)))
    (hN : sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y))
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {s : Y} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) L, L' = L := fun L hL =>
    noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hL
  obtain ⟨S', R', T', W', hstd, hab', hE4'⟩ :=
    TightLargeHypR.exists_std8_mu hs.large hM hs' ⟨W, hs.hW.1, hab, hE4⟩
  have hcomp := h2 Y Rd Sd z M S' R' T' W' s hstd hdisc
  have hconn := hstd.dstarConnected_secFam hTri hE4' hab'
  by_cases hE8 : ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) M → ∀ z' : Y,
        IsUniqueInvolution K' z' → z' ≠ z * s
  · obtain ⟨K'', R'', z'', hF, hind⟩ := exists_triFrame_of_std8Core hstd.toStd8Core hE4' hab' hE8
    have hHyp : Hyp51 (Subgroup.closure ({z, s, z''} : Set Y)) :=
      hH Y Rd Sd z hs.large ![tightCore Rd, M, K''] ![z, s, z''] ![R', T', R''] hF hind
    have hc01 : z * s = s * z := triFrame_comm_gen hF hΩ 0 1
    have hzs : z ≠ s := hF.x_ne hnt (i := 0) (j := 1) (by decide)
    have hDB : Subgroup.closure ({s, z} : Set Y) ≤ Subgroup.closure ({z, s, z''} : Set Y) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set Y)) 2 :=
      T7A.isElemAbelian2_closure_pair (hF.sq 1) (hF.sq 0) (hF.ne_one 1) (hF.ne_one 0) hzs.symm
        hc01.symm
    have h3 := (lemma54_odd_and_eq hHyp hDB hD).2
    have hα : alphaOf (Subgroup.closure ({s, z} : Set Y)) =
        alphaOf (Subgroup.closure ({t, z} : Set Y)) := hA M hM J hs.hJ s t hs' hs.ht
    have hzsB : z * s ∈ Subgroup.closure ({z, s, z''} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    intro c hc
    obtain ⟨ν, hν, hνc⟩ := hstd.exists_mul_mem_sigmaNorm_of_centralizer hcomp hconn hc
    have hν' : ν ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({s, z} : Set Y)) : Set Y) :=
      T8T.oddCoreOf_centralizer_le_normalizer hHyp.1 hHyp.2.1 hzsB h3
        (oddCoreOf_layerY_le hΩ.conjInvariant hν)
    rw [hα] at hν'
    have := (Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y)).mul_mem
      ((Subgroup.normalizer _).inv_mem hν') (hN hνc)
    simpa using this
  · push Not at hE8
    obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
    rw [hzt] at hz'
    exact (hstd.centralizer_le_sigmaNorm_of_zt hcomp hconn hK' hz').trans hN

theorem tightAlphaNormR_of_const (hA : TightAlphaConstR r n) (h2 : TightC27_2R r n)
    (hTri : TightSecTriangleR r n) (hH : TightHyp51TriR r n) : TightAlphaNormR r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc hE4 hab _
  have hA' := hA Y Rd Sd z hs.large hdisc ⟨W, hs.hW.1, hab, hE4⟩
  have hN := hs.sigmaNorm_le_normalizer_alpha hA'
  exact sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
    hs.centralizer_le_normalizer_alpha_of_nbr h2 hTri hH hdisc hab hE4 hA' hN hM hs')

theorem tightAlphaConstR_of_frame (hF : TightAlphaFrameR r n) (h2 : TightC27_2R r n)
    (h4 : TightC27_4R r n) (hTri : TightSecTriangleR r n) : TightAlphaConstR r n := by
  intro Y _ _ Rd Sd z hL hdisc hμ J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2'
  by_cases hframe : ∃ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
      TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P ∧
        x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y)
  · exact hF Y Rd Sd z hL hdisc hframe J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2'
  · exfalso
    have key : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
        IsUniqueInvolution M s → Subgroup.centralizer ({z * s} : Set Y) ≤
          sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
      intro M hM s hs'
      obtain ⟨S', R', T', W', hstd, hab', hE4'⟩ := TightLargeHypR.exists_std8_mu hL hM hs' hμ
      have hcomp := h2 Y Rd Sd z M S' R' T' W' s hstd hdisc
      have hconn := hstd.dstarConnected_secFam hTri hE4' hab'
      by_cases hE8 : ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
          K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) M → ∀ z' : Y,
            IsUniqueInvolution K' z' → z' ≠ z * s
      · obtain ⟨K'', R'', z'', hF', hind⟩ :=
          exists_triFrame_of_std8Core hstd.toStd8Core hE4' hab' hE8
        exact absurd ⟨![tightCore Rd, M, K''], ![z, s, z''], ![R', T', R''], hF', hind⟩ hframe
      · push Not at hE8
        obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
        rw [hzt] at hz'
        exact hstd.centralizer_le_sigmaNorm_of_zt hcomp hconn hK' hz'
    obtain ⟨S', R', T', W', hstd⟩ := TightLargeHypR.exists_std8 hL hJ₁ h1
    have htop := h4 Y Rd Sd z J₁ S' R' T' W' t₁ hstd hdisc
    have hle : H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
      sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => key M hM s hs')
    rw [htop] at hle
    exact hdisc (dConnected_of_sigmaNorm_eq_top hstd.mem hstd.trans (top_le_iff.mp hle))

theorem tightConnLeafR'_of_residuals₅ (h26_2 : TightC26_2R r n) (h26_13 : TightC26_13R r n)
    (h5 : TightSec5CliqueR r n) (hB : TightBenderEndR) (hE4 : TightF26E4R r n)
    (hTri : TightSecTriangleR r n) (hT4 : Thm4RBelow r n) (hH : TightHyp51TriR r n)
    (hF : TightAlphaFrameR r n) (hYs : TightC27_YsmallR r n) : TightConnLeafR' r n :=
  have h2 := tightC27_2R_of h26_2 h26_13
  have h4 := tightC27_4R_of h2 (tightC27_4aR_of_min h2 (tightC27_4MR_of h5)) hB
  tightConnLeafR'_of_residuals₃ h26_2 h26_13 h5 hB hE4 hTri hT4 hH
    (tightAlphaNormR_of_const (tightAlphaConstR_of_frame hF h2 h4 hTri) h2 hTri hH) hYs

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
