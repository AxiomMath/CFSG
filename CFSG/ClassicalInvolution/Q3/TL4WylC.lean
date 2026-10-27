module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278AN
public import CFSG.ClassicalInvolution.Q3.TL4OddFrNbr
public import CFSG.ClassicalInvolution.Q3.TL4WylB
public import CFSG.ClassicalInvolution.Q3.TL4WylB2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

namespace Wyl

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

theorem layerY_le_sigmaNorm_of_dConn (h : TypeRFam r Ω) {K : Subgroup G} (hK : T8.XMem Ω x K)
    (hconn : DConnected (secFam Ω x)) (hO : oddCoreOf (layerY Ω x) ≤ sigmaNorm Ω K) :
    layerY Ω x ≤ sigmaNorm Ω K := by
  have hcl := h.hyp.conjInvariant
  refine iSup₂_le fun C hC => ?_
  obtain ⟨L, hL, rfl⟩ := hC
  obtain ⟨ν, hν, hνL⟩ := exists_conj_mem_dComp_of_conn h hK hconn hL
  have hνN : (ν : G) ∈ sigmaNorm Ω K := hO ⟨ν, hν, rfl⟩
  have hle : conjSub (ν : G) L ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (T8.normalizer_le_sigmaNorm_of_mem hcl hK.1 hνL)
  intro c hc
  have h1 : (ν : G) * c * (ν : G)⁻¹ ∈ sigmaNorm Ω K :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using coreAt_le x L hc))
  have h2 := (sigmaNorm Ω K).mul_mem ((sigmaNorm Ω K).mul_mem
    ((sigmaNorm Ω K).inv_mem hνN) h1) hνN
  simpa [mul_assoc] using h2

theorem centralizer_le_sigmaNorm_of_layerY_le {n : ℕ} (h : TypeRFam r Ω) (hT4 : Thm4RBelow r n)
    (hn : Nat.card (SecQuot Ω x) < n) {K : Subgroup G} (hK : T8.XMem Ω x K)
    (hY : layerY Ω x ≤ sigmaNorm Ω K) :
    Subgroup.centralizer ({x} : Set G) ≤ sigmaNorm Ω K := by
  have hcl := h.hyp.conjInvariant
  have hΦ := h.secFam (x := x)
  have hT : T4Hyp r (SecQuot Ω x) (secFam Ω x) :=
    { hyp := hΦ.hyp
      twoGroup := hΦ.twoGroup
      quat := hΦ.quat
      tight := hΦ.tight
      noTwins := fun J hJ J' hJ' u hu hu' => (hΦ.noTwins J hJ J' ⟨hJ', u, hu, hu'⟩).symm
      aEmpty := aEmpty_secFam h
      odd := secQuot_oddCore_eq_bot }
  intro c hc
  have hKc : T8.XMem Ω x (conjSub c K) := XMem.conj' hcl hK hc
  rw [T8.mem_sigmaNorm_iff hcl hK.1]
  by_cases hconj : ∃ g : SecQuot Ω x, conjSub g (secImg Ω x K) = secImg Ω x (conjSub c K)
  · obtain ⟨gb, hgb⟩ := hconj
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have e1 : secImg Ω x (conjSub (g : G) K) = secImg Ω x (conjSub c K) := by
      rw [← conjSub_secImg]
      exact hgb
    have hKg : T8.XMem Ω x (conjSub (g : G) K) :=
      XMem.conj' hcl hK (layerY_le_centralizer g.2)
    obtain ⟨ν, -, hν⟩ := exists_conj_of_secImg_eq h hKg hKc e1
    rw [hν, ← conjSub_mul]
    have hy : (ν : G) * (g : G) ∈ sigmaNorm Ω K :=
      (sigmaNorm Ω K).mul_mem (hY ν.2) (hY g.2)
    exact (T8.mem_sigmaNorm_iff hcl hK.1).mp hy
  · have hc' := hT4 (SecQuot Ω x) hn (secFam Ω x) hT (secImg Ω x K) (secImg_mem hK)
      (secImg Ω x (conjSub c K)) (secImg_mem hKc) hconj
    have hne : secImg Ω x (conjSub c K) ≠ secImg Ω x K := fun e =>
      hconj ⟨1, by rw [conjSub_one, e]⟩
    have hnbr := mem_omegaNbr_of_commutes (secImg_mem hKc) hne hc'
    obtain ⟨m, hm, hmn⟩ := exists_conj_omegaNbr_of_secImg h hK hKc hnbr
    have hmK : conjSub (m : G) K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hcl hK.1).mp (hY m.2)
    exact Relation.ReflTransGen.tail hmK ⟨hcl c K hK.1, Or.inl hmn⟩

end Wyl

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_exists_triFrame (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) :
    ∃ P : Fin 3 → Subgroup Y, T8T.TriFrame (CoreAssembly.conjClass (tightCore Rd))
        ![tightCore Rd, J, (F.ρ 2).K] ![z, t, F.zz 2] P ∧
      F.zz 2 ∉ Subgroup.closure ({z, t} : Set Y) := by
  have h02 : (F.ρ 2).K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    have := F.hadj 0 2 (by decide)
    rwa [F.h0] at this
  have h12 : (F.ρ 2).K ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J := by
    have := F.hadj 1 2 (by decide)
    rwa [F.h1] at this
  obtain ⟨P, hP⟩ := exists_triFrame_of_commonNbr hs.large hs.hJ h02 h12 hs.ht (F.hz 2)
  refine ⟨P, hP, ?_⟩
  intro hmem
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  rcases eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hcomm hmem with h | h | h | h
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

theorem TightStd8R.alphaConst_of_wylD4 (hF : TightAlphaFrameR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y)) := by
  obtain ⟨F⟩ :=
    Wyl.exists_frameData hs.toStd8Core hμ (Wyl.not_dbarConnected_of_ne hs.toStd8Core hne)
  obtain ⟨P, hP, hind⟩ := hs.wyl_exists_triFrame F
  exact hF Y Rd Sd z hs.large hdisc ⟨_, _, P, hP, by simpa using hind⟩

theorem TightStd8R.alphaOf_odd_of_wylD4 (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set Y)))) := by
  have hΩ := hs.hyp
  have hnt : ∀ M ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ M' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hM
  obtain ⟨F⟩ :=
    Wyl.exists_frameData hs.toStd8Core hμ (Wyl.not_dbarConnected_of_ne hs.toStd8Core hne)
  obtain ⟨P, hP, hind⟩ := hs.wyl_exists_triFrame F
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set Y)) :=
    hH Y Rd Sd z hs.large ![tightCore Rd, J, (F.ρ 2).K] ![z, t, F.zz 2] P hP hind
  have hc01 : z * t = t * z := triFrame_comm_gen hP hΩ 0 1
  have hz2 : z * z = 1 := hP.sq 0
  have ht2 : t * t = 1 := hP.sq 1
  have hz1 : z ≠ 1 := hP.ne_one 0
  have ht1 : t ≠ 1 := hP.ne_one 1
  have hzt : t ≠ z := (hP.x_ne hnt (i := 0) (j := 1) (by decide)).symm
  have hDB : Subgroup.closure ({t, z} : Set Y) ≤ Subgroup.closure ({z, t, F.zz 2} : Set Y) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt hc01.symm
  exact (lemma54_odd_and_eq hHyp hDB hD).1

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
