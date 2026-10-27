module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Tri
public import CFSG.ClassicalInvolution.Q3.TL4Conn274

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

section Cit3


@[expose] def TightHyp51TriR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y),
    TightLargeHypR r n Y Rd Sd z →
      ∀ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
        TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P →
          x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y) →
            Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set Y))

@[expose] def TightAlphaNormR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          (∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
            ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) →
            (∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
              K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J → ∀ z' : Y,
                IsUniqueInvolution K' z' → z' ≠ z * t) →
              H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
                Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y)

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.alphaOf_eq_bot (h4 : TightC27_4R r n) (hH : TightHyp51TriR r n)
    (hN : TightAlphaNormR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE4 : ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hab : ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
      ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J → ∀ z' : Y,
        IsUniqueInvolution K' z' → z' ≠ z * t) :
    alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥ := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hnt : ∀ M ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ M' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hM
  obtain ⟨K', R', z', hF, hind⟩ := exists_triFrame_of_std8Core hs.toStd8Core hE4 hab hE8
  have hHyp : Hyp51 (Subgroup.closure ({z, t, z'} : Set Y)) :=
    hH Y Rd Sd z hs.large ![tightCore Rd, J, K'] ![z, t, z'] ![R, T, R'] hF hind
  have hzt : z * t = t * z := triFrame_comm_gen hF hΩ 0 1
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hzt' : t ≠ z := (hF.x_ne hnt (i := 0) (j := 1) (by decide)).symm
  have hDB : Subgroup.closure ({t, z} : Set Y) ≤ Subgroup.closure ({z, t, z'} : Set Y) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt' hzt.symm
  obtain ⟨hodd, -⟩ := lemma54_odd_and_eq hHyp hDB hD
  have hH274 := hN Y Rd Sd z J S R T W t hs hdisc hE4 hab hE8
  have htop := h4 Y Rd Sd z J S R T W t hs hdisc
  rw [htop, top_le_iff] at hH274
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH274
  have hle : alphaOf (Subgroup.closure ({t, z} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnorm, hodd⟩
  have hO : classicalInvolutionOddCore Y = ⊥ := hs.large.cls.2.2
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem TightStd8R.oddCoreOf_centralizer_le_sigmaNorm (h4 : TightC27_4R r n)
    (hH : TightHyp51TriR r n) (hN : TightAlphaNormR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE4 : ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hab : ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
      ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J → ∀ z' : Y,
        IsUniqueInvolution K' z' → z' ≠ z * t) :
    oddCoreOf (Subgroup.centralizer ({z * t} : Set Y)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have hα := hs.alphaOf_eq_bot h4 hH hN hdisc hE4 hab hE8
  have hzA : z ∈ Subgroup.closure ({t, z} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htA : t ∈ Subgroup.closure ({t, z} : Set Y) := Subgroup.subset_closure (Set.mem_insert _ _)
  have haA : z * t ∈ Subgroup.closure ({t, z} : Set Y) := Subgroup.mul_mem _ hzA htA
  have hzt : z ≠ t := ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have ha1 : z * t ≠ 1 := mul_ne_one_of_ne hs.hz.sq hzt
  intro x hx
  have hxz : x * z = z * x := oddCoreOf_centralizer_commutes hα haA ha1 hzA x hx
  exact hs.centralizer_le_sigmaNorm (Subgroup.mem_centralizer_singleton_iff.mpr hxz)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
