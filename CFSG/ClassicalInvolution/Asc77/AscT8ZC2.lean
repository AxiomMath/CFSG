module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC1
import CFSG.ClassicalInvolution.Asc77.AscT8ZC2EngB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open scoped commutatorElement

namespace T8ZZ

variable {p f : ℕ} [Fact p.Prime]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_xMem_of_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K L : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hL : L ∈ omegaNbr Ω K) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) := by
  exact exists_xMem_of_omegaNbrE hΩ.conjInvariant
    (fun hM hR hRM => T3.isSylow2In_of_mem_RSet_of_le hp hΩ hM hR hRM)
    (fun hM => hΩ.exists_uniqueInvolution hp hq hM) (fun hR => hΩ.eight_le_of_mem_RSet hp hR) hnt hz
    hL

theorem exists_common_sylow (hs : Std8 p f Ω K J S R T W z t) {L : Subgroup G}
    (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧ (∀ r ∈ P, r * t = t * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) ∧ t ∈ Subgroup.normalizer (L : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact exists_common_sylowE hs.hz hs.ht hLK hLJ
    (fun hz₀ hL₀ => exists_xMem_of_omegaNbr hp hq hΩ hnt hz₀ hL₀)
    (fun hR hy hym hyR => T8V.comm_mem_oddCoreOf_of_pow hp hq hΩ hLK.1 hR hy hym hyR)
    (T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht)
    (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)

theorem oddCore_commutes_zz [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    (j : Fin 4) {n : G} (hn : n ∈ oddCoreOf (T8.layerJoin Ω (z * t))) :
    n * F.zz j = F.zz j * n := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨-, hαV'⟩ := alphaOf_vGroup_eq hs F
  exact oddCore_commutes_zzE F F.vGroup hαV' (fun j => F.zz0_mul_mem_vGroup c j)
    (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * t)) hα j hn

theorem eq_frame_of_layerImg_eq [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    (j : Fin 4) {L : Subgroup G} (hL : T8.XMem Ω (z * t) L)
    (h : T8.layerImg Ω (z * t) L = T8.layerImg Ω (z * t) (F.ρ j).K) : L = (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  obtain ⟨n, hn, hnK⟩ :=
    T8.exists_oddCore_conj_of_layerImg_eq hp hq hΩ hx (frame_xMem hs F j) hL h.symm
  have hcomm := oddCore_commutes_zz hs hα F j hn
  have hz' : IsUniqueInvolution L (F.zz j) := by
    have h1 := (F.hz j).conj n
    rw [hnK] at h1
    have e : n * F.zz j * n⁻¹ = F.zz j := by
      rw [hcomm]
      group
    rwa [e] at h1
  exact hnt (F.ρ j).K (F.ρ j).hK L ⟨hL.1, F.zz j, F.hz j, hz'⟩

theorem commonNbr_mem_frame [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hnconn : ¬ DConnected (T8.layerFamQ Ω (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J) :
    ∃ j : Fin 4, j ≠ 0 ∧ L = (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  obtain ⟨P, hP, hPz, hPt, hzN, htN⟩ := exists_common_sylow hs hLK hLJ
  have hLΩ : L ∈ Ω := hLK.1
  have hPx : P ≤ T8.cenZ (z * t) := fun r hr => by
    rw [T8.mem_cenZ_iff]
    calc r * (z * t) = (r * z) * t := by group
      _ = (z * r) * t := by rw [hPz r hr]
      _ = z * (r * t) := by group
      _ = z * (t * r) := by rw [hPt r hr]
      _ = z * t * r := by group
  have hXL : T8.XMem Ω (z * t) L :=
    ⟨hLΩ, Subgroup.mul_mem _ hzN htN, P, hP, fun r hr => T8.mem_cenZ_iff.mp (hPx hr)⟩
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hp hq hLΩ
  have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hLΩ hP)
  have huP : u ∈ P := T3.mem_of_isPGroup hu hP.1 hP.2.1 (by omega)
  have hzu : z * u = u * z := (hPz u huP).symm
  have hne : T8.layerImg Ω (z * t) K ≠ T8.layerImg Ω (z * t) L :=
    T8.layerImg_ne_of_involutions hp hq hΩ hx (T8.xMem_zt hs) hXL hs.hz hu hzu
      (T8.ne_of_mem_omegaNbr hs.noTwins hLK hs.hz hu)
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := fun r hr =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hPz r hr))
  have hadj := T8.layerImg_omegaNbr hp hq hΩ hx (T8.xMem_zt hs) hXL hP hPx hPN hne
  obtain ⟨j, hj0, hj⟩ := layerImg_nbr_eq_frame hs hnconn F hXL hadj
  exact ⟨j, hj0, eq_frame_of_layerImg_eq hs hα F j hXL hj⟩

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
