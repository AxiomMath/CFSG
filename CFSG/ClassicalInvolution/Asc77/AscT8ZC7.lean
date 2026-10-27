module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC6
public import CFSG.ClassicalInvolution.Asc77.AscT8YC7
public import CFSG.ClassicalInvolution.Asc77.AscT8ZC3
public import CFSG.ClassicalInvolution.Asc77.AscT8ZC4
public import CFSG.ClassicalInvolution.Asc77.AscT8ZC5

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

theorem layerImg_nbr_in_frame_z [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hL : T8.XMem Ω z L) (hLK : L ≠ K)
    (hadj : T8.layerImg Ω z L ∈
        omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z (F.ρ j).K) ∨
      T8.layerImg Ω z (F.ρ j).K ∈ omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z L)) :
    ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ T8.layerImg Ω z L = T8.layerImg Ω z (F.ρ i).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hLnbr : L ∈ omegaNbr Ω K := omegaNbr_of_xMem_z hs hL hLK
  have key : ∃ n ∈ oddCoreOf (T8.layerJoin Ω z), conjSub n L ∈ omegaNbr Ω (F.ρ j).K := by
    rcases hadj with h | h
    · obtain ⟨n, hn, hn'⟩ := T8.exists_oddCore_conj_omegaNbr hp hq hΩ hs.hz.sq
        (frame_xMem_z hs F j) hL h
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      have h1 := omegaNbr_conj hΩ.conjInvariant hn' n⁻¹
      rwa [conjSub_inv_conjSub] at h1
    · obtain ⟨n, hn, hn'⟩ := T8.exists_oddCore_conj_omegaNbr hp hq hΩ hs.hz.sq hL
        (frame_xMem_z hs F j) h
      exact ⟨n, hn, T3.omegaNbr_symm (l6_2 p f) hp hq hΩ (hΩ.conjInvariant n L hL.1)
        (F.ρ j).hK hn'⟩
  obtain ⟨n, hn, hn1⟩ := key
  have hncen : n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ z (oddCoreOf_le_self _ hn)
  have hnK : conjSub n K = K :=
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
        hncen)
  have hn2 : conjSub n L ∈ omegaNbr Ω K := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hLnbr n
    rwa [hnK] at h1
  obtain ⟨i, hi0, hij, hLi⟩ :=
    commonNbr_frame_eq hs hdisc hμ hne huni hα F hj hn2 hn1
  refine ⟨i, hi0, hij, ?_⟩
  rw [← T8.layerImg_conj_of_mem_oddCore (K := L) hn, hLi]

theorem layerImg_frame_of_path [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    {B : Subgroup (T8.LayerQuot Ω z)}
    (hpath : Relation.ReflTransGen
      (fun A C => C ∈ linkFam (T8.layerFamQ Ω z) (T8.layerImg Ω z K) ∧
        (C ∈ omegaNbr (T8.layerFamQ Ω z) A ∨ A ∈ omegaNbr (T8.layerFamQ Ω z) C))
      (T8.layerImg Ω z (F.ρ 1).K) B) :
    ∃ i : Fin 4, i ≠ 0 ∧ B = T8.layerImg Ω z (F.ρ i).K := by
  induction hpath with
  | refl => exact ⟨1, by decide, rfl⟩
  | @tail b c hab hbc ih =>
    obtain ⟨i, hi0, hbi⟩ := ih
    obtain ⟨hcmem, hadj⟩ := hbc
    obtain ⟨L, hL, hLc⟩ := exists_xMem_of_mem_layerFamQ hcmem.1
    have hLK : L ≠ K := fun h => hcmem.2 (by rw [← hLc, h])
    have hadj' : T8.layerImg Ω z L ∈ omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z (F.ρ i).K) ∨
        T8.layerImg Ω z (F.ρ i).K ∈ omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z L) := by
      rw [hLc, ← hbi]
      exact hadj
    obtain ⟨i', hi'0, -, himg⟩ :=
      layerImg_nbr_in_frame_z hs hdisc hμ hne huni hα F hi0 hL hLK hadj'
    exact ⟨i', hi'0, by rw [← hLc, himg]⟩

theorem singleFrameFact0_proved : SingleFrameFact0 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα F M hM
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hz2 : z * z = 1 := hs.hz.sq
  have hΨ := T8.hypOmegaMod_layerQuot hp hq hΩ hz2
  have hntΨ := T8.noTwins_layerQuot hp hq hΩ hnt hz2
  have hOX : classicalInvolutionOddCore (T8.LayerQuot Ω z) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree _
  have hk : ∀ g : T8.LayerQuot Ω z,
      conjSub g (T8.layerImg Ω z K) = T8.layerImg Ω z K := layerImg_z_normal hs
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (z_not_central hs)
  let B : Fin 3 → Subgroup (T8.LayerQuot Ω z) := fun i => T8.layerImg Ω z (F.ρ i.succ).K
  have hBk : ∀ i, B i ∈ linkFam (T8.layerFamQ Ω z) (T8.layerImg Ω z K) := by
    intro i
    refine ⟨T8.layerImg_mem (frame_xMem_z hs F _), ?_⟩
    have h := frame_layerImg_ne_z hs F (Fin.succ_ne_zero i)
    rwa [F.h0] at h
  have hBinj : Function.Injective B := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne_z hs F (fun h' => hij (Fin.succ_injective _ h')) h
  have hBadj : ∀ i j, i ≠ j → B j ∈ omegaNbr (T8.layerFamQ Ω z) (B i) := fun i j hij =>
    frame_layerImg_nbr_z hs F (fun h' => hij (Fin.succ_injective _ h'))
  rcases link_dichotomy hn hlt hp hq hΨ hntΨ hOX hk B hBk hBinj hBadj with
    hconn | ⟨C, hCmem, hCinj, hCadj⟩
  ·
    have hXM := xMem_z_of_nbr hs hM
    have hMk : T8.layerImg Ω z M ∈ linkFam (T8.layerFamQ Ω z) (T8.layerImg Ω z K) :=
      ⟨T8.layerImg_mem hXM, layerImg_nbr_ne_z hs hM⟩
    have hpath := link_path hp hΨ hk hconn (hBk 0) hMk
    obtain ⟨i, hi0, himg⟩ := layerImg_frame_of_path hs hdisc hμ hne huni hα F hpath
    exact ⟨i, eq_of_layerImg_eq_z hs hμ hne hα F hi0 hXM himg⟩
  ·
    exfalso
    have hC2 : ∀ i, C i = T8.layerImg Ω z (F.ρ 2).K ∨ C i = T8.layerImg Ω z (F.ρ 3).K := by
      intro i
      obtain ⟨L, hL, hLC⟩ := exists_xMem_of_mem_layerFamQ (hCmem i).1
      have hLK : L ≠ K := fun h => (hCmem i).2 (by rw [← hLC, h])
      have hadj : T8.layerImg Ω z L ∈
          omegaNbr (T8.layerFamQ Ω z) (T8.layerImg Ω z (F.ρ 1).K) := by
        rw [hLC]
        exact hCadj i
      obtain ⟨i', hi0, hi1, himg⟩ := layerImg_nbr_in_frame_z hs hdisc hμ hne huni hα F
        (j := 1) (by decide) hL hLK (Or.inl hadj)
      rw [← hLC, himg]
      fin_cases i'
      · exact absurd rfl hi0
      · exact absurd rfl hi1
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h0 := hC2 0
    have h1 := hC2 1
    have h2 := hC2 2
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first
        | exact absurd (hCinj (h0.trans h1.symm)) (by decide)
        | exact absurd (hCinj (h0.trans h2.symm)) (by decide)
        | exact absurd (hCinj (h1.trans h2.symm)) (by decide)

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
