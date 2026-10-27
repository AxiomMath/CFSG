module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4B
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)
open CFSG.ClassicalInvolution.Asc77.T8R.Loc (Loc26)
open scoped commutatorElement

namespace LinkDisc

section Gen

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem le_centralizer_of_xMem (h : TypeRFam r Ω) {x : G} {M A : Subgroup G} (hM : XMem Ω x M)
    (hA : IsPGroup 2 ↥A) (hAM : A ≤ M) (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨hMΩ, hxM, P, hP, hPx⟩ := hM
  intro a ha
  have h1 : ⁅x, a⁆ ∈ oddCoreOf M := comm_mem_oddCoreOf_of_twoGroup (h.twoGroup M hMΩ) hP hxM
    (fun p hp => (hPx p hp).symm) (hAM ha)
  have h2 : ⁅x, a⁆ ∈ A := by
    rw [commutatorElement_def]
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxA a).mp ha) (A.inv_mem ha)
  have hmem : ⁅x, a⁆ ∈ A ⊓ oddCoreOf M := ⟨h2, h1⟩
  rw [S1916.inf_oddCoreOf_eq_bot hA M] at hmem
  have h3 : ⁅x, a⁆ = 1 := Subgroup.mem_bot.mp hmem
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc a * x = (x * a * x⁻¹ * a⁻¹)⁻¹ * (x * a) := by group
    _ = x * a := by rw [← commutatorElement_def, h3, inv_one, one_mul]

variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem loc26_of_conj (hs : Std8Core Ω K J S R T W z t) (h : TypeRFam r Ω) {Q : Subgroup G}
    (hQ : Odd (Nat.card Q)) (hQz : Q ≤ Subgroup.centralizer ({z} : Set G))
    (hzQ : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hconj : ∀ L ∈ omegaNbr Ω K, ∃ ν ∈ Q, L = conjSub ν J) : Loc26 Ω K J S R T z t Q := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hcz : ∀ {P : Subgroup G}, Commutes P R → P ≤ Subgroup.centralizer ({z} : Set G) :=
    fun hc x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hc x hx z hzR)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) :=
    hcz (Q3CP.l67Gen G Ω hΩ S T hTΩ R hRΩ hTS hRS (Q3CL.T8R.Loc.R_ne_T hs).symm)
  have htz : t ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht).symm
  have hzz : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hνt : ∀ ν ∈ Q, ν * t * ν⁻¹ * t⁻¹ ∈ Q := fun ν hν => by
    have e : ν * t * ν⁻¹ * t⁻¹ = ν * (t * ν⁻¹ * t⁻¹) := by group
    rw [e]
    exact Q.mul_mem hν ((Subgroup.mem_normalizer_iff.mp (hzQ htz) ν⁻¹).mp (Q.inv_mem hν))
  set A := J ⊓ Subgroup.centralizer ({z} : Set G) with hAdef
  set H := A ⊔ Q with hHdef
  have hAH : A ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (inf_le_right.trans hzQ) Subgroup.le_normalizer
  have hHeq : H = A ⊔ oddCoreOf H :=
    le_antisymm (sup_le_sup_left (le_oddCoreOf_of_normal_odd hQH hHN hQ) A)
      (sup_le hAH (oddCoreOf_le_self H))
  have hTA : IsSylow2In T A := ⟨le_inf hTJ hTz, hTsyl.2.1, fun P hPA hP2 hTP =>
    hTsyl.2.2 P (hPA.trans inf_le_left) hP2 hTP⟩
  have hSH : (S : Subgroup G) ⊓ H = T := by
    have hle := T8R.natCard_le_of_eq_sup_oddCoreOf hAH hHeq hTA inf_le_right
      S.isPGroup'.to_inf_left
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hTS (hTA.1.trans hAH)) hle).symm
  have hconjH : ∀ ν ∈ Q, ∀ {P : Subgroup G}, P ≤ conjSub ν J →
      P ≤ Subgroup.centralizer ({z} : Set G) → P ≤ H := by
    intro ν hν P hPJ hPz x hx
    have hνz := hQz hν
    have h1 : ν⁻¹ * x * ν ∈ A :=
      ⟨mem_conjSub_iff.mp (hPJ hx), Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hνz) (hPz hx)) hνz⟩
    have e : x = ν * (ν⁻¹ * x * ν) * ν⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (hQH hν) (hAH h1)) (H.inv_mem (hQH hν))
  refine ⟨hQ, fun {P} hP hPS => ?_, fun {M} hM h4 hMJ hMK => ?_, fun {L} hL {y} hy => ?_,
    fun {y} hy => ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
    have hMK : M ≠ K := by
      rintro rfl
      exact hcon.1 (eq_of_isSylow2In_of_le_sylow_gen hPM hRsyl hPS hRS)
    have hPz := hcz (Q3CP.l67Gen G Ω hΩ S P hP R hRΩ hPS hRS hcon.1)
    have hMnbr : M ∈ omegaNbr Ω K :=
      ⟨hM, hMK, P, hP, hPM.1, fun x hx => h.tight K hK z hs.hz (hPz hx)⟩
    obtain ⟨ν, hν, rfl⟩ := hconj M hMnbr
    have hPT : P ≤ T := hSH ▸ le_inf hPS (hconjH ν hν hPM.1 hPz)
    have hcardP : Nat.card P = Nat.card T := hΩ.omega3 _ hM J hJΩ P T hPM hTsyl
    exact hcon.2 (Subgroup.eq_of_le_of_card_ge hPT (le_of_eq hcardP.symm))
  ·
    obtain ⟨ν, hν, rfl⟩ := hconj M hMK
    have hx : XMem Ω z (conjSub ν J) := xMem_of_mem_omegaNbr_gen h hMK hs.hz
    have hA2 : IsPGroup 2 ↥(conjSub ν J ⊓ (S : Subgroup G)) := S.isPGroup'.to_inf_right
    have hzS : z ∈ (S : Subgroup G) := hRS hzR
    have hzN : z ∈ Subgroup.normalizer
        ((conjSub ν J ⊓ (S : Subgroup G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.mp hx.2.1 y)
        (Subgroup.mem_normalizer_iff.mp ((S : Subgroup G).le_normalizer hzS) y)
    have hAz := le_centralizer_of_xMem h hx hA2 inf_le_left hzN
    have hAT : conjSub ν J ⊓ (S : Subgroup G) ≤ T :=
      hSH ▸ le_inf inf_le_right (hconjH ν hν inf_le_left hAz)
    exact hMJ (Sec6Gen.eq_of_le_of_le hΩ hM hJΩ hA2 h4 inf_le_left (hAT.trans hTJ))
  ·
    obtain ⟨ν, hν, rfl⟩ := hconj L hL
    rw [← (hs.ht.conj ν).eq hy]
    exact hνt ν hν
  ·
    have hyK : y ∈ Subgroup.normalizer (K : Set G) := h.tight K hK z hs.hz hy
    have hJy : conjSub y J ∈ omegaNbr Ω K := by
      have h1 := omegaNbr_conj hΩ.conjInvariant hs.hJ y
      rwa [conjSub_eq_of_mem_normalizer hyK] at h1
    obtain ⟨ν, hν, hνe⟩ := hconj _ hJy
    have h1 : IsUniqueInvolution (conjSub y J) (ν * t * ν⁻¹) := by
      rw [hνe]
      exact hs.ht.conj ν
    have e1 : y * t * y⁻¹ = ν * t * ν⁻¹ := (hs.ht.conj y).eq h1
    have hyz : y * z * y⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hy, mul_inv_cancel_right]
    have e2 : y * (z * t) * y⁻¹ * (z * t)⁻¹ = z * (ν * t * ν⁻¹ * t⁻¹) * z⁻¹ := by
      calc y * (z * t) * y⁻¹ * (z * t)⁻¹ = (y * z * y⁻¹) * (y * t * y⁻¹) * t⁻¹ * z⁻¹ := by
            group
        _ = z * (ν * t * ν⁻¹ * t⁻¹) * z⁻¹ := by rw [hyz, e1]; group
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.mp (hzQ hzz) _).mp (hνt ν hν)

theorem false_of_conj (hs : Std8Core Ω K J S R T W z t) (h : TypeRFam r Ω)
    (hodd : classicalInvolutionOddCore G = ⊥) (hZ : Subgroup.center G = ⊥) {Q : Subgroup G}
    (hQ : Odd (Nat.card Q)) (hQz : Q ≤ Subgroup.centralizer ({z} : Set G))
    (hzQ : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G))
    (hconj : ∀ L ∈ omegaNbr Ω K, ∃ ν ∈ Q, L = conjSub ν J) : False := by
  have hcl : ConjInvariant Ω := hs.stand.hyp.conjInvariant
  obtain ⟨g, hg⟩ := hs.stand.trans J hs.hJ.1
  have hgz : g * z * g⁻¹ = t := by
    have h1 := hs.hz.conj g
    rw [hg] at h1
    exact h1.eq hs.ht
  have hQ' : Odd (Nat.card (conjSub g Q)) := by
    rw [Q3CL.T8R.Loc.natCard_conjSub']
    exact hQ
  have hQt : conjSub g Q ≤ Subgroup.centralizer ({t} : Set G) := by
    have h1 := conjSub_mono (n := g) hQz
    rwa [Balance.conjSub_centralizer_singleton, hgz] at h1
  have htQ : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (conjSub g Q : Set G) := by
    intro y hy
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [← hgz] at hyt
    have hy' : g⁻¹ * y * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [hyt]
        _ = z * (g⁻¹ * y * g) := by group
    have h3 : conjSub (g⁻¹ * y * g) Q = Q := mem_normalizer_iff_conjSub_eq.mp (hzQ hy')
    rw [mem_normalizer_iff_conjSub_eq]
    calc conjSub y (conjSub g Q) = conjSub g (conjSub (g⁻¹ * y * g) Q) := by
          simp only [← conjSub_mul]
          congr 1
          group
      _ = conjSub g Q := by rw [h3]
  have hconj' : ∀ L ∈ omegaNbr Ω J, ∃ ν ∈ conjSub g Q, L = conjSub ν K := by
    intro L hL
    have hL' : conjSub g⁻¹ L ∈ omegaNbr Ω K := by
      have h1 := omegaNbr_conj hcl hL g⁻¹
      rwa [← hg, conjSub_inv_conjSub] at h1
    have hK' : conjSub g⁻¹ K ∈ omegaNbr Ω K := by
      have h1 := omegaNbr_conj hcl hs.symm'.hJ g⁻¹
      rwa [← hg, conjSub_inv_conjSub] at h1
    obtain ⟨ν, hν, hνe⟩ := hconj _ hL'
    obtain ⟨ν₀, hν₀, hν₀e⟩ := hconj _ hK'
    refine ⟨g * (ν * ν₀⁻¹) * g⁻¹, ⟨ν * ν₀⁻¹, Q.mul_mem hν (Q.inv_mem hν₀), rfl⟩, ?_⟩
    have e1 : L = conjSub g (conjSub ν J) := by rw [← hνe, conjSub_conjSub_inv]
    have e2 : K = conjSub g (conjSub ν₀ J) := by rw [← hν₀e, conjSub_conjSub_inv]
    rw [e1, e2]
    simp only [← conjSub_mul]
    congr 1
    group
  exact false_of_loc26_gen hs hodd hZ (loc26_of_conj hs h hQ hQz hzQ hconj)
    (loc26_of_conj hs.symm' h hQ' hQt htQ hconj')

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem false_of_secImg_eq (hL : TightLargeHypR r n Y Rd Sd z) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hB1 : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      secImg (CoreAssembly.conjClass (tightCore Rd)) z L =
        secImg (CoreAssembly.conjClass (tightCore Rd)) z J) : False := by
  have h := TightLargeHypR.typeRFam hL
  have hcl := h.hyp.conjInvariant
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hJ.1
  obtain ⟨S, R, T, W, hs⟩ := TightLargeHypR.exists_std8 hL hJ hu
  refine false_of_conj hs.toStd8Core h hL.cls.2.2 hL.center
    (oddCoreOf_odd_natCard (layerY (CoreAssembly.conjClass (tightCore Rd)) z))
    ((oddCoreOf_le_self _).trans layerY_le_centralizer) (fun c hc => ?_) (fun L hL' => ?_)
  · exact mem_normalizer_oddCore_of_mem_normalizer
      (mem_normalizer_iff_conjSub_eq.mpr (layerY_conjSub_eq hcl hc))
  · obtain ⟨ν, hν, e⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJ)
      (xMem_of_mem_omegaNbr_core hL hL') (hB1 L hL').symm
    exact ⟨ν, ⟨ν, hν, rfl⟩, e⟩

end Cit3

end LinkDisc

end CFSG.ClassicalInvolution.Q3.TL4
