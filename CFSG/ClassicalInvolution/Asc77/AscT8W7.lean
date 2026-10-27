module

public import CFSG.ClassicalInvolution.Asc77.AscT8W6
public import CFSG.ClassicalInvolution.Asc77.AscT8W4
public import CFSG.ClassicalInvolution.Asc77.AscT8W5
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section Good

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_good_involution_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    ∃ t₁ : G, t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₁ ≠ t ∧ t * t₁ = t₁ * t ∧ z * t₁ = t₁ * z ∧
      t₁ ∈ omegaNbrGen Ω K ∧ (∀ r ∈ R, r * t₁ = t₁ * r) ∧ conjSub t₁ J = J ∧
      Subgroup.centralizer ({t₁} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({t * t₁} : Set G) ≤ sigmaNorm Ω K ∧
      ∃ J₁ : Subgroup G, J₁ ∈ Ω ∧ J₁ ≤ omegaNbrGen Ω K ∧ IsUniqueInvolution J₁ t₁ := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hKX : ¬ K ≤ omegaNbrGen Ω K := T8S2.not_le_omegaNbrGen hs (s26XProper_E4 hs hdisc)
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  obtain ⟨S₂, hRS₂, hTS₂, hS₂X⟩ := exists_sylow_RT hs
  obtain ⟨g, hgX, hgS, hgne⟩ := exists_zStar_conj hs hdisc hE (T8R.c26_1 p f) hRS₂ hTS₂ hS₂X
  have hgiX : g⁻¹ ∈ X := X.inv_mem hgX
  have ht1X : g⁻¹ * t * g ∈ X := X.mul_mem (X.mul_mem hgiX htX) hgX
  have hct : g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹ = t :=
    sX_centralizes_t hs hE hRS₂ hTS₂ hKX hgS ht1X
  have htt1 : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
    calc t * (g⁻¹ * t * g) = (g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
          rw [hct]
      _ = g⁻¹ * t * g * t := by group
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hs.hR.1; omega)
  have hS₂2 : IsPGroup 2 ↥(S₂ : Subgroup G) := S₂.isPGroup'
  have hcommK : ∀ r ∈ R, r * (g⁻¹ * t * g) = g⁻¹ * t * g * r := fun r hr =>
    commute_of_mem_two_subgroup hs hdisc hS₂2 (hs.hR.2.1 hr) ht1X (hRS₂ hr) hgS
  have hzt1 : z * (g⁻¹ * t * g) = g⁻¹ * t * g * z := hcommK z hzR
  have ht1sq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have ht1ne : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply hs.ht.ne_one
    have := congrArg (fun y => g * y * g⁻¹) h
    simpa [mul_assoc] using this
  have hgN : g ∈ sigmaNorm Ω K := s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK hgX
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  have hJ1mem : conjSub g⁻¹ J ∈ dComp Ω K := ((sigmaNorm Ω K).inv_mem hgN J).mp hJmem
  have hb : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hs.ht.conj g⁻¹
    rwa [inv_inv] at this
  have hJ1Ω : conjSub g⁻¹ J ∈ Ω := hΩ.conjInvariant g⁻¹ J hJΩ
  have hC1 : Subgroup.centralizer ({g⁻¹ * t * g} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJ1Ω (hnt _ hJ1Ω) hb).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJ1mem)
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  obtain ⟨y, hyX, hy⟩ := exists_conj_mul_E4 hs hdisc hE hgX hgne htt1
  have hyN : y ∈ sigmaNorm Ω K := s26_omegaNbrGen_le_sigmaNorm hΩ.conjInvariant hK hyX
  have hC2 : Subgroup.centralizer ({t * (g⁻¹ * t * g)} : Set G) ≤ sigmaNorm Ω K := by
    refine T8.centralizer_le_of_conj hyN ?_
    have : y⁻¹ * (t * (g⁻¹ * t * g)) * y = t := by rw [← hy]; group
    rw [this]
    exact hCt
  have hnJ : conjSub (g⁻¹ * t * g) J = J :=
    sX_normalizes_J hs hE hRS₂ hTS₂ hKX (s := g⁻¹ * t * g) hgS ht1X
  have hJ1X : conjSub g⁻¹ J ≤ X := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ J := by simpa using mem_conjSub_iff.mp hy
    have h2 : g * y * g⁻¹ ∈ X := hJX h1
    have := X.mul_mem (X.mul_mem hgiX h2) hgX
    simpa [mul_assoc] using this
  exact ⟨g⁻¹ * t * g, ht1sq, ht1ne, hgne, htt1, hzt1, ht1X, hcommK, hnJ, hC1, hC2,
    conjSub g⁻¹ J, hJ1Ω, hJ1X, hb⟩

theorem oddCoreOf_layerJoin_le_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    oddCoreOf (T8.layerJoin Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨t₁, ht1sq, ht1ne, hne, htt1, hzt1, -, -, -, hC1, hC2, -⟩ :=
    exists_good_involution_E4 hs hdisc hE
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hs.stand.odd hΩ hs.hz hs.hJ hs.ht
  have htx : t ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    have h1 : t * (z * t) = z := by rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have h2 : z * t * t = z := by rw [mul_assoc, hs.ht.sq, mul_one]
    rw [h1, h2])
  have ht1x : t₁ ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    calc t₁ * (z * t) = (t₁ * z) * t := by rw [mul_assoc]
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by rw [mul_assoc]
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by rw [mul_assoc])
  exact T8.oddCoreOf_layerJoin_le_of_good_pair hΩ hs.ht.sq ht1sq htt1 hs.ht.ne_one ht1ne hne.symm
    htx ht1x hCt hC1 hC2

end Good

end T8W

end CFSG.ClassicalInvolution.Asc77
