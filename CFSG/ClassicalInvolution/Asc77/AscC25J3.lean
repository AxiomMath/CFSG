module

public import CFSG.ClassicalInvolution.Asc77.AscC25J2
public import CFSG.ClassicalInvolution.Asc77.AscC25I10
public import CFSG.ClassicalInvolution.Asc77.AscC25J1
public import CFSG.ClassicalInvolution.Asc77.AscR10Lz
public import CFSG.ClassicalInvolution.Asc77.AscR10Q9Fin
public import CFSG.ClassicalInvolution.Asc77.AscR10Viol
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Omega5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => crossIn K' a

theorem typed5_data9 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (ha2 : a * a = 1) (ha1 : a ≠ 1) {e₀ : ℕ} (h3 : 3 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
    {a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))}
    (T : TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀)
    (hO5 : SectionOrthTypeU p e₀ (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 5 true) :
    ∃ t₀ y c₁ : G, C25I.IsSwap K K' z t₀ ∧ a * t₀ = t₀ * a ∧
      (∃ c : G, c * a = a * c ∧ c * z * c⁻¹ = t₀) ∧ c₁ * a = a * c₁ ∧ y ∈ conjSub c₁ K' ∧
      orderOf y = 4 ∧ y * a = a * y ∧ y * (z * t₀) = (z * t₀) * y ∧
      ∀ c : G, c * a = a * c → a * (z * t₀) ≠ c * z * c⁻¹ := by
  classical
  obtain ⟨tg, n, hT, D, hC⟩ := hO5
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨⟨sw, hsw2, hs1, hs2, hs3, ⟨xq, hsx⟩, ⟨x', yq, hyq, hyq4, hyqc⟩⟩, hcen⟩ :=
    twinSwapQ5U h.hp h3 D hT hC T
  let w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩
  let ζ : ↥(conjGen Lₐ) := ⟨⟨z, hzA⟩, hzX⟩
  have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
  have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
  have hL'mem : conjSub w Lₐ ∈ conjFamily Lₐ := ⟨w, rfl⟩
  have hL'X : conjSub w Lₐ ≤ conjGen Lₐ := le_conjGen hL'mem
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := Subtype.ext (Subtype.ext hzz)
  obtain ⟨t₀, ht₀s, ht₀2, ht₀z⟩ :=
    C25I.exists_involution_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 hsw2 hs1
  obtain ⟨c, hc⟩ := C25I.exists_conj_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 ht₀2
    (x := xq) (by rw [ht₀s]; exact hsx)
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := rfl
  have hCa : ∀ x : ↥(conjGen Lₐ), φ x * a = a * φ x := fun x =>
    Subgroup.mem_centralizer_singleton_iff.mp (x : ↥(Subgroup.centralizer ({a} : Set G))).2
  obtain ⟨t₀G, ht₀G⟩ : ∃ g : G, g = φ t₀ := ⟨_, rfl⟩
  have ht₀G2 : t₀G * t₀G = 1 := by rw [ht₀G, ← map_mul, ht₀2, map_one]
  have ht₀Gz : t₀G * z = z * t₀G := by rw [ht₀G, ← hφζ, ← map_mul, ← map_mul, ht₀z]
  have hcG : φ c * z * (φ c)⁻¹ = t₀G := by
    rw [ht₀G, ← hc, ← hφζ, map_mul, map_mul, map_inv]
  have hat₀ : a * t₀G = t₀G * a := by rw [ht₀G]; exact (hCa t₀).symm
  have ht₀G' : t₀G = (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) :=
    ht₀G
  have hsw1 : (QuotientGroup.mk t₀ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = sw := ht₀s
  have ht₀C : t₀G ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [ht₀G]
    exact ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hnotN : conjSub t₀G K ≠ K := by
    intro hN
    have ht'K : conjSub t' K = K' := conjSub_t'_K h
    have hc1 : conjSub (t' * t₀G * t') K' = K' := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K' h, hN, ht'K]
    have hcC : t' * t₀G * t' ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'a ht₀C) ht'a
    have hfix := conjSub_crossIn_eq (K := K') hcC (mem_normalizer_iff_conjSub_eq.mpr hc1)
    have h1 : conjSub ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
        (conjSub w Lₐ) = conjSub w Lₐ := by
      have e2 : ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) * w =
          w * (⟨t' * t₀G * t', hcC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
        apply Subtype.ext
        change (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * t' =
          t' * (t' * t₀G * t')
        rw [← ht₀G']
        calc t₀G * t' = (t' * t') * t₀G * t' := by rw [h.ht'2]; group
          _ = t' * (t' * t₀G * t') := by group
      rw [← conjSub_mul, e2, conjSub_mul, hfix]
    have hsecw : conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ)) =
        secImg (conjGen Lₐ) (conjSub w Lₐ) := by
      have h2 := secAct_secImg (conjGen Lₐ)
        ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) hL'X
      rw [h1] at h2
      calc conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ))
          = (secImg (conjGen Lₐ) (conjSub w Lₐ)).map (secAct (conjGen Lₐ)
              ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))).toMonoidHom := by
            rw [secAct_of_mem (conjGen Lₐ) (t₀ : ↥(conjGen Lₐ)).2, ← hsw1]
            rfl
        _ = secImg (conjGen Lₐ) (conjSub w Lₐ) := h2
    rw [hsecw] at hs3
    exact T.ne hs3.symm
  have hsw' : conjSub (t₀G * t') K = K := by
    rcases cz_cover h ht₀Gz with h1 | h1
    · exact absurd h1 hnotN
    · exact h1
  have hswK : conjSub t₀G K = K' := by
    have e1 : conjSub t₀G K' = K := by
      have := hsw'
      rwa [conjSub_mul, conjSub_t'_K h] at this
    calc conjSub t₀G K = conjSub t₀G (conjSub t₀G K') := by rw [e1]
      _ = conjSub (t₀G * t₀G) K' := by rw [conjSub_mul]
      _ = K' := by rw [ht₀G2, conjSub_one]
  have hIS : IsSwap K K' z t₀G := ⟨ht₀G2, ht₀Gz, hswK⟩
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective x'
  have hx₂2 : (ζ * t₀) * (ζ * t₀) = 1 := by
    have h1 := (show Commute ζ t₀ from ht₀z.symm).mul_pow 2
    rw [pow_two, pow_two, pow_two, hζ2, ht₀2, mul_one] at h1
    exact h1
  let M : Subgroup ↥(conjGen Lₐ) :=
    (conjSub ((x₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ).subgroupOf
      (conjGen Lₐ)
  have hM : ∃ m ∈ M, (QuotientGroup.mk m :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = yq := by
    rw [← hx₀, C25I.conjSub_mk_secImg (conjGen Lₐ) x₀ hLX] at hyq
    obtain ⟨m, hm, hmy⟩ := hyq
    exact ⟨m, hm, hmy⟩
  have hc' : yq * (QuotientGroup.mk (ζ * t₀) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) =
      QuotientGroup.mk (ζ * t₀) * yq := by
    rw [QuotientGroup.mk_mul, ht₀s]
    exact hyqc
  obtain ⟨h₁, y, ⟨m, hmM, hym⟩, hy4, hyx⟩ :=
    C25I.exists_order_four_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hx₂2 M hyq4 hc' hM
  have hmK' : (φ x₀)⁻¹ * φ m * φ x₀ ∈ K' := by
    have h2 := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hmM)
    exact (Subgroup.mem_subgroupOf.mp h2).1
  obtain ⟨c₁G, hc₁G⟩ : ∃ g : G, g = φ h₁ * φ x₀ := ⟨_, rfl⟩
  have hyG : φ y = c₁G * ((φ x₀)⁻¹ * φ m * φ x₀) * c₁G⁻¹ := by
    rw [hym, map_mul, map_mul, map_inv, hc₁G, mul_inv_rev]
    group
  have hyK : φ y ∈ conjSub c₁G K' := by
    rw [hyG]
    exact conj_mem_conjSub hmK'
  have hc₁a : c₁G * a = a * c₁G := by
    rw [hc₁G, mul_assoc, hCa x₀, ← mul_assoc, hCa h₁, mul_assoc]
  have hy4G : orderOf (φ y) = 4 := by rw [orderOf_injective φ hφinj y]; exact hy4
  have hyxG : φ y * (z * t₀G) = (z * t₀G) * φ y := by
    have := congrArg φ hyx
    simp only [map_mul, hφζ] at this
    rw [← ht₀G] at this
    exact this
  have hlast : ∀ c : G, c * a = a * c → a * (z * t₀G) ≠ c * z * c⁻¹ := by
    intro c hca heq
    have hcC : c ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hca
    let cY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨c, hcC⟩
    let aY : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let ζY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨z, hzA⟩
    let x₂Y : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ((ζ * t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
    have hrel : aY * x₂Y = cY * ζY * cY⁻¹ := by
      apply Subtype.ext
      change a * φ (ζ * t₀) = c * z * c⁻¹
      rw [map_mul, hφζ, ← ht₀G]
      exact heq
    have hx₂Ymem : x₂Y ∈ conjGen Lₐ := (ζ * t₀ : ↥(conjGen Lₐ)).2
    have haY : aY ∈ conjGen Lₐ := by
      have h1 : aY = (cY * ζY * cY⁻¹) * x₂Y⁻¹ := by
        rw [← hrel]
        group
      rw [h1]
      exact Subgroup.mul_mem _ (hXn.conj_mem _ hzX cY) (Subgroup.inv_mem _ hx₂Ymem)
    let aX : ↥(conjGen Lₐ) := ⟨aY, haY⟩
    have haX1 : aX = 1 :=
      C25I.eq_one_of_central (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hcen
        (fun v => Subtype.ext (Subtype.ext (hCa v))) (Subtype.ext (Subtype.ext ha2))
    apply ha1
    exact congrArg (fun x : ↥(conjGen Lₐ) => ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G))
      haX1
  exact ⟨t₀G, φ y, c₁G, hIS, hat₀, ⟨φ c, hCa c, hcG⟩, hc₁a, hyK, hy4G, hCa y, hyxG, hlast⟩



end Omega5

end CFSG.ClassicalInvolution.Asc77.C25J
