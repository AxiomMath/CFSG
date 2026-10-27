module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigC2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem secImg_conjSub_eq_or (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hStar : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y →
      2 < Nat.card ↥(L ⊓ (P : Subgroup Y)) → y = t ∨ y = u)
    {U₀ : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}
    (hU₀K : U₀ ≤ secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R))
    (hU₀ : 2 < Nat.card ↥U₀)
    (hU₀N : U₀ ≤ pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)))
    {c : Y} (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y)) :
    secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (conjSub c (tightCore R)) =
        secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ∨
      secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (conjSub c (tightCore R)) =
        secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J := by
  have hcl : ConjInvariant (CoreAssembly.conjClass (tightCore R)) :=
    hs.large.datum.hypOmegaGen.conjInvariant
  have hmap : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (conjSub c (tightCore R)) =
      (secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)).map
        (secAct hcl hc).toMonoidHom :=
    secImg_conjSub_eq_map hcl hc (tightCore R)
  set σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) :=
    secAct hcl hc with hσ
  set U₁ : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) :=
    U₀.map σ.toMonoidHom with hU₁
  have hU₁K' : U₁ ≤ secImg (CoreAssembly.conjClass (tightCore R)) (t * u)
      (conjSub c (tightCore R)) := by
    rw [hU₁, hmap]
    exact Subgroup.map_mono hU₀K
  have hcardmap : Nat.card ↥(U₀.map σ.toMonoidHom) = Nat.card ↥U₀ :=
    Subgroup.card_map_of_injective σ.injective
  have hU₁card : 2 < Nat.card ↥U₁ := by
    rw [hU₁, hcardmap]
    exact hU₀
  have hU₁N : U₁ ≤ pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    rw [hU₁]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar :
        (pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    calc U₀.map σ.toMonoidHom
        ≤ (pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))).map
            σ.toMonoidHom := Subgroup.map_mono hU₀N
      _ ≤ pCore 2 (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
          rw [Subgroup.map_le_iff_le_comap, hchar.fixed σ]
  obtain ⟨P₂, hP₂, hP₂P, hpc⟩ := exists_sylow_image hs
  have hU₁inf : U₁ ≤ secImg (CoreAssembly.conjClass (tightCore R)) (t * u)
      (conjSub c (tightCore R)) ⊓
      P₂.map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) (t * u)))) :=
    le_inf hU₁K' (hU₁N.trans hpc)
  have hinfcard : 2 < Nat.card ↥(secImg (CoreAssembly.conjClass (tightCore R)) (t * u)
      (conjSub c (tightCore R)) ⊓
      P₂.map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) (t * u))))) :=
    lt_of_lt_of_le hU₁card (Subgroup.card_le_of_le hU₁inf)
  obtain ⟨ν, hν, hνcard⟩ :=
    exists_conj_lt_card_inf (conjSub c (tightCore R)) hP₂ (k := 2) hinfcard
  have hPcard : 2 < Nat.card ↥(conjSub (ν : Y) (conjSub c (tightCore R)) ⊓
      (P : Subgroup Y)) :=
    lt_of_lt_of_le hνcard (Subgroup.card_le_of_le (inf_le_inf_left _ hP₂P))
  have hK0Ω : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hKcΩ : conjSub c (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) :=
    hcl c (tightCore R) hK0Ω
  have hLΩ : conjSub (ν : Y) (conjSub c (tightCore R)) ∈
      CoreAssembly.conjClass (tightCore R) :=
    hcl (ν : Y) (conjSub c (tightCore R)) hKcΩ
  have ht : IsUniqueInvolution (tightCore R) t := hs.large.datum.isUniqueInvolution_core
  have hy : IsUniqueInvolution (conjSub (ν : Y) (conjSub c (tightCore R)))
      (ν * (c * t * c⁻¹) * (ν : Y)⁻¹) :=
    (ht.conj c).conj (ν : Y)
  rcases hStar (conjSub (ν : Y) (conjSub c (tightCore R))) hLΩ
      (ν * (c * t * c⁻¹) * (ν : Y)⁻¹) hy hPcard with hyt | hyu
  · left
    have hy_t : IsUniqueInvolution (conjSub (ν : Y) (conjSub c (tightCore R))) t :=
      (congrArg (fun z => IsUniqueInvolution
        (conjSub (ν : Y) (conjSub c (tightCore R))) z) hyt).mp hy
    have hL_eq : conjSub (ν : Y) (conjSub c (tightCore R)) = tightCore R :=
      (TightLargeHypR.typeRFam hs.large).noTwins (tightCore R) hK0Ω
        (conjSub (ν : Y) (conjSub c (tightCore R)))
        ⟨hLΩ, t, ht, hy_t⟩
    rw [(secImg_conj_of_mem hν (conjSub c (tightCore R))).symm, hL_eq]
  · right
    have hy_u : IsUniqueInvolution (conjSub (ν : Y) (conjSub c (tightCore R))) u :=
      (congrArg (fun z => IsUniqueInvolution
        (conjSub (ν : Y) (conjSub c (tightCore R))) z) hyu).mp hy
    have hL_eq : conjSub (ν : Y) (conjSub c (tightCore R)) = J :=
      (TightLargeHypR.typeRFam hs.large).noTwins J hs.hJ.1
        (conjSub (ν : Y) (conjSub c (tightCore R)))
        ⟨hLΩ, u, hs.hu, hy_u⟩
    rw [(secImg_conj_of_mem hν (conjSub c (tightCore R))).symm, hL_eq]

theorem c264One_of_secInO2_star (hr : 4 ≤ r) (h4 : Thm4RBelow r n)
    (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hStar : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y →
      2 < Nat.card ↥(L ⊓ (P : Subgroup Y)) → y = t ∨ y = u)
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t) :
    C264One (CoreAssembly.conjClass (tightCore R)) t u := by
  obtain ⟨W, hW⟩ := exists_std8 hs
  obtain ⟨U₀, hU₀K, hU₀, hU₀N⟩ := exists_core_le_pCore hr h4 hs hO2
  exact hW.c264One_of_conj fun c hc => secImg_conjSub_eq_or hs hStar hU₀K hU₀ hU₀N hc

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264
