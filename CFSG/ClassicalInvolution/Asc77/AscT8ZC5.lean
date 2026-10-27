module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC2

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

theorem z_not_central [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t) :
    ¬ ({z} : Set G) ⊆ Subgroup.center G := by
  intro hc
  have hz : z ∈ Subgroup.center G := hc rfl
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem
    hs.hz
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
  · exact hs.hz.ne_one (by rw [h] at hz; simpa using hz)
  · have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.1 hb a)
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcomm
    exact hKs inferInstance

theorem xMem_z_K (hs : Std8 p f Ω K J S R T W z t) : T8.XMem Ω z K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  refine ⟨hK, ?_, R, T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hs.hR.1 hs.hR.2.1, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  · have h := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]

theorem xMem_z_of_nbr (hs : Std8 p f Ω K J S R T W z t) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) : T8.XMem Ω z M := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨P, hP, hPz, hzN⟩ := exists_xMem_of_omegaNbr hp hq hΩ hnt hs.hz hM
  exact ⟨hM.1, hzN, P, hP, hPz⟩

theorem omegaNbr_of_xMem_z (hs : Std8 p f Ω K J S R T W z t) {L : Subgroup G}
    (hL : T8.XMem Ω z L) (hne : L ≠ K) : L ∈ omegaNbr Ω K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hLΩ, -, P, hP, hPz⟩ := hL
  refine ⟨hLΩ, hne, P, mem_RSet_of_isSylow2In hLΩ hP, hP.1, fun r hr => ?_⟩
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
    (Subgroup.mem_centralizer_singleton_iff.mpr (hPz r hr))

theorem exists_xMem_of_mem_layerFamQ {x : G} {C : Subgroup (T8.LayerQuot Ω x)}
    (hC : C ∈ T8.layerFamQ Ω x) : ∃ L, T8.XMem Ω x L ∧ T8.layerImg Ω x L = C := by
  obtain ⟨_, ⟨_, ⟨L, hL, rfl⟩, -, rfl⟩, rfl⟩ := hC
  exact ⟨L, hL, rfl⟩

theorem z_mem_layerJoin_z (hs : Std8 p f Ω K J S R T W z t) : z ∈ T8.layerJoin Ω z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hK := xMem_z_K hs
  have hRK : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hs.hR.1 hs.hR.2.1
  have hRa : R ≤ T8.cenZ z := fun r hr => by
    rw [T8.mem_cenZ_iff]
    have h := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]
  have hL := hK.isSylow2In_layerRes_of_le hp hq hΩ hz2 hRK hRa
  have h8 := hΩ.eight_le_of_mem_RSet hp hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRK.2.1 (by omega)
  exact T8.le_layerJoin ⟨K, hK, rfl⟩ (hL.1 hzR)

theorem layerImg_z_normal (hs : Std8 p f Ω K J S R T W z t) (g : T8.LayerQuot Ω z) :
    conjSub g (T8.layerImg Ω z K) = T8.layerImg Ω z K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hz2 : z * z = 1 := hs.hz.sq
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hzY := z_mem_layerJoin_z hs
  have hXK := xMem_z_K hs
  have hLY : T8.layerRes z K ≤ T8.layerJoin Ω z := T8.le_layerJoin ⟨K, hXK, rfl⟩
  have huniq : IsUniqueInvolution (T8.layerImg Ω z K) (T8V.layerMk z z hzY) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf (hXK.isUniqueInvolution_layerRes hp hq hΩ hz2 hs.hz) hLY)
  have hcen : ∀ g' : T8.LayerQuot Ω z, g' * T8V.layerMk z z hzY = T8V.layerMk z z hzY * g' := by
    intro g'
    obtain ⟨g'', rfl⟩ := QuotientGroup.mk_surjective g'
    have hg : (g'' : G) ∈ T8.cenZ z := T8.layerJoin_le_cenZ z g''.2
    have hcz : (g'' : G) * z = z * g'' := T8.mem_cenZ_iff.mp hg
    have hc2 : g'' * (⟨z, hzY⟩ : ↥(T8.layerJoin Ω z)) = ⟨z, hzY⟩ * g'' :=
      Subtype.ext (by simpa using hcz)
    change QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω z)) g'' *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω z)) ⟨z, hzY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω z)) ⟨z, hzY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω z)) g''
    rw [← map_mul, ← map_mul, hc2]
  have hgz : g * T8V.layerMk z z hzY * g⁻¹ = T8V.layerMk z z hzY := by
    rw [hcen g]
    group
  have hΨ := T8.hypOmegaMod_layerQuot hp hq hΩ hz2
  have hnt' := T8.noTwins_layerQuot hp hq hΩ hnt hz2
  have hkΨ := T8.layerImg_mem hXK
  have h1 := huniq.conj g
  rw [hgz] at h1
  exact hnt' _ hkΨ _ ⟨hΨ.conjInvariant g _ hkΨ, _, huniq, h1⟩

theorem layerImg_nbr_ne_z (hs : Std8 p f Ω K J S R T W z t) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) :
    T8.layerImg Ω z M ≠ T8.layerImg Ω z K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨s, hs'⟩ := hΩ.exists_uniqueInvolution hp hq hM.1
  have hzs : z * s = s * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hM hs'
  exact T8.layerImg_ne_of_involutions hp hq hΩ hs.hz.sq (xMem_z_of_nbr hs hM) (xMem_z_K hs)
    hs' hs.hz hzs.symm (T8.ne_of_mem_omegaNbr hs.noTwins hM hs.hz hs').symm

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
