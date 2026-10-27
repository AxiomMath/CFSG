module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OrbB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

theorem E3.exists_sylow_le_centralizer_of_conj {G : Type} [Group G] [Finite G] {r : ℕ}
    {Ω : Set (Subgroup G)} (h : TypeRFam r Ω) {a u : G} (ha : a * a = 1) {X J : Subgroup G}
    (hJΩ : J ∈ Ω) (hu : IsUniqueInvolution J u) (hc : ∀ y ∈ X, ⁅a, y⁆ ∈ oddCoreOf X)
    (hOu : oddCoreOf X ≤ Subgroup.centralizer ({u} : Set G)) {l : G} (hl : l ∈ X)
    (hMX : conjSub l J ≤ X) :
    ∃ P : Subgroup G, IsSylow2In P (conjSub l J) ∧ P ≤ Subgroup.centralizer ({a} : Set G) := by
  set O := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    mem_normalizer_of_conjSub_eq (E3.conjSub_oddCoreOf hl)
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := Balance.isPGroup_zpowers_of_mul_self_eq_one ha
  have hcomm : ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ O := fun x hx => by
    have := hc x hx
    rwa [commutatorElement_def] at this
  have haO : ∀ x ∈ O, a * x * a⁻¹ ∈ O := fun x hx => by
    have e : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact O.mul_mem (hcomm x (hOX hx)) hx
  have hMΩ : conjSub l J ∈ Ω := h.hyp.conjInvariant l J hJΩ
  have hz : IsUniqueInvolution (conjSub l J) (l * u * l⁻¹) := hu.conj l
  have hON : O ≤ Subgroup.normalizer (conjSub l J : Set G) := by
    intro o ho
    apply h.tight _ hMΩ _ hz
    have ho' : l⁻¹ * o * l ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hl)) o).mp ho
      simpa using this
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hOu ho')
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc o * (l * u * l⁻¹) = l * ((l⁻¹ * o * l) * u) * l⁻¹ := by group
      _ = l * (u * (l⁻¹ * o * l)) * l⁻¹ := by rw [h1]
      _ = l * u * l⁻¹ * o := by group
  exact E3.exists_sylow_le_centralizer_of_modOdd hOodd hON ha2 haO
    (fun x hx => hcomm x (hMX hx))

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.omegaNbr_subset_orbOf_L (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) L ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hc : ConjInvariant Ω := hF.large.datum.hypOmegaGen.conjInvariant
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  obtain ⟨g, hgJ, hgK, -⟩ := hF.exists_conj_edge' hLπ
  have hO := hF.omegaNbr_subset_orbOf htu ht h163
  have e := E3.orbOf_conj hc hJΩ (tightCore R) g
  rw [hgJ, hgK] at e
  intro M hM
  have hM' : conjSub g⁻¹ M ∈ omegaNbr Ω J := by
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  rw [e]
  exact ⟨_, hO hM', conjSub_conjSub_inv g M⟩

theorem E3Frame.omegaNbr_eq_of_cent (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (hLn : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hct : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
      ⁅t, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) L =
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have h := TightLargeHypR.typeRFam hF.large
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hLΩ : L ∈ Ω := by
    obtain ⟨x, -, hxL⟩ := hLπ
    rw [← hxL]
    exact hc x _ hK₀Ω
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have hsub : omegaNbr Ω L ⊆ omegaNbr Ω (tightCore R) := by
    intro M hM
    have hMπ := hF.omegaNbr_subset_orbOf_L htu ht h163 hLπ hM
    obtain ⟨l, hl, hlM⟩ := hF.exists_conj_of_mem_orbOf_L hLπ hMπ
    have hMX : conjSub l J ≤ E3.orbGen Ω L J := by
      rw [hlM]
      exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) L J) => N) M hMπ
    obtain ⟨P, hP, hPt⟩ := E3.exists_sylow_le_centralizer_of_conj h ht2 hJΩ hF.inv hct
      (hF.oddCoreOf_orbGen_le_centralizer hLπ) hl hMX
    rw [hlM] at hP
    refine ⟨hM.1, ?_, P, mem_RSet_of_isSylow2In hM.1 hP, hP.1,
      hPt.trans (h.tight _ hK₀Ω t hd.isUniqueInvolution_core)⟩
    rintro rfl
    exact hLn (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hLΩ hK₀Ω hM)
  obtain ⟨x, -, hxL⟩ := hLπ
  have himg : omegaNbr Ω L = conjSub x '' omegaNbr Ω (tightCore R) := by
    ext M
    constructor
    · intro hM
      refine ⟨conjSub x⁻¹ M, ?_, conjSub_conjSub_inv x M⟩
      have h1 := omegaNbr_conj hc hM x⁻¹
      rwa [← hxL, conjSub_inv_conjSub] at h1
    · rintro ⟨M, hM, rfl⟩
      have h1 := omegaNbr_conj hc hM x
      rwa [hxL] at h1
  have hcard : (omegaNbr Ω L).ncard = (omegaNbr Ω (tightCore R)).ncard := by
    rw [himg]
    exact Set.ncard_image_of_injective _ (conjSub_injective x)
  have : Finite (Subgroup Y) :=
    Finite.of_injective (fun H : Subgroup Y => (H : Set Y)) SetLike.coe_injective
  exact Set.eq_of_subset_of_ncard_le hsub hcard.symm.le (Set.toFinite _)

@[expose] def TightE3S3NotBeta (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
        L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
          L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
            omegaNbr (CoreAssembly.conjClass (tightCore R)) L ≠
              omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)

theorem tightE3S3Cent_of_notBeta {n : ℕ} (hB : TightE3S3NotBeta n) : TightE3S3Cent n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2 h163 L hLπ hLs hLn
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  obtain ⟨g, hgJ, hgK, hgt⟩ := hF.exists_conj_edge' hLπ
  have hJt : J ≤ Subgroup.centralizer ({t} : Set Y) :=
    edge_le_centralizer_of_alpha hd hJn hF.inv (hF.alpha J hJn u hF.inv)
  have hLΩ : L ∈ Ω := hLs.1
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := Q3T6.Mu.omegaStarNbr_symm hΩG hK₀Ω hLΩ hLs
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  have htU : t ∈ U := T3.mem_of_isPGroup hd.isUniqueInvolution_core hUK
    (Sec6Gen.isPGroup_of_mem_USet hΩG hU) (le_trans (by norm_num) hU4)
  have htL : conjSub t L = L := mem_normalizer_iff_conjSub_eq.mp (hUN htU)
  set t₀ := g⁻¹ * t * g with ht₀def
  have ht₀J : conjSub t₀ J = J := by
    rw [ht₀def, conjSub_mul, conjSub_mul, hgJ, htL, ← hgJ, conjSub_inv_conjSub]
  have ht₀C : t₀ ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hF.inv.conj_eq ht₀J
    calc t₀ * u = t₀ * u * t₀⁻¹ * t₀ := by group
      _ = u * t₀ := by rw [h1]
  have ht₀K : ∀ k ∈ tightCore R, t₀ * k * t₀⁻¹ = k := by
    intro k hk
    have hkJ : g * k * g⁻¹ ∈ J := by
      rw [← hgK]
      exact conj_mem_conjSub hk
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hJt hkJ)
    calc t₀ * k * t₀⁻¹ = g⁻¹ * (t * (g * k * g⁻¹)) * t⁻¹ * g := by rw [ht₀def]; group
      _ = g⁻¹ * ((g * k * g⁻¹) * t) * t⁻¹ * g := by rw [← h1]
      _ = k := by group
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have horb : conjSub g (E3.orbGen Ω J (tightCore R)) = E3.orbGen Ω L J := by
    rw [← E3.orbGen_conj hc hJΩ g, hgJ, hgK]
  rcases hF.cent_or_cent_conj htu ht h163 g ht2 ht₀C ht₀K with h | h
  · refine (hB Y R S t J u hF htu ht Sb hex hedge hμ hnE2 h163 L hLπ hLs hLn
      (hF.omegaNbr_eq_of_cent htu ht h163 hLπ hLn ?_)).elim
    rw [← horb]
    exact h
  · rw [hgt, horb] at h
    exact h

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
