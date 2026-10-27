module

public import CFSG.ClassicalInvolution.Q3.Q3WAClose
public import CFSG.ClassicalInvolution.Q3.Q3URStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups commutatorElement

section Tail

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_scalar_of_mem_center_su3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {n : ℕ} (hn3 : 3 ≤ n) {z : Su K p f n} (hz : z ∈ Subgroup.center (Su K p f n)) :
    ∃ c : K, suMat z = Matrix.scalar (Fin n) c := by
  have hZ := (isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hK hn3
    (fun h => hq (Prod.mk.inj h).2)).2
  let e := MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)
  have hz' : e z ∈ Subgroup.center (StatedSU n (p ^ f) K) := by
    rw [← map_center_mulEquiv e]
    exact ⟨z, hz, rfl⟩
  rw [hZ, Subgroup.mem_subgroupOf] at hz'
  obtain ⟨c, hc⟩ := hz'
  refine ⟨(c : K), ?_⟩
  have : ((e z : StatedSU n (p ^ f) K) : GL (Fin n) K) = (z : GL (Fin n) K) := rfl
  rw [← Matrix.GeneralLinearGroup.coe_scalar]
  exact (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (hc.trans this)).symm

theorem tailBlockU_eq_one_of_mem_center3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {k : ℕ} (hk : 1 ≤ k) {s : Su K p f k}
    (hs : tailBlockU K p f k s ∈ Subgroup.center (Su K p f (k + 2))) : s = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_su3 hK hq (by omega : 3 ≤ k + 2) hs
  have h0 : suMat (tailBlockU K p f k s) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    rw [tailBlockU, suMat_blockEmb, blockMat_apply_of_not_mem_left _ (by simp)]
    simp
  have hc1 : c = 1 := by
    rw [hc] at h0
    simpa [Matrix.scalar_apply] using h0
  apply tailBlockU_injective k
  rw [map_one]
  apply suMat_injective
  rw [hc, hc1, map_one, suMat_one]

theorem injective_comp_tailBlockU3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {k : ℕ}
    (hk : 1 ≤ k) {H : Type} [Group H] {ψ : Su K p f (k + 2) →* H}
    (hker : ψ.ker ≤ Subgroup.center (Su K p f (k + 2))) :
    Function.Injective (ψ.comp (tailBlockU K p f k)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  exact tailBlockU_eq_one_of_mem_center3 hK hq hk (hker (MonoidHom.mem_ker.mpr hs))

end Tail

structure UCore3 (m : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) where
  hm : 2 ≤ m
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hK : K ∈ Ω
  hz : IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeUDict 3 1 m Ω z

section Chain

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCore3.ncard_locFamily_le [Finite G] (c : UCore3 m Ω K z) :
    (locFamily Ω z).ncard ≤
      1 + (longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
        (by have := c.hm; omega : 2 ≤ m + 1)).ncard := by
  have hk : 2 ≤ m + 1 := by have := c.hm; omega
  have hsub : locFamily Ω z ⊆ insert c.d.Q₀
      ((fun R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1)) => R.map c.d.ψ) ''
        longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk) := by
    intro K' hK'
    rcases c.d.fam_cases hk K' hK' with h | ⟨R, hR, rfl⟩
    · left
      obtain ⟨L, hL, rfl⟩ := mem_locFamily_iff.mp hK'
      have hcL := card_locImg3 c.hΩ c.hex hL
      have hcard := c.d.card_le
      rw [card_sl2_gf3] at hcard
      exact Subgroup.eq_of_le_of_card_ge h (by rw [hcL]; exact hcard)
    · exact Or.inr ⟨R, hR, rfl⟩
  have himg := Set.ncard_image_le
    (f := fun R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1)) => R.map c.d.ψ)
    (Set.toFinite (longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk))
  have hins := Set.ncard_insert_le c.d.Q₀
    ((fun R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1)) => R.map c.d.ψ) ''
      longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem UCore3.typeU_centralizingMembers [Finite G] (c : UCore3 m Ω K z)
    {ψ : Su (GaloisField 3 2) 3 1 (m + 1 + 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1 + 2)))
    (hΩψ : ∀ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
      (by have := c.hm; omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω) {g₀ : G}
    (hg₀ : (rootSU2 (GaloisField 3 2) 3 1 (by have := c.hm; omega : 2 ≤ m + 1 + 2)).map ψ =
      conjSub g₀ K) :
    centralizingMembers Ω {g₀ * z * g₀⁻¹} =
      insert ((rootSU2 (GaloisField 3 2) 3 1 (by have := c.hm; omega : 2 ≤ m + 1 + 2)).map ψ)
        ((fun R => R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) ''
          longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
            (by have := c.hm; omega : 2 ≤ m + 1)) := by
  have hm := c.hm
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have hF : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_of_charP_ne_two (K := GaloisField 3 2)
    (p := 3) (by norm_num)
  set N := (rootSU2 (GaloisField 3 2) 3 1 hn).map ψ with hNdef
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩
  have hNm : N ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj c.hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hxN : g₀ * z * g₀⁻¹ ∈ N := by
    rw [hg₀]
    exact conj_mem_conjSub c.hz.mem
  have hmemΩ : ∀ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk,
      R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1))) ∈ Ω := by
    intro R hR
    have := hΩψ _ (map_tailBlockU_mem_longRootSetU h2 hk hR)
    rwa [Subgroup.map_map] at this
  have hcomm : ∀ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk,
      Commutes (R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) N := by
    rintro R hR _ ⟨s, hs, rfl⟩ _ ⟨_, ⟨r, rfl⟩, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg ψ (tailBlockU_commutes_rootSU2 s r)
  have h𝓡 : (fun R => R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) ''
      longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk ⊆
      centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨hmemΩ R hR, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm R hR y hy _ hxN
  have hNR : N ∉ (fun R => R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) ''
      longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk := by
    rintro ⟨R, hR, hRN⟩
    have h1 := hcomm R hR
    have hRN' : R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1))) = N := hRN
    rw [hRN'] at h1
    have h2' : Commutes K K := by
      rw [hg₀] at h1
      exact (commutes_conjSub_iff g₀).mp h1
    exact not_commutes_self3 c.hz h2'
  have hinj : Function.Injective
      (fun R : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1)) =>
        R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) :=
    Subgroup.map_injective (injective_comp_tailBlockU3 hF (by norm_num) (by omega : 1 ≤ m + 1) hker)
  have hcard : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤
      1 + ((fun R => R.map (ψ.comp (tailBlockU (GaloisField 3 2) 3 1 (m + 1)))) ''
        longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hk).ncard := by
    rw [Set.ncard_image_of_injective _ hinj, ncard_centralizingMembers_conj c.hΩ.conjInvariant,
      ncard_centralizingMembers_eq3 c.hΩ c.hex c.hP1 c.hO3]
    exact c.ncard_locFamily_le
  exact centralizingMembers_eq_insert hNm h𝓡 hNR hcard

theorem UCore3.typeU_closure [Finite G] (c : UCore3 m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {ψ : Su (GaloisField 3 2) 3 1 (m + 1 + 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1 + 2)))
    (hΩψ : ∀ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
      (by have := c.hm; omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω) :
    ∀ N ∈ {L : Subgroup G | ∃ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ}, ∀ L ∈ Ω, L ≠ N → Commutes N L →
      L ∈ {L : Subgroup G | ∃ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ} := by
  have hm := c.hm
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_of_charP_ne_two (K := GaloisField 3 2)
    (p := 3) (by norm_num)
  rintro N ⟨R₀, hR₀, rfl⟩ L hL hLN hcomm
  obtain ⟨g₁, rfl⟩ := (mem_longRootSetU_iff hn).mp hR₀
  set F := GaloisField 3 2
  have hN₀Ω : (rootSU2 F 3 1 hn).map ψ ∈ Ω := hΩψ _ ⟨_, isLongRootSU2_standard hn⟩
  obtain ⟨g₀, hg₀⟩ := hsingle _ hN₀Ω
  have hNeq : ((rootSU2 F 3 1 hn).map (MulAut.conj g₁).toMonoidHom).map ψ =
      conjSub (ψ g₁) ((rootSU2 F 3 1 hn).map ψ) := map_map_conj ψ g₁ _
  rw [hNeq] at hLN hcomm
  set L' := conjSub (ψ g₁)⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := c.hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub (ψ g₁) L' := (conjSub_conjSub_inv _ L).symm
  have hL'N : L' ≠ (rootSU2 F 3 1 hn).map ψ := fun e => hLN (by rw [hLL', e])
  have hcomm' : Commutes ((rootSU2 F 3 1 hn).map ψ) L' := by
    rw [hLL'] at hcomm
    exact (commutes_conjSub_iff _).mp hcomm
  have hxN : g₀ * z * g₀⁻¹ ∈ (rootSU2 F 3 1 hn).map ψ := by
    rw [hg₀]; exact conj_mem_conjSub c.hz.mem
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' _ hxN y hy).symm⟩
  rw [c.typeU_centralizingMembers hker hΩψ hg₀] at hL'x
  rcases hL'x with h | ⟨R', hR', hRL'⟩
  · exact absurd h hL'N
  · refine ⟨((R'.map (tailBlockU F 3 1 (m + 1))).map (MulAut.conj g₁).toMonoidHom), ?_, ?_⟩
    · exact longRootSetU_conjInvariant hn g₁ _ (map_tailBlockU_mem_longRootSetU h2 hk hR')
    · have hRL'' : (R'.map (tailBlockU F 3 1 (m + 1))).map ψ = L' := by
        rw [Subgroup.map_map]; exact hRL'
      rw [map_map_conj, hRL'']
      exact hLL'

end Chain

section MemberIso

variable {G : Type} [Group G]

theorem nonempty_su_two_equiv_of_member3 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* L) := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨z', hz'⟩ := hΩ.classical L hL
  obtain ⟨e₁⟩ := hz'.nonempty_equiv_sl2 (hex L hL)
  obtain ⟨e₃⟩ := nonempty_sl2_mulEquiv_su_two (K := GaloisField 3 2) (p := 3) (f := 1) hK
  have hcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 2) 3 1) = 3 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    norm_num
  obtain ⟨r⟩ := nonempty_ringEquiv_zmod_three hcard
  exact ⟨e₃.symm.trans ((typeU_slEquivOfRingEquiv r).trans e₁.symm)⟩

end MemberIso

section Recognition

variable {G : Type} [Group G]

theorem map_codRestrict_subgroupOf3 {H : Type} [Group H] (Gs : Subgroup G) (θ : H →* G)
    (hθ : ∀ g, θ g ∈ Gs) (S : Subgroup H) :
    S.map (θ.codRestrict Gs hθ) = (S.map θ).subgroupOf Gs := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, Subtype.ext h⟩

theorem exists_psi_of_chainU3 (hP : Phan3Rec) {m : ℕ} (hm : 2 ≤ m) {U : Fin (m + 2) → Subgroup G}
    (hiso : ∀ i, Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* U i))
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j))
    (htriple : ∀ i j k : Fin (m + 2), (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
      ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G,
        θ.range = (U i ⊔ U j) ⊔ (U j ⊔ U k) ∧
          θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = U i ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = U j ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = U k) :
    ∃ ψ : Su (GaloisField 3 2) 3 1 (m + 1 + 2) →* G,
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1 + 2)) ∧ ψ.range = ⨆ i, U i ∧
      ∀ i : Fin (m + 2), (blockEmb2 (GaloisField 3 2) 3 1 (m + 2) i).range.map ψ = U i := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  have hW : WeakPhanA (GaloisField 3 2) 3 1 (m + 2) (fun i => (U i).subgroupOf Gs)
      (fun i j => (U i).subgroupOf Gs ⊔ (U j).subgroupOf Gs) :=
    { iso := fun i => ⟨((hiso i).some.trans (Subgroup.subgroupOfEquivOfLe (hUle i)).symm)⟩
      join := fun i j _ => rfl
      comm := fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy)
      pair := fun i j hj => by
        obtain ⟨W, hWp⟩ := hpair i j hj
        have hWe := typeU_standardPair_eq_sup hK hq2 hWp
        have := typeU_standardPair_subgroupOf (J := Gs)
          (hWe ▸ sup_le (hUle i) (hUle j)) hWp
        rw [hWe, typeU_subgroupOf_sup_of_le (hUle i) (hUle j)] at this
        exact this
      gen := iSup_subgroupOf_self U }
  have hT : Phan.Q3G.AdjacentTripleBlocks (GaloisField 3 2) 3 1 (fun i => (U i).subgroupOf Gs)
      (fun i j => (U i).subgroupOf Gs ⊔ (U j).subgroupOf Gs) := by
    intro i j k hj hk
    obtain ⟨θ, hrange, hker, b₀, b₁, b₂⟩ := htriple i j k hj hk
    have hle : (U i ⊔ U j) ⊔ (U j ⊔ U k) ≤ Gs :=
      sup_le (sup_le (hUle i) (hUle j)) (sup_le (hUle j) (hUle k))
    have hθ : ∀ g, θ g ∈ Gs := fun g => hle (hrange ▸ ⟨g, rfl⟩)
    refine ⟨θ.codRestrict Gs hθ, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : (θ.codRestrict Gs hθ).range = ((U i ⊔ U j) ⊔ (U j ⊔ U k)).subgroupOf Gs := by
        rw [← hrange]
        ext x
        simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨a, rfl⟩
        · rintro ⟨a, h⟩
          exact ⟨a, Subtype.ext h⟩
      rw [h1, typeU_subgroupOf_sup_of_le (sup_le (hUle i) (hUle j)) (sup_le (hUle j) (hUle k)),
        typeU_subgroupOf_sup_of_le (hUle i) (hUle j),
        typeU_subgroupOf_sup_of_le (hUle j) (hUle k)]
    · intro x hx
      apply hker
      simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
    · rw [map_codRestrict_subgroupOf3, b₀]
    · rw [map_codRestrict_subgroupOf3, b₁]
    · rw [map_codRestrict_subgroupOf3, b₂]
  obtain ⟨ψ', hsurj, hker, hblk⟩ := hP (n := m + 2) (by omega) hW hT
  refine ⟨Gs.subtype.comp ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro i
    rw [← Subgroup.map_map, hblk i, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle i)]

end Recognition

section Main

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCore3.typeU_of_chain [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hP : Phan3Rec) (c : UCore3 m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : RouteD.DeltaConnected Ω) (U : Fin (m + 2) → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j))
    (htriple : ∀ i j k : Fin (m + 2), (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
      ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G,
        θ.range = (U i ⊔ U j) ⊔ (U j ⊔ U k) ∧
          θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = U i ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = U j ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = U k) :
    ∃ ψ : Su (GaloisField 3 2) 3 1 (m + 1 + 2) →* G, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (m + 1 + 2)) ∧
      (∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ) ∧
      CFSG.Blueprint.OddLieType G := by
  have hm := c.hm
  have hn : 2 ≤ m + 1 + 2 := by omega
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨ψ, hker, hrange, hblk⟩ := exists_psi_of_chainU3 hP hm
    (fun i => nonempty_su_two_equiv_of_member3 c.hΩ c.hex (hUΩ i))
    hcomm hpair htriple
  set F := GaloisField 3 2
  have hU0 : (rootSU2 F 3 1 hn).map ψ = U ⟨0, by omega⟩ := hblk ⟨0, by omega⟩
  have hΩψ : ∀ R ∈ longRootSetU (K := F) (p := 3) (f := 1) hn, R.map ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, rfl⟩ := (mem_longRootSetU_iff hn).mp hR
    rw [map_map_conj, hU0]
    exact c.hΩ.conjInvariant _ _ (hUΩ _)
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ longRootSetU (K := F) (p := 3) (f := 1) hn,
    L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨(rootSU2 F 3 1 hn).map ψ, _, ⟨_, isLongRootSU2_standard hn⟩, rfl⟩
  have hcl := c.typeU_closure hsingle hker hΩψ
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  have hsurj : Function.Surjective ψ := by
    refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := c.hΩ.generated.symm
      _ ≤ ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range ψ R
  obtain ⟨-, -, -, hodd⟩ := unitary_simple_central_quotient_native_model (GaloisField 3 2) 3 1 hK
    (by norm_num) (n := m + 2) (by omega) hnab ψ hsurj hker
  exact ⟨ψ, hsurj, hker, fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩, hodd⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
