module

public import CFSG.ClassicalInvolution.RouteD.TypeUBridge
public import CFSG.ClassicalInvolution.RouteD.GenerationA
public import CFSG.ClassicalInvolution.Phan.Main

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section Pairs

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem typeU_standardPair_eq_sup (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V) : W = U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  have hB : (B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, B12_sup_B23 hK hq]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hW : W = ((B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← hB, Subgroup.map_sup]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem typeU_map_codRestrict {G : Type*} [Group G] (θ : G →* X) (J : Subgroup X)
    (hJ : ∀ g, θ g ∈ J) (A : Subgroup G) :
    A.map (θ.codRestrict J hJ) = (A.map θ).subgroupOf J := by
  ext x
  simp only [Subgroup.mem_map, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, Subtype.ext h⟩

theorem typeU_standardPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : UnitaryBlockStandardPair K p f W U V) :
    UnitaryBlockStandardPair K p f (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict J hJ, c, ?_, ?_, ?_⟩
  · rw [← hrange]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, h⟩
      exact ⟨a, Subtype.ext h⟩
  · intro x hx
    apply hker
    simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [typeU_map_codRestrict, typeU_map_codRestrict, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [typeU_map_codRestrict, typeU_map_codRestrict, h1, h2]
      exact ⟨rfl, rfl⟩

end Pairs

section Recognition

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem weakPhan_recognition_blocks (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ ψ : Su K p f (n + 1) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su K p f (n + 1)) ∧
      ∀ i : Fin n, (blockEmb2 K p f n i).range.map ψ = U i := by
  obtain ⟨F, hFι, hFinj, -⟩ := coherent_family hK (by omega) hW
  obtain ⟨ψ, hψ2, -⟩ := phanUniversal K p f hK hq hn F
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hW.gen]
    refine iSup_le fun i => ?_
    rw [← hFι i, ← hψ2 i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : CFSG.IsQuasisimple (Su K p f (n + 1)) := by
    have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK
      (n := n + 1) (by omega) (by
        intro h
        have : n + 1 = 3 := (Prod.mk.inj h).1
        omega)).1
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK (n + 1))).symm h
  have hnontriv : ∃ k, ψ k ≠ 1 := by
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    have hsub : Subsingleton (Su K p f 2) := by
      refine ⟨fun a b => hFinj i ?_⟩
      rw [← hψ2 i, MonoidHom.comp_apply, MonoidHom.comp_apply, hall, hall]
    have hcard : Nat.card (Su K p f 2) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h1 : (1 : ℕ) < Nat.card (Su K p f 2) := by
      obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
      rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv P hP).toEquiv,
        CFSG.LieType.Steinberg.card_SU_two hK]
      have h24 : 24 ≤ (p ^ f) ^ 2 - 1 := by
        have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
        omega
      nlinarith
    omega
  refine ⟨ψ, hsurj, CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hquasi hnontriv, ?_⟩
  intro i
  rw [← MonoidHom.range_comp, hψ2 i, hFι i]

end Recognition

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem typeU_subgroupOf_sup_of_le {A B Y : Subgroup G} (hA : A ≤ Y) (hB : B ≤ Y) :
    (A ⊔ B).subgroupOf Y = A.subgroupOf Y ⊔ B.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, inf_eq_left.mpr hB,
    inf_eq_left.mpr (sup_le hA hB)]

theorem exists_psi_of_chainU (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m) {U : Fin (m + 2) → Subgroup G}
    (hiso : ∀ i, Nonempty (Su (GaloisField p (2 * f)) p f 2 ≃* U i))
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) :
    ∃ ψ : Su (GaloisField p (2 * f)) p f (m + 1 + 2) →* G,
      ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1 + 2)) ∧
      ψ.range = ⨆ i, U i ∧
      ∀ i : Fin (m + 2), (blockEmb2 (GaloisField p (2 * f)) p f (m + 2) i).range.map ψ = U i := by
  have hK := typeU_card_field (p := p) (f := f) hq
  have hq2 : p ^ f ≠ 2 := by omega
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  have hW : WeakPhanA (GaloisField p (2 * f)) p f (m + 2) (fun i => (U i).subgroupOf Gs)
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
  obtain ⟨ψ', hsurj, hker, hblk⟩ := weakPhan_recognition_blocks hK hq (n := m + 2) (by omega) hW
  refine ⟨Gs.subtype.comp ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro i
    rw [← Subgroup.map_map, hblk i, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle i)]

end Chain

section Consistency

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem typeU_centralizingMembers [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) {ψ : Su (GaloisField p (2 * f)) p f (m + 1 + 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1 + 2)))
    (hΩψ : ∀ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω) {g₀ : G}
    (hg₀ : (rootSU2 (GaloisField p (2 * f)) p f (by omega : 2 ≤ m + 1 + 2)).map ψ =
      conjSub g₀ K) :
    centralizingMembers Ω {g₀ * z * g₀⁻¹} =
      insert ((rootSU2 (GaloisField p (2 * f)) p f (by omega : 2 ≤ m + 1 + 2)).map ψ)
        ((fun R => R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) ''
          longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
            (by omega : 2 ≤ m + 1)) := by
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have hF := typeU_card_field (p := p) (f := f) hq
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  set N := (rootSU2 (GaloisField p (2 * f)) p f hn).map ψ with hNdef
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hNm : N ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hxN : g₀ * z * g₀⁻¹ ∈ N := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  have hmemΩ : ∀ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk,
      R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1))) ∈ Ω := by
    intro R hR
    have := hΩψ _ (map_tailBlockU_mem_longRootSetU h2 hk hR)
    rwa [Subgroup.map_map] at this
  have hcomm : ∀ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk,
      Commutes (R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) N := by
    rintro R hR _ ⟨s, hs, rfl⟩ _ ⟨_, ⟨r, rfl⟩, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg ψ (tailBlockU_commutes_rootSU2 s r)
  have h𝓡 : (fun R => R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) ''
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk ⊆
      centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨hmemΩ R hR, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm R hR y hy _ hxN
  have hNR : N ∉ (fun R => R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) ''
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk := by
    rintro ⟨R, hR, hRN⟩
    have h1 := hcomm R hR
    have hRN' : R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1))) = N := hRN
    rw [hRN'] at h1
    have h2' : Commutes K K := by
      rw [hg₀] at h1
      exact (commutes_conjSub_iff g₀).mp h1
    exact not_commutes_self_of_isClassicalMember hz h2'
  have hinj : Function.Injective
      (fun R : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1)) =>
        R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) :=
    Subgroup.map_injective (injective_comp_tailBlockU hF hq (by omega : 1 ≤ m + 1) hker)
  have hcard : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤
      1 + ((fun R => R.map (ψ.comp (tailBlockU (GaloisField p (2 * f)) p f (m + 1)))) ''
        longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hk).ncard := by
    rw [Set.ncard_image_of_injective _ hinj, ncard_centralizingMembers_conj hΩ.conjInvariant,
      ncard_centralizingMembers_eq hΩ hP1]
    exact hshape.ncard_locFamily_le hp2 hm
  exact centralizingMembers_eq_insert hNm h𝓡 hNR hcard

end Consistency

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem typeU_closure [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeU p f m Ω z) (hP1 : LocalOddCentral Ω {z})
    {ψ : Su (GaloisField p (2 * f)) p f (m + 1 + 2) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f (m + 1 + 2)))
    (hΩψ : ∀ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω) :
    ∀ N ∈ {L : Subgroup G | ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
        (by omega : 2 ≤ m + 1 + 2), L = R.map ψ}, ∀ L ∈ Ω, L ≠ N → Commutes N L →
      L ∈ {L : Subgroup G | ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
        (by omega : 2 ≤ m + 1 + 2), L = R.map ψ} := by
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  rintro N ⟨R₀, hR₀, rfl⟩ L hL hLN hcomm
  obtain ⟨g₁, rfl⟩ := (mem_longRootSetU_iff hn).mp hR₀
  set F := GaloisField p (2 * f)
  have hN₀Ω : (rootSU2 F p f hn).map ψ ∈ Ω := hΩψ _ ⟨_, isLongRootSU2_standard hn⟩
  obtain ⟨g₀, hg₀⟩ := hsingle _ hN₀Ω
  have hNeq : ((rootSU2 F p f hn).map (MulAut.conj g₁).toMonoidHom).map ψ =
      conjSub (ψ g₁) ((rootSU2 F p f hn).map ψ) := map_map_conj ψ g₁ _
  rw [hNeq] at hLN hcomm
  set L' := conjSub (ψ g₁)⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub (ψ g₁) L' := (conjSub_conjSub_inv _ L).symm
  have hL'N : L' ≠ (rootSU2 F p f hn).map ψ := fun e => hLN (by rw [hLL', e])
  have hcomm' : Commutes ((rootSU2 F p f hn).map ψ) L' := by
    rw [hLL'] at hcomm
    exact (commutes_conjSub_iff _).mp hcomm
  have hxN : g₀ * z * g₀⁻¹ ∈ (rootSU2 F p f hn).map ψ := by
    rw [hg₀]; exact conj_mem_conjSub hz.mem
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' _ hxN y hy).symm⟩
  rw [typeU_centralizingMembers hp2 hq hm hΩ hK hz hshape hP1 hker hΩψ hg₀] at hL'x
  rcases hL'x with h | ⟨R', hR', hRL'⟩
  · exact absurd h hL'N
  · refine ⟨((R'.map (tailBlockU F p f (m + 1))).map (MulAut.conj g₁).toMonoidHom), ?_, ?_⟩
    · exact longRootSetU_conjInvariant hn g₁ _ (map_tailBlockU_mem_longRootSetU h2 hk hR')
    · have hRL'' : (R'.map (tailBlockU F p f (m + 1))).map ψ = L' := by
        rw [Subgroup.map_map]; exact hRL'
      rw [map_map_conj, hRL'']
      exact hLL'

end Closure

section MemberIso

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

noncomputable def typeU_slEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    [DecidableEq (Fin n)] (r : R ≃+* S) : SL(n, R) ≃* SL(n, S) where
  toFun := Matrix.SpecialLinearGroup.map (r : R →+* S)
  invFun := Matrix.SpecialLinearGroup.map (r.symm : S →+* R)
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

theorem nonempty_su_two_equiv_of_member (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    Nonempty (Su (GaloisField p (2 * f)) p f 2 ≃* L) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hK := typeU_card_field (p := p) (f := f) hq
  obtain ⟨z', hz'⟩ := hΩ.classical L hL
  obtain ⟨e₁⟩ := hz'.nonempty_equiv_sl2 (hex L hL)
  obtain ⟨e₃⟩ := nonempty_sl2_mulEquiv_su_two (K := GaloisField p (2 * f)) (p := p) (f := f) hK
  have hcard : Nat.card (GaloisField p f) =
      Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * f)) p f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK, GaloisField.card p f hf]
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  let _ : Fintype (CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * f)) p f) :=
    Fintype.ofFinite _
  have hcard' : Fintype.card (GaloisField p f) =
      Fintype.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * f)) p f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let r := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨e₃.symm.trans ((typeU_slEquivOfRingEquiv r).symm.trans e₁.symm)⟩

end MemberIso

section Closing

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_lieSystemData_of_longRootSetU (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k)
    {Ω : Set (Subgroup G)} (ψ : Su (GaloisField p (2 * f)) p f k →* G)
    (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f k))
    (hΩ : ∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p)
      (f := f) (by omega : 2 ≤ k), L = R.map ψ) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = k := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU k p f := by
    refine ⟨Fact.out, by omega, hk, ?_⟩
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  have hk2 : 2 ≤ k := by omega
  refine ⟨{
    card := 1
    tag := fun _ => .PSU
    rank := fun _ => k
    exp := fun _ => f
    hom := fun _ => ψ.comp e.toMonoidHom
    isFundTag := fun _ => trivial
    admissible := fun _ => hadm
    exp_eq := fun _ => Or.inl rfl
    ker_le_center := ?_
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := ?_
    fundamental := ?_
    meets := ?_ }, rfl, 0, rfl, rfl⟩
  · intro _ x hx
    have h1 : e x ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f k) :=
      hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact h1 (e y)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨e.symm y, by simp⟩
  · intro L hL
    obtain ⟨R, hR, rfl⟩ := (hΩ L).mp hL
    refine ⟨0, R.map e.symm.toMonoidHom, (he _).mpr ?_, ?_⟩
    · rw [Subgroup.map_map]
      have : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id _ := by
        ext x; simp
      rw [this, Subgroup.map_id]
      exact hR
    · show R.map ψ = (R.map e.symm.toMonoidHom).map (ψ.comp e.toMonoidHom)
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp
  · intro i
    refine ⟨(rootSU2 (GaloisField p (2 * f)) p f hk2).map e.symm.toMonoidHom, (he _).mpr ?_, ?_⟩
    · rw [Subgroup.map_map]
      have : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id _ := by
        ext x; simp
      rw [this, Subgroup.map_id]
      exact ⟨_, isLongRootSU2_standard hk2⟩
    · rw [Subgroup.map_map]
      show ((rootSU2 (GaloisField p (2 * f)) p f hk2).map
        ((ψ.comp e.toMonoidHom).comp e.symm.toMonoidHom)) ∈ Ω
      have : ((ψ.comp e.toMonoidHom).comp e.symm.toMonoidHom) = ψ := by
        ext x; simp
      rw [this]
      exact (hΩ _).mpr ⟨_, ⟨_, isLongRootSU2_standard hk2⟩, rfl⟩

end Closing

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem routeD_typeU_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin (m + 2) → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = m + 3 := by
  have hn : 2 ≤ m + 1 + 2 := by omega
  set F := GaloisField p (2 * f)
  obtain ⟨ψ, hker, hrange, hblk⟩ := exists_psi_of_chainU (p := p) (f := f) hq hm
    (fun i => nonempty_su_two_equiv_of_member hq hΩ hex (hUΩ i)) hcomm hpair
  have hU0 : (rootSU2 F p f hn).map ψ = U ⟨0, by omega⟩ := hblk ⟨0, by omega⟩
  have hΩψ : ∀ R ∈ longRootSetU (K := F) (p := p) (f := f) hn, R.map ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, rfl⟩ := (mem_longRootSetU_iff hn).mp hR
    rw [map_map_conj, hU0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ longRootSetU (K := F) (p := p) (f := f) hn,
    L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨(rootSU2 F p f hn).map ψ, _, ⟨_, isLongRootSU2_standard hn⟩, rfl⟩
  have hcl := typeU_closure hp2 hq hm hΩ hK hz hsingle hshape hP1 hker hΩψ
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  refine exists_lieSystemData_of_longRootSetU hp2 hq (by omega : 3 ≤ m + 1 + 2) ψ ?_ hker ?_
  · refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
      _ ≤ ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range ψ R
  · intro L
    exact ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩

end Main

end CFSG.ClassicalInvolution.RouteD
