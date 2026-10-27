module

public import CFSG.ClassicalInvolution.Q3.Q3WANodes
public import CFSG.ClassicalInvolution.Q3.Q3WAMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

theorem ncard_centralizingMembers_eq3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) :
    (centralizingMembers Ω {x}).ncard = (locFamily Ω x).ncard := by
  have hinj : Set.InjOn (locImg Ω x) (centralizingMembers Ω {x}) :=
    fun L hL L' hL' h => locImg_injOn3 hΩ hex hP1 hO3 hL hL' h
  rw [locFamily_eq_image, hinj.ncard_image]

section Chain

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACore3.ncard_locFamily_le [Finite G] (c : ACore3 m Ω K z) :
    (locFamily Ω z).ncard ≤
      1 + (longRootSet (K := GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1)).ncard := by
  have hk : 2 ≤ m + 1 := by have := c.hm; omega
  have hsub : locFamily Ω z ⊆ insert c.d.Q₀
      ((fun R : Subgroup SL(m + 1, GaloisField 3 1) => R.map c.d.ψ) ''
        longRootSet (K := GaloisField 3 1) hk) := by
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
    (f := fun R : Subgroup SL(m + 1, GaloisField 3 1) => R.map c.d.ψ)
    (Set.toFinite (longRootSet (K := GaloisField 3 1) hk))
  have hins := Set.ncard_insert_le c.d.Q₀
    ((fun R : Subgroup SL(m + 1, GaloisField 3 1) => R.map c.d.ψ) ''
      longRootSet (K := GaloisField 3 1) hk)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem ACore3.typeA_centralizingMembers [Finite G] (c : ACore3 m Ω K z)
    {ψ : SL(m + 1 + 2, GaloisField 3 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField 3 1))
    (hΩψ : ∀ R ∈ longRootSet (K := GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1 + 2),
      R.map ψ ∈ Ω)
    {g₀ : G} (hg₀ : (rootSL2 (GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1 + 2)).map ψ =
      conjSub g₀ K) :
    centralizingMembers Ω {g₀ * z * g₀⁻¹} =
      insert ((rootSL2 (GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1 + 2)).map ψ)
        ((fun R => R.map (ψ.comp (tailBlock (GaloisField 3 1) (m + 1)))) ''
          longRootSet (K := GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1)) := by
  have hm := c.hm
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have h2 := two_ne_zero_gf3
  set F := GaloisField 3 1 with hF
  set N := (rootSL2 F hn).map ψ with hNdef
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩
  have hNm : N ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj c.hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hxN : g₀ * z * g₀⁻¹ ∈ N := by
    rw [hg₀]
    exact conj_mem_conjSub c.hz.mem
  have hmemΩ : ∀ R ∈ longRootSet (K := F) hk, R.map (ψ.comp (tailBlock F (m + 1))) ∈ Ω := by
    intro R hR
    have := hΩψ _ (map_tailBlock_mem_longRootSet h2 hk hR)
    rwa [Subgroup.map_map] at this
  have hcomm : ∀ R ∈ longRootSet (K := F) hk,
      Commutes (R.map (ψ.comp (tailBlock F (m + 1)))) N := by
    rintro R hR _ ⟨s, hs, rfl⟩ _ ⟨_, ⟨r, rfl⟩, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg ψ (tailBlock_commutes_rootSL2 hn s r)
  have h𝓡 : (fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk ⊆
      centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨hmemΩ R hR, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm R hR y hy _ hxN
  have hNR : N ∉ (fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk := by
    rintro ⟨R, hR, hRN⟩
    have h1 := hcomm R hR
    have hRN' : R.map (ψ.comp (tailBlock F (m + 1))) = N := hRN
    rw [hRN'] at h1
    have h2' : Commutes K K := by
      rw [hg₀] at h1
      exact (commutes_conjSub_iff g₀).mp h1
    exact not_commutes_self3 c.hz h2'
  have hinj : Function.Injective
      (fun R : Subgroup SL(m + 1, F) => R.map (ψ.comp (tailBlock F (m + 1)))) :=
    Subgroup.map_injective (injective_comp_tailBlock hker)
  have hcard : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤
      1 + ((fun R => R.map (ψ.comp (tailBlock F (m + 1)))) '' longRootSet (K := F) hk).ncard := by
    rw [Set.ncard_image_of_injective _ hinj, ncard_centralizingMembers_conj c.hΩ.conjInvariant,
      ncard_centralizingMembers_eq3 c.hΩ c.hex c.hP1 c.hO3]
    exact c.ncard_locFamily_le
  exact centralizingMembers_eq_insert hNm h𝓡 hNR hcard



theorem ACore3.typeA_closure [Finite G] (c : ACore3 m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ψ : SL(m + 1 + 2, GaloisField 3 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField 3 1))
    (hΩψ : ∀ R ∈ longRootSet (K := GaloisField 3 1) (by have := c.hm; omega : 2 ≤ m + 1 + 2),
      R.map ψ ∈ Ω) :
    ∀ N ∈ {L : Subgroup G | ∃ R ∈ longRootSet (K := GaloisField 3 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ}, ∀ L ∈ Ω, L ≠ N → Commutes N L →
      L ∈ {L : Subgroup G | ∃ R ∈ longRootSet (K := GaloisField 3 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ} := by
  have hm := c.hm
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  have h2 := two_ne_zero_gf3
  rintro N ⟨R₀, hR₀, rfl⟩ L hL hLN hcomm
  obtain ⟨g₁, rfl⟩ := (mem_longRootSet_iff hn).mp hR₀
  set F := GaloisField 3 1
  have hN₀Ω : (rootSL2 F hn).map ψ ∈ Ω := hΩψ _ ⟨_, isLongRootSL2_standard hn⟩
  obtain ⟨g₀, hg₀⟩ := hsingle _ hN₀Ω
  have hNeq : ((rootSL2 F hn).map (MulAut.conj g₁).toMonoidHom).map ψ =
      conjSub (ψ g₁) ((rootSL2 F hn).map ψ) := map_map_conj ψ g₁ _
  rw [hNeq] at hLN hcomm
  set L' := conjSub (ψ g₁)⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := c.hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub (ψ g₁) L' := (conjSub_conjSub_inv _ L).symm
  have hL'N : L' ≠ (rootSL2 F hn).map ψ := fun e => hLN (by rw [hLL', e])
  have hcomm' : Commutes ((rootSL2 F hn).map ψ) L' := by
    rw [hLL'] at hcomm
    exact (commutes_conjSub_iff _).mp hcomm
  have hxN : g₀ * z * g₀⁻¹ ∈ (rootSL2 F hn).map ψ := by
    rw [hg₀]; exact conj_mem_conjSub c.hz.mem
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' _ hxN y hy).symm⟩
  rw [c.typeA_centralizingMembers hker hΩψ hg₀] at hL'x
  rcases hL'x with h | ⟨R', hR', hRL'⟩
  · exact absurd h hL'N
  · refine ⟨((R'.map (tailBlock F (m + 1))).map (MulAut.conj g₁).toMonoidHom), ?_, ?_⟩
    · exact longRootSet_conjInvariant hn g₁ _ (map_tailBlock_mem_longRootSet h2 hk hR')
    · have hRL'' : (R'.map (tailBlock F (m + 1))).map ψ = L' := by
        rw [Subgroup.map_map]; exact hRL'
      rw [map_map_conj, hRL'']
      exact hLL'



theorem ACore3.typeA_of_chain [Finite G] (c : ACore3 m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : RouteD.DeltaConnected Ω)
    (U : Fin (m + 2) → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ ψ : SL(m + 1 + 2, GaloisField 3 1) →* G, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField 3 1) ∧
      (∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ longRootSet (K := GaloisField 3 1)
        (by have := c.hm; omega : 2 ≤ m + 1 + 2), L = R.map ψ) ∧
      CFSG.IsQuasisimple G ∧ CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (m + 1 + 2) 3 1 := by
  have hm1 : 1 ≤ m := by have := c.hm; omega
  have hn : 2 ≤ m + 1 + 2 := by have := c.hm; omega
  have h2 := two_ne_zero_gf3
  obtain ⟨ψ, hker, hrange, hblk⟩ := exists_psi_of_chain3 card_gf3 hm1 hcomm hpair
  set F := GaloisField 3 1
  have hU0 : (rootSL2 F hn).map ψ = U ⟨0, by omega⟩ := hblk ⟨0, by omega⟩
  have hΩψ : ∀ R ∈ longRootSet (K := F) hn, R.map ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hn).mp hR
    rw [map_map_conj, hU0]
    exact c.hΩ.conjInvariant _ _ (hUΩ _)
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ longRootSet (K := F) hn, L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨(rootSL2 F hn).map ψ, _, ⟨_, isLongRootSL2_standard hn⟩, rfl⟩
  have hcl := c.typeA_closure hsingle hker hΩψ
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  have hsurj : Function.Surjective ψ := by
    refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := c.hΩ.generated.symm
      _ ≤ ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range ψ R
  have htop : ⨆ i, U i = ⊤ := by
    rw [← hrange]
    exact MonoidHom.range_eq_top.mpr hsurj
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_three card_gf3
  obtain ⟨-, -, -, hqs, hmodel, -⟩ := weakCT3_recognition_blocks (X := G) (n := m + 2)
    (by omega) (U := U) hcomm
    (fun i j hj => (hpair i j hj).imp fun W hW =>
      WeakCT.LinearBlockStandardPair.of_ringEquiv e hW) htop
  exact ⟨ψ, hsurj, hker, fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩, hqs, hmodel⟩



end Chain

section Main

variable {G : Type} [Group G]

theorem routeD_typeA3 [Finite G] {m : ℕ} (hm : 6 ≤ m) {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K z) (d : ShapeADict 3 1 m Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) :
    ∃ ψ : SL(m + 1 + 2, GaloisField 3 1) →* G, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField 3 1) ∧
      (∀ L : Subgroup G, L ∈ Ω ↔ ∃ R ∈ longRootSet (K := GaloisField 3 1)
        (by omega : 2 ≤ m + 1 + 2), L = R.map ψ) ∧
      CFSG.IsQuasisimple G ∧ CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (m + 1 + 2) 3 1 := by
  let c : ACtx3 m Ω K z :=
    { hm := by omega, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, hO3 := hO3,
      d := d, hlift := Or.inl (by omega) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβΩ, hβcl, hnK, ⟨W1, hW1⟩, hnβ0, ⟨W2, hW2⟩, hlast, hmid⟩ :=
    c.exists_partner nd (by omega) hsingle
  have hsecond := c.commutes_beta_second_last nd hm hsingle hβΩ hβcl hnK hmid hlast
  let U : Fin (m + 2) → Subgroup G := fun i =>
    if i.val = 0 then K else if i.val = 1 then β else nd.j (i.val - 2)
  have hU : ∀ i : Fin (m + 2), (i.val = 0 ∧ U i = K) ∨ (i.val = 1 ∧ U i = β) ∨
      (∃ a, a < m ∧ i.val = a + 2 ∧ U i = nd.j a) := by
    intro i
    by_cases h0 : i.val = 0
    · exact Or.inl ⟨h0, by simp only [U, h0, ↓reduceIte]⟩
    · by_cases h1 : i.val = 1
      · exact Or.inr (Or.inl ⟨h1, by simp only [U, h1, one_ne_zero, ↓reduceIte]⟩)
      · refine Or.inr (Or.inr ⟨i.val - 2, by omega, by omega, ?_⟩)
        simp only [U, h0, h1, ↓reduceIte]
  refine c.toACore3.typeA_of_chain hsingle hconn U ?_ ?_ ?_
  · intro i
    rcases hU i with ⟨-, h⟩ | ⟨-, h⟩ | ⟨a, ha, -, h⟩
    · rw [h]; exact hK
    · rw [h]; exact hβΩ
    · rw [h]; exact (nd.mem a ha).1
  · intro i j hij
    rcases hU i with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨a, ha, hi, h⟩ <;>
    rcases hU j with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨b, hb, hj, h'⟩
    all_goals first | (exfalso; omega) | skip
    · rw [h, h']
      exact nd.commK b hb
    · rw [h, h']
      have hb1 : b = m - 1 ∨ b = m - 2 ∨ (1 ≤ b ∧ b ≤ m - 3) := by omega
      rcases hb1 with rfl | rfl | ⟨hb1, hb2⟩
      · exact hlast
      · exact hsecond
      · exact hmid b hb1 hb2
    · rw [h, h']
      exact nd.far a ha b hb (by omega)
  · intro i j hij
    rcases hU i with ⟨hi, h⟩ | ⟨hi, h⟩ | ⟨a, ha, hi, h⟩ <;>
    rcases hU j with ⟨hj, h'⟩ | ⟨hj, h'⟩ | ⟨b, hb, hj, h'⟩
    all_goals first | (exfalso; omega) | skip
    · rw [h, h']
      exact ⟨W1, hW1⟩
    · rw [h, h']
      have hb0 : b = 0 := by omega
      subst hb0
      exact ⟨W2, hW2⟩
    · rw [h, h']
      have hb : b = a + 1 := by omega
      subst hb
      exact nd.pair a hb


end Main

end CFSG.ClassicalInvolution.Q3.Q3W
