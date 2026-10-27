module

public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.Q3.Q3WAClose
public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement

theorem pow3_of_mem_fundamental {t : StatedLieTag} {K : Type} [Group K] {D : UniversalRootDatum K}
    (hsc : FundamentalSingleClass t D) {R₀ : Subgroup K} (hR₀ : R₀ ∈ fundamentalSubgroups t D)
    (h₀ : Pow3 R₀) : ∀ R ∈ fundamentalSubgroups t D, Pow3 R := by
  intro R hR
  obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
  exact h₀.conjSub g

structure ExtModel3U (t tY : StatedLieTag) (T Y : LieUniversal) (a : ℕ) where
  Rθ : Subgroup T.K
  twin : Fin (a - 1) → Subgroup T.K
  Θ : Y.K →* T.K
  Rθ_mem : Rθ ∈ fundamentalSubgroups t T.D
  twin_mem : ∀ i, twin i ∈ fundamentalSubgroups t T.D
  Θ_ker : Θ.ker ≤ Subgroup.center Y.K
  Θ_mem : ∀ R ∈ fundamentalSubgroups tY Y.D, R.map Θ ∈ fundamentalSubgroups t T.D
  Θ_comm : ∀ R ∈ fundamentalSubgroups tY Y.D, Commutes (R.map Θ) Rθ
  twin_comm : ∀ i, Commutes (twin i) Rθ
  twin_comm_Θ : ∀ i, ∀ R ∈ fundamentalSubgroups tY Y.D, Commutes (twin i) (R.map Θ)
  twin_inj : Function.Injective twin
  pow_T : ∀ R ∈ fundamentalSubgroups t T.D, Pow3 R
  pow_Y : ∀ R ∈ fundamentalSubgroups tY Y.D, Pow3 R
  cop_T : ∀ z ∈ Subgroup.center T.K, ¬ 3 ∣ orderOf z
  cop_Y : ∀ z ∈ Subgroup.center Y.K, ¬ 3 ∣ orderOf z

section Assemble

variable {t tY : StatedLieTag} {T Y : LieUniversal}

theorem nonempty_extModel3U_one (hscT : FundamentalSingleClass t T.D)
    (hscY : FundamentalSingleClass tY Y.D) {R₀T : Subgroup T.K}
    (hR₀T : R₀T ∈ fundamentalSubgroups t T.D) (hpT : Pow3 R₀T) {R₀Y : Subgroup Y.K}
    (hR₀Y : R₀Y ∈ fundamentalSubgroups tY Y.D) (hpY : Pow3 R₀Y) {Rθ : Subgroup T.K}
    (hRθ : Rθ ∈ fundamentalSubgroups t T.D) (Θ : Y.K →* T.K) (hker : Θ.ker ≤ Subgroup.center Y.K)
    (hΘ₀ : R₀Y.map Θ ∈ fundamentalSubgroups t T.D) (hcomm : Commutes Θ.range Rθ)
    (hcopT : ∀ z ∈ Subgroup.center T.K, ¬ 3 ∣ orderOf z)
    (hcopY : ∀ z ∈ Subgroup.center Y.K, ¬ 3 ∣ orderOf z) :
    Nonempty (ExtModel3U t tY T Y 1) := by
  refine ⟨{
    Rθ := Rθ
    twin := fun i => Fin.elim0 i
    Θ := Θ
    Rθ_mem := hRθ
    twin_mem := fun i => Fin.elim0 i
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := fun i => Fin.elim0 i
    twin_comm_Θ := fun i => Fin.elim0 i
    twin_inj := fun i => Fin.elim0 i
    pow_T := pow3_of_mem_fundamental hscT hR₀T hpT
    pow_Y := pow3_of_mem_fundamental hscY hR₀Y hpY
    cop_T := hcopT
    cop_Y := hcopY }⟩
  · intro R hR
    obtain ⟨g, rfl⟩ := hscY R₀Y hR₀Y R hR
    rw [← CFSG.ClassicalInvolution.Generic.conjSub_map]
    exact conjSub_mem_fundamentalSubgroups hΘ₀ (Θ g)
  · intro R hR a ha b hb
    exact hcomm a (Subgroup.map_le_range Θ R ha) b hb

end Assemble


theorem LocalShapeC3.ncard_locFamily_le {G : Type} [Group G] [Finite G] {a : ℕ} {c : CompData}
    {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeC3 a c Ω x) (hfin : Finite c.G) :
    (locFamily Ω x).ncard ≤ a + c.fund.ncard := by
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := h
  have hfinS : Finite c.G := hfin
  let cc : ι → Subgroup (locQuot Ω x) := fun i => (D.hom i).range
  have hΦ : locFamily Ω x ⊆
      {K | ∃ R ∈ (D.kind i₁).fund, K = R.map (D.hom i₁)} ∪ cc '' {i : ι | i ≠ i₁} := by
    intro K hK
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K hK
    by_cases hi : i = i₁
    · subst hi
      exact Or.inl ⟨R, hR, rfl⟩
    · right
      have key : ∀ c' : CompData, c' = CompData.sl23 → ∀ (φ : c'.G →* locQuot Ω x)
          (R : Subgroup c'.G), R ∈ c'.fund → R.map φ = φ.range := by
        rintro c' rfl φ R hR'
        have : R = ⊤ := hR'
        rw [this, Subgroup.map_top]
      exact ⟨i, hi, (key _ (hrest i hi) (D.hom i) R hR).symm⟩
  have hcomp : {K | ∃ R ∈ (D.kind i₁).fund, K = R.map (D.hom i₁)}.ncard ≤ c.fund.ncard := by
    have key : ∀ c' : CompData, c' = c → Finite c'.G → ∀ φ : c'.G →* locQuot Ω x,
        {K | ∃ R ∈ c'.fund, K = R.map φ}.ncard ≤ c.fund.ncard := by
      rintro c' rfl hf φ
      have himg : {K | ∃ R ∈ c'.fund, K = R.map φ} = (fun R => R.map φ) '' c'.fund := by
        ext K
        constructor
        · rintro ⟨R, hR, rfl⟩
          exact ⟨R, hR, rfl⟩
        · rintro ⟨R, hR, rfl⟩
          exact ⟨R, hR, rfl⟩
      rw [himg]
      exact Set.ncard_image_le (Set.toFinite _)
    exact key _ hk (hk ▸ hfinS) (D.hom i₁)
  have hcr : (cc '' {i : ι | i ≠ i₁}).ncard ≤ a := by
    calc (cc '' {i : ι | i ≠ i₁}).ncard ≤ ({i : ι | i ≠ i₁} : Set ι).ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ = a := by
          have h1 : ({i : ι | i ≠ i₁} : Set ι) = Set.univ \ {i₁} := by
            ext i
            simp
          rw [h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ i₁), Set.ncard_univ, hcard]
          omega
  calc (locFamily Ω x).ncard
      ≤ ({K | ∃ R ∈ (D.kind i₁).fund, K = R.map (D.hom i₁)} ∪ cc '' {i : ι | i ≠ i₁}).ncard :=
        Set.ncard_le_ncard hΦ (Set.toFinite _)
    _ ≤ {K | ∃ R ∈ (D.kind i₁).fund, K = R.map (D.hom i₁)}.ncard +
        (cc '' {i : ι | i ≠ i₁}).ncard := Set.ncard_union_le _ _
    _ ≤ a + c.fund.ncard := by omega

abbrev ExtModel3 (t : StatedLieTag) (n : ℕ) (tY : StatedLieTag) (nY a : ℕ) : Type :=
  ExtModel3U t tY (modelUniv t n 3 1 Nat.prime_three) (modelUniv tY nY 3 1 Nat.prime_three) a

section Core

variable {G : Type} [Group G] [Finite G]

theorem routeD_core3 {t : StatedLieTag} {n : ℕ} {tY : StatedLieTag} {nY a : ℕ} (ha : 1 ≤ a)
    (hscT : FundamentalSingleClass t (modelUniv t n 3 1 Nat.prime_three).D)
    (hfinY : Finite (modelUniv tY nY 3 1 Nat.prime_three).K) (M : ExtModel3 t n tY nY a)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hconn : RouteD.DeltaConnected Ω) {z : G} (hz : IsClassicalMember3 K₀ z)
    (hshape : LocalShapeC3 a (CompData.model tY nY) Ω z) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) (ψ : (modelUniv t n 3 1 Nat.prime_three).K →* G)
    (hker : ψ.ker ≤ Subgroup.center _)
    (hΩψ : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D, R.map ψ ∈ Ω) :
    Function.Surjective ψ ∧ ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D, L = R.map ψ := by
  classical
  have hcopψ : ∀ w ∈ ψ.ker, ¬ 3 ∣ orderOf w := fun w hw => M.cop_T w (hker hw)
  have hnc : ∀ L ∈ Ω, ¬ Commutes L L := fun L hL => by
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    exact not_commutes_self3 hw
  set N₀ : Subgroup G := M.Rθ.map ψ with hN₀
  have hN₀Ω : N₀ ∈ Ω := hΩψ _ M.Rθ_mem
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ hN₀Ω
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  set x : G := g₀ * z * g₀⁻¹ with hx
  have hK₀z : K₀ ∈ centralizingMembers Ω {z} := ⟨hK₀, isSubnormal_le hz.subnormal⟩
  have hN₀x : N₀ ∈ centralizingMembers Ω {x} := by
    rw [hx, centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K₀, hK₀z, hg₀.symm⟩
  set ΘΩ : Set (Subgroup G) := (fun R => (R.map M.Θ).map ψ) ''
    fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D with hΘΩ
  set TW : Set (Subgroup G) := (fun i => (M.twin i).map ψ) '' Set.univ with hTW
  set 𝓡 : Set (Subgroup G) := TW ∪ ΘΩ with h𝓡
  have hmem : ∀ S ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
      Commutes S M.Rθ → S.map ψ ∈ centralizingMembers Ω {x} := fun S hS hc =>
    mem_centralizingMembers_of_commutes (hΩψ S hS) hxN (commutes_map ψ hc)
  have h𝓡sub : 𝓡 ⊆ centralizingMembers Ω {x} := by
    rintro _ (⟨i, -, rfl⟩ | ⟨R, hR, rfl⟩)
    · exact hmem _ (M.twin_mem i) (M.twin_comm i)
    · exact hmem _ (M.Θ_mem R hR) (M.Θ_comm R hR)
  have hN₀R : N₀ ∉ 𝓡 := by
    have hnc₀ := hnc N₀ hN₀Ω
    rintro (⟨i, -, hi⟩ | ⟨R, hR, hRN⟩)
    · have hi' : (M.twin i).map ψ = N₀ := hi
      refine hnc₀ ?_
      have := commutes_map ψ (M.twin_comm i)
      rwa [hi'] at this
    · have hRN' : (R.map M.Θ).map ψ = N₀ := hRN
      refine hnc₀ ?_
      have := commutes_map ψ (M.Θ_comm R hR)
      rwa [hRN'] at this
  have hdisj : Disjoint TW ΘΩ := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, -, rfl⟩ ⟨R, hR, hRi⟩
    have hRi' : (R.map M.Θ).map ψ = (M.twin i).map ψ := hRi
    refine hnc _ (hΩψ _ (M.twin_mem i)) ?_
    have := commutes_map ψ (M.twin_comm_Θ i R hR)
    rwa [hRi'] at this
  have hTWinj : Function.Injective (fun i : Fin (a - 1) => (M.twin i).map ψ) := by
    intro i j hij
    exact M.twin_inj (eq_of_map_eq_of_pow3 ψ hker hcopψ (M.pow_T _ (M.twin_mem i))
      (M.pow_T _ (M.twin_mem j)) hij)
  have hΘinj : Set.InjOn (fun R => (R.map M.Θ).map ψ)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) := by
    intro R hR R' hR' h
    have h1 : R.map M.Θ = R'.map M.Θ :=
      eq_of_map_eq_of_pow3 ψ hker hcopψ ((M.pow_Y R hR).map M.Θ) ((M.pow_Y R' hR').map M.Θ) h
    exact eq_of_map_eq_of_pow3 M.Θ M.Θ_ker (fun w hw => M.cop_Y w (M.Θ_ker hw))
      (M.pow_Y R hR) (M.pow_Y R' hR') h1
  have hTWcard : TW.ncard = a - 1 := by
    rw [hTW, Set.ncard_image_of_injective _ hTWinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hΘcard : ΘΩ.ncard =
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D).ncard := by
    rw [hΘΩ, hΘinj.ncard_image]
  have h𝓡card : 𝓡.ncard = (a - 1) +
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D).ncard := by
    rw [h𝓡, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hTWcard, hΘcard]
  have hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard := by
    rw [hx, ncard_centralizingMembers_conj hΩ.conjInvariant,
      ncard_centralizingMembers_eq3 hΩ hex hP1 hO3, h𝓡card]
    have h3 : (locFamily Ω z).ncard ≤
        a + (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D).ncard :=
      hshape.ncard_locFamily_le hfinY
    omega
  have hEq : centralizingMembers Ω {x} = insert N₀ 𝓡 :=
    centralizingMembers_eq_insert hN₀x h𝓡sub hN₀R hcard
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ fundamentalSubgroups t
      (modelUniv t n 3 1 Nat.prime_three).D, L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨N₀, M.Rθ, M.Rθ_mem, rfl⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨R, hR, rfl⟩ L hL hLN hcomm
    obtain ⟨h, hh⟩ := hscT M.Rθ M.Rθ_mem R hR
    have hNeq : R.map ψ = conjSub (ψ h) N₀ := by
      rw [hh, hN₀, conjSub_map]
    set L' := conjSub (ψ h)⁻¹ L with hL'
    have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
    have hLL' : L = conjSub (ψ h) L' := (conjSub_conjSub_inv _ L).symm
    have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hNeq, hLL', e])
    have hcomm' : Commutes N₀ L' := by
      rw [hNeq, hLL'] at hcomm
      exact (commutes_conjSub_iff _).mp hcomm
    have hL'x : L' ∈ centralizingMembers Ω {x} :=
      mem_centralizingMembers_of_commutes hL'Ω hxN hcomm'.symm
    rw [hEq] at hL'x
    rcases hL'x with h1 | h1
    · exact absurd h1 hL'N
    · obtain ⟨S, hS, hSL'⟩ : ∃ S ∈ fundamentalSubgroups t
          (modelUniv t n 3 1 Nat.prime_three).D, L' = S.map ψ := by
        rcases h1 with ⟨i, -, hi⟩ | ⟨R', hR', hR'L'⟩
        · exact ⟨M.twin i, M.twin_mem i, hi.symm⟩
        · exact ⟨R'.map M.Θ, M.Θ_mem R' hR', hR'L'.symm⟩
      refine ⟨conjSub h S, conjSub_mem_fundamentalSubgroups hS h, ?_⟩
      rw [hLL', hSL', conjSub_map]
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  refine ⟨?_, fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩⟩
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range ψ R

end Core

end CFSG.ClassicalInvolution.Q3.Q3W
