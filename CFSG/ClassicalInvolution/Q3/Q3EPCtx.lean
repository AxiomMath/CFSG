module

public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section DictConj

variable {G : Type} [Group G] {tY : StatedLieTag} {nY : ℕ}

noncomputable def ShapeDictT.conj3 {Ω : Set (Subgroup G)} {z : G} (hΩ : ConjInvariant Ω) (g : G)
    (d : ShapeDictT 3 1 tY nY Ω z) : ShapeDictT 3 1 tY nY Ω (g * z * g⁻¹) where
  ψ := (locQuotConj hΩ g z).toMonoidHom.comp d.ψ
  ker_le := by
    intro x hx
    refine d.ker_le ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (locQuotConj hΩ g z).injective (by simpa using hx)
  Q₀ := d.Q₀.map (locQuotConj hΩ g z).toMonoidHom
  commutes := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨y, rfl⟩
    have := d.commutes a ha (d.ψ y) ⟨y, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, this]
  mem_fam := fun R hR => by
    rw [← Gaps.locFamily_conj hΩ g z]
    exact ⟨R.map d.ψ, d.mem_fam R hR, Subgroup.map_map _ _ _⟩
  fam_cases := fun K' hK' => by
    rw [← Gaps.locFamily_conj hΩ g z] at hK'
    obtain ⟨K'', hK'', rfl⟩ := hK'
    rcases d.fam_cases K'' hK'' with h | ⟨R, hR, rfl⟩
    · exact Or.inl (Subgroup.map_mono h)
    · exact Or.inr ⟨R, hR, Subgroup.map_map _ _ _⟩
  card_le := by
    refine le_trans (le_of_eq ?_) d.card_le
    exact Nat.card_congr (d.Q₀.equivMapOfInjective (locQuotConj hΩ g z).toMonoidHom
      (locQuotConj hΩ g z).injective).toEquiv.symm

end DictConj

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem ETCtx3.exists_nodeSystem_D6' (c : ETCtx3 .POmegaPlus 6 Ω K z)
    (hadm : StatedLieAdmissible .POmegaPlus 6 3 1) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem 3 1 (edgeD 6) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 3 1 hp trivial hadm
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 6)
    (fun a => rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeD 6)
    (fun a b hab h1 h2 => commutes_rankOne_plusDatum (n := 6) (K := GaloisField 3 1)
      (by norm_num) (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1)
    (fun a b h => standardPair_plusDatum_edge (F := GaloisField 3 1) (by norm_num) h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

theorem ETCtx3.exists_nodeSystem_E7' (c : ETCtx3 .E7 0 Ω K z)
    (hadm : StatedLieAdmissible .E7 0 3 1) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem 3 1 (edgeE 7) Ω K z j ∧
      ∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hl := ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 3 1 hp trivial hadm
  have hdiv : (modelUniv .E7 0 3 1 Nat.prime_three).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E7 0 3 1 Nat.prime_three).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 7; decide⟩
  obtain ⟨j, hj, hcomm, hpair, hK⟩ := c.exists_nodes (r := 7)
    (fun a => rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a)
    (fun a => rankOne_mem_fundamental _ (hl a trivial)) (edgeE 7)
    (fun a b hab h1 h2 => commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))).2.2.1 a b hab h1 h2).1)
    (fun a b h => stdPair_edge_E7 h)
  exact ⟨j, ⟨fun a => (hj a).1, fun a => (hj a).2.1, hK, hcomm, hpair⟩, fun a => (hj a).2.2⟩

end Nodes

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem ETCtx3.locLayer_le_normalizer (c : ETCtx3 tY nY Ω K z) :
    locLayer Ω z ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLK : L = K
  · subst hLK
    exact Subgroup.le_normalizer
  · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (K : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => c.commutes_K_of_ne hL hLK k hk x hx

omit [Finite G] in
theorem ETCtx3.conjSub_layer_member (c : ETCtx3 tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) :
    conjSub t N ∈ centralizingMembers Ω {z} ∧ conjSub t N ≠ K := by
  refine ⟨TypeEPattern.conjSub_mem_centralizingMembers c.hΩ.conjInvariant htz hN, fun h => hNK ?_⟩
  have := congrArg (conjSub t) h
  rwa [TypeEPattern.conjSub_conjSub_self h2t, hKt] at this

theorem ETCtx3.locAut_mem_range (c : ETCtx3 tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY
      (modelUniv tY nY 3 1 Nat.prime_three).D, R.map c.d.ψ)
    (k : (modelUniv tY nY 3 1 Nat.prime_three).K) :
    Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      (R.map c.d.ψ).map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K⟩ := c.conjSub_layer_member htz h2t hKt hNz hNK
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K
    rw [← hNeq, Gaps.locAut_locImg c.hΩ.conjInvariant htz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

theorem ETCtx3.exists_ctx_member (c : ETCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {M : Subgroup G} (hM : M ∈ Ω) {x : G}
    (hx : IsClassicalMember3 M x) : Nonempty (ETCtx3 tY nY Ω M x) := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hzx : IsClassicalMember3 M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hxe : x = g * z * g⁻¹ := involution_unique3 hx hzx
  subst hxe
  exact ⟨{
    hΩ := c.hΩ
    hex := c.hex
    hK := hM
    hz := hzx
    hP1 := Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
    hO3 := localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
    d := ShapeDictT.conj3 c.hΩ.conjInvariant g c.d
    hY := c.hY }⟩

end Layer

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem ETCtx3.fixed_of_commutes (c : ETCtx3 tY nY Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    {β M : Subgroup G} (htβ : IsClassicalMember3 β t) (hM : M ∈ centralizingMembers Ω {z})
    (hMβ : Commutes β M) :
    ∀ x ∈ locImg Ω z M, Gaps.locAut c.hΩ.conjInvariant ht x = x :=
  (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht hM).mp fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t htβ.mem n hn).symm

theorem ETCtx3.commutes_partner_of_centralizes (c : ETCtx3 tY nY Ω K z)
    (hMFZ : Gaps.FundNoncentral 3) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNt : N ≤ Subgroup.centralizer ({t} : Set G))
    (hNK : Commutes K N) : Commutes β N := by
  obtain ⟨W, hW⟩ := hKβ
  have hnK : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  exact ((commutes_iff_le_centralizer3 hMFZ c.hΩ c.hex hP1t hO3t Dt hβ ht hN.1 hNK.symm
    hnK).mpr hNt).symm

end Partner

section Toral

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

@[expose] def ToralNormalE3 (c : ETCtx3 tY nY Ω K z) {t : G} (ht : t * z * t⁻¹ = z) : Prop :=
  ∃ (k₀ : (modelUniv tY nY 3 1 Nat.prime_three).K)
    (v : Fin (modelUniv tY nY 3 1 Nat.prime_three).D.rank → ZMod 2),
    ∀ γ ∈ (modelUniv tY nY 3 1 Nat.prime_three).D.roots,
      ((conjSub k₀ ((modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ).map
          (Gaps.locAut c.hΩ.conjInvariant ht).toMonoidHom =
        (conjSub k₀ ((modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ ∧
      ((∀ x ∈ (conjSub k₀ ((modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup γ ⊔
          (modelUniv tY nY 3 1 Nat.prime_three).D.rootGroup (-γ))).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

end Toral

end CFSG.ClassicalInvolution.Q3.Q3W
