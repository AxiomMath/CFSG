module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_sSup {S : Set (Subgroup G)} {t : G}
    (h : ∀ K ∈ S, t ∈ normalizer (K : Set G)) :
    t ∈ normalizer ((sSup S : Subgroup G) : Set G) := by
  have hle : ∀ g : G, (∀ K ∈ S, g ∈ normalizer (K : Set G)) →
      (sSup S).map (MulAut.conj g).toMonoidHom ≤ sSup S := by
    intro g hg
    rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    rintro _ ⟨k, hk, rfl⟩
    exact le_sSup hK ((mem_normalizer_iff.mp (hg K hK) k).mp hk)
  refine LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (hle t h)
    (hle t⁻¹ fun K hK => inv_mem (h K hK))

variable [Finite G]

theorem layer_le_normalizer {L : Subgroup G} (hL : IsComponent L) :
    layer G ≤ normalizer (L : Set G) :=
  CFSG.LocalCores.layer_le_normalizer hL

theorem not_le_coreActionKernel_of_isPComponent {L : Subgroup G} (hL : IsPComponent 2 L) :
    ¬ L ≤ coreActionKernel L := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, a, b, hab⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).mp hL
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  induction a using QuotientGroup.induction_on with
  | H u =>
  induction b using QuotientGroup.induction_on with
  | H v =>
  have hc : (QuotientGroup.mk u : L ⧸ pPrimeCore 2 L) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk u := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := (mem_coreActionKernel.mp (h u.2)).2 v v.2
    have : w = (u * v)⁻¹ * (v * u) := by
      apply Subtype.ext
      rw [show (w : G) = _ from hwe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [← this]
  rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul]

omit [Finite G] in
theorem le_coreActionKernel_of_commutator_le {L N : Subgroup G}
    (hN : N ≤ normalizer (L : Set G)) (hc : ⁅L, N⁆ ≤ (pPrimeCore 2 L).map L.subtype) :
    N ≤ coreActionKernel L := fun g hg =>
  mem_coreActionKernel.mpr ⟨hN hg, fun l hl => by
    have h := hc (commutator_mem_commutator (inv_mem hl) (inv_mem hg))
    rwa [commutatorElement_def, inv_inv, inv_inv] at h⟩

theorem le_or_le_of_isPComponent_centralizer {X Y M : Subgroup G} {t : G} (hXY : ⁅X, Y⁆ = ⊥)
    (hX : t ∈ normalizer (X : Set G)) (hY : t ∈ normalizer (Y : Set G))
    (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) (hMXY : M ≤ X ⊔ Y) :
    M ≤ X ∨ M ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hCdef
  set D := (X ⊓ C) ⊔ (Y ⊓ C) with hDdef
  have hperf : ⁅M, M⁆ = M :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hMC hM)
  have hMD : M ≤ D := by
    rw [← hperf]
    exact (commutator_mono (le_inf hMXY hMC) (le_inf hMXY hMC)).trans
      (LocalAnalysis.ComponentInitial.commutator_fixed_sup_le hXY hX hY)
  have hDC : D ≤ C := sup_le inf_le_right inf_le_right
  have hMD' : IsPComponent 2 (M.subgroupOf D) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hMD hDC hM
  have hXYC : ⁅X ⊓ C, Y ⊓ C⁆ = ⊥ :=
    eq_bot_iff.2 (hXY ▸ commutator_mono inf_le_left inf_le_left)
  have hnormX : D ≤ normalizer ((X ⊓ C : Subgroup G) : Set G) :=
    sup_le le_normalizer ((commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact hXYC)).trans (centralizer_le_normalizer _))
  have hnormY : D ≤ normalizer ((Y ⊓ C : Subgroup G) : Set G) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.1 hXYC).trans (centralizer_le_normalizer _))
      le_normalizer
  have hNX : ((X ⊓ C).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnormX
  have hNY : ((Y ⊓ C).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hnormY
  rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 (M.subgroupOf D)
      ((X ⊓ C).subgroupOf D) hMD' hNX.isSubnormal with h1 | ⟨h1n, h1⟩
  · exact Or.inl ((LocalCores.le_of_subgroupOf_le hMD h1).trans inf_le_left)
  rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 (M.subgroupOf D)
      ((Y ⊓ C).subgroupOf D) hMD' hNY.isSubnormal with h2 | ⟨h2n, h2⟩
  · exact Or.inr ((LocalCores.le_of_subgroupOf_le hMD h2).trans inf_le_left)
  exfalso
  have htop : (X ⊓ C).subgroupOf D ⊔ (Y ⊓ C).subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (le_sup_left : X ⊓ C ≤ D) (le_sup_right : Y ⊓ C ≤ D),
      subgroupOf_self]
  have hk : (⊤ : Subgroup D) ≤ coreActionKernel (M.subgroupOf D) := by
    rw [← htop]
    exact sup_le (le_coreActionKernel_of_commutator_le h1n h1)
      (le_coreActionKernel_of_commutator_le h2n h2)
  exact not_le_coreActionKernel_of_isPComponent hMD' (le_top.trans hk)

theorem exists_mem_le_of_le_sSup {M : Subgroup G} {t : G} (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) :
    ∀ (n : ℕ) (S : Finset (Subgroup G)), S.card ≤ n → (∀ K ∈ S, IsComponent K) →
      (∀ K ∈ S, t ∈ normalizer (K : Set G)) → M ≤ sSup (S : Set (Subgroup G)) →
        ∃ L ∈ S, M ≤ L := by
  classical
  have hMne : ∀ S : Finset (Subgroup G), M ≤ sSup (S : Set (Subgroup G)) → S.Nonempty := by
    intro S hS
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, sSup_empty, le_bot_iff] at hS
    have : Nontrivial M := B5a.nontrivial_of_isPComponent_subgroupOf hMC hM
    rw [hS] at this
    exact not_nontrivial _ this
  intro n
  induction n with
  | zero =>
    intro S hS _ _ hMS
    obtain ⟨K, hK⟩ := hMne S hMS
    exact absurd (Finset.card_pos.2 ⟨K, hK⟩) (by omega)
  | succ n ih =>
    intro S hS hcomp hnorm hMS
    obtain ⟨L, hL⟩ := hMne S hMS
    set S' := S.erase L with hS'def
    have hS'card : S'.card ≤ n := by
      rw [hS'def, Finset.card_erase_of_mem hL]
      omega
    have hsplit : sSup (S : Set (Subgroup G)) = L ⊔ sSup (S' : Set (Subgroup G)) := by
      conv_lhs => rw [← Finset.insert_erase hL]
      rw [Finset.coe_insert, sSup_insert]
    have hcommute : ⁅L, sSup (S' : Set (Subgroup G))⁆ = ⊥ := by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
      refine sSup_le fun K hK => ?_
      have hK' := Finset.mem_erase.1 hK
      rcases LocalCores.distinct_components_commute (hcomp K hK'.2) (hcomp L hL) with h | h
      · exact absurd h hK'.1
      · exact commutator_eq_bot_iff_le_centralizer.mp h
    have hnormS' : t ∈ normalizer ((sSup (S' : Set (Subgroup G)) : Subgroup G) : Set G) :=
      mem_normalizer_sSup fun K hK => hnorm K (Finset.mem_of_mem_erase hK)
    rw [hsplit] at hMS
    rcases le_or_le_of_isPComponent_centralizer hcommute (hnorm L hL) hnormS' hMC hM hMS with
      h | h
    · exact ⟨L, hL, h⟩
    · obtain ⟨L', hL', hML'⟩ := ih S' hS'card (fun K hK => hcomp K (Finset.mem_of_mem_erase hK))
        (fun K hK => hnorm K (Finset.mem_of_mem_erase hK)) h
      exact ⟨L', Finset.mem_of_mem_erase hL', hML'⟩

theorem exists_isComponent_le {M : Subgroup G} {t : G}
    (ht : ∀ L : Subgroup G, IsComponent L → t ∈ normalizer (L : Set G))
    (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G)))) (hME : M ≤ layer G) :
    ∃ L : Subgroup G, IsComponent L ∧ M ≤ L := by
  classical
  have : Finite (Subgroup G) := Finite.of_injective (fun K : Subgroup G => (K : Set G))
    SetLike.coe_injective
  set S₀ : Finset (Subgroup G) := (Set.toFinite {K : Subgroup G | IsComponent K}).toFinset
    with hS₀
  have hmem : ∀ K, K ∈ S₀ ↔ IsComponent K := fun K => by
    rw [hS₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsSup : sSup (S₀ : Set (Subgroup G)) = layer G := by
    rw [hS₀, Set.Finite.coe_toFinset]
    rfl
  obtain ⟨L, hL, hML⟩ := exists_mem_le_of_le_sSup hMC hM S₀.card S₀ le_rfl
    (fun K hK => (hmem K).1 hK) (fun K hK => ht K ((hmem K).1 hK)) (hsSup ▸ hME)
  exact ⟨L, (hmem L).1 hL, hML⟩

theorem le_of_isPComponent_of_perfect {C K L J : Subgroup G} (hKC : K ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hL : L.IsSubnormal) (hJK : J ≤ K) (hJL : J ≤ L)
    (hJ : ⁅J, J⁆ = J) (hJO : ¬ J ≤ (pPrimeCore 2 K).map K.subtype) : K ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 (K.subgroupOf C) (L.subgroupOf C) hK
      hL.subgroupOf with h | ⟨-, h⟩
  · exact LocalCores.le_of_subgroupOf_le hKC h
  refine absurd ?_ hJO
  rw [← hJ, commutator_le]
  intro x hx y hy
  have hxC : x ∈ C := hKC (hJK hx)
  have hyC : y ∈ C := hKC (hJK hy)
  have h1 := h (commutator_mem_commutator (show (⟨x, hxC⟩ : C) ∈ K.subgroupOf C from hJK hx)
    (show (⟨y, hyC⟩ : C) ∈ L.subgroupOf C from hJL hy))
  have h2 := mem_map_of_mem C.subtype h1
  rw [pPrimeCore_map_subgroupOf 2 K C hKC] at h2
  simpa only [commutatorElement_def, coe_subtype, coe_mul, coe_inv] using h2

end CFSG.ComponentClassification.GSThmB.Pump516
