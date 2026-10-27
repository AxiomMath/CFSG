module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_map_conj_le {K M : Subgroup G}
    (h : ∀ g ∈ K, M.map (MulAut.conj g).toMonoidHom ≤ M) :
    K ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (h g hg) ?_
  intro x hx
  have h2 : (MulAut.conj g⁻¹).toMonoidHom x ∈ M := h g⁻¹ (K.inv_mem hg) ⟨x, hx, rfl⟩
  exact ⟨_, h2, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem oddOrderSubgroup_le (H : Subgroup G) : oddOrderSubgroup H ≤ H :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem oddOrderSubgroup_map_mulEquiv (φ : G ≃* G) (H : Subgroup G) :
    (oddOrderSubgroup H).map φ.toMonoidHom = oddOrderSubgroup (H.map φ.toMonoidHom) := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hx, by simpa using hodd⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by simpa using hodd⟩, rfl⟩

theorem normalizer_le_normalizer_oddOrderSubgroup (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddOrderSubgroup H : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv oddOrderSubgroup_map_mulEquiv H

theorem exists_pow_mem_oddOrderSubgroup [Finite G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    ∃ k : ℕ, h ^ (2 ^ k) ∈ oddOrderSubgroup H := by
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  refine ⟨k, Subgroup.subset_closure ⟨H.pow_mem hh _, ?_⟩⟩
  have : orderOf (h ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  rwa [this]

theorem mem_of_odd_orderOf_of_pow_mem {D : Subgroup G} {y : G} (hy : Odd (orderOf y)) {k : ℕ}
    (hk : y ^ (2 ^ k) ∈ D) : y ∈ D := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hy)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact D.pow_mem hk m

theorem oddOrderSubgroup_le_of_pow_mem {H D : Subgroup G}
    (hD : ∀ h ∈ H, ∃ k : ℕ, h ^ (2 ^ k) ∈ D) : oddOrderSubgroup H ≤ D :=
  (Subgroup.closure_le D).mpr fun y hy => by
    obtain ⟨k, hk⟩ := hD y hy.1
    exact mem_of_odd_orderOf_of_pow_mem hy.2 hk

theorem hasNoTwoQuotient_oddOrderSubgroup (H : Subgroup G) :
    HasNoTwoQuotient (oddOrderSubgroup H) := by
  intro N _ hN
  rw [eq_top_iff]
  have hgen : oddOrderSubgroup H ≤ N.map (oddOrderSubgroup H).subtype := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    have hyK : y ∈ oddOrderSubgroup H := Subgroup.subset_closure hy
    obtain ⟨k, hk⟩ := hN (QuotientGroup.mk (⟨y, hyK⟩ : oddOrderSubgroup H))
    have hmem : (⟨y, hyK⟩ : oddOrderSubgroup H) ^ (2 ^ k) ∈ N := by
      rwa [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have hodd : Odd (orderOf (⟨y, hyK⟩ : oddOrderSubgroup H)) := by
      rw [Subgroup.orderOf_mk]
      exact hy.2
    exact ⟨_, mem_of_odd_orderOf_of_pow_mem hodd hmem, rfl⟩
  intro x _
  obtain ⟨n, hn, hnx⟩ := hgen x.2
  have : n = x := Subtype.ext hnx
  exact this ▸ hn

theorem oddOrderSubgroup_eq_twoResidual [Finite G] (H : Subgroup G) :
    oddOrderSubgroup H = twoResidual H := by
  have hHK : H ≤ Subgroup.normalizer (oddOrderSubgroup H : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddOrderSubgroup H)
  exact le_antisymm
    (oddOrderSubgroup_le_of_pow_mem (twoResidual_isTwoQuotient H))
    (twoResidual_le_of_isTwoQuotient (oddOrderSubgroup_le H) hHK
      fun _ hh => exists_pow_mem_oddOrderSubgroup hh)

theorem minParabolic_of_uniqueMax [Finite G] {H T X : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTn : ¬ H ≤ Subgroup.normalizer (T : Set G)) (hTX : T ≤ X) (hXH : X < H)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ X) : MinParabolic H T X := by
  have hmaxX : IsMaxSubgroupIn H X := by
    refine ⟨hXH, fun K hXK hKH => ?_⟩
    by_contra hne
    exact absurd (hmax K (hTX.trans hXK.le) (lt_of_le_of_ne hKH hne)) (not_le_of_gt hXK)
  refine ⟨hT, hTn, isUniqueMaxOver_iff.mpr ⟨hmaxX, hTX, fun N hN hTN => ?_⟩⟩
  have hNX : N ≤ X := hmax N hTN hN.1
  by_contra hne
  exact absurd (hN.2 X (lt_of_le_of_ne hNX hne) hXH.le) (ne_of_lt hXH)

theorem minParabolic_of_isMinimalParabolic [Finite G] {S P : Subgroup G}
    (h : IsMinimalParabolic S P) : MinParabolic P S (uniqueMaxOver S P) := by
  obtain ⟨hSI, hIP, hmax⟩ := uniqueMaxOver_spec h
  exact minParabolic_of_uniqueMax h.1 h.2.1 hSI hIP hmax

theorem ReducedAction.minParabolic {G : Type} [Group G] [Finite G] {S P V : Subgroup G}
    (hR : ReducedAction G S P V) : MinParabolic P S (uniqueMaxOver S P) :=
  minParabolic_of_isMinimalParabolic hR.obstruction.minParabolic

theorem FFActor.minParabolic {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (h : FFActor V H T M E) : MinParabolic H T M :=
  minParabolic_of_uniqueMax h.sylow
    (fun hle => h.not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer h.sylow.1).mpr hle))
    h.max.1 h.max.2.1 h.max.2.2

section Reduced

variable [Finite G]

theorem reduced_detects_commutator {H T X V : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTn : ¬ H ≤ Subgroup.normalizer (T : Set G)) (hTX : T ≤ X) (hXH : X < H)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ X)
    (hV : IsTwoReducedIn H V) (hVH : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    H = oddOrderSubgroup H ⊔ T ∧ HasNoTwoQuotient (oddOrderSubgroup H) ∧
      H ⊓ Subgroup.centralizer (V : Set G) ≤ X ∧
      T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H ∧
      ∀ A : Subgroup G, A ≤ T → T ≤ Subgroup.normalizer (A : Set G) →
        (⁅oddOrderSubgroup H, A⁆ < oddOrderSubgroup H ↔ A ≤ pCoreOf 2 H) ∧
        (A ≤ pCoreOf 2 H ↔ A ≤ Subgroup.centralizer (V : Set G)) := by
  have hmp := minParabolic_of_uniqueMax hT hTn hTX hXH hmax
  have hK := oddOrderSubgroup_eq_twoResidual H
  refine ⟨?_, hasNoTwoQuotient_oddOrderSubgroup H,
    (hmp.inf_centralizer_le_kerIn hV hVH).trans kerIn_le, hmp.inf_centralizer_eq_pCoreOf hV hVH,
    fun A hAT hTA => ⟨?_, ?_⟩⟩
  · rw [hK, sup_comm]
    exact (sup_twoResidual_eq hT).symm
  · rw [hK]
    exact hmp.commutator_lt_iff_le_pCoreOf hAT hTA
  · rw [hmp.le_pCoreOf_iff_le_centralizer hV hVH A, le_inf_iff]
    exact ⟨fun h => h.2, fun h => ⟨hAT, h⟩⟩

theorem reduced_detects_commutator_thompsonJ {H T X V : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTn : ¬ H ≤ Subgroup.normalizer (T : Set G)) (hTX : T ≤ X) (hXH : X < H)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ X)
    (hV : IsTwoReducedIn H V) (hVH : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    (⁅oddOrderSubgroup H, thompsonJ T⁆ < oddOrderSubgroup H ↔ thompsonJ T ≤ pCoreOf 2 H) ∧
      (thompsonJ T ≤ pCoreOf 2 H ↔ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :=
  (reduced_detects_commutator hT hTn hTX hXH hmax hV hVH).2.2.2.2 (thompsonJ T)
    (B6.thompsonJ_le T) (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T))

end Reduced

end CFSG.QuasithinUnique.Setup
