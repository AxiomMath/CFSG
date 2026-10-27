module

public import CFSG.LargeExtraspecial.S14SMKDeltaBasic
public import CFSG.LargeExtraspecial.S14SMKDeltaLin
public import CFSG.LargeExtraspecial.S14SMKLbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.LargeExtraspecial.SMod20
  CFSG.RankThree.OrthogonalInvolutions QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Rank

theorem card_le_of_isElementaryAbelian (ψ : Mbar0 S ≃* T46) (E : Subgroup S.Mbar)
    [CFSG.IsElementaryAbelian 2 E] : Nat.card E ≤ 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : IsPGroup 2 (E.map (planeHom S ψ)) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 E).map _
  obtain ⟨i, hi⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Fin 891)
    (by rw [Nat.card_fin]; decide)
  have hfix : ∀ m ∈ E, planeHom S ψ m i = i := fun m hm => hi ⟨planeHom S ψ m, m, hm, rfl⟩
  have : CFSG.IsElementaryAbelian 2 (E.map (piM S ψ)) := CFSG.IsElementaryAbelian.map _
  have hle := rank_le_nine (E := E.map (piM S ψ)) i.2 ?_ ?_ ?_
  · rwa [card_map_of_injective (piM_injective ψ)] at hle
  · rintro _ ⟨m, -, rfl⟩
    exact piM_mem_normalizer ψ m
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_stabilizer_wPlane, image_wPlane_piM, hfix m hm]
  · rintro _ ⟨⟨m, -, rfl⟩, hc⟩
    rw [← UAloc_eq_UA i.2]
    refine autPerm_mem_UAloc_of_commute i.2 (mbarHom S ψ m) fun u hu => ?_
    rw [UAloc_eq_UA i.2] at hu
    exact ((mem_centralizer_iff.mp hc) u hu).symm

theorem card_le_of_isElementaryAbelian' (ψ : Mbar0 S ≃* T46) {E : Subgroup S.O}
    (hE : E ≤ S.Mbar) [CFSG.IsElementaryAbelian 2 E] : Nat.card E ≤ 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 (E.subgroupOf S.Mbar) := CFSG.IsElementaryAbelian.subgroupOf hE
  have h := card_le_of_isElementaryAbelian ψ (E.subgroupOf S.Mbar)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv] at h

end Rank

theorem card_L0_ge (S : Setting G) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG) : 2 ^ S.width ≤ Nat.card (S.L0 g) := by
  have hzM : S.z ∈ (S.conjBy g).M :=
    mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm
  have h := card_centralizer_ge (S.conjBy g) hzM (z_not_mem_Qa S hxQ) S.z_sq
  rwa [S.width_conjBy g] at h

theorem ρ_fix_of_Dl_eq_bot (S : Setting G) {g : G}
    (hbot : S.QG ⊓ S.Qa g = ⊥)
    (hfix : S.fixQt (g * S.z * g⁻¹) =
      S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)))
    {k : G} (hk : k ∈ S.L0 g) {c : S.Qt} (hc : c ∈ S.fixQt (g * S.z * g⁻¹)) :
    ((S.ρ ⟨k, hk.2⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := by
  rw [hfix] at hc
  obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hc
  have h1 := commutator_mem_Dl S hk ⟨huQ, hu.2⟩
  rw [hbot, mem_bot] at h1
  have e : k * u * k⁻¹ = u := by
    calc k * u * k⁻¹ = k * u * k⁻¹ * u⁻¹ * u := by group
      _ = u := by rw [h1, one_mul]
  rw [S.ρ_cl ⟨k, hk.2⟩ huQ]
  exact congrArg S.cl e

theorem isElementaryAbelian_Lbar_of_Dl_eq_bot (S : Setting G) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hbot : S.QG ⊓ S.Qa g = ⊥)
    (hfix : S.fixQt (g * S.z * g⁻¹) =
      S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G))) :
    CFSG.IsElementaryAbelian 2 (S.Lbar g) := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hC : LinearMap.BilinForm.orthogonal S.q.polarBilin (S.fixQt (g * S.z * g⁻¹)) ≤
      S.fixQt (g * S.z * g⁻¹) := by
    rw [← S.commQt_eq_orthogonal hxM hx2]
    exact S.commQt_le_fixQt hxM hx2
  have key : ∀ m ∈ S.Lbar g, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      TauCeti.QuadraticMap.orthogonalGroup S.q ∧
      ∀ c ∈ S.fixQt (g * S.z * g⁻¹), (m : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := by
    rintro _ ⟨⟨k, hkM⟩, hkL, rfl⟩
    exact ⟨(S.ρ _).2, fun c hc => ρ_fix_of_Dl_eq_bot S hbot hfix (mem_subgroupOf.mp hkL) hc⟩
  refine { is_comm := ⟨fun u v => ?_⟩, exponent_dvd_p := ?_ }
  · obtain ⟨hu1, hu2⟩ := key u u.2
    obtain ⟨hv1, hv2⟩ := key v v.2
    apply Subtype.ext
    apply Subtype.ext
    exact commute_of_fix hu1 hv1 hC hu2 hv2
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
    obtain ⟨hu1, hu2⟩ := key u u.2
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, pow_two]
    exact mul_self_of_fix hu1 hC hu2

theorem QG_inf_Qa_ne_bot (ψ : Mbar0 S ≃* T46) (hw : S.width = 10) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hno : ¬ ∃ y ∈ S.QG, y * (g * S.z * g⁻¹) * y⁻¹ = g * S.z * g⁻¹ * S.z) :
    S.QG ⊓ S.Qa g ≠ ⊥ := by
  intro hbot
  have hfix : S.fixQt (g * S.z * g⁻¹) =
      S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) := by
    by_contra h
    exact hno (S.lemma_3_2_1 hxM h)
  have := isElementaryAbelian_Lbar_of_Dl_eq_bot S hxM hbot hfix
  have h1 := card_le_of_isElementaryAbelian' ψ (S.Lbar_le_Mbar g)
  have h2 := S.card_Lbar_mul g
  rw [hbot, card_bot, mul_one] at h2
  have h3 := card_L0_ge S hxM hxQ
  rw [hw, ← h2] at h3
  have : (2 : ℕ) ^ 10 ≤ 2 ^ 9 := h3.trans h1
  norm_num at this

end CFSG.LargeExtraspecial.S14.SMK
