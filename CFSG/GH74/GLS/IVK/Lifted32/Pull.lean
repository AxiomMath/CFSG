module

public import CFSG.GH74.GLS.IVK.Lifted32.AbsData
public import CFSG.GH74.GLS.Stage2.Local.Bar

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

namespace Pull

section Basic

variable {G : Type} [Group G] {z : G} {S : Subgroup G} {X Y : Subgroup (CentralizerBar z)}

theorem mem_pull {s : G} :
    s ∈ pull z S X ↔ s ∈ S ∧ ∃ hs : s ∈ Cen z, toBar z ⟨s, hs⟩ ∈ X := by
  unfold pull
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hsS, c, hc, rfl⟩
    exact ⟨hsS, c.2, hc⟩
  · rintro ⟨hsS, hs, h⟩
    exact ⟨hsS, ⟨s, hs⟩, h, rfl⟩

theorem pull_le : pull z S X ≤ S := inf_le_left

theorem pull_mono (h : X ≤ Y) : pull z S X ≤ pull z S Y :=
  inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

theorem pull_inf : pull z S (X ⊓ Y) = pull z S X ⊓ pull z S Y := by
  ext s
  rw [Subgroup.mem_inf, mem_pull, mem_pull, mem_pull]
  constructor
  · rintro ⟨hsS, hs, hX, hY⟩
    exact ⟨⟨hsS, hs, hX⟩, ⟨hsS, hs, hY⟩⟩
  · rintro ⟨⟨hsS, hs, hX⟩, ⟨-, hs', hY⟩⟩
    exact ⟨hsS, hs, hX, hY⟩

theorem mem_pull_of {s : G} (hs : s ∈ S) (hsC : s ∈ Cen z) (h : toBar z ⟨s, hsC⟩ ∈ X) :
    s ∈ pull z S X :=
  mem_pull.2 ⟨hs, hsC, h⟩

theorem toBar_mem_of_mem_pull {s : G} (hs : s ∈ pull z S X) (hsC : s ∈ Cen z) :
    toBar z ⟨s, hsC⟩ ∈ X := by
  obtain ⟨-, hsC', h⟩ := mem_pull.1 hs
  exact h

theorem mem_barOf {K : Subgroup G} {s : G} (hsK : s ∈ K) (hsC : s ∈ Cen z) :
    toBar z ⟨s, hsC⟩ ∈ barOf z K :=
  Subgroup.mem_map.2 ⟨⟨s, hsC⟩, hsK, rfl⟩

theorem exists_of_mem_barOf {K : Subgroup G} {t : CentralizerBar z} (ht : t ∈ barOf z K) :
    ∃ s : G, s ∈ K ∧ ∃ hsC : s ∈ Cen z, toBar z ⟨s, hsC⟩ = t := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ht
  exact ⟨c, hc, c.2, rfl⟩

theorem barOf_sup {K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ Cen z) (h₂ : K₂ ≤ Cen z) :
    barOf z (K₁ ⊔ K₂) = barOf z K₁ ⊔ barOf z K₂ := by
  unfold barOf
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem pull_barOf_S (hSC : S ≤ Cen z) : pull z S (barOf z S) = S := by
  refine le_antisymm pull_le (fun s hs => mem_pull_of hs (hSC hs) ?_)
  exact mem_barOf hs (hSC hs)

theorem toBar_comm {s s' : G} (hs : s ∈ Cen z) (hs' : s' ∈ Cen z) (h : ⁅s, s'⁆ ∈ Cen z) :
    toBar z ⟨⁅s, s'⁆, h⟩ = ⁅toBar z ⟨s, hs⟩, toBar z ⟨s', hs'⟩⁆ := by
  rw [← map_commutatorElement]
  rfl

theorem comm_mem_pull (hSC : S ≤ Cen z) {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) :
    ⁅s, s'⁆ ∈ pull z S X ↔ ⁅toBar z ⟨s, hSC hs⟩, toBar z ⟨s', hSC hs'⟩⁆ ∈ X := by
  have hc : ⁅s, s'⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs hs') (S.inv_mem hs)) (S.inv_mem hs')
  have hcC : ⁅s, s'⁆ ∈ Cen z := hSC hc
  rw [mem_pull]
  constructor
  · rintro ⟨-, hcC', h⟩
    rwa [toBar_comm (hSC hs) (hSC hs') hcC'] at h
  · intro h
    exact ⟨hc, hcC, by rwa [toBar_comm (hSC hs) (hSC hs') hcC]⟩

theorem pull_normal (hSC : S ≤ Cen z) (hN : ∀ t ∈ barOf z S, ∀ y ∈ X, t * y * t⁻¹ ∈ X) :
    ∀ s ∈ S, ∀ y ∈ pull z S X, s * y * s⁻¹ ∈ pull z S X := by
  intro s hs y hy
  obtain ⟨hyS, hyC, hX⟩ := mem_pull.1 hy
  have hsC := hSC hs
  have hconj : s * y * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hyS) (S.inv_mem hs)
  refine mem_pull_of hconj (hSC hconj) ?_
  have e : toBar z ⟨s * y * s⁻¹, hSC hconj⟩ =
      toBar z ⟨s, hsC⟩ * toBar z ⟨y, hyC⟩ * (toBar z ⟨s, hsC⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact hN _ (mem_barOf hs hsC) _ hX

@[expose] def pullHom (z : G) (S : Subgroup G) (hS : S ≤ Cen z) : ↥S →* CentralizerBar z :=
  (toBar z).comp (Subgroup.inclusion hS)

theorem range_pullHom (hS : S ≤ Cen z) : (pullHom z S hS).range = barOf z S := by
  unfold pullHom barOf
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem pull_eq_map_comap (hS : S ≤ Cen z) :
    pull z S X = (X.comap (pullHom z S hS)).map S.subtype := by
  ext s
  rw [mem_pull, Subgroup.mem_map]
  constructor
  · rintro ⟨hsS, hs, h⟩
    exact ⟨⟨s, hsS⟩, h, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, hS t.2, ht⟩

theorem barOf_pull (hX : X ≤ barOf z S) : barOf z (pull z S X) = X := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨-, _hs, h⟩ := mem_pull.1 hc
    exact h
  · intro hx
    obtain ⟨s, hsS, hsC, rfl⟩ := exists_of_mem_barOf (hX hx)
    exact Subgroup.mem_map.2 ⟨⟨s, hsC⟩, mem_pull_of hsS hsC hx, rfl⟩

theorem pull_sup (hSC : S ≤ Cen z) (hX : X ≤ barOf z S) (hY : Y ≤ barOf z S)
    : pull z S (X ⊔ Y) = pull z S X ⊔ pull z S Y := by
  rw [pull_eq_map_comap hSC, pull_eq_map_comap hSC, pull_eq_map_comap hSC,
    ← Subgroup.map_sup,
    Subgroup.comap_sup_eq_of_le_range _ (by rwa [range_pullHom hSC]) (by rwa [range_pullHom hSC])]

theorem relIndex_pull (hSC : S ≤ Cen z) (hY : Y ≤ barOf z S) :
    (pull z S X).relIndex (pull z S Y) = X.relIndex Y := by
  rw [pull_eq_map_comap hSC, pull_eq_map_comap hSC,
    Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq, range_pullHom hSC, inf_eq_right.2 hY]

end Basic

section Syl

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {X Y : Subgroup (CentralizerBar z)}

theorem toBar_injOn (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) {s s' : G} (hs : s ∈ S)
    (hs' : s' ∈ S) (h : toBar z ⟨s, hS.le hs⟩ = toBar z ⟨s', hS.le hs'⟩) : s = s' := by
  have hker : (⟨s, hS.le hs⟩ : ↥(Cen z))⁻¹ * ⟨s', hS.le hs'⟩ ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hSs : s⁻¹ * s' ∈ S := S.mul_mem (S.inv_mem hs) hs'
  have h1 : orderOf (⟨_, hker⟩ : (toBar z).ker) ∣ Nat.card (toBar z).ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  have hodd : Odd (orderOf ((⟨s, hS.le hs⟩ : ↥(Cen z))⁻¹ * ⟨s', hS.le hs'⟩ : ↥(Cen z))) :=
    Odd.of_dvd_nat (odd_card_ker_toBar z) h1
  have hord : orderOf ((⟨s, hS.le hs⟩ : ↥(Cen z))⁻¹ * ⟨s', hS.le hs'⟩ : ↥(Cen z)) =
      orderOf (⟨s⁻¹ * s', hSs⟩ : ↥S) := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨s⁻¹ * s', hSs⟩ : ↥S)]
    rfl
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS.isPGroup) ⟨s⁻¹ * s', hSs⟩
  rw [hord, hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    have : Even (2 ^ k) := (Nat.even_pow).2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have := congrArg Subtype.val hk
  simpa [inv_mul_eq_one] using this

theorem pullHom_injective (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) :
    Function.Injective (pullHom z S hS.le) := by
  intro s s' h
  exact Subtype.ext (toBar_injOn hS s.2 s'.2 h)

theorem pull_zpowers (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) {s : G} (hs : s ∈ S)
    (hsC : s ∈ Cen z) : pull z S (zpowers (toBar z ⟨s, hsC⟩)) = zpowers s := by
  have e : toBar z ⟨s, hsC⟩ = pullHom z S hS.le ⟨s, hs⟩ := rfl
  rw [e, pull_eq_map_comap hS.le, ← MonoidHom.map_zpowers,
    Subgroup.comap_map_eq_self_of_injective (pullHom_injective hS), MonoidHom.map_zpowers]
  rfl

end Syl

end Pull

end CFSG.GH74.GLS.IVK.Lifted32
