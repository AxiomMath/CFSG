module

public import CFSG.LargeExtraspecial.S6ThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

theorem commute_of_comm_mem_zpowers {X : Type*} [Group X] {t x y r : X} (hyt : Commute y t)
    (hrt : Commute r t) (hc : y * x * y⁻¹ * x⁻¹ ∈ zpowers t)
    (hs : r * x * r⁻¹ * x⁻¹ ∈ zpowers t) :
    Commute (r * y * r⁻¹ * y⁻¹) x := by
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hc
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hs
  set c := t ^ i with hcdef
  set s := t ^ j with hsdef
  have hcy : Commute c y := (hyt.zpow_right i).symm
  have hcr : Commute c r := (hrt.zpow_right i).symm
  have hsy : Commute s y := (hyt.zpow_right j).symm
  have hsr : Commute s r := (hrt.zpow_right j).symm
  have hcs : Commute c s := Commute.zpow_zpow_self t i j
  have h1 : y * x * y⁻¹ = c * x := by rw [hi]; group
  have h3 : r * x * r⁻¹ = s * x := by rw [hj]; group
  have h2 : y⁻¹ * x * y = c⁻¹ * x := by
    have e : y * (c⁻¹ * x) * y⁻¹ = x := by
      rw [show y * (c⁻¹ * x) * y⁻¹ = (y * c⁻¹) * x * y⁻¹ by group, ← hcy.inv_left.eq,
        show c⁻¹ * y * x * y⁻¹ = c⁻¹ * (y * x * y⁻¹) by group, h1]
      group
    calc y⁻¹ * x * y = y⁻¹ * (y * (c⁻¹ * x) * y⁻¹) * y := by rw [e]
      _ = c⁻¹ * x := by group
  have h4 : r⁻¹ * x * r = s⁻¹ * x := by
    have e : r * (s⁻¹ * x) * r⁻¹ = x := by
      rw [show r * (s⁻¹ * x) * r⁻¹ = (r * s⁻¹) * x * r⁻¹ by group, ← hsr.inv_left.eq,
        show s⁻¹ * r * x * r⁻¹ = s⁻¹ * (r * x * r⁻¹) by group, h3]
      group
    calc r⁻¹ * x * r = r⁻¹ * (r * (s⁻¹ * x) * r⁻¹) * r := by rw [e]
      _ = s⁻¹ * x := by group
  have h5 : r * y * r⁻¹ * x * (r * y * r⁻¹)⁻¹ = c * x := by
    calc r * y * r⁻¹ * x * (r * y * r⁻¹)⁻¹ = r * (y * (r⁻¹ * x * r) * y⁻¹) * r⁻¹ := by group
      _ = r * ((y * s⁻¹) * x * y⁻¹) * r⁻¹ := by rw [h4]; group
      _ = r * (s⁻¹ * (y * x * y⁻¹)) * r⁻¹ := by rw [← hsy.inv_left.eq]; group
      _ = (r * (s⁻¹ * c)) * x * r⁻¹ := by rw [h1]; group
      _ = (s⁻¹ * c) * (r * x * r⁻¹) := by
          rw [← ((hsr.inv_left).mul_left hcr).eq]; group
      _ = c * x := by
          rw [h3, show s⁻¹ * c * (s * x) = s⁻¹ * (c * s) * x by group, hcs.eq]; group
  have hcY : Commute c⁻¹ (r * y * r⁻¹) :=
    ((hcr.mul_right hcy).mul_right hcr.inv_right).inv_left
  have h6 : r * y * r⁻¹ * y⁻¹ * x * (r * y * r⁻¹ * y⁻¹)⁻¹ = x := by
    calc r * y * r⁻¹ * y⁻¹ * x * (r * y * r⁻¹ * y⁻¹)⁻¹ =
          (r * y * r⁻¹) * (y⁻¹ * x * y) * (r * y * r⁻¹)⁻¹ := by group
      _ = ((r * y * r⁻¹) * c⁻¹) * x * (r * y * r⁻¹)⁻¹ := by rw [h2]; group
      _ = c⁻¹ * (r * y * r⁻¹ * x * (r * y * r⁻¹)⁻¹) := by rw [← hcY.eq]; group
      _ = x := by rw [h5]; group
  calc r * y * r⁻¹ * y⁻¹ * x = (r * y * r⁻¹ * y⁻¹ * x * (r * y * r⁻¹ * y⁻¹)⁻¹) *
        (r * y * r⁻¹ * y⁻¹) := by group
    _ = x * (r * y * r⁻¹ * y⁻¹) := by rw [h6]

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def nqPre (t : S.O) [NQHyp S g t]
    (W : Submodule (ZMod 2) (NQ S g t)) : Subgroup S.O where
  carrier := {x | ∃ h : x ∈ Nbar S g t, nqMk (⟨x, h⟩ : Nbar S g t) ∈ W}
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have e : nqMk (⟨x * y, mul_mem hx hy⟩ : Nbar S g t) =
        nqMk (⟨x, hx⟩ : Nbar S g t) + nqMk (⟨y, hy⟩ : Nbar S g t) :=
      nqMk_mul (⟨x, hx⟩ : Nbar S g t) ⟨y, hy⟩
    rw [e]
    exact add_mem hxW hyW
  one_mem' := ⟨one_mem _, by
    have e : nqMk (⟨1, one_mem _⟩ : Nbar S g t) = 0 := (nqMk_eq_zero_iff _).mpr (one_mem _)
    rw [e]
    exact W.zero_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    refine ⟨inv_mem hx, ?_⟩
    have e : nqMk (⟨x⁻¹, inv_mem hx⟩ : Nbar S g t) = -nqMk (⟨x, hx⟩ : Nbar S g t) := by
      rw [eq_neg_iff_add_eq_zero, ← nqMk_mul, nqMk_eq_zero_iff]
      simp
    rw [e]
    exact neg_mem hxW

variable {t : S.O} [NQHyp S g t]

theorem nqPre_le (W : Submodule (ZMod 2) (NQ S g t)) : nqPre S g t W ≤ Nbar S g t :=
  fun _ hx => hx.1

theorem zpowers_le_nqPre (htN : t ∈ Nbar S g t) (W : Submodule (ZMod 2) (NQ S g t)) :
    zpowers t ≤ nqPre S g t W := by
  rw [zpowers_le]
  refine ⟨htN, ?_⟩
  rw [(nqMk_eq_zero_iff _).mpr (mem_zpowers t)]
  exact W.zero_mem

theorem nqSub_nqPre (htN : t ∈ Nbar S g t) (W : Submodule (ZMod 2) (NQ S g t)) :
    nqSub S g t (nqPre S g t W) = W := by
  ext m
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  rw [mem_nqSub (zpowers_le_nqPre htN W (mem_zpowers t))]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨n.2, h⟩⟩

theorem nqPre_nqSub {D : Subgroup S.O} (htD : zpowers t ≤ D) (hDN : D ≤ Nbar S g t) :
    nqPre S g t (nqSub S g t D) = D := by
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    exact (mem_nqSub (htD (mem_zpowers t)) _).mp hx
  · intro hx
    exact ⟨hDN hx, (mem_nqSub (htD (mem_zpowers t)) _).mpr hx⟩

theorem nqPre_inf (W₁ W₂ : Submodule (ZMod 2) (NQ S g t)) :
    nqPre S g t W₁ ⊓ nqPre S g t W₂ = nqPre S g t (W₁ ⊓ W₂) := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨h, h1⟩, ⟨h', h2⟩⟩ := Subgroup.mem_inf.mp hx
    exact ⟨h, h1, h2⟩
  · rintro ⟨h, h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨⟨h, h1⟩, h, h2⟩

theorem nqPre_bot (htN : t ∈ Nbar S g t) : nqPre S g t ⊥ = zpowers t := by
  ext x
  constructor
  · rintro ⟨h, hx⟩
    rw [Submodule.mem_bot, nqMk_eq_zero_iff] at hx
    exact hx
  · intro hx
    exact zpowers_le_nqPre htN ⊥ hx

theorem card_nqPre (ht1 : t ≠ 1) (htt : t * t = 1) (htN : t ∈ Nbar S g t)
    (W : Submodule (ZMod 2) (NQ S g t)) :
    Nat.card (nqPre S g t W) = 2 * 2 ^ finrank (ZMod 2) W := by
  have h := card_inf_Nbar_eq ht1 htt htN (X := nqPre S g t W)
    (zpowers_le_nqPre htN W (mem_zpowers t))
  rw [inf_eq_left.mpr (nqPre_le W), nqSub_nqPre htN W] at h
  exact h

theorem conj_mem_nqPre {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    {W : Submodule (ZMod 2) (NQ S g t)} (hW : ∀ e : Y, ∀ v ∈ W, nqRep S g t hY e v ∈ W)
    {r x : S.O} (hr : r ∈ Rbar S g t) (hx : x ∈ nqPre S g t W) : r * x * r⁻¹ ∈ nqPre S g t W := by
  obtain ⟨hxN, hxW⟩ := hx
  have hN : NQHyp S g t := inferInstance
  have hrN : r * x * r⁻¹ ∈ Nbar S g t :=
    (nConj (⟨r, hr⟩ : Rbar S g t) ⟨x, hxN⟩).2
  refine ⟨hrN, ?_⟩
  have he : resV hN.conj_mem t ⟨r, hr⟩ ∈ Y := by
    rw [← hY, ← range_resV hN.conj_mem t]; exact ⟨_, rfl⟩
  have := hW ⟨_, he⟩ _ hxW
  rw [nqRep_apply hY (x := ⟨r, hr⟩) rfl] at this
  exact this

end CFSG.LargeExtraspecial.S14
