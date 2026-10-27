module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Link

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR)

variable {G : Type} [Group G] {L : Subgroup G} (e : L ≃* T46)

@[expose] noncomputable def iotaG : T46 →* G := L.subtype.comp e.symm.toMonoidHom

@[expose] noncomputable def phiG : SUJ →* G := (iotaG e).comp psiT

@[expose] noncomputable def toG (H : Subgroup (Equiv.Perm (Fin 693))) : Subgroup G :=
  (H.subgroupOf T46).map (iotaG e)

variable {e}

theorem iotaG_injective : Function.Injective (iotaG e) :=
  L.subtype_injective.comp e.symm.injective

theorem iotaG_mem (g : T46) : iotaG e g ∈ L := (e.symm g).2

theorem range_iotaG : (iotaG e).range = L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact iotaG_mem g
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp [iotaG]⟩

theorem mem_toG {H : Subgroup (Equiv.Perm (Fin 693))} {x : G} :
    x ∈ toG e H ↔ ∃ g : T46, (g : Equiv.Perm (Fin 693)) ∈ H ∧ iotaG e g = x := by
  simp [toG, Subgroup.mem_subgroupOf]

theorem toG_le_L (H : Subgroup (Equiv.Perm (Fin 693))) : toG e H ≤ L := by
  rintro _ ⟨g, -, rfl⟩
  exact iotaG_mem g

theorem iotaG_mem_toG {H : Subgroup (Equiv.Perm (Fin 693))} {g : T46} :
    iotaG e g ∈ toG e H ↔ (g : Equiv.Perm (Fin 693)) ∈ H := by
  rw [mem_toG]
  constructor
  · rintro ⟨g', hg', he⟩
    rwa [← iotaG_injective he]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem toG_mono {H K : Subgroup (Equiv.Perm (Fin 693))} (h : H ≤ K) : toG e H ≤ toG e K :=
  fun x hx => by
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 hx
    exact mem_toG.2 ⟨g, h hg, rfl⟩

theorem toG_inf (H K : Subgroup (Equiv.Perm (Fin 693))) :
    toG e (H ⊓ K) = toG e H ⊓ toG e K := by
  ext x
  rw [Subgroup.mem_inf, mem_toG, mem_toG, mem_toG]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg.1, rfl⟩, ⟨g, hg.2, rfl⟩⟩
  · rintro ⟨⟨g, hg, rfl⟩, ⟨g', hg', he⟩⟩
    rw [iotaG_injective he] at hg'
    exact ⟨g, ⟨hg, hg'⟩, rfl⟩

theorem card_toG {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    Nat.card (toG e H) = Nat.card H := by
  rw [toG, Subgroup.card_map_of_injective iotaG_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv

theorem toG_sup {H K : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) (hK : K ≤ T46) :
    toG e (H ⊔ K) = toG e H ⊔ toG e K := by
  rw [toG, toG, toG, Subgroup.subgroupOf_sup hH hK, Subgroup.map_sup]

theorem toG_bot : toG e ⊥ = ⊥ := by
  rw [toG, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem toG_T46 : toG e T46 = L := by
  rw [toG, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, range_iotaG]

theorem exists_iotaG {x : G} (hx : x ∈ L) : ∃ y : T46, iotaG e y = x :=
  ⟨e ⟨x, hx⟩, by simp [iotaG]⟩

theorem mem_L_of_conj_mem {x y : G} (hy : y ∈ L) (h : y * x * y⁻¹ ∈ L) : x ∈ L := by
  have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hy) h) hy

theorem conjR_toG (H : Subgroup (Equiv.Perm (Fin 693))) (g : T46) :
    conjR (toG e H) (iotaG e g) = toG e (conjR H (g : Equiv.Perm (Fin 693))) := by
  ext x
  rw [mem_conjR]
  constructor
  · intro hx
    have hxL : x ∈ L := mem_L_of_conj_mem (iotaG_mem g) (toG_le_L H hx)
    obtain ⟨y, rfl⟩ := exists_iotaG (e := e) hxL
    rw [← map_inv, ← map_mul, ← map_mul, iotaG_mem_toG] at hx
    rw [iotaG_mem_toG, mem_conjR]
    simpa using hx
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_toG.1 hx
    rw [mem_conjR] at hy
    rw [← map_inv, ← map_mul, ← map_mul, iotaG_mem_toG]
    simpa using hy

theorem toG_zpowers (g : T46) : toG e (zpowers (g : Equiv.Perm (Fin 693))) = zpowers (iotaG e g) := by
  ext x
  rw [mem_toG, mem_zpowers_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    refine ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  · rintro ⟨k, rfl⟩
    exact ⟨g ^ k, by simp [zpow_mem_zpowers], by rw [map_zpow]⟩

theorem normalizer_toG {H : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) :
    normalizer (toG e H : Set G) ⊓ L = toG e (normalizer (H : Set (Equiv.Perm (Fin 693))) ⊓ T46) := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hn, hxL⟩
    obtain ⟨y, rfl⟩ := exists_iotaG (e := e) hxL
    rw [iotaG_mem_toG, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_normalizer_iff.2 fun w => ?_, y.2⟩
    by_cases hw : w ∈ T46
    · have := Subgroup.mem_normalizer_iff.1 hn (iotaG e ⟨w, hw⟩)
      rw [← map_inv, ← map_mul, ← map_mul, iotaG_mem_toG, iotaG_mem_toG] at this
      simpa using this
    · have h1 : w ∉ H := fun h => hw (hH h)
      have h2 : (y : Equiv.Perm (Fin 693)) * w * (y : Equiv.Perm (Fin 693))⁻¹ ∉ H := fun h =>
        hw (by
          have := hH h
          have e' : w = (y : Equiv.Perm (Fin 693))⁻¹ * ((y : Equiv.Perm (Fin 693)) * w *
            (y : Equiv.Perm (Fin 693))⁻¹) * (y : Equiv.Perm (Fin 693)) := by group
          rw [e']
          exact mul_mem (mul_mem (inv_mem y.2) this) y.2)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_toG.1 hx
    refine ⟨Subgroup.mem_normalizer_iff.2 fun z => ?_, iotaG_mem y⟩
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := mem_toG.1 hz
      rw [← map_inv, ← map_mul, ← map_mul, iotaG_mem_toG]
      exact (Subgroup.mem_normalizer_iff.1 hy.1 w).1 hw
    · intro hz
      have hzL : z ∈ L := mem_L_of_conj_mem (iotaG_mem y) (toG_le_L H hz)
      obtain ⟨w, rfl⟩ := exists_iotaG (e := e) hzL
      rw [← map_inv, ← map_mul, ← map_mul, iotaG_mem_toG] at hz
      rw [iotaG_mem_toG]
      exact (Subgroup.mem_normalizer_iff.1 hy.1 w).2 (by simpa using hz)

section Phi

theorem phiG_apply (B : SUJ) : phiG e B = iotaG e (psiT B) := rfl

theorem phiG_mem (B : SUJ) : phiG e B ∈ L := iotaG_mem _

theorem phiG_mem_toG {H : Subgroup (Equiv.Perm (Fin 693))} {B : SUJ} :
    phiG e B ∈ toG e H ↔ psi0 B ∈ H :=
  iotaG_mem_toG

end Phi

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
