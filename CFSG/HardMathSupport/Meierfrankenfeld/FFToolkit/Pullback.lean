module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

def pullback {L G X : Type*} [Group L] [Group G] [Group X] (φ : L →* X) (ψ : G →* X) :
    Subgroup (L × G) where
  carrier := {p | φ p.1 = ψ p.2}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

variable {L G X : Type*} [Group L] [Group G] [Group X]
variable {φ : L →* X} {ψ : G →* X}

theorem mem_pullback {p : L × G} : p ∈ pullback φ ψ ↔ φ p.1 = ψ p.2 := Iff.rfl

theorem pullback_snd_surjective (hφ : Function.Surjective φ) :
    Function.Surjective ((MonoidHom.snd L G).comp (pullback φ ψ).subtype) := by
  intro g
  obtain ⟨l, hl⟩ := hφ (ψ g)
  exact ⟨⟨(l, g), hl⟩, rfl⟩

theorem pullback_fst_surjective (hψ : Function.Surjective ψ) :
    Function.Surjective ((MonoidHom.fst L G).comp (pullback φ ψ).subtype) := by
  intro l
  obtain ⟨g, hg⟩ := hψ (φ l)
  exact ⟨⟨(l, g), hg.symm⟩, rfl⟩

theorem mem_ker_snd_iff (p : pullback φ ψ) :
    p ∈ ((MonoidHom.snd L G).comp (pullback φ ψ).subtype).ker ↔ (p : L × G).2 = 1 :=
  MonoidHom.mem_ker

theorem mem_ker_fst_iff (p : pullback φ ψ) :
    p ∈ ((MonoidHom.fst L G).comp (pullback φ ψ).subtype).ker ↔ (p : L × G).1 = 1 :=
  MonoidHom.mem_ker

theorem fst_mem_ker_of_snd_eq_one (p : pullback φ ψ) (hp : (p : L × G).2 = 1) :
    (p : L × G).1 ∈ φ.ker := by
  rw [MonoidHom.mem_ker]
  have h := mem_pullback.mp p.2
  rw [h, hp, map_one]

theorem snd_mem_ker_of_fst_eq_one (p : pullback φ ψ) (hp : (p : L × G).1 = 1) :
    (p : L × G).2 ∈ ψ.ker := by
  rw [MonoidHom.mem_ker]
  have h := mem_pullback.mp p.2
  rw [← h, hp, map_one]

theorem ker_pullback_snd_le_center (hφk : φ.ker ≤ Subgroup.center L) :
    ((MonoidHom.snd L G).comp (pullback φ ψ).subtype).ker ≤
      Subgroup.center (pullback φ ψ) := by
  intro p hp
  have hp2 : (p : L × G).2 = 1 := (mem_ker_snd_iff p).mp hp
  have hz : (p : L × G).1 ∈ Subgroup.center L := hφk (fst_mem_ker_of_snd_eq_one p hp2)
  rw [Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  apply Prod.ext
  · simp only [Subgroup.coe_mul, Prod.fst_mul]
    exact Subgroup.mem_center_iff.mp hz _
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hp2, mul_one, one_mul]

theorem card_ker_pullback_snd [Finite L] :
    Nat.card ((MonoidHom.snd L G).comp (pullback φ ψ).subtype).ker = Nat.card φ.ker := by
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1 : L × G).1, fst_mem_ker_of_snd_eq_one p.1 ((mem_ker_snd_iff p.1).mp p.2)⟩
      invFun := fun k => ⟨⟨((k : L), (1 : G)), (MonoidHom.mem_ker.mp k.2).trans (map_one ψ).symm⟩,
        (mem_ker_snd_iff _).mpr rfl⟩
      left_inv := fun p => Subtype.ext (Subtype.ext (Prod.ext rfl ((mem_ker_snd_iff p.1).mp p.2).symm))
      right_inv := fun k => Subtype.ext rfl }

theorem card_ker_pullback_fst [Finite G] :
    Nat.card ((MonoidHom.fst L G).comp (pullback φ ψ).subtype).ker = Nat.card ψ.ker := by
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1 : L × G).2, snd_mem_ker_of_fst_eq_one p.1 ((mem_ker_fst_iff p.1).mp p.2)⟩
      invFun := fun k => ⟨⟨((1 : L), (k : G)), (map_one φ).trans (MonoidHom.mem_ker.mp k.2).symm⟩,
        (mem_ker_fst_iff _).mpr rfl⟩
      left_inv := fun p => Subtype.ext (Subtype.ext (Prod.ext ((mem_ker_fst_iff p.1).mp p.2).symm rfl))
      right_inv := fun k => Subtype.ext rfl }

theorem map_commutator_eq_top {P Q : Type*} [Group P] [Group Q] [Group.IsPerfect Q] (f : P →* Q)
    (hf : Function.Surjective f) : Subgroup.map f (commutator P) = ⊤ := by
  have hmap : Subgroup.map f ⊤ = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hf
  rw [commutator_def, Subgroup.map_commutator, hmap]
  exact Group.isPerfect_def.mp ‹Group.IsPerfect Q›

theorem card_quotient_commutator_dvd_ker {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hf : Subgroup.map f (commutator P) = ⊤) :
    Nat.card (P ⧸ commutator P) ∣ Nat.card f.ker := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' (commutator P)).comp f.ker.subtype) := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have hfp : f p ∈ Subgroup.map f (commutator P) := by
      rw [hf]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hfh⟩ := Subgroup.mem_map.mp hfp
    refine ⟨⟨p * h⁻¹, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hfh, mul_inv_cancel]
    · show (QuotientGroup.mk (p * h⁻¹) : P ⧸ commutator P) = QuotientGroup.mk p
      rw [QuotientGroup.eq]
      have hkey : (p * h⁻¹)⁻¹ * p = h := by group
      rw [hkey]
      exact hh
  exact Subgroup.card_dvd_of_surjective hsurj

theorem isPerfect_pullback [Finite L] [Finite G] [Group.IsPerfect L] [Group.IsPerfect G]
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (_hφk : φ.ker ≤ Subgroup.center L) (_hψk : ψ.ker ≤ Subgroup.center G)
    (hcop : Nat.Coprime (Nat.card φ.ker) (Nat.card ψ.ker)) :
    Group.IsPerfect (pullback φ ψ) := by
  refine Group.isPerfect_def.mpr ?_
  apply Subgroup.index_eq_one.mp
  have h1 : Nat.card (pullback φ ψ ⧸ commutator (pullback φ ψ)) ∣ Nat.card φ.ker := by
    have h := card_quotient_commutator_dvd_ker
      ((MonoidHom.snd L G).comp (pullback φ ψ).subtype)
      (map_commutator_eq_top _ (pullback_snd_surjective hφ))
    rwa [card_ker_pullback_snd] at h
  have h2 : Nat.card (pullback φ ψ ⧸ commutator (pullback φ ψ)) ∣ Nat.card ψ.ker := by
    have h := card_quotient_commutator_dvd_ker
      ((MonoidHom.fst L G).comp (pullback φ ψ).subtype)
      (map_commutator_eq_top _ (pullback_fst_surjective hψ))
    rwa [card_ker_pullback_fst] at h
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact Nat.dvd_one.mp h3

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
