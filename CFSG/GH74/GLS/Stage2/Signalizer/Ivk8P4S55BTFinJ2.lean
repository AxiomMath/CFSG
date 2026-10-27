module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2C
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2D
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2B

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative FinJ2

namespace FinJ2

theorem map_centralizer {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {R : Subgroup H} (hR : ∀ z, z ∈ R ↔ ∃ a, f a = z) (x : G) :
    (centralizer ({x} : Set G)).map f = R ⊓ centralizer ({f x} : Set H) := by
  ext z
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(hR _).2 ⟨a, rfl⟩, by rw [← map_mul, ← map_mul, ha]⟩
  · rintro ⟨hz, hzx⟩
    obtain ⟨a, rfl⟩ := (hR z).1 hz
    exact ⟨a, hf (by rw [map_mul, map_mul]; exact hzx), rfl⟩

end FinJ2

theorem finCellB_j2
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .J2) : FinCellB Y := by
  obtain ⟨e⟩ := hY
  have θ : Y ≃* ↥j2P := (e : Y ≃* NativeSporadic.J2).trans j2PermEquiv
  obtain ⟨Φ₀, -, -, -, hcardA⟩ := ctuc_j2_full_automorphism_permutation_model
  have : Finite Y := Finite.of_equiv _ θ.symm.toEquiv
  set Φ : MulAut Y ≃* ↥j2R := (MulAut.congr θ).trans Φ₀.symm with hΦ
  set f : Y →* Equiv.Perm (Fin 315) := j2P.subtype.comp θ.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.injective
  set F : MulAut Y →* Equiv.Perm (Fin 315) := j2R.subtype.comp Φ.toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp Φ.injective
  have hRange : ∀ z, z ∈ j2R ↔ ∃ a, F a = z := fun z =>
    ⟨fun hz => ⟨Φ.symm ⟨z, hz⟩, by simp [hFdef]⟩, fun ⟨a, ha⟩ => ha ▸ (Φ a).2⟩
  have hc : center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    have h1 := j2_autModel.inj ((θ z : ↥j2P) : Equiv.Perm (Fin 315)) (j2_autModel.le (θ z).2)
      fun q hq => by
        have h2 := congrArg (fun w => ((θ w : ↥j2P) : Equiv.Perm (Fin 315)))
          (mem_center_iff.mp hz (θ.symm ⟨q, hq⟩))
        simpa using h2.symm
    exact θ.injective (Subtype.ext (by simpa using h1))
  have hcardY : Nat.card Y = 604800 := by rw [Nat.card_congr θ.toEquiv, card_j2P]
  have hcard : Nat.card (MulAut Y) = 1209600 := by
    rw [Nat.card_congr (MulAut.congr θ).toEquiv, hcardA]
  have hidx : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    rw [hcard, hcardY]
  have h3 : ∀ y : Y, orderOf y = 3 → ∃ a b : Y, KleinWit y a b := by
    intro y hy
    have hfy : orderOf (f y) = 3 := by rw [orderOf_injective f hf y, hy]
    obtain ⟨u₁, hu₁, u₂, hu₂, hw⟩ := klein (θ y).2 hfy
    refine ⟨θ.symm ⟨u₁, hu₁⟩, θ.symm ⟨u₂, hu₂⟩, (kleinWit_map_iff hf).1 ?_⟩
    have e1 : f (θ.symm ⟨u₁, hu₁⟩) = u₁ := by simp [hfdef]
    have e2 : f (θ.symm ⟨u₂, hu₂⟩) = u₂ := by simp [hfdef]
    rw [e1, e2]
    exact hw
  have h5 : ∀ x : MulAut Y, orderOf x = 5 →
      ¬ 8 ∣ Nat.card ↥(centralizer ({x} : Set (MulAut Y))) := by
    intro x hx
    rw [← Subgroup.card_map_of_injective hF, map_centralizer hF hRange x]
    exact not_eight_dvd ((hRange _).2 ⟨x, rfl⟩) (by rw [orderOf_injective F hF x, hx])
  have h7 : ∀ s y : Y, orderOf s = 2 → orderOf y = 7 → s * y ≠ y * s := by
    intro s y hs hy hsy
    have hfs : orderOf (f s) = 2 := by rw [orderOf_injective f hf s, hs]
    have hfy : orderOf (f y) = 7 := by rw [orderOf_injective f hf y, hy]
    apply not_seven_dvd (θ s).2 hfs
    rw [← hfy]
    apply Subgroup.orderOf_dvd_natCard
    refine Subgroup.mem_inf.mpr ⟨(θ y).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h := congrArg f hsy
    rw [map_mul, map_mul] at h
    exact h.symm
  exact finCellB_of_facts hc hcard hidx h3 h5 h7

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
