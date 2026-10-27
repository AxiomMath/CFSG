module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamModel
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.Generic.S45.LEvSporAut

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M] {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem Ivk73Cfg.of_model
    {P R A : Subgroup M} {tX : M} (hM : Ivk73Model P R A tX)
    (h : Ivk73Cfg N L K Q) (θ : ↥L ≃* ↥P) {b₁ b₂ : ℕ}
    (hR : ∀ S : Subgroup M, S ≤ R → (∀ a ∈ A, ∀ s ∈ S, s * a = a * s) → IsPGroup 2 ↥S →
      Nat.card ↥S ≤ b₁)
    (hP : ∀ S : Subgroup M, S ≤ P → (∀ a ∈ A, ∀ s ∈ S, s * a = a * s) → Nat.card ↥S ≤ b₂) :
    Nat.card N ≤ 2 * Nat.card ↥L ∧
      Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
      (∀ S : Subgroup N, S ≤ centralizer (K : Set N) → IsPGroup 2 ↥S → Nat.card ↥S ≤ b₁) ∧
      Nat.card ↥(centralizer (K : Set N) ⊓ L) ≤ b₂ := by
  have := h.normal
  have hA := hM.autModel
  have hC : centralizer (L : Set N) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact h.cent_trivial n (fun l hl => (Subgroup.mem_centralizer_iff.1 hn l hl).symm)
  set ι : N →* M := hA.embed L θ with hιdef
  have hι : Function.Injective ι := hA.embed_injective L θ hC
  have hιR : ∀ x, ι x ∈ R := fun x => hA.embed_mem L θ x
  have hιL : ∀ s : ↥L, ι (s : N) = ((θ s : ↥P) : M) := fun s => hA.embed_coe L θ s
  have hιLmem : ∀ x ∈ L, ι x ∈ P := fun x hx => by
    have := hιL ⟨x, hx⟩
    rw [show ((⟨x, hx⟩ : ↥L) : N) = x from rfl] at this
    rw [this]
    exact (θ ⟨x, hx⟩).2
  have hnormRP : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P := hA.conj_mem
  have hPL : Nat.card ↥P = Nat.card ↥L := (Nat.card_congr θ.toEquiv).symm
  have hcardN : Nat.card N ≤ 2 * Nat.card ↥L := by
    have h1 : Nat.card N ≤ Nat.card ↥R :=
      Nat.card_le_card_of_injective (fun x => (⟨ι x, hιR x⟩ : ↥R))
        (fun x y hxy => hι (congrArg Subtype.val hxy))
    have := hM.card_le
    omega
  have hOut2 : Nat.card (Outer ↥L) ≤ 2 := by
    refine GHInv.card_outer_le_of_card_mulAut_le h.center_L_eq_bot ?_
    have h1 : Nat.card (MulAut ↥L) = Nat.card (MulAut ↥P) :=
      Nat.card_congr (MulAut.congr θ).toEquiv
    have h2 : Nat.card (MulAut ↥P) ≤ Nat.card ↥R :=
      Nat.card_le_card_of_injective (fun α : MulAut ↥P => (⟨hA.hom α, hA.elt_mem α⟩ : ↥R))
        (fun α β hab => hA.hom_injective (congrArg Subtype.val hab))
    have := hM.card_le
    omega
  obtain ⟨u, huL, huQ, hu2, hB⟩ := h.exists_inner_comp (GHInv.hOut_of_card_outer_le_two hOut2)
  set y : ↥L := ⟨u, huL⟩ with hy
  have hy2 : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu2
  set t : M := ((θ y : ↥P) : M) with htdef
  have htP : t ∈ P := (θ y).2
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hy2
  rcases hM.classes t htP ht2 with ⟨g, hgR, hgt⟩ | hno
  swap
  · exfalso
    let e1 : ↥(centralizer ({y} : Set ↥L)) ≃* ↥(centralizerIn P t) :=
      (GHInv.centralizerEquiv θ y (θ y) rfl).trans (GHInv.centralizerSubtypeEquiv P (θ y))
    have hno' : GHInv.NoU2Comp ↥(centralizer ({y} : Set ↥L)) := GHInv.NoU2Comp.of_equiv e1 hno
    obtain ⟨hU, hZ⟩ := h.u2_data_subgroupOf
    let ψ₀ : ↥((K.subgroupOf L).subgroupOf (centralizer ({y} : Set ↥L))) ≃* ↥(K.subgroupOf L) :=
      Subgroup.subgroupOfEquivOfLe hB.1
    obtain ⟨hU', hZ'⟩ := u2_data_of_mulEquiv ψ₀.symm ⟨hU, hZ⟩
    exact hno' _ hB.2 hU' hZ'
  have hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P := hnormRP g hgR
  have hgP' : ∀ p ∈ P, g⁻¹ * p * g ∈ P := fun p hp => by
    have := hnormRP g⁻¹ (R.inv_mem hgR) p hp
    simpa using this
  have hcardC : Nat.card ↥(centralizer ({y} : Set ↥L)) = 240 := by
    rw [GHInv.card_centralizer_eq_centralizerIn P θ y]
    show Nat.card ↥(centralizerIn P t) = 240
    rw [hgt, GHInv.card_centralizerIn_conj_of_norm hgP hgP']
    exact hM.card_cent
  have hKdvd : Nat.card ↥K ∣ 240 := by
    have h1 : Nat.card ↥(K.subgroupOf L) ∣ Nat.card ↥(centralizer ({y} : Set ↥L)) :=
      Subgroup.card_dvd_of_le hB.1
    have h2 : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.K_le).toEquiv
    rw [h2, hcardC] at h1
    exact h1
  obtain ⟨-, -, hKbar, ⟨eK⟩⟩ :=
    GHInv.u2_a5_of_dvd_240 h.K_quasi h.kbar_cases (odd_center_K h.kbar_cases) hKdvd
  set K' : Subgroup M := K.map ι with hK'
  have hK'P : K' ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    exact hιLmem k (h.K_le hk)
  let e5 : ↥K' ≃* alternatingGroup (Fin 5) := (Subgroup.equivMapOfInjective K ι hι).symm.trans eK
  have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
  have hut : ι u = t := hιL y
  have hKt : ∀ k ∈ K', k * t = t * k := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← hut, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 huC k hk]
  obtain ⟨K₁, hK₁mem, ⟨e₁⟩, hK₁P, hK₁t⟩ :=
    conj_setup_N (N := R) (H := P) (K := K') (t := tX) (g := g) hgR hnormRP hK'P e5 hgt hKt
  have hK₁A : K₁ = A :=
    eq_of_perfect_le_derived (D := centralizerIn P tX) (K := K₁) (M := A) (le_inf hK₁P hK₁t)
      (a5_perfect e₁) hM.derived (by rw [hM.card_A, a5_card e₁])
  have hAK' : ∀ z, z ∈ A → g * z * g⁻¹ ∈ K' := fun z hz => by
    rw [← hK₁A] at hz
    exact (hK₁mem z).1 hz
  have key : ∀ S : Subgroup N, S ≤ centralizer (K : Set N) →
      ∃ S' : Subgroup M, S' ≤ R ∧ (∀ a ∈ A, ∀ s ∈ S', s * a = a * s) ∧
        Nat.card ↥S' = Nat.card ↥S ∧ (S ≤ L → S' ≤ P) ∧ (IsPGroup 2 ↥S → IsPGroup 2 ↥S') := by
    intro S hS
    refine ⟨(S.map ι).map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact R.mul_mem (R.mul_mem (R.inv_mem hgR) (hιR s)) hgR
    · rintro a ha _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      obtain ⟨k, hk, hkι⟩ := Subgroup.mem_map.1 (hAK' a ha)
      have hcomm : ι s * ι k = ι k * ι s := by
        rw [← map_mul, ← map_mul, ← Subgroup.mem_centralizer_iff.1 (hS hs) k hk]
      have hak : a = g⁻¹ * ι k * g := by
        have : ι k = g * a * g⁻¹ := hkι
        rw [this]
        group
      calc g⁻¹ * ι s * g * a = g⁻¹ * (ι s * ι k) * g := by rw [hak]; group
        _ = g⁻¹ * (ι k * ι s) * g := by rw [hcomm]
        _ = a * (g⁻¹ * ι s * g) := by rw [hak]; group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
        Subgroup.card_map_of_injective hι]
    · intro hSL
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hgP' _ (hιLmem s (hSL hs))
    · intro hSp
      exact hSp.of_equiv ((Subgroup.equivMapOfInjective S ι hι).trans
        (Subgroup.equivMapOfInjective (S.map ι) (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective))
  refine ⟨hcardN, hKbar, fun S hS hSp => ?_, ?_⟩
  · obtain ⟨S', hS'R, hS'A, hcard, -, hpg⟩ := key S hS
    rw [← hcard]
    exact hR S' hS'R hS'A (hpg hSp)
  · obtain ⟨S', -, hS'A, hcard, hSP, -⟩ := key (centralizer (K : Set N) ⊓ L) inf_le_left
    rw [← hcard]
    exact hP S' (hSP inf_le_right) hS'A

end CFSG.GH74.GLS.IVK
