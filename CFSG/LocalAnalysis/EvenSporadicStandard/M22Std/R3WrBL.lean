module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrC

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.S6Check

variable {X : Type} [Group X] [Finite X] {zb : X} {f : X →* Wr} {E : Subgroup X}

theorem card_units_int : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, -1, by decide, ?_⟩
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Int.units_eq_one_or z

theorem int_units_eq_of_mul_eq_one {a b : ℤˣ} (h : a * b = 1) : a = b := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp_all

theorem WrSit.base_large (h : WrSit X zb f E) {q : X}
    (hq : (f q).e = false) (hq2 : q * q = 1) : 128 ∣ Nat.card (centralizer ({q} : Set X)) := by
  classical
  have hcheck := of_decide_eq_true (Certificates.certificate25910)
  have hsq : f q * f q = 1 := by rw [← map_mul, hq2, map_one]
  obtain ⟨u, v, hfq⟩ : ∃ u v, f q = ⟨u, v, false⟩ :=
    ⟨(f q).a, (f q).b, Wr.ext rfl rfl hq⟩
  rw [hfq] at hsq
  have hu2 : u * u = 1 := congrArg Wr.a hsq
  have hv2 : v * v = 1 := congrArg Wr.b hsq
  obtain ⟨⟨a, ha⟩, c, hcu, hcs⟩ := hcheck.1 u hu2
  obtain ⟨⟨b, hb⟩, c', hcv, hcs'⟩ := hcheck.1 v hv2
  set Cu : Subgroup (Equiv.Perm (Fin 6)) := centralizer ({u} : Set (Equiv.Perm (Fin 6))) with hCu
  set Cv : Subgroup (Equiv.Perm (Fin 6)) := centralizer ({v} : Set (Equiv.Perm (Fin 6))) with hCv
  have hcC : ∀ w : Equiv.Perm (Fin 6), Nat.card ↥(centralizer ({w} : Set (Equiv.Perm (Fin 6)))) =
      cS6 w := fun w => by
    rw [Nat.card_eq_fintype_card, cS6]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun c => mem_centralizer_singleton_iff)
  let φ : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6) →* ℤˣ :=
    (Equiv.Perm.sign.comp (MonoidHom.fst _ _)) * (Equiv.Perm.sign.comp (MonoidHom.snd _ _))
  let K : Subgroup (Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)) := Cu.prod Cv
  let ψ : ↥K →* ℤˣ := φ.comp K.subtype
  have hKcard : Nat.card K = cS6 u * cS6 v := by
    rw [card_subgroup_prod, hCu, hCv, hcC, hcC]
  have hrange : ψ.range = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun z => ?_
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨⟨(c, 1), mem_centralizer_singleton_iff.2 hcu, Subgroup.one_mem _⟩, ?_⟩
      show Equiv.Perm.sign c * Equiv.Perm.sign (1 : Equiv.Perm (Fin 6)) = -1
      rw [hcs, map_one, mul_one]
  have hr2 : Nat.card ψ.range = 2 := by
    rw [hrange, Subgroup.card_top, card_units_int]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hKcard, hr2] at h1
  set Λ0 : Subgroup (Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)) := ψ.ker.map K.subtype with hΛ0
  have hΛcard : Nat.card Λ0 = Nat.card ψ.ker :=
    Subgroup.card_map_of_injective (K := ψ.ker) (f := K.subtype) K.subtype_injective
  have hΛmem : ∀ p ∈ Λ0, p.1 ∈ Cu ∧ p.2 ∈ Cv ∧
      Equiv.Perm.sign p.1 = Equiv.Perm.sign p.2 := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨k.2.1, k.2.2, ?_⟩
    have h2 : φ (k : _) = 1 := hk
    exact int_units_eq_of_mul_eq_one h2
  have h128 : 128 ∣ Nat.card ψ.ker := by
    rw [ha, hb] at h1
    exact ⟨a * b, by nlinarith⟩
  let ι' : ↥Λ0 →* Wr := Wr.inclP.comp Λ0.subtype
  have hι'range : ∀ p : ↥Λ0, ι' p ∈ f.range := fun p => by
    obtain ⟨g, hg⟩ := h.exists_matched (hΛmem p p.2).2.2
    exact ⟨g, hg⟩
  let ι : ↥Λ0 →* X :=
    (MonoidHom.ofInjective h.inj).symm.toMonoidHom.comp (ι'.codRestrict f.range hι'range)
  have hf_ι : ∀ p : ↥Λ0, f (ι p) = ι' p := fun p => by
    have := (MonoidHom.ofInjective h.inj).apply_symm_apply (ι'.codRestrict f.range hι'range p)
    exact congrArg Subtype.val this
  have hι : Function.Injective ι := by
    intro p p' hpp
    have h1' : ι' p = ι' p' := by rw [← hf_ι, ← hf_ι, hpp]
    exact Subtype.ext (Prod.ext (congrArg Wr.a h1') (congrArg Wr.b h1'))
  have hrange_le : ι.range ≤ centralizer ({q} : Set X) := by
    rintro _ ⟨p, rfl⟩
    rw [mem_centralizer_singleton_iff]
    obtain ⟨hp1, hp2, -⟩ := hΛmem p p.2
    have hp1' : (p : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)).1 * u =
        u * (p : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)).1 := mem_centralizer_singleton_iff.1 hp1
    have hp2' : (p : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)).2 * v =
        v * (p : Equiv.Perm (Fin 6) × Equiv.Perm (Fin 6)).2 := mem_centralizer_singleton_iff.1 hp2
    apply h.inj
    rw [map_mul, map_mul, hf_ι, hfq]
    show (⟨_, _, false⟩ : Wr) * ⟨u, v, false⟩ = ⟨u, v, false⟩ * ⟨_, _, false⟩
    simp [hp1', hp2']
  have hd : Nat.card ι.range = Nat.card Λ0 :=
    (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hdvd : Nat.card Λ0 ∣ Nat.card (centralizer ({q} : Set X)) := by
    rw [← hd]
    exact Subgroup.card_dvd_of_le hrange_le
  rw [hΛcard] at hdvd
  exact dvd_trans h128 hdvd

end CFSG.EvenSporadicStandard.M22Std
