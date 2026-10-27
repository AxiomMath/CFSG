module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDAct

open Subgroup

private theorem relIndex_dvd_index_of_normal_right {G : Type*} [Group G] [Finite G]
    (S K : Subgroup G) [K.Normal] : S.relIndex K ∣ S.index := by
  have h1 : S.relIndex K * K.index = (S ⊓ K).index := by
    have h := Subgroup.relIndex_inf_mul_relIndex S K ⊤
    rwa [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  have h2 : (S ⊓ K).relIndex S * S.index = (S ⊓ K).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h3 : (S ⊓ K).relIndex S = K.relIndex (S ⊔ K) := by
    rw [Subgroup.relIndex_sup_right, inf_comm, Subgroup.inf_relIndex_right]
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ S ⊔ K)
  have hpos : 0 < K.relIndex (S ⊔ K) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hm
    exact Subgroup.index_ne_zero_of_finite hm
  refine ⟨m, ?_⟩
  rw [hm, ← h2, h3] at h1
  have h4 : K.relIndex (S ⊔ K) * (S.relIndex K * m) = K.relIndex (S ⊔ K) * S.index := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hpos h4).symm

theorem odd_index_comap {H A : Type*} [Group H] [Group A] [Finite H] [Finite A] (f : H →* A)
    (hf : f.range.Normal) (P : Sylow 2 A) : Odd ((P : Subgroup A).comap f).index := by
  have hdvd : ((P : Subgroup A).comap f).index ∣ (P : Subgroup A).index := by
    rw [Subgroup.index_comap]
    exact relIndex_dvd_index_of_normal_right (P : Subgroup A) f.range
  exact Odd.of_dvd_nat (by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact P.not_dvd_index) hdvd

theorem exists_sylow_le_comap {H A : Type*} [Group H] [Group A] [Finite H] [Finite A]
    (f : H →* A) (hf : f.range.Normal) (P : Sylow 2 A) :
    ∃ T : Sylow 2 H, (T : Subgroup H) ≤ (P : Subgroup A).comap f := by
  let Q : Subgroup H := (P : Subgroup A).comap f
  have hQodd : Odd Q.index := odd_index_comap f hf P
  have hne : Nonempty (Sylow 2 Q) := Sylow.nonempty
  obtain ⟨T₀⟩ := hne
  have hTsub_le : (T₀ : Subgroup Q).map Q.subtype ≤ Q := Subgroup.map_subtype_le _
  have hTsub_p : IsPGroup 2 ((T₀ : Subgroup Q).map Q.subtype) :=
    T₀.isPGroup'.map Q.subtype
  have hTsub_idx : ¬ 2 ∣ ((T₀ : Subgroup Q).map Q.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out T₀.not_dvd_index hQodd.not_two_dvd_nat
  refine ⟨hTsub_p.toSylow hTsub_idx, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact hTsub_le

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

@[expose] def actC (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) :
    ↥(centralizer ({t} : Set G)) →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem coe_actC_apply (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (h : ↥(centralizer ({t} : Set G))) (l : ↥L) :
    ((actC hN h l : ↥L) : G) = (h : G) * l * (h : G)⁻¹ :=
  rfl

theorem actC_of_mem (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hL : L ≤ centralizer ({t} : Set G)) (l : ↥L) : actC hN ⟨l, hL l.2⟩ = MulAut.conj l := by
  ext u
  rw [coe_actC_apply, MulAut.conj_apply]
  rfl

theorem mem_ker_actC (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (h : ↥(centralizer ({t} : Set G))) :
    h ∈ (actC hN).ker ↔ (h : G) ∈ centralizer (L : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 : ((actC hN h) ⟨x, hx⟩ : G) = x := by
      simpa using congrArg (fun e : MulAut ↥L => (e ⟨x, hx⟩ : G)) hh
    rw [coe_actC_apply, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  · intro hh
    ext u
    rw [coe_actC_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_centralizer_iff.mp hh) u u.2).symm

theorem inn_le_range_actC (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hL : L ≤ centralizer ({t} : Set G)) :
    (MulAut.conj : ↥L →* MulAut ↥L).range ≤ (actC hN).range := by
  rintro _ ⟨l, rfl⟩
  exact ⟨⟨l, hL l.2⟩, actC_of_mem hN hL l⟩

theorem normal_range_actC [Finite G] (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hL : L ≤ centralizer ({t} : Set G))
    (hidx : (MulAut.conj : ↥L →* MulAut ↥L).range.index = 2) : (actC hN).range.Normal := by
  have hIR : (MulAut.conj : ↥L →* MulAut ↥L).range ≤ (actC hN).range :=
    inn_le_range_actC hN hL
  have hdvd : (actC hN).range.index ∣ 2 := hidx ▸ Subgroup.index_dvd_of_le hIR
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

theorem exists_sylow_actC_le [Finite G] (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hL : L ≤ centralizer ({t} : Set G))
    (hidx : (MulAut.conj : ↥L →* MulAut ↥L).range.index = 2) (P : Sylow 2 (MulAut ↥L)) :
    ∃ T : Sylow 2 ↥(centralizer ({t} : Set G)),
      ∀ g ∈ (T : Subgroup ↥(centralizer ({t} : Set G))),
        actC hN g ∈ (P : Subgroup (MulAut ↥L)) := by
  obtain ⟨T, hT⟩ := exists_sylow_le_comap (actC hN) (normal_range_actC hN hL hidx) P
  exact ⟨T, fun g hg => hT hg⟩

end CFSG.OddStandard.SmallF3.L33.KD.SDAct
