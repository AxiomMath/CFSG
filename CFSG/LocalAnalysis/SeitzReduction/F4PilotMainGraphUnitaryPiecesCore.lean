module

public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Core

variable {M P : Type*} [Group M] [Group P]

theorem uPiece_map_centralizer_le (j : M →* P) (S : Subgroup M) :
    (centralizer (S : Set M)).map j ≤ centralizer ((S.map j : Subgroup P) : Set P) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hx s hs]

theorem uPiece_comap_centralizer_le (j : M →* P) (hj : Function.Injective j) (S : Subgroup M) :
    (centralizer ((S.map j : Subgroup P) : Set P)).comap j ≤ centralizer (S : Set M) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro s hs
  apply hj
  rw [map_mul, map_mul]
  exact mem_centralizer_iff.1 hx (j s) ⟨s, hs, rfl⟩

variable [Finite M] [Finite P]

theorem uPiece_perfectCore_centralizer_eq_comap (j : M →* P) (hj : Function.Injective j)
    (S : Subgroup M) {B : Subgroup P}
    (hB : perfectCore (centralizer ((S.map j : Subgroup P) : Set P)) = B)
    (hperf : ⁅B.comap j, B.comap j⁆ = B.comap j) :
    perfectCore (centralizer (S : Set M)) = B.comap j := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, ← hB]
    have h1 : j x ∈ (perfectCore (centralizer (S : Set M))).map j := ⟨x, hx, rfl⟩
    rw [CFSG.Quasithin.map_perfectCore] at h1
    exact CFSG.Quasithin.perfectCore_mono (uPiece_map_centralizer_le j S) h1
  · refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hperf
    refine le_trans ?_ (uPiece_comap_centralizer_le j hj S)
    exact comap_mono (hB ▸ CFSG.Quasithin.perfectCore_le _)

end Core

section Quotient

variable {M : Type*} [Group M] {G : Type*} [Group G]

theorem uPiece_range_inf_centralizer_map_eq (Φ : M →* G) (hker : Φ.ker ≤ center M)
    {S : Subgroup M}
    (hrig : ∀ x : M, (∀ s ∈ S, ⁅x, s⁆ ∈ center M) → x ∈ centralizer (S : Set M)) :
    Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G) = (centralizer (S : Set M)).map Φ := by
  apply le_antisymm
  · rintro _ ⟨⟨x, rfl⟩, hxC⟩
    refine ⟨x, hrig x fun s hs => hker ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.1 hxC (Φ s) ⟨s, hs, rfl⟩).symm
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hx s hs]

variable [Finite M] [Finite G]

theorem uPiece_natCard_perfectCore_range_inf_centralizer_map (Φ : M →* G)
    (hker : Φ.ker ≤ center M) {S : Subgroup M}
    (hrig : ∀ x : M, (∀ s ∈ S, ⁅x, s⁆ ∈ center M) → x ∈ centralizer (S : Set M))
    (hP : perfectCore (centralizer (S : Set M)) ⊓ center M = ⊥) :
    Nat.card (perfectCore (Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G))) =
      Nat.card (perfectCore (centralizer (S : Set M))) := by
  set Q := perfectCore (centralizer (S : Set M))
  rw [uPiece_range_inf_centralizer_map_eq Φ hker hrig, ← CFSG.Quasithin.map_perfectCore Φ]
  have hinj : Function.Injective (Φ.comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h2 : (a : M) ∈ Q ⊓ center M := ⟨a.2, hker ha⟩
    rw [hP] at h2
    exact Subtype.ext (mem_bot.1 h2)
  have hrange : (Φ.comp Q.subtype).range = Q.map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end Quotient

section Transfer

variable {M P G : Type*} [Group M] [Group P] [Group G] [Finite M] [Finite P] [Finite G]

theorem uPiece_natCard (j : M →* P) (hj : Function.Injective j)
    (hjZ : ∀ z ∈ center M, j z ∈ center P) (S : Subgroup M) {B : Subgroup P}
    (hB : perfectCore (centralizer ((S.map j : Subgroup P) : Set P)) = B)
    (hrig : ∀ y : P, (∀ s ∈ S.map j, ⁅y, s⁆ ∈ center P) →
      y ∈ centralizer ((S.map j : Subgroup P) : Set P))
    (hBZ : B ⊓ center P = ⊥) (hperf : ⁅j.range ⊓ B, j.range ⊓ B⁆ = j.range ⊓ B)
    (Φ : M →* G) (hker : Φ.ker ≤ center M) :
    Nat.card (perfectCore (Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G))) =
      Nat.card (j.range ⊓ B : Subgroup P) := by
  have hperf' : ⁅B.comap j, B.comap j⁆ = B.comap j := by
    apply map_injective hj
    rw [map_commutator, map_comap_eq, hperf]
  have hcore := uPiece_perfectCore_centralizer_eq_comap j hj S hB hperf'
  have hrigM : ∀ x : M, (∀ s ∈ S, ⁅x, s⁆ ∈ center M) → x ∈ centralizer (S : Set M) := by
    intro x hx
    apply uPiece_comap_centralizer_le j hj S
    rw [mem_comap]
    apply hrig
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_commutatorElement]
    exact hjZ _ (hx s hs)
  have hPZ : perfectCore (centralizer (S : Set M)) ⊓ center M = ⊥ := by
    rw [hcore, eq_bot_iff]
    rintro z ⟨hzB, hzZ⟩
    have hz : j z ∈ B ⊓ center P := ⟨hzB, hjZ z hzZ⟩
    rw [hBZ, mem_bot] at hz
    rw [mem_bot]
    exact hj (hz.trans (map_one j).symm)
  rw [uPiece_natCard_perfectCore_range_inf_centralizer_map Φ hker hrigM hPZ, hcore,
    ← map_comap_eq]
  exact Nat.card_congr (equivMapOfInjective _ j hj).toEquiv

end Transfer

end CFSG.SeitzReduction.F4Pilot
