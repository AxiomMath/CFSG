module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der68

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Prelim72

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_QP {z : G} {M P Q : Subgroup G} {p : ℕ} (hP : M ≤ normalizer (P : Set G))
    (hQ : QP z p P Q) : M ≤ normalizer (Q : Set G) := by
  have := hQ.2.1
  have h := le_normalizer_of_characteristic hP (Q.subgroupOf P)
  rwa [Subgroup.map_subgroupOf_eq_of_le hQ.1] at h

omit [Finite G] in
theorem mem_normalizer_inf {g : G} {H K : Subgroup G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro x
  exact ⟨fun hx => ⟨(hH x).mp hx.1, (hK x).mp hx.2⟩, fun hx => ⟨(hH x).mpr hx.1, (hK x).mpr hx.2⟩⟩

theorem Op_Fm_eq {q : ℕ} (hq : q.Prime) (M : Subgroup G) : Op q (Fm M) = Op q M := by
  have : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ ?_
  · refine le_Op_of_isPGroup_of_le_Fm hq ?_ (Op_le q (Fm M) |>.trans le_rfl)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (pCore_isPGroup (p := q) (G := ↥(Fm M)))
    exact IsPGroup.of_card (n := n) (by rw [card_Op, hn])
  · have hOF : Op q M ≤ Fm M := Op_le_Fm q hq M
    set K : Subgroup ↥(Fm M) := (Op q M).subgroupOf (Fm M) with hK
    have hKn : K.Normal := ⟨fun x hx g => by
      rw [hK, Subgroup.mem_subgroupOf] at hx ⊢
      have hgM : ((g : ↥(Fm M)) : G) ∈ M := Fm_le M g.2
      have := (mem_normalizer_iff.mp (le_normalizer_Op q M hgM) (x : G)).mp hx
      simpa using this⟩
    have hKp : IsPGroup q ↥K := (isPGroup_Op q hq M).of_equiv (Subgroup.subgroupOfEquivOfLe hOF).symm
    have hKle : K ≤ pCore q ↥(Fm M) := le_sSup ⟨hKn, hKp⟩
    calc Op q M = K.map (Fm M).subtype := (Subgroup.map_subgroupOf_eq_of_le hOF).symm
      _ ≤ Op q (Fm M) := Subgroup.map_mono hKle

theorem Fm_le_of_forall {M N : Subgroup G} (h : ∀ q : ℕ, q.Prime → Op q M ≤ N) : Fm M ≤ N := by
  rw [Fm_def, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore (G := ↥M), Subgroup.map_iSup]
  exact iSup_le fun q => h q (Nat.prime_of_mem_primeFactors q.2)

theorem Op_ne_bot_of_dvd {M : Subgroup G} {b : ℕ} (hb : b.Prime) (hd : b ∣ Nat.card ↥(Fm M)) :
    Op b M ≠ ⊥ := by
  have : Fact b.Prime := ⟨hb⟩
  obtain ⟨Q⟩ : Nonempty (Sylow b ↥(Fm M)) := inferInstance
  have hQne : (Q : Subgroup ↥(Fm M)) ≠ ⊥ := Sylow.ne_bot_of_dvd_card Q hd
  have hle : (Q : Subgroup ↥(Fm M)).map (Fm M).subtype ≤ Op b M :=
    le_Op_of_isPGroup_of_le_Fm hb (sylow_image_isPGroup _ Q) (Subgroup.map_subtype_le _)
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Fm M).subtype_injective] at hle
  exact hQne hle

theorem centralizer_ne_top {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ} (hC : Ctx6 G z k S M p) {v : G}
    (hv : v ≠ 1) : centralizer ({v} : Set G) ≠ ⊤ := by
  intro htop
  have hsimple : IsSimpleGroup G := hC.ctx.std.kps.1
  obtain ⟨a, b, hab⟩ := hC.ctx.std.kps.2.1
  have hvc : v ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({v} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact hv (Subgroup.mem_bot.mp (h ▸ hvc))
  · have : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem Op_two_eq_bot {z : G} (h : Hyp6A z) {M : Subgroup G} (hM : M ∈ maximalOverCentralizer z) :
    Op 2 M = ⊥ := by
  have hodd : Odd (Nat.card ↥(Fm M)) := odd_card_Fm h hM
  have hle : Op 2 M ≤ Fm M := Op_le_Fm 2 Nat.prime_two M
  have hP : IsPGroup 2 ↥(Op 2 M) := isPGroup_Op 2 Nat.prime_two M
  have hdvd : Nat.card ↥(Op 2 M) ∣ Nat.card ↥(Fm M) := Subgroup.card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have hn0 : n = 0 := by
    by_contra hn0
    have h2 : 2 ∣ Nat.card ↥(Op 2 M) := by rw [hn]; exact dvd_pow_self 2 hn0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

end Prelim72

end CFSG.GH74.GLS.Stage2.Bender.Thm1
