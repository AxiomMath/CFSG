module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
public import Certificates.Certificate25640
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.TwoPart
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import CFSG.Sporadic.FischerOddCore.Fi22Unitary

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi22

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

theorem rep_tT
    {k : ℕ} (hk : k < 6) : Rep 3510 (tT k) (fi22ExtRep k) :=
  rep_arrayMap_ofNat (by norm_num) (rep_fi22ExtRep hk)

theorem rep_uT : Rep 3510 uT fi22U :=
  rep_arrayMap_ofNat (by norm_num) rep_fi22U

theorem siftP_iff
    {T : Table} {g : Equiv.Perm (Fin 3510)} (hT : Rep 3510 T g) :
    siftP T = true ↔ g ∈ fi22P :=
  fi22InP_iff (co2Rep_natArr_iff.2 hT)

theorem fi22U_sq : fi22U ^ 2 = 1 := by
  rw [sq]
  exact fi22U_mul_self

theorem mem_fi22R_iff'
    {g : Equiv.Perm (Fin 3510)} :
    g ∈ fi22R ↔ g ∈ fi22P ∨ g * fi22U ∈ fi22P := by
  rw [← (fi22R_semidirect).2.2]
  exact mem_sup_zpowers_iff fi22U_sq fun p hp => fi22U_conj_mem hp

theorem siftR_iff
    {T : Table} {g : Equiv.Perm (Fin 3510)} (hT : Rep 3510 T g) :
    siftR T = true ↔ g ∈ fi22R := by
  rw [siftR, Bool.or_eq_true, siftP_iff hT, siftP_iff (Rep.compT hT rep_uT), mem_fi22R_iff']

theorem exists_comm_not_mem {k : ℕ} (hk : k < 6) :
    ∃ c ∈ fi22R, c ∉ fi22P ∧ c * fi22ExtRep k = fi22ExtRep k * c :=
  Certificates.certificate25640.1 k hk

theorem fi22_index_two :
    ∀ x ∈ fi22R, x ∉ fi22P → ∀ y ∈ fi22R, y ∉ fi22P → x⁻¹ * y ∈ fi22P := by
  intro x hx hxP y hy hyP
  have hxiP : x⁻¹ ∉ fi22P := fun h => hxP (by simpa using fi22P.inv_mem h)
  exact (fi22R_mul_mem_P_iff (fi22R.inv_mem hx) hy).2 ⟨fun h => absurd h hxiP,
    fun h => absurd h hyP⟩

theorem exists_fi22P_conj
    {k : ℕ} (hk : k < 6) {c : Equiv.Perm (Fin 3510)}
    (hc : c ∈ fi22R) : ∃ g ∈ fi22P, c * fi22ExtRep k * c⁻¹ = g * fi22ExtRep k * g⁻¹ := by
  obtain ⟨z, hz, hzP, hzt⟩ := exists_comm_not_mem hk
  exact exists_conj_of_index_two fi22_index_two hz hzP hzt hc

theorem conj_mem_P
    {r p : Equiv.Perm (Fin 3510)} (hr : r ∈ fi22R)
    (hp : p ∈ fi22P) : r * p * r⁻¹ ∈ fi22P :=
  (Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer hr) p).1 hp

theorem cover_R :
    ∀ v ∈ fi22R, orderOf v = 2 →
    ∃ r ∈ (List.range 6).map fi22ExtRep, ∃ c ∈ fi22R, v = c * r * c⁻¹ := by
  intro v hv h2
  obtain ⟨k, hk, r, hr, hrv⟩ := fi22R_involution_conj hv h2
  refine ⟨fi22ExtRep k, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, r⁻¹, fi22R.inv_mem hr, ?_⟩
  rw [← hrv]
  group

theorem cover_P :
    ∀ v ∈ fi22P, orderOf v = 2 →
    ∃ r ∈ (List.range 3).map fi22ExtRep, ∃ c ∈ fi22P, v = c * r * c⁻¹ := by
  intro v hv h2
  obtain ⟨k, hk, r, hr, hrv⟩ := fi22R_involution_conj (fi22P_le_R hv) h2
  have hk3 : k < 3 := by
    by_contra h
    have hout := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).2
    rw [show 3 + (k - 3) = k by omega] at hout
    exact hout (hrv ▸ conj_mem_P hr hv)
  obtain ⟨g, hg, e⟩ := exists_fi22P_conj (k := k) hk (fi22R.inv_mem hr)
  refine ⟨fi22ExtRep k, List.mem_map.2 ⟨k, List.mem_range.2 hk3, rfl⟩, g, hg, ?_⟩
  rw [← e, ← hrv]
  group

theorem cover_outer
    {τ : Equiv.Perm (Fin 3510)} (hτ : τ ∈ fi22R)
    (h2 : orderOf τ = 2) (hτP : τ ∉ fi22P) :
    ∃ k, 3 ≤ k ∧ k < 6 ∧ ∃ g ∈ fi22P, τ = g * fi22ExtRep k * g⁻¹ := by
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj hτ h2
  have hk3 : 3 ≤ k := by
    by_contra h
    have hP := (CTUC_Fi22_all_extension_involutions_covered.1 k (by omega))
    apply hτP
    have := conj_mem_P (fi22R.inv_mem hr) hP
    rwa [← hrτ, show r⁻¹ * (r * τ * r⁻¹) * r⁻¹⁻¹ = τ by group] at this
  obtain ⟨g, hg, e⟩ := exists_fi22P_conj (k := k) hk (fi22R.inv_mem hr)
  refine ⟨k, hk3, hk, g, hg, ?_⟩
  rw [← e, ← hrτ]
  group

theorem card_centralizerIn_P
    {k : ℕ} (hk : k < 3) :
    Nat.card ↥(centralizerIn fi22P (fi22ExtRep k)) =
      [1769472, 53084160, 18393661440][k]! := by
  obtain ⟨h0, h1, -, -, -, hcard⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.cons.injEq] at hcard
  interval_cases k
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 0}) = _
    rw [h0, hcard.1]
    rfl
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1}) = _
    rw [h1, hcard.2.1]
    rfl
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 2}) = _
    rw [fi22ExtRep_two, ← AT_Fi22_involution_centralizer_class.2.2.1,
      AT_Fi22_involution_centralizer_class.2.2.2.2.1]
    rfl

theorem card_centralizerIn_P_outer
    {k : ℕ} (hk : k < 3) :
    Nat.card ↥(centralizerIn fi22P (fi22ExtRep (3 + k))) =
      [3317760, 1045094400, 2903040][k]! := by
  obtain ⟨-, -, h3, h4, h5, hcard⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.cons.injEq] at hcard
  interval_cases k
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 3}) = _
    rw [h3, hcard.2.2.1]
    rfl
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 4}) = _
    rw [h4, hcard.2.2.2.1]
    rfl
  · show Nat.card ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 5}) = _
    rw [h5, hcard.2.2.2.2.1]
    rfl

theorem card_centralizerIn_R
    {k : ℕ} (hk : k < 6) :
    Nat.card ↥(centralizerIn fi22R (fi22ExtRep k)) =
      2 * Nat.card ↥(centralizerIn fi22P (fi22ExtRep k)) := by
  obtain ⟨z, hz, hzP, hzt⟩ := exists_comm_not_mem hk
  exact card_inf_centralizer_R hz hzP hzt

theorem two_part_P
    {k : ℕ} (hk : k < 3) :
    2 ^ (Nat.card ↥(centralizerIn fi22P (fi22ExtRep k))).factorization 2 =
      [65536, 131072, 65536][k]! := by
  rw [card_centralizerIn_P hk]
  interval_cases k
  · exact (two_pow_factorization_eq (k := 16) (b := 27) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 17) (b := 405) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 16) (b := 280665) (by decide) (by norm_num)).trans rfl

theorem two_part_R_inner
    {k : ℕ} (hk : k < 3) :
    2 ^ (Nat.card ↥(centralizerIn fi22R (fi22ExtRep k))).factorization 2 =
      [131072, 262144, 131072][k]! := by
  rw [card_centralizerIn_R (by omega), card_centralizerIn_P hk]
  interval_cases k
  · exact (two_pow_factorization_eq (k := 17) (b := 27) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 18) (b := 405) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 17) (b := 280665) (by decide) (by norm_num)).trans rfl

theorem two_part_R_outer
    {k : ℕ} (hk : k < 3) :
    2 ^ (Nat.card ↥(centralizerIn fi22R (fi22ExtRep (3 + k)))).factorization 2 =
      [16384, 16384, 2048][k]! := by
  rw [card_centralizerIn_R (by omega), card_centralizerIn_P_outer hk]
  interval_cases k
  · exact (two_pow_factorization_eq (k := 14) (b := 405) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 14) (b := 127575) (by decide) (by norm_num)).trans rfl
  · exact (two_pow_factorization_eq (k := 11) (b := 2835) (by decide) (by norm_num)).trans rfl

theorem center_fi22P :
    Subgroup.center fi22P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 3510)) ∈
      Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [fi22P_centralizer, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem fi22_autModel :
    AutModel fi22P fi22R where
  le := fi22P_le_R
  conj_mem := fun _ hx _ hp => conj_mem_P hx hp
  surj := fun α => by
    obtain ⟨r, hr⟩ := fi22RAut.surjective α
    refine ⟨r, r.2, fun p => ?_⟩
    have := congrArg (fun β : MulAut fi22P => ((β p : fi22P) : Equiv.Perm (Fin 3510))) hr
    simpa [fi22RAut_apply, fi22ConjHom_apply] using this.symm
  inj := fun x hx hc => by
    have hxc : x ∈ Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hc h hh).symm
    rw [fi22P_centralizer, Subgroup.mem_bot] at hxc
    exact hxc

theorem card_fi22R_le :
    Nat.card fi22R ≤ 2 * Nat.card fi22P := by
  rw [card_fi22R, card_fi22P]

end CFSG.EvenSporadicStandard.HypOne.Fi22
