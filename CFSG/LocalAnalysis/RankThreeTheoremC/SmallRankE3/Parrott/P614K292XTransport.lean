module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

namespace P614K292X

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} [Finite H] {n : G}
    (hn : ∀ h ∈ H, n * h * n⁻¹ ∈ H) : n ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hn h, fun hh => ?_⟩
  let φ : H → H := fun k => ⟨n * k * n⁻¹, hn k k.2⟩
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (by simpa [φ] using congrArg Subtype.val hab)
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨_, hh⟩
  have hk' : n * (k : G) * n⁻¹ = n * h * n⁻¹ := congrArg Subtype.val hk
  have hkh : (k : G) = h := by simpa using hk'
  exact hkh ▸ k.2

theorem index_eq_relIndex_of_sup_eq_top [Finite G] {H N : Subgroup G} [N.Normal]
    (hHN : H ⊔ N = ⊤) : H.index = H.relIndex N := by
  have h1 := relIndex_mul_index (inf_le_left : H ⊓ N ≤ H)
  have h2 := relIndex_mul_index (inf_le_right : H ⊓ N ≤ N)
  rw [inf_relIndex_left] at h1
  rw [inf_relIndex_right] at h2
  have h3 : N.relIndex H = N.index := by rw [← relIndex_sup_right, hHN, relIndex_top_right]
  rw [h3] at h1
  have h0 : N.index ≠ 0 := index_ne_zero_of_finite
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (by rw [h1, ← h2, mul_comm])

theorem exists_sylow_le_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : ¬ p ∣ T.index) : ∃ S : Sylow p G, (S : Subgroup G) ≤ T := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
  have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
  have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hT
  exact ⟨hS.toSylow hSi, by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _⟩

theorem isSolvable_of_derivedSeries_le {n : ℕ} {H : Subgroup G} (hH : derivedSeries G n ≤ H)
    [Group.IsSolvable H] : Group.IsSolvable G := by
  haveI : (derivedSeries G n).Normal := derivedSeries_normal G n
  haveI : Group.IsSolvable (G ⧸ derivedSeries G n) := by
    rw [Group.isSolvable_def]
    refine ⟨n, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) n, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  exact Group.isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' (derivedSeries G n))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]; exact hH)

theorem isElemAbelian_comap {G' : Type*} [Group G'] {p : ℕ} {A : Subgroup G'} {φ : G →* G'}
    (hφ : Function.Injective φ) (hA : IsElemAbelian p A) : IsElemAbelian p (A.comap φ) := by
  have := hA.1
  refine ⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun a ha => hφ ?_⟩
  · have hc := congrArg Subtype.val (mul_comm' (⟨φ a, a.2⟩ : A) ⟨φ b, b.2⟩)
    simpa using hc
  · rw [map_pow, hA.2 _ ha, map_one]

end General

section Transport

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {y : GL (Fin 3) K} {v : Fin 3 → K}

theorem threeFrameIn_le : threeFrameIn ν y v ≤ L := by
  intro g hg
  obtain ⟨s, -, rfl⟩ := mem_threeFrameIn.1 hg
  exact (ν s).2

theorem coe_mem_threeFrameIn_iff (hν : Function.Injective ν) {s : ↥(slPi π 3 (p ^ f) K)} :
    ((ν s : ↥L) : X) ∈ threeFrameIn ν y v ↔ (s : GL (Fin 3) K) ∈ threeFrame y v := by
  constructor
  · intro h
    obtain ⟨t, ht, hts⟩ := mem_threeFrameIn.1 h
    have : t = s := hν (Subtype.ext hts)
    exact this ▸ ht
  · intro h
    exact mem_threeFrameIn.2 ⟨s, h, rfl⟩

theorem coe_nu_conj (s t : ↥(slPi π 3 (p ^ f) K)) :
    ((ν (s * t * s⁻¹) : ↥L) : X) = ((ν s : ↥L) : X) * ((ν t : ↥L) : X) * ((ν s : ↥L) : X)⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem comp_injective (hν : Function.Injective ν) : Function.Injective (L.subtype.comp ν) :=
  fun _ _ h => hν (Subtype.ext h)

theorem card_threeFrameIn (hν : Function.Injective ν) (hF : threeFrame y v ≤ slPi π 3 (p ^ f) K) :
    Nat.card (threeFrameIn ν y v) = Nat.card (threeFrame y v) := by
  rw [threeFrameIn, Subgroup.card_map_of_injective (comp_injective hν)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv

theorem isElemAbelian_threeFrameIn (hF : IsElemAbelian 3 (threeFrame y v)) :
    IsElemAbelian 3 (threeFrameIn ν y v) :=
  (hF.subgroupOf (slPi π 3 (p ^ f) K)).map (L.subtype.comp ν)

theorem center_le_threeFrameIn (M : LModel L π p f K ν)
    (hZ : StatedScalars (Fin 3) K ⊓ slPi π 3 (p ^ f) K ≤ threeFrame y v) :
    (center ↥L).map L.subtype ≤ threeFrameIn ν y v := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨s, rfl⟩ := M.surj c
  have hs := M.mem_center_of_map_mem hc
  rw [CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq M.piField M.modThree,
    Subgroup.mem_subgroupOf] at hs
  exact mem_threeFrameIn.2 ⟨s, hZ ⟨hs, s.2⟩, rfl⟩

theorem mem_normalizer_threeFrameIn_of_commute [Finite X] {c : X}
    (hc : ∀ l ∈ L, l * c = c * l) : c ∈ normalizer (threeFrameIn ν y v : Set X) :=
  mem_normalizer_of_conj_mem fun k hk => by
    rw [← hc k (threeFrameIn_le hk), mul_inv_cancel_right]
    exact hk

theorem coe_mem_normalizer_threeFrameIn [Finite X] (hν : Function.Injective ν)
    {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : (s : GL (Fin 3) K) ∈ normalizer (threeFrame y v : Set (GL (Fin 3) K))) :
    ((ν s : ↥L) : X) ∈ normalizer (threeFrameIn ν y v : Set X) := by
  refine mem_normalizer_of_conj_mem fun g hg => ?_
  obtain ⟨t, ht, rfl⟩ := mem_threeFrameIn.1 hg
  rw [← coe_nu_conj, coe_mem_threeFrameIn_iff hν, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact (mem_normalizer_iff.1 hs _).1 ht

theorem coe_mem_normalizer_threeFrame (hν : Function.Injective ν)
    (hF : threeFrame y v ≤ slPi π 3 (p ^ f) K) (h9 : Nat.card (threeFrame y v) = 9)
    {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : ((ν s : ↥L) : X) ∈ normalizer (threeFrameIn ν y v : Set X)) :
    (s : GL (Fin 3) K) ∈ normalizer (threeFrame y v : Set (GL (Fin 3) K)) := by
  haveI : Finite ↥(threeFrame y v) := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  refine mem_normalizer_of_conj_mem fun h hh => ?_
  set t : ↥(slPi π 3 (p ^ f) K) := ⟨h, hF hh⟩
  have h1 : ((ν t : ↥L) : X) ∈ threeFrameIn ν y v := (coe_mem_threeFrameIn_iff hν).2 hh
  have h2 := (mem_normalizer_iff.1 hs _).1 h1
  rw [← coe_nu_conj, coe_mem_threeFrameIn_iff hν, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv] at h2
  exact h2

end Transport

end P614K292X

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
