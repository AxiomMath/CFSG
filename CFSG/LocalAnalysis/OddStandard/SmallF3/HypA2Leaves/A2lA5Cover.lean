module

public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {n : ℕ}

noncomputable def a2lA5Emb (hn : 5 ≤ n) : alternatingGroup (Fin 5) →* alternatingGroup (Fin n) :=
  ((Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp (alternatingGroup (Fin 5)).subtype).codRestrict
    _ fun σ => by
      rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, Perm.viaEmbeddingHom_apply,
        Perm.viaEmbedding, Perm.sign_extendDomain]
      exact σ.2

theorem a2lA5Emb_injective (hn : 5 ≤ n) : Function.Injective (a2lA5Emb hn) := fun _ _ h =>
  Subtype.ext (Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn) (congrArg Subtype.val h))

theorem a2lA5Emb_cycleType (hn : 5 ≤ n) (σ : alternatingGroup (Fin 5)) :
    ((a2lA5Emb hn σ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType =
      (σ : Perm (Fin 5)).cycleType := by
  classical
  show (Perm.viaEmbedding (σ : Perm (Fin 5)) (Fin.castLEEmb hn)).cycleType = _
  unfold Perm.viaEmbedding
  convert Perm.cycleType_extendDomain
    (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2) (g := (σ : Perm (Fin 5))) using 3

theorem a2l_a5_cycleType {σ : alternatingGroup (Fin 5)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    (σ : Perm (Fin 5)).cycleType = {2, 2} := by
  have hσ2 : (σ : Perm (Fin 5)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, h2, OneMemClass.coe_one]
  have hσ1 : (σ : Perm (Fin 5)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hsign : Perm.sign (σ : Perm (Fin 5)) = 1 := Perm.mem_alternatingGroup.mp σ.2
  obtain ⟨k, hk⟩ : ∃ k, (σ : Perm (Fin 5)).cycleType = Multiset.replicate k 2 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one hσ2⟩
  have hsum := Perm.sum_cycleType_le (σ : Perm (Fin 5))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ1 (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact absurd hsign (by decide)
  · rw [hk]
    rfl

def a2lDouble : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide⟩

theorem a2lDouble_cycleType : ((a2lDouble : alternatingGroup (Fin 5)) : Perm (Fin 5)).cycleType =
    {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

def a2lThree : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide⟩

theorem a2lDouble_noncomm : a2lDouble * a2lThree ≠ a2lThree * a2lDouble := by
  decide

theorem a2l_preimage_a5 [Finite H] {π : H →* alternatingGroup (Fin n)} (hπ : TwoCover π)
    (hn : 5 ≤ n) :
    ∃ N : Subgroup H, π.ker ≤ N ∧ CFSG.IsQuasisimple ↥N ∧ CFSG.pRank 2 ↥N ≤ 1 ∧
      IsPGroup 2 ↥(center ↥N) ∧ Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 5)) := by
  classical
  have hinj : Function.Injective (a2lA5Emb hn) := a2lA5Emb_injective hn
  set N : Subgroup H := (a2lA5Emb hn).range.comap π with hN
  have hkerN : π.ker ≤ N := MonoidHom.ker_le_comap π _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥N →* alternatingGroup (Fin 5), ∀ x : ↥N, a2lA5Emb hn (ρ x) = π x := by
    choose f hf using fun x : ↥N => MonoidHom.mem_range.1 (Subgroup.mem_comap.1 x.2)
    refine ⟨{ toFun := f, map_one' := hinj ?_, map_mul' := fun x y => hinj ?_ }, hf⟩
    · rw [hf, map_one]
      simp
    · rw [hf, map_mul, hf, hf, Subgroup.coe_mul, map_mul]
  have hρ1 : ∀ x : ↥N, ρ x = 1 ↔ π x = 1 := fun x => by
    rw [← hρ x, ← map_one (a2lA5Emb hn)]
    exact ⟨fun h => by rw [h], fun h => hinj h⟩
  have hρsurj : Function.Surjective ρ := fun σ => by
    obtain ⟨y, hy⟩ := hπ.surj (a2lA5Emb hn σ)
    have hyN : y ∈ N := Subgroup.mem_comap.2 ⟨σ, hy.symm⟩
    exact ⟨⟨y, hyN⟩, hinj (by rw [hρ ⟨y, hyN⟩]; exact hy)⟩
  obtain ⟨z, hzc, hz1, hz2, hzk⟩ := hπ.exists_z
  have hzker : z ∈ π.ker := by
    by_contra h
    have hbot : π.ker = ⊥ := eq_bot_iff.2 fun k hk => by
      rcases hzk k hk with rfl | rfl
      · exact one_mem _
      · exact absurd hk h
    have h2 := hπ.card_ker
    rw [hbot, Subgroup.card_bot] at h2
    omega
  have hzN : z ∈ N := hkerN hzker
  have hcenter : center ↥N = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hc : ρ x ∈ center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := hρsurj g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      rw [alternatingGroup.center_eq_bot (by simp)] at hc
      exact Subgroup.mem_bot.mp hc
    · intro hx
      have hxk : (x : H) ∈ π.ker := MonoidHom.mem_ker.2 ((hρ1 x).1 hx)
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hπ.ker_le_center hxk) y)
  have hpg : IsPGroup 2 ↥(center ↥N) := fun g => ⟨1, by
    have hg : (g : ↥N) ∈ ρ.ker := hcenter ▸ g.2
    have hgk : ((g : ↥N) : H) ∈ π.ker :=
      MonoidHom.mem_ker.2 ((hρ1 (g : ↥N)).1 (MonoidHom.mem_ker.1 hg))
    apply Subtype.ext
    apply Subtype.ext
    simpa using hπ.sq_eq_one_of_mem_ker' hgk⟩
  have hquot : Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)⟩
  have hrank : CFSG.pRank 2 ↥N ≤ 1 := by
    have hu : orderOf (⟨z, hzN⟩ : ↥N) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (by simpa using hz2)
      · intro h
        exact hz1 (congrArg Subtype.val h)
    refine GH74.GLS.IVK.Lifted.pRank_two_le_one_of_unique_involution hu fun t ht => ?_
    have ht2 : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht
      omega
    by_cases hπt : π t.1 = 1
    · rcases hzk t.1 (MonoidHom.mem_ker.2 hπt) with h | h
      · exact absurd (Subtype.ext h) ht1
      · exact Subtype.ext h
    · exfalso
      have hρt1 : ρ t ≠ 1 := fun h => hπt ((hρ1 t).1 h)
      have hρt2 : ρ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
      have hct : ((π t.1 : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2} := by
        rw [← hρ t, a2lA5Emb_cycleType]
        exact a2l_a5_cycleType hρt2 hρt1
      exact (hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn hct).2
        (by simpa using congrArg Subtype.val ht2)
  have hA5 : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hmap : (commutator ↥N).map ρ = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρsurj]
    exact hA5.commutator_eq_top
  obtain ⟨m, hmM, hm⟩ : ∃ m ∈ commutator ↥N, ρ m = a2lDouble := by
    have : a2lDouble ∈ (commutator ↥N).map ρ := by
      rw [hmap]
      trivial
    exact Subgroup.mem_map.1 this
  have hm2 : m.1 ^ 2 ∈ π.ker ∧ m.1 ^ 2 ≠ 1 := by
    refine hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn ?_
    rw [← hρ m, hm, a2lA5Emb_cycleType]
    exact a2lDouble_cycleType
  have hmz : m.1 ^ 2 = z := (hzk _ hm2.1).resolve_left hm2.2
  have hkerM : ρ.ker ≤ commutator ↥N := fun x hx => by
    have hxk : (x : H) ∈ π.ker := MonoidHom.mem_ker.2 ((hρ1 x).1 (MonoidHom.mem_ker.1 hx))
    rcases hzk _ hxk with h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · have : x = m ^ 2 := Subtype.ext (by rw [h, ← hmz]; rfl)
      rw [this]
      exact pow_mem hmM 2
  have hperf : commutator ↥N = ⊤ := by
    have h := Subgroup.comap_map_eq ρ (commutator ↥N)
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hkerM] at h
    exact h.symm
  obtain ⟨e⟩ := hquot
  refine ⟨N, hkerN, ⟨Group.isPerfect_def.2 hperf, e.isSimpleGroup, ?_⟩, hrank, hpg, ⟨e⟩⟩
  refine ⟨e.symm a2lDouble, e.symm a2lThree, fun h => a2lDouble_noncomm ?_⟩
  simpa using congrArg e h

end CFSG.OddStandard.SmallF3.HypA2Leaves
