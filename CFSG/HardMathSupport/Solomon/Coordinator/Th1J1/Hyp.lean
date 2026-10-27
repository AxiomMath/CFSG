module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Zero

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp (R S : Subgroup G) : Prop where
  solv : Group.IsSolvable ↥R
  not3 : ¬ 3 ∣ Nat.card R
  not5 : ¬ 5 ∣ Nat.card R
  oddcore : ∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) →
    ¬ 2 ∣ Nat.card N → N = ⊥
  le : S ≤ R
  two : IsPGroup 2 S
  syl : ¬ 2 ∣ S.relIndex R

theorem Hyp.exists_O2 {R S : Subgroup G} (h : Hyp R S) :
    ∃ U : Subgroup G, U ≤ S ∧ IsPGroup 2 U ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
      (∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) → IsPGroup 2 K → K ≤ U) ∧
      ∀ x ∈ R, (∀ u ∈ U, u * x = x * u) → x ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.solv
  have hS'2 : IsPGroup 2 (S.subgroupOf R) :=
    h.two.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  have hS'idx : ¬ 2 ∣ (S.subgroupOf R).index := h.syl
  let T : Sylow 2 ↥R := hS'2.toSylow hS'idx
  have hcore : CFSG.pPrimeCore 2 ↥R = ⊥ := by
    refine eq_bot_iff.2 (sSup_le fun K hK => ?_)
    obtain ⟨hKn, hKc⟩ := hK
    have hodd : ¬ 2 ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hKc
    have hbot := h.oddcore (K.map R.subtype) (by rintro _ ⟨k, -, rfl⟩; exact k.2)
      (fun r hr => by
        have key : ∀ r : R, ∀ y ∈ K.map R.subtype, (r : G) * y * (r : G)⁻¹ ∈ K.map R.subtype := by
          rintro r _ ⟨k, hk, rfl⟩
          exact ⟨r * k * r⁻¹, hKn.conj_mem k hk r, by simp⟩
        exact mem_normalizer_of_conj_mem' (key ⟨_, hr⟩) (fun y hy => by
          simpa using key ⟨_, R.inv_mem hr⟩ y hy))
      (by rwa [Subgroup.card_map_of_injective R.subtype_injective])
    exact le_of_eq ((Subgroup.map_eq_bot_iff_of_injective K R.subtype_injective).1 hbot)
  have hchar : CFSG.IsCharacteristicP 2 ↥R :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥R 2 hcore
      layer_eq_bot_of_solvable'
  have hCP : Subgroup.centralizer (CFSG.pCore 2 ↥R : Set ↥R) ≤ CFSG.pCore 2 ↥R := hchar
  have hnorm : (CFSG.pCore 2 ↥R).Normal := CFSG.pCore_normal
  have hp2 : IsPGroup 2 (CFSG.pCore 2 ↥R) := CFSG.pCore_isPGroup
  refine ⟨(CFSG.pCore 2 ↥R).map R.subtype, ?_, hp2.map R.subtype, ?_, ?_, ?_⟩
  ·
    have hle : CFSG.pCore 2 ↥R ≤ (T : Subgroup ↥R) := hp2.le_sylow_of_normal T
    rintro _ ⟨x, hx, rfl⟩
    have := hle hx
    exact this
  · intro r hr
    have key : ∀ r : R, ∀ y ∈ (CFSG.pCore 2 ↥R).map R.subtype,
        (r : G) * y * (r : G)⁻¹ ∈ (CFSG.pCore 2 ↥R).map R.subtype := by
      rintro r _ ⟨k, hk, rfl⟩
      exact ⟨r * k * r⁻¹, hnorm.conj_mem k hk r, by simp⟩
    exact mem_normalizer_of_conj_mem' (key ⟨_, hr⟩) (fun y hy => by
      simpa using key ⟨_, R.inv_mem hr⟩ y hy)
  ·
    intro K hKR hKn hK2 x hxK
    have hKnorm : (K.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKR).2 hKn
    have hK2' : IsPGroup 2 (K.subgroupOf R) :=
      hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKR).symm
    have hle : K.subgroupOf R ≤ CFSG.pCore 2 ↥R := le_sSup ⟨hKnorm, hK2'⟩
    have hmem : (⟨x, hKR hxK⟩ : ↥R) ∈ K.subgroupOf R := Subgroup.mem_subgroupOf.2 hxK
    exact ⟨⟨x, hKR hxK⟩, hle hmem, rfl⟩
  · intro x hx hc
    have hxc : (⟨x, hx⟩ : ↥R) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥R : Set ↥R) := by
      intro k hk
      exact Subtype.ext (hc k ⟨k, hk, rfl⟩)
    exact ⟨⟨x, hx⟩, hCP hxc, rfl⟩

theorem Hyp.mono {R S R' : Subgroup G} (h : Hyp R S) (hSR' : S ≤ R') (hR'R : R' ≤ R) :
    Hyp R' S := by
  obtain ⟨U, hUS, hU2, hUn, -, hUc⟩ := h.exists_O2
  refine ⟨?_, ?_, ?_, ?_, hSR', h.two, ?_⟩
  · have := h.solv
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hR'R)
      (Subgroup.inclusion_injective hR'R)
  · exact fun h3 => h.not3 (h3.trans (Subgroup.card_dvd_of_le hR'R))
  · exact fun h5 => h.not5 (h5.trans (Subgroup.card_dvd_of_le hR'R))
  · intro N hNR' hR'N hodd
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ R := hR'R (hNR' hx)
    have hxU : x ∈ U := by
      refine hUc x hxR (fun u hu => ?_)
      have huR' : u ∈ R' := hSR' (hUS hu)
      have hc1 : x * u * x⁻¹ * u⁻¹ ∈ U := mul_mem
        ((Subgroup.mem_normalizer_iff.1 (hUn hxR) u).1 hu) (U.inv_mem hu)
      have hc2 : x * u * x⁻¹ * u⁻¹ ∈ N := by
        have := mul_mem hx ((Subgroup.mem_normalizer_iff.1 (hR'N huR') x⁻¹).1 (N.inv_mem hx))
        simpa [mul_assoc] using this
      have h1 := eq_one_of_mem_pgroup_odd hU2 hodd hc1 hc2
      calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * (x * u) := by group
        _ = x * u := by rw [h1]; simp
    exact Subgroup.mem_bot.2 (eq_one_of_mem_pgroup_odd hU2 hodd hxU hx)
  · have h1 := Subgroup.relIndex_mul_relIndex S R' R hSR' hR'R
    exact fun h2 => h.syl (h2.trans ⟨_, h1.symm⟩)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
