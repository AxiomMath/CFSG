module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

section Transport

variable {G : Type*} [Group G]

theorem charTwo_iff_internal {H : Subgroup G} :
    CharTwo H ↔ Subgroup.centralizer (CFSG.Open.pCore 2 H : Set H) ≤ CFSG.Open.pCore 2 H := by
  constructor
  · intro h element helement
    have hambient : element.val ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro other ⟨preimage, hpreimage, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp helement preimage hpreimage)
    have hcore := h ⟨element.property, hambient⟩
    have hinternal : element ∈ (pCoreOf 2 H).subgroupOf H := hcore
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf] at hinternal
  · intro h x hx
    obtain ⟨hxH, hxC⟩ := hx
    have hmem : (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer (CFSG.Open.pCore 2 H : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (y : G) ∈ pCoreOf 2 H := ⟨y, hy, rfl⟩
      apply Subtype.ext
      simpa using (Subgroup.mem_centralizer_iff.mp hxC _ hy')
    exact ⟨_, h hmem, rfl⟩

theorem charTwo_map_subtype {K : Subgroup G} {L : Subgroup K}
    (h : Subgroup.centralizer (CFSG.Open.pCore 2 L : Set L) ≤ CFSG.Open.pCore 2 L) :
    CharTwo (L.map K.subtype) := by
  rw [charTwo_iff_internal]
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
    (L.equivMapOfInjective K.subtype K.subtype_injective) h

theorem map_subtype_normalizer {K X : Subgroup G} (hXK : X ≤ K) :
    (Subgroup.normalizer ((X.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer (X : Set G) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_normalizer_iff.mpr ?_⟩
    intro y
    constructor
    · intro hy
      exact (Subgroup.mem_normalizer_iff.mp hk ⟨y, hXK hy⟩).mp hy
    · intro hy
      have hyK : y ∈ K := by
        have := hXK hy
        have h2 : (k : G)⁻¹ * (↑k * y * (↑k)⁻¹) * ↑k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) this) k.2
        simpa [mul_assoc] using h2
      exact (Subgroup.mem_normalizer_iff.mp hk ⟨y, hyK⟩).mpr hy
  · rintro ⟨hgK, hg⟩
    refine ⟨⟨g, hgK⟩, Subgroup.mem_normalizer_iff.mpr ?_, rfl⟩
    intro y
    exact Subgroup.mem_normalizer_iff.mp hg y

theorem map_subtype_centralizer {K X : Subgroup G} (hXK : X ≤ K) :
    (Subgroup.centralizer ((X.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer (X : Set G) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hk ⟨y, hXK hy⟩ hy
    exact congrArg Subtype.val this
  · rintro ⟨hgK, hg⟩
    refine ⟨⟨g, hgK⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg y hy)

end Transport

variable {G : Type*} [Group G] [Finite G]

theorem CharTwo.of_normal {H K : Subgroup G} (hK : CharTwo K) (hHK : H ≤ K)
    (hn : (H.subgroupOf K).Normal) : CharTwo H := by
  rw [charTwo_iff_internal] at hK ⊢
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroupOf_self_centralizing_pCore 2
    Nat.prime_two H K hHK hn hK

theorem CharTwo.inf_normalizer {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : IsPGroup 2 X) : CharTwo (K ⊓ Subgroup.normalizer (X : Set G)) := by
  rw [← map_subtype_normalizer hXK]
  exact charTwo_map_subtype
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_normalizer 2 Nat.prime_two
      (charTwo_iff_internal.mp hK) _ (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm))

theorem CharTwo.inf_centralizer {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : IsPGroup 2 X) : CharTwo (K ⊓ Subgroup.centralizer (X : Set G)) := by
  rw [← map_subtype_centralizer hXK]
  exact charTwo_map_subtype
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_centralizer 2 Nat.prime_two
      (charTwo_iff_internal.mp hK) _ (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm))

private theorem charTwo_normalizer_of_normal {U V : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hVU : V ≤ Subgroup.normalizer (U : Set G))
    (hU : CharTwo (Subgroup.normalizer (U : Set G))) :
    CharTwo (Subgroup.normalizer (V : Set G)) := by
  set A := Subgroup.normalizer (U : Set G) with hA
  set B := Subgroup.normalizer (V : Set G) with hB
  set Q := pCoreOf 2 B with hQ
  set D := B ⊓ Subgroup.centralizer (Q : Set G) with hD
  have hVB : V ≤ B := Subgroup.le_normalizer
  have hVQ : V ≤ Q :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V B hVB
      Subgroup.normal_in_normalizer hV
  have hAB : CharTwo (A ⊓ B) := hU.inf_normalizer hVU hV
  have hUQ : U ≤ Q := hUV.trans hVQ
  have hDC : D ≤ Subgroup.centralizer (Q : Set G) := inf_le_right
  have hDA : D ≤ A :=
    hDC.trans ((Subgroup.centralizer_le (by exact_mod_cast hUQ)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hDAB : D ≤ A ⊓ B := le_inf hDA inf_le_left
  have hBnormD : B ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf B B _
      Subgroup.le_normalizer
      ((CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 B).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _))
  have hDnormal : (D.subgroupOf (A ⊓ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDAB).mpr (inf_le_right.trans hBnormD)
  have hCD : CharTwo D := hAB.of_normal hDAB hDnormal
  have hDB : D ≤ B := inf_le_left
  have hO2D : pCoreOf 2 D ≤ Q := by
    apply CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 D) B
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 D).trans hDB)
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 D).trans hDB)).mpr ?_
      exact hBnormD.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 D)
    · exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 D
  have hDcentral : D ≤ Subgroup.centralizer (pCoreOf 2 D : Set G) :=
    hDC.trans (Subgroup.centralizer_le (by exact_mod_cast hO2D))
  exact (le_inf le_rfl hDcentral).trans (hCD.trans hO2D)

private theorem exists_mem_inf_normalizer_not_mem {U V : Subgroup G} (hV : IsPGroup 2 V)
    (hUV : U ≤ V) (hne : U ≠ V) :
    ∃ x ∈ V ⊓ Subgroup.normalizer (U : Set G), x ∉ U := by
  have : Group.IsNilpotent V := hV.isNilpotent
  have hlt : U.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hUV ?_
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ U.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  obtain ⟨x, hx, hxn⟩ := Set.exists_of_ssubset hnorm
  refine ⟨x, ?_, hxn⟩
  rw [← map_subtype_normalizer hUV]
  exact ⟨x, hx, rfl⟩

theorem charTwo_normalizer_of_le {U V : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hU : CharTwo (Subgroup.normalizer (U : Set G))) :
    CharTwo (Subgroup.normalizer (V : Set G)) := by
  suffices h : ∀ n : ℕ, ∀ U : Subgroup G, U ≤ V → Nat.card V - Nat.card U = n →
      CharTwo (Subgroup.normalizer (U : Set G)) → CharTwo (Subgroup.normalizer (V : Set G)) from
    h _ U hUV rfl hU
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hUV hn hU
    by_cases hUeq : U = V
    · rwa [hUeq] at hU
    · obtain ⟨x, hx, hxU⟩ := exists_mem_inf_normalizer_not_mem hV hUV hUeq
      set U' := V ⊓ Subgroup.normalizer (U : Set G) with hU'
      have hUU' : U ≤ U' := le_inf hUV Subgroup.le_normalizer
      have hlt : U < U' := lt_of_le_of_ne hUU' fun h => hxU (h ▸ hx)
      have hU'V : U' ≤ V := inf_le_left
      have hU'p : IsPGroup 2 U' := hV.to_le hU'V
      have hU'norm : U' ≤ Subgroup.normalizer (U : Set G) := inf_le_right
      have hcharU' : CharTwo (Subgroup.normalizer (U' : Set G)) :=
        charTwo_normalizer_of_normal hU'p hUU' hU'norm hU
      have hcard : Nat.card U < Nat.card U' := Subgroup.card_lt_of_lt hlt
      have hcardV : Nat.card U' ≤ Nat.card V := Subgroup.card_le_of_le hU'V
      exact ih (Nat.card V - Nat.card U') (by omega) U' hU'V rfl hcharU'

theorem charTwo_normalizer_of_inf_center
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T D : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hD : IsPGroup 2 D)
    (hDZ : D ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥) :
    CharTwo (Subgroup.normalizer (D : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := D ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) with hW
  have hWD : W ≤ D := inf_le_left
  have hWp : IsPGroup 2 W := hD.to_le hWD
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2.2 t ht).symm
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 G := hT.2.1.toSylow hT2
  have hCW : CharTwo (Subgroup.normalizer (W : Set G)) :=
    hev _ ⟨W, hDZ, hWp, rfl⟩ ⟨S, hTW⟩
  exact charTwo_normalizer_of_le hD hWD hCW

end CFSG.QuasithinUnique
