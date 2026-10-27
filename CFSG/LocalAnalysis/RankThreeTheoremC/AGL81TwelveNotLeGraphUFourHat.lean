module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.UFour

open CFSG.QuasithinUnique Subgroup

variable {A : Type} [Group A]

theorem normalizer_subgroupOf_eq {K T : Subgroup A} (hTK : T ≤ K) :
    Subgroup.normalizer ((T.subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (Subgroup.normalizer (T : Set A)).comap K.subtype := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (f := K.subtype) (H := T)
    (by rw [Subgroup.range_subtype]; exact hTK)
  rw [Subgroup.comap_subtype] at h
  exact h.symm

theorem mk_mem_normalizer_hatOf {P T : Subgroup A} (hTP : T ≤ P) {c : A} (hcP : c ∈ P)
    (hcT : c ∈ Subgroup.normalizer (T : Set A)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨c, hcP⟩ ∈
      Subgroup.normalizer ((hatOf P T : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) : Set _) := by
  have h1 : (⟨c, hcP⟩ : ↥P) ∈
      Subgroup.normalizer ((T.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
    rw [normalizer_subgroupOf_eq hTP]
    exact hcT
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    (Subgroup.mem_map_of_mem _ h1)

theorem exists_sylow_hatOf [Finite A] {Y P T : Subgroup A} (hPY : P ≤ Y)
    (hT : IsSylowTwoOf T Y) (hTP : T ≤ P) :
    ∃ S : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P), (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) = hatOf P T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (hatOf P T) :=
    (hT.2.1.comap_of_injective P.subtype P.subtype_injective).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hidx : ¬ 2 ∣ (hatOf P T).index := by
    intro hdvd
    have h1 : (hatOf P T).index ∣ (T.subgroupOf P).index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    have h2 : (T.subgroupOf P).index ∣ (T.subgroupOf Y).index :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex T P Y hTP hPY)
    exact hT.2.2 (hdvd.trans (h1.trans h2))
  exact ⟨hp.toSylow hidx, rfl⟩

theorem exists_hat_sylow_normalizing [Finite A] {Y P T : Subgroup A} {c : A} (hPY : P ≤ Y)
    (hT : IsSylowTwoOf T Y) (hTP : T ≤ P) (hcP : c ∈ P) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcT : c ∈ Subgroup.normalizer (T : Set A)) :
    ∃ (S : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P)) (c' : ↥P ⧸ CFSG.pCore 2 ↥P), c' ^ 3 = 1 ∧ c' ≠ 1 ∧
      c' ∈ Subgroup.normalizer ((S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) : Set _) := by
  obtain ⟨S, hS⟩ := exists_sylow_hatOf hPY hT hTP
  have hc3' : (⟨c, hcP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  refine ⟨S, QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨c, hcP⟩, ?_, ?_, ?_⟩
  · rw [← map_pow, hc3', map_one]
  · intro h
    have hmem : (⟨c, hcP⟩ : ↥P) ∈ CFSG.pCore 2 ↥P := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) ⟨_, hmem⟩
    have hk' : (⟨c, hcP⟩ : ↥P) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : (⟨c, hcP⟩ : ↥P) ^ 3 ^ 1 = 1 := by simpa using hc3'
    exact hc1 (congrArg Subtype.val (Sym.eq_one_of_pow_two_pow_three ⟨k, hk'⟩ ⟨1, h3⟩))
  · rw [hS]
    exact mk_mem_normalizer_hatOf hTP hcP hcT

theorem card_le_nine_hatOf [Finite A] {P : Subgroup A}
    (h9 : ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9) :
    ∀ U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsPGroup 3 U → Nat.card U ≤ 9 := by
  intro U hU
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU
  by_contra hgt
  have hgt : 9 < Nat.card U := Nat.lt_of_not_le hgt
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have h1 : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card ↥P := by
    have h1 : 3 ^ 3 ∣ Nat.card U := by
      rw [hn]
      exact pow_dvd_pow 3 hn3
    exact h1.trans ((Subgroup.card_subgroup_dvd_card U).trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  have hKp : IsPGroup 3 (K.map P.subtype) := (IsPGroup.of_card hK).map P.subtype
  have h := h9 _ (Subgroup.map_subtype_le K) hKp
  rw [Subgroup.card_map_of_injective P.subtype_injective, hK] at h
  norm_num at h

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.UFour
