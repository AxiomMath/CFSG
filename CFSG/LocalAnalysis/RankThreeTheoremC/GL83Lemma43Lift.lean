module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PPointCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ABGLocalTools CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l43_exists_lift {O B Y : Subgroup G} (hOB : O ≤ B) (hBO : B ≤ normalizer (O : Set G))
    (hYB : Y ≤ normalizer (B : Set G)) (hYO : Y ≤ normalizer (O : Set G))
    (hY2 : IsPGroup 2 Y) (hO3 : ¬ 3 ∣ Nat.card O) (hB3 : ∀ b ∈ B, b ^ 3 ∈ O)
    (hS : IsSylowOf 2 (Y ⊓ O) O) :
    ∃ T : Subgroup G, Y ⊓ O ≤ T ∧ T ≤ B ∧ Y ≤ normalizer (T : Set G) ∧ T ⊓ O = Y ⊓ O ∧
      T ⊔ O = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S : Subgroup G := Y ⊓ O with hSdef
  set N : Subgroup G := B ⊓ normalizer (S : Set G) with hN
  have hSO : S ≤ O := inf_le_right
  have hSN : S ≤ N := le_inf (hSO.trans hOB) Subgroup.le_normalizer
  have hNS : N ≤ normalizer (S : Set G) := inf_le_right
  have hNB : N ≤ B := inf_le_left
  have hYS : Y ≤ normalizer (S : Set G) := le_normalizer_inf' Subgroup.le_normalizer hYO
  have hYN : Y ≤ normalizer (N : Set G) :=
    le_normalizer_inf' hYB (hYS.trans Subgroup.le_normalizer)
  have hodd : ¬ 2 ∣ S.relIndex N := by
    have hSNO : S ≤ N ⊓ O := le_inf hSN hSO
    have h1 : IsSylowOf 2 S (N ⊓ O) := hS.of_le hSNO inf_le_right
    have h2 : ¬ 2 ∣ S.relIndex (N ⊓ O) := (isSylowOf_iff.mp h1).2.2
    have h3 : ¬ 2 ∣ (N ⊓ O).relIndex N :=
      not_two_dvd_relIndex_inf (hNB.trans hBO) fun n hn => hB3 n (hNB hn)
    rw [← Subgroup.relIndex_mul_relIndex S (N ⊓ O) N hSNO inf_le_left]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact h2 h
    · exact h3 h
  obtain ⟨T, hST, hTN, hYT, hTidx, hT3⟩ := exists_normalized_sylow_mod (p := 2) (q := 3) hSN hNS
    hYS hYN hY2 hodd
  have hTB : T ≤ B := hTN.trans hNB
  have hTO : T ⊓ O = S := by
    refine le_antisymm ?_ (le_inf hST hSO)
    rintro t ⟨htT, htO⟩
    obtain ⟨k, hk⟩ := hT3 t htT
    have hd : orderOf t ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨t, htO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ k) (orderOf t) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (fun h => hO3 (h.trans hd)))
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have htc : t = (t ^ (3 ^ k)) ^ c := hc.symm
    rw [htc]
    exact S.pow_mem hk c
  have hO'n : (O.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).mpr hBO
  have hBTO : ∀ b ∈ B, ∃ t ∈ T, ∃ o ∈ O, b = t * o := by
    set φ : N →* B ⧸ O.subgroupOf B :=
      (QuotientGroup.mk' (O.subgroupOf B)).comp (Subgroup.inclusion hNB) with hφ
    have hfrat : ∀ r ∈ B, ∃ n ∈ N, ∃ o ∈ O, r = n * o := by
      intro r hr
      obtain ⟨o, ho, m, hm, hrm⟩ := exists_mul_normalizer_of_isSylowOf hS hBO hr
      have hmB : m ∈ B := by
        have : m = o⁻¹ * r := by rw [hrm]; group
        rw [this]
        exact B.mul_mem (B.inv_mem (hOB ho)) hr
      refine ⟨m, ⟨hmB, hm⟩, m⁻¹ * o * m, ?_, by rw [hrm]; group⟩
      have := (mem_normalizer_iff.mp (hBO (B.inv_mem hmB)) o).mp ho
      simpa [mul_assoc] using this
    have hφsurj : Function.Surjective φ := by
      intro g
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨n, hn, o, ho, hrn⟩ := hfrat r r.2
      refine ⟨⟨n, hn⟩, ?_⟩
      show (QuotientGroup.mk (⟨n, hNB hn⟩ : B) : B ⧸ O.subgroupOf B) = QuotientGroup.mk r
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : ((⟨n, hNB hn⟩ : B)⁻¹ * r : B) = ⟨o, hOB ho⟩ := Subtype.ext (by
        change n⁻¹ * (r : G) = o
        rw [hrn]; group)
      rw [this]
      exact ho
    have hBbar3 : IsPGroup 3 (B ⧸ O.subgroupOf B) := fun g => ⟨1, by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hB3 r r.2)⟩
    obtain ⟨a, ha⟩ := hBbar3.exists_card_eq
    set Tim : Subgroup (B ⧸ O.subgroupOf B) := (T.subgroupOf N).map φ with hTim
    have hTimidx : Tim.index ∣ T.relIndex N := Subgroup.index_map_dvd (T.subgroupOf N) hφsurj
    have hTim1 : Tim.index = 1 := by
      have hdvd : Tim.index ∣ 3 ^ a := ha ▸ Subgroup.index_dvd_card Tim
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · simpa using hb
      · exfalso
        apply hTidx
        exact (dvd_pow_self 3 hb0.ne').trans (hb ▸ hTimidx)
    have htop : Tim = ⊤ := Subgroup.index_eq_one.mp hTim1
    intro r hr
    obtain ⟨n, hn, o, ho, hrn⟩ := hfrat r hr
    have hφn : φ ⟨n, hn⟩ ∈ Tim := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨t', ht', hφt⟩ := hφn
    have ht : (t' : G) ∈ T := ht'
    have hto : (t' : G)⁻¹ * n ∈ O := by
      have := (QuotientGroup.eq (a := (⟨t', hNB t'.2⟩ : B)) (b := ⟨n, hNB hn⟩)).mp hφt
      have h2 := Subgroup.mem_subgroupOf.mp this
      simpa using h2
    refine ⟨t', ht, (t' : G)⁻¹ * n * o, O.mul_mem hto ho, ?_⟩
    rw [hrn]; group
  refine ⟨T, hST, hTB, hYT, hTO, le_antisymm (sup_le hTB hOB) ?_⟩
  intro b hb
  obtain ⟨t, ht, o, ho, rfl⟩ := hBTO b hb
  exact Subgroup.mul_mem_sup ht ho

omit [Finite G] in
theorem l43_normalizer_le_of_characteristic {Y Y₀ : Subgroup G} (hle : Y₀ ≤ Y)
    (hc : (Y₀.subgroupOf Y).Characteristic) : normalizer (Y : Set G) ≤ normalizer (Y₀ : Set G) := by
  intro g hg
  let φ : ↥Y ≃* ↥Y := Y.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ y : ↥Y, ((φ y : ↥Y) : G) = g * (y : G) * g⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨g, hg⟩ y
  have key : ∀ y : ↥Y, φ y ∈ Y₀.subgroupOf Y ↔ y ∈ Y₀.subgroupOf Y := fun y =>
    SetLike.ext_iff.mp (hc.fixed φ) y
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhY : h ∈ Y := hle hh
    have h1 := (key ⟨h, hhY⟩).mpr (Subgroup.mem_subgroupOf.mpr hh)
    have h2 := Subgroup.mem_subgroupOf.mp h1
    rw [hφ] at h2
    exact h2
  · intro hh
    have hhY : h ∈ Y := (Subgroup.mem_normalizer_iff.mp hg h).mpr (hle hh)
    have h2 : ((φ ⟨h, hhY⟩ : ↥Y) : G) ∈ Y₀ := by
      rw [hφ]
      exact hh
    exact Subgroup.mem_subgroupOf.mp ((key ⟨h, hhY⟩).mp (Subgroup.mem_subgroupOf.mpr h2))

end CFSG.LocalAnalysis.RankThreeTheoremC
