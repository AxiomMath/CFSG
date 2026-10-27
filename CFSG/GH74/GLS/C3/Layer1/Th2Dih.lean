module

public import CFSG.GH74.GLS.C3.Layer1.Th2Shape
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.Back112Kfacts
public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

namespace Dih

section Transfer

variable {G D : Type} [Group G] [Group D]

open CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral (IsEA)

theorem rankTwoShape_of_injective {P : Subgroup G} (ι : D →* G) (hι : Function.Injective ι)
    (hP : ι.range = P)
    (h1 : ∀ V : Subgroup D, IsEA V → Nat.card ↥V ≤ 4)
    (h2 : ∀ V : Subgroup D, IsEA V → ∃ W : Subgroup D, V ≤ W ∧ IsEA W ∧ Nat.card ↥W = 4)
    (h3 : ∀ W₁ W₂ : Subgroup D, IsEA W₁ → Nat.card ↥W₁ = 4 → IsEA W₂ → Nat.card ↥W₂ = 4 →
      ∃ z ∈ W₁, z ∈ W₂ ∧ z * z = 1 ∧ z ≠ 1) :
    RankTwoShape P := by
  have hEA : ∀ {A : Subgroup G}, A ≤ P → CFSG.IsElementaryAbelian 2 ↥A → IsEA (A.comap ι) := by
    intro A hAP hA d hd
    obtain ⟨hab, hsq⟩ := Back.forall_of_isElementaryAbelian hA
    refine ⟨hι ?_, fun d' hd' => hι ?_⟩
    · rw [map_mul, map_one]; exact hsq _ hd
    · rw [map_mul, map_mul]; exact hab _ hd _ hd'
  have hcard : ∀ {A : Subgroup G}, A ≤ P → Nat.card ↥(A.comap ι) = Nat.card ↥A := by
    intro A hAP
    have h : Nat.card ↥((A.comap ι).map ι) = Nat.card ↥(A.comap ι) :=
      Subgroup.card_map_of_injective hι
    rw [Subgroup.map_comap_eq_self (hP ▸ hAP)] at h
    exact h.symm
  refine ⟨fun A hAP hA => ?_, fun A hAP hA => ?_, fun U₁ U₂ hU₁ hU₂ => ?_⟩
  · rw [← hcard hAP]
    exact h1 _ (hEA hAP hA)
  · obtain ⟨W, hVW, hW, hc⟩ := h2 _ (hEA hAP hA)
    refine ⟨W.map ι, fun a ha => ?_, ?_, ?_, ?_⟩
    · obtain ⟨d, rfl⟩ : a ∈ ι.range := hP ▸ hAP ha
      exact ⟨d, hVW ha, rfl⟩
    · rintro _ ⟨w, -, rfl⟩
      exact (hP ▸ ⟨w, rfl⟩ : ι w ∈ P)
    · refine Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
      · obtain ⟨w, hw, rfl⟩ := hu
        obtain ⟨w', hw', rfl⟩ := hv
        rw [← map_mul, ← map_mul, (hW w hw).2 w' hw']
      · obtain ⟨w, hw, rfl⟩ := hu
        rw [← map_mul, (hW w hw).1, map_one]
    · rw [Subgroup.card_map_of_injective hι]; exact hc
  · obtain ⟨hle₁, hE₁, hc₁⟩ := hU₁
    obtain ⟨hle₂, hE₂, hc₂⟩ := hU₂
    obtain ⟨z, hz₁, hz₂, hzz, hz1⟩ := h3 _ _ (hEA hle₁ hE₁) (by rw [hcard hle₁]; exact hc₁)
      (hEA hle₂ hE₂) (by rw [hcard hle₂]; exact hc₂)
    refine ⟨ι z, hz₁, hz₂, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [sq, ← map_mul, hzz, map_one]) ?_
    intro h
    exact hz1 (hι (by rw [h, map_one]))

end Transfer

section Dihedral

open DihedralGroup CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral

variable {k : ℕ}

def fourSubAt (k : ℕ) [NeZero k] (hk : 2 ∣ k) (i : ZMod k) : Subgroup (DihedralGroup k) where
  carrier := {g | g = r 0 ∨ g = r ((k / 2 : ℕ) : ZMod k) ∨ g = sr i ∨
    g = sr (i + ((k / 2 : ℕ) : ZMod k))}
  one_mem' := Or.inl (DihedralGroup.one_def).symm
  mul_mem' := by
    intro a b ha hb
    have hh := half_add_half hk
    have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
    have hsub : ∀ a : ZMod k, a - ((k / 2 : ℕ) : ZMod k) = a + ((k / 2 : ℕ) : ZMod k) :=
      fun a => by rw [sub_eq_add_neg, hneg]
    have hadd : ∀ a : ZMod k, a + ((k / 2 : ℕ) : ZMod k) + ((k / 2 : ℕ) : ZMod k) = a :=
      fun a => by rw [add_assoc, hh, add_zero]
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, hh, hneg, hsub, hadd]
  inv_mem' := by
    intro a ha
    have hh := half_add_half hk
    have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hneg]

theorem mem_fourSubAt_iff [NeZero k] (hk : 2 ∣ k) (i : ZMod k) (g : DihedralGroup k) :
    g ∈ fourSubAt k hk i ↔ g = r 0 ∨ g = r ((k / 2 : ℕ) : ZMod k) ∨ g = sr i ∨
      g = sr (i + ((k / 2 : ℕ) : ZMod k)) := Iff.rfl

theorem card_fourSubAt [NeZero k] (hk : 2 ∣ k) (i : ZMod k) :
    Nat.card (fourSubAt k hk i) = 4 := by
  have hne := half_ne_zero hk (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne k)) hk)
  have hset : ((fourSubAt k hk i : Subgroup (DihedralGroup k)) : Set (DihedralGroup k)) =
      {r 0, r ((k / 2 : ℕ) : ZMod k), sr i, sr (i + ((k / 2 : ℕ) : ZMod k))} := by
    ext g
    simp [mem_fourSubAt_iff]
  have h1 : Nat.card (fourSubAt k hk i) = ((fourSubAt k hk i : Subgroup (DihedralGroup k)) :
      Set (DihedralGroup k)).ncard := Nat.card_coe_set_eq _
  rw [h1, hset]
  have d1 : r (0 : ZMod k) ≠ r ((k / 2 : ℕ) : ZMod k) :=
    fun h => hne (DihedralGroup.r.inj h).symm
  have d2 : sr i ≠ sr (i + ((k / 2 : ℕ) : ZMod k)) := fun h => hne (by
    have := DihedralGroup.sr.inj h
    exact (add_eq_left.1 this.symm))
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d2]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by simp, by simp⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨d1, ?_, ?_⟩ <;> intro h <;> cases h

theorem isEA_fourSubAt [NeZero k] (hk : 2 ∣ k) (i : ZMod k) : IsEA (fourSubAt k hk i) := by
  have hh := half_add_half hk
  have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
  have hsub : ∀ a : ZMod k, a - ((k / 2 : ℕ) : ZMod k) = a + ((k / 2 : ℕ) : ZMod k) :=
    fun a => by rw [sub_eq_add_neg, hneg]
  have hadd : ∀ a : ZMod k, a + ((k / 2 : ℕ) : ZMod k) + ((k / 2 : ℕ) : ZMod k) = a :=
    fun a => by rw [add_assoc, hh, add_zero]
  intro a ha
  rw [mem_fourSubAt_iff] at ha
  refine ⟨?_, fun b hb => ?_⟩
  · rcases ha with rfl | rfl | rfl | rfl <;> simp [r_mul_r, sr_mul_sr, hh]
  · rw [mem_fourSubAt_iff] at hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, hh, hneg, hsub, hadd]

theorem exists_le_fourSubAt [NeZero k] (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)}
    (hV : IsEA V) : ∃ i, V ≤ fourSubAt k hk i := by
  by_cases h : ∃ i, sr i ∈ V
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, fun g hg => ?_⟩
    rcases sq_eq_one_cases hk (hV g hg).1 with rfl | rfl | ⟨j, rfl⟩
    · exact Or.inl DihedralGroup.one_def
    · exact Or.inr (Or.inl rfl)
    · rcases refl_mem_four hk hV hi hg with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · push Not at h
    refine ⟨0, fun g hg => ?_⟩
    rcases sq_eq_one_cases hk (hV g hg).1 with rfl | rfl | ⟨j, rfl⟩
    · exact Or.inl DihedralGroup.one_def
    · exact Or.inr (Or.inl rfl)
    · exact absurd hg (h j)

theorem card_le_four_of_isEA [NeZero k] (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)}
    (hV : IsEA V) : Nat.card ↥V ≤ 4 := by
  obtain ⟨i, hi⟩ := exists_le_fourSubAt hk hV
  rw [← card_fourSubAt hk i]
  exact Subgroup.card_le_of_le hi

theorem exists_four_ge_of_isEA [NeZero k] (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)}
    (hV : IsEA V) : ∃ W : Subgroup (DihedralGroup k), V ≤ W ∧ IsEA W ∧ Nat.card ↥W = 4 := by
  obtain ⟨i, hi⟩ := exists_le_fourSubAt hk hV
  exact ⟨fourSubAt k hk i, hi, isEA_fourSubAt hk i, card_fourSubAt hk i⟩

theorem exists_common_involution [NeZero k] (hk : 2 ∣ k) {W₁ W₂ : Subgroup (DihedralGroup k)}
    (h₁ : IsEA W₁) (c₁ : Nat.card ↥W₁ = 4) (h₂ : IsEA W₂) (c₂ : Nat.card ↥W₂ = 4) :
    ∃ z ∈ W₁, z ∈ W₂ ∧ z * z = 1 ∧ z ≠ 1 := by
  refine ⟨z₀ k, z₀_mem_four hk h₁ c₁, z₀_mem_four hk h₂ c₂, z₀_mul_self hk, fun h => ?_⟩
  exact half_ne_zero hk (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne k)) hk)
    (DihedralGroup.r.inj (h.trans DihedralGroup.one_def))

end Dihedral

end Dih

theorem rankTwoShape_of_dihedral {G : Type} [Group G] [Finite G] {P : Subgroup G} {n : ℕ}
    (h : IVK.IsDihedralTwoGroup ↥P n) : RankTwoShape P := by
  obtain ⟨hn, k, hk, hk2, ⟨e⟩⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h4 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
  have hkd : 2 ∣ k := ⟨2 ^ m, by omega⟩
  have : NeZero k := ⟨by omega⟩
  refine Dih.rankTwoShape_of_injective (P.subtype.comp e.symm.toMonoidHom)
    (P.subtype_injective.comp e.symm.injective) ?_
    (fun V hV => Dih.card_le_four_of_isEA hkd hV)
    (fun V hV => Dih.exists_four_ge_of_isEA hkd hV)
    (fun W₁ W₂ h₁ c₁ h₂ c₂ => Dih.exists_common_involution hkd h₁ c₁ h₂ c₂)
  have hsurj : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.symm.surjective
  rw [MonoidHom.range_comp, hsurj, Subgroup.map_top, Subgroup.range_subtype]

namespace Dih

theorem exists_dihedral_of_sylow_kBar {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (e : kBar K ≃* IVK.L2 F) : ∃ n : ℕ, IVK.IsDihedralTwoGroup ↥P n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥K →* MulAut (kBar K) :=
    (MulAut.conj : kBar K →* MulAut (kBar K)).comp (QuotientGroup.mk' (pPrimeCore 2 ↥K))
  have hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) :=
    IVK.conj_injective_of_L2 e
  set P' : Subgroup ↥K := P.subgroupOf K with hP'
  have hinj : Function.Injective (φ.comp P'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have h3 : (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (p : ↥K) = 1 := hcen (by
      rw [map_one]; exact hp)
    have h4 : (p : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : ((p : ↥K) : G) ∈ pPrimeCoreOf 2 K :=
      Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨(p : ↥K).2, h4⟩
    have hp' : ((p : ↥K) : G) ∈ P := Subgroup.mem_subgroupOf.1 p.2
    have h7 : ((p : ↥K) : G) ∈ P ⊓ pPrimeCoreOf 2 K := ⟨hp', h5⟩
    rw [Back.Setup91.inf_pPrimeCoreOf_eq_bot K hP.isPGroup, Subgroup.mem_bot] at h7
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h7)
  have hrange : φ.range = IVK.innAut (kBar K) := by
    rw [MonoidHom.range_comp, QuotientGroup.range_mk', Subgroup.map_top]
    rfl
  have hSylTop : IsSylowOf 2 P' ⊤ := by
    rw [← isSylowOf_map_subtype_iff K, hP', Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype, inf_eq_left.2 hP.le]
    exact hP
  have hSyl : IsSylowOf 2 (P'.map φ) (IVK.innAut (kBar K)) := by
    have := Thm1.isSylowOf_map_hom φ hSylTop
    rwa [Subgroup.map_top, hrange] at this
  obtain ⟨T', hBT'⟩ := hSyl.isPGroup.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := IVK.ivk_1_2a_exists F hF (kBar K) e T'
  have hBN : P'.map φ ≤ (N.T : Subgroup (MulAut (kBar K))) := by rw [hNT]; exact hBT'
  have hPeq : N.P = P'.map φ :=
    hSyl.eq_of_le (le_inf hBN hSyl.le) inf_le_right N.T.isPGroup'.to_inf_left
  obtain ⟨n, hn⟩ := IVK.ivk_1_2c F hF (kBar K) e' N
  have hrange' : (φ.comp P'.subtype).range = N.P := by
    rw [hPeq, MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : ↥P ≃* ↥N.P :=
    (Subgroup.subgroupOfEquivOfLe hP.le).symm.trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange'))
  exact ⟨n, Thm1.isDihedralTwoGroup_of_equiv ψ hn⟩

end Dih

theorem rankTwoShape_sylow_L2 {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) (_hq : IsQuasisimple (kBar K)) {Pr : ℕ → Prop}
    (hPr : ∀ q, Pr q → Odd q) (h : HasL2Model (kBar K) Pr) : RankTwoShape P := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    Thm1.exists_l2_model_of_hasL2Model (Back.hasL2Model_mono hPr h)
  obtain ⟨n, hn⟩ := Dih.exists_dihedral_of_sylow_kBar hP hF e
  exact rankTwoShape_of_dihedral hn

theorem card_sylow_L2_five {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) (h : HasL2Model (kBar K) (fun q => q = 5)) : Nat.card ↥P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, F, hFf, hFin, hf, hPr, hcard, ⟨e⟩⟩ := Back.exists_psl_model_of_hasL2Model h
  have h5 : Nat.card F = 5 := by rw [hcard]; exact hPr
  have hF : IVK.L2Field F := ⟨by rw [h5]; decide, by rw [h5]; decide⟩
  have hK60 : Nat.card (kBar K) = 60 := by
    rw [IVK.ivk_1_2b F hF (kBar K) (e.trans (IVK.L2.equivPSL F).symm), h5]
    norm_num
  have hKcard : Nat.card ↥K = Nat.card (kBar K) * Nat.card ↥(pPrimeCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have h60 : (60 : ℕ).factorization 2 = 2 := by
    have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Back.Setup91.factorization_two_of_odd (by decide : Odd 15)]
  rw [hP.card_eq, hKcard, hK60, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
    Finsupp.add_apply, Back.Setup91.factorization_two_of_odd hodd, add_zero, h60]
  norm_num

end CFSG.GH74.GLS.Th2
