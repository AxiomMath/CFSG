module

public import CFSG.CGT.Foote82.T66.Proof511Syl
public import CFSG.CGT.Foote82.T66.Proof511Rows
public import CFSG.CGT.Foote82.T66.Proof511Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Reduction

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup

theorem psp4_card_ne {q N : ℕ} (h5 : 5 ≤ q) (hq : q % 8 = 3 ∨ q % 8 = 5)
    (hN : N = 720 ∨ N = 5040)
    (h : N = q * (q ^ 2 - 1) ∨ N = q ^ 2 * ((q ^ 2) ^ 2 - 1) ∨
      ∃ k : ℕ, k ^ 2 = q ∧ 3 ≤ k ∧ N = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1))) : False := by
  rcases h with h | h | ⟨k, -, hk3, h⟩
  · have hq17 : q ≤ 17 := by
      by_contra hlt
      have h1 : 324 ≤ q ^ 2 := by nlinarith
      have h2 : 18 * 323 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    rcases hN with rfl | rfl <;> interval_cases q <;> first | omega | simp_all
  · have h1 : 25 ≤ q ^ 2 := by nlinarith
    have h2 : 625 ≤ (q ^ 2) ^ 2 := by nlinarith
    have h3 : 25 * 624 ≤ q ^ 2 * ((q ^ 2) ^ 2 - 1) := Nat.mul_le_mul h1 (by omega)
    omega
  · have h1 : 9 ≤ k ^ 2 := by nlinarith
    have h2 : 81 ≤ k ^ 4 := by nlinarith
    have h3 : 8 * 80 ≤ (k ^ 2 - 1) * (k ^ 4 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : 81 * (8 * 80) ≤ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := Nat.mul_le_mul h2 h3
    omega

variable {G : Type} [Group G] [Finite G]

theorem card_of_alt_six_or_seven {L : Type*} [Group L]
    (hk : Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (L ≃* alternatingGroup (Fin 7))) :
    Nat.card L = 360 ∨ Nat.card L = 2520 := by
  rcases hk with he | he
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := he
    right
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

namespace Red

variable {J L : Subgroup G} {H : Type} [Group H] [Finite H] (r : Red J L H)
include r

theorem not_central_involution {w : H} (hw : w ∈ r.Lb) (hwo : orderOf w = 2)
    (hwc : ∀ y ∈ r.Lb, y * w = w * y) : False := by
  haveI := r.simpleL
  have hc : r.eL ⟨w, hw⟩ ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := r.eL.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg r.eL (Subtype.ext (hwc y y.2))
  rw [center_eq_bot_of_simple r.nonabL, mem_bot, MulEquiv.map_eq_one_iff] at hc
  have h1 : w = 1 := congrArg Subtype.val hc
  rw [h1, orderOf_one] at hwo
  exact absurd hwo (by norm_num)

theorem psp4_row (hk : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (hL : CFSG.Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f) :
    CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSp 2 3 1 := by
  haveI := r.simple
  have hcardL : Nat.card ↥r.Lb = 360 ∨ Nat.card ↥r.Lb = 2520 := by
    rw [Nat.card_congr r.eL.toEquiv]
    exact card_of_alt_six_or_seven hk
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
    rcases hcardL with h360 | h2520
    · exact CFSG.GH74.lieModel_of_mulEquiv r.quotEquiv.symm hL
    · exfalso
      have hS : Nat.card ↥(generalizedFitting H) = 25920 := by
        rw [CFSG.GH74.card_of_lieModel_PSp (by norm_num) (by norm_num) hL]
        decide
      have hd := Subgroup.card_dvd_of_le r.le_F
      rw [hS, h2520] at hd
      norm_num at hd
  · exfalso
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h5 : 5 ≤ p ^ f := by
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨-, -, K, _, _, hK, ⟨eK⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hL
    have hs : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) := eK.symm.isSimpleGroup
    rcases CFSG.ComponentClassification.GSThmB.Catalog7Std.pComponent_of_psp4 hp hp2 hf hK h5 hs
        r.cent_eq eK r.order r.le_C r.le_F r.pcomp with ⟨w, hw, hwo, hwc⟩ | ⟨-, hc⟩
    · exact r.not_central_involution hw hwo hwc
    · refine psp4_card_ne h5 hq (N := Nat.card ↥r.Lb * 2) ?_ ?_
      · rcases hcardL with h | h <;> rw [h] <;> norm_num
      · rcases hc with hc | hc | ⟨k, hk2, hk3, hc⟩
        · exact Or.inl hc
        · exact Or.inr (Or.inl hc)
        · exact Or.inr (Or.inr ⟨k, hk2, hk3, hc⟩)

end Red

theorem reduce_b'
    (hM : CFSG.GH74.ModelsFormStatement) {X J L : Subgroup G} {z : G} (h : Hyp X J L z)
    (hk : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hsyl : ∀ P : Sylow 2 ↥J, CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(P : Subgroup ↥J)) :
    Nonempty (↥J ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 9)) ∨
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSp 2 3 1 := by
  obtain ⟨H, _, _, ⟨r⟩⟩ := h.exists_red
  haveI := r.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA8 : ∀ T : Sylow 2 ↥(generalizedFitting H),
      CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(T : Subgroup ↥(generalizedFitting H)) := by
    intro T
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥J))
    obtain ⟨e₁⟩ := r.sylow_equiv T P
    obtain ⟨Q, ⟨e₂⟩⟩ := hsyl P
    exact ⟨Q, ⟨e₁.trans e₂⟩⟩
  obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥(generalizedFitting H)))
  have D := CFSG.EvenSporadicStandard.HNRecog.GH73.A8SylowData.of_sylow T₀ (hA8 T₀)
  have hX := hM ↥(generalizedFitting H) r.nonab
    (CFSG.EvenSporadicStandard.HNRecog.GH73.three_le_twoRank_of_e16 D.exists_e16) D.gen_four
  rcases CFSG.EvenSporadicStandard.HNRecog.GH73.survivors D hX with he | he |
      ⟨p, f, hp, hp2, hf, hq, hL⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (r.lift_alt (by norm_num) e)
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inl (r.lift_alt (by norm_num) e))
  · exact Or.inr (Or.inr (r.psp4_row hk hp hp2 hf hq hL))

theorem reduce_b
    (hM : CFSG.GH74.ModelsFormStatement) {X J L : Subgroup G} {z : G} (h : Hyp X J L z)
    (hk : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hsyl : ∀ (P : Sylow 2 ↥J) (Q : Sylow 2 ↥(alternatingGroup (Fin 8))), Nonempty (↥P ≃* ↥Q)) :
    Nonempty (↥J ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 9)) ∨
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSp 2 3 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine reduce_b' hM h hk fun P => ?_
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥(alternatingGroup (Fin 8))))
  exact ⟨Q, hsyl P Q⟩

@[expose] def SporSqOne (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Blueprint.NativeSporadic.IsSporadic Y s →
    ∀ P : Sylow 2 Y, Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36

@[expose] def PSU4SqOne : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → p ^ f % 8 = 3 →
    CFSG.Blueprint.LieModel Y .PSU 4 p f →
      ∀ P : Sylow 2 Y, Nat.card {x : ↥(P : Subgroup Y) // x ^ 2 = 1} = 36

theorem reduce_a'
    (hM : CFSG.GH74.ModelsFormStatement)
    (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hM22 : SporSqOne .M22) (hM23 : SporSqOne .M23) (hJ2 : SporSqOne .J2) (hJ3 : SporSqOne .J3)
    (hMcL : SporSqOne .McL) (hU4 : PSU4SqOne)
    {X J L : Subgroup G} {z : G} (h : Hyp X J L z)
    (hk : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hsyl : ∀ P : Sylow 2 ↥J, IsA10Type ↥(P : Subgroup ↥J)) :
    Nonempty (↥J ≃* alternatingGroup (Fin 10)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 11)) ∨
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 4 3 1 := by
  obtain ⟨H, _, _, ⟨r⟩⟩ := h.exists_red
  haveI := r.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : ∀ T : Sylow 2 ↥(generalizedFitting H),
      IsA10Type ↥(T : Subgroup ↥(generalizedFitting H)) := by
    intro T
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥J))
    obtain ⟨e₁⟩ := r.sylow_equiv T P
    obtain ⟨e₂⟩ := hsyl P
    exact ⟨e₁.trans e₂⟩
  obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥(generalizedFitting H)))
  have D := A10SylowData.of_sylow T₀ (hT T₀)
  have h44 := D.sqOne T₀
  have hX := hM ↥(generalizedFitting H) r.nonab
    (CFSG.EvenSporadicStandard.HNRecog.GH73.three_le_twoRank_of_e16 D.exists_e16) D.gen_four
  have hodd : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}, p.Prime → p ≠ 2 →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f →
      CFSG.Blueprint.LieModel ↥(generalizedFitting H) t n p f →
      Nonempty (↥L ≃* alternatingGroup (Fin 7)) → False :=
    fun hp hp2 hadm hL h7 => r.false_of_alt7 hGLS hO h7 ⟨_, _, _, _, hp, hp2, hadm, hL⟩
  rcases hX with ⟨p, f, hp, hp2, hf, hL | hL⟩ | ⟨p, f, hp, hp2, hf, hL⟩ | ⟨f, hL⟩ |
      ⟨p, f, hp, hp2, hf, hq, hL⟩ | ⟨p, f, hp, hp2, hf, hq, hL⟩ | ⟨p, f, hp, hf, hq, hL⟩ |
      ⟨p, f, hp, hf, hq, hL⟩ | (hL | hL | hL | hL) | ⟨n, hn, hn', hL⟩ |
      (hL | hL | hL | hL | hL | hL | hL | hL)
  · exact absurd hL
      (CFSG.EvenSporadicStandard.HNRecog.GH73.not_g2_of_e16 D.exists_e16 hp hp2 hf)
  · exact absurd hL
      (CFSG.EvenSporadicStandard.HNRecog.GH73.not_trialityD4_of_e16 D.exists_e16 hp hp2 hf)
  · exact absurd hL (not_psp4_of_card D.card_eq hp hp2)
  · exact absurd hL (not_ree_of_card D.card_eq)
  ·
    rcases hk with h6 | h7
    · rcases r.psl4_card h6 hp hp2 hL with h3 | h9
      · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
        exact Or.inr (Or.inr (CFSG.GH74.lieModel_of_mulEquiv r.quotEquiv.symm hL))
      · exact absurd (h9 ▸ hq) (by norm_num)
    · exact (hodd hp hp2 ⟨hp, hf, by simp⟩ hL h7).elim
  ·
    rcases hk with h6 | h7
    · rcases r.psu4_card h6 hp hp2 hL with h3 | h9
      · have h36 := hU4 _ p f hp hp2 (by rw [h3]) hL T₀
        omega
      · exact absurd hL (not_psu4_of_card_of_mod_eight D.card_eq hp2 (by rw [h9]))
    · exact (hodd hp hp2 ⟨hp, hf, by simp⟩ hL h7).elim
  · exact absurd hL (not_psl5_of_card D.card_eq (Nat.odd_iff.mpr (by omega)))
  · have hp2 : p ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    exact absurd hL (not_psu5_of_card D.card_eq hp2 (Nat.odd_iff.mpr (by omega)))
  · exact absurd hL (not_l28_of_card D.card_eq)
  · exact absurd hL (not_l216_of_card D.card_eq)
  · exact absurd hL (not_l34_of_card D.card_eq)
  · exact absurd hL (not_sz8_of_card D.card_eq)
  · by_cases h10 : n = 10
    · subst h10
      obtain ⟨e⟩ := hL
      exact Or.inl (r.lift_alt (by norm_num) e)
    · by_cases h11 : n = 11
      · subst h11
        obtain ⟨e⟩ := hL
        exact Or.inr (Or.inl (r.lift_alt (by norm_num) e))
      · exact absurd hL (not_alternating_of_card D.card_eq hn (by omega))
  · exact absurd hL (not_M12_of_card D.card_eq)
  · have h36 := hM22 _ hL T₀
    omega
  · have h36 := hM23 _ hL T₀
    omega
  · exact absurd hL (not_J1_of_card D.card_eq)
  · have h36 := hJ2 _ hL T₀
    omega
  · have h36 := hJ3 _ hL T₀
    omega
  · have h36 := hMcL _ hL T₀
    omega
  · exact absurd hL (not_Ly_of_card D.card_eq)

theorem reduce_a
    (hM : CFSG.GH74.ModelsFormStatement)
    (hGLS : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hM22 : SporSqOne .M22) (hM23 : SporSqOne .M23) (hJ2 : SporSqOne .J2) (hJ3 : SporSqOne .J3)
    (hMcL : SporSqOne .McL) (hU4 : PSU4SqOne)
    {X J L : Subgroup G} {z : G} (h : Hyp X J L z)
    (hk : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hsyl : ∀ (P : Sylow 2 ↥J) (Q : Sylow 2 ↥(alternatingGroup (Fin 10))), Nonempty (↥P ≃* ↥Q)) :
    Nonempty (↥J ≃* alternatingGroup (Fin 10)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 11)) ∨
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 4 3 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine reduce_a' hM hGLS hO hM22 hM23 hJ2 hJ3 hMcL hU4 h hk fun P => ?_
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥(alternatingGroup (Fin 10))))
  obtain ⟨e₁⟩ := hsyl P Q
  obtain ⟨e₂⟩ := isA10Type_of_alt10 Q
  exact ⟨e₁.trans e₂⟩

end CFSG.CGT.Foote82.Proof511
