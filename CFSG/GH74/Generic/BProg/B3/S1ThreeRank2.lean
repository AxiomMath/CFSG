module

public import CFSG.GH74.Generic.S1.Exo.Q3HFinal
public import CFSG.GH74.Generic.BProg.B3.S1IdentRank
public import CFSG.GH74.Generic.BProg.B3.LocBalRee
public import CFSG.GH74.GLS.Prop27.LocBalFinal
public import CFSG.GH74.E2.CompCertsU34

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Filter.ClassicalOdd CFSG.Assembly CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S1.Exo
open scoped commutatorElement

theorem kg3_S_cases (hR : RankTwoStmt) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hle : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 4)
    (ψ : Q8 →* S) (hψ : Function.Injective ψ)
    (hperf : ∀ M : Subgroup S, ⁅M, M⁆ = M → M ≤ centralizer ({ψ (QuaternionGroup.a 2)} : Set S) → M = ⊥)
    (hU : ¬ StatedClassicalModel S .PSU 3 2 2) :
    StatedClassicalModel S .PSL 3 3 1 ∨ StatedClassicalModel S .PSU 3 3 1 ∨
      Nonempty (S ≃* StatedM11) := by
  classical
  have heven : Even (Nat.card S) := CFSG.GH74.even_card_of_nonabelian_simple hnonab
  have h2 : twoRank S = 2 := twoRank_eq_two hle (CFSG.Walter.two_le_twoRank S hnonab heven)
  obtain ⟨E, hE2, hE4⟩ := exists_four_of_twoRank_eq_two h2
  have hzsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, q8_z_sq, map_one]
  have hz1 : ψ (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    exact q8_z_ne (hψ (h.trans (map_one ψ).symm))
  have hthree : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f = 3 → p = 3 ∧ f = 1 := by
    intro p f hp hf hq3
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 := hq3 ▸ dvd_pow_self p (by omega : f ≠ 0)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
    subst hp3
    refine ⟨rfl, ?_⟩
    have : 3 ^ f = 3 ^ 1 := by rw [hq3]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  rcases hR S hnonab h2 with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ |
      ⟨p, f, hp, hp2, hf, h⟩ | h | h7 | h
  · exact (no_q8_of_psl2_model hp hp2 h ψ hψ).elim
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by have := hp.two_le; omega
      exact this.trans (Nat.le_self_pow (by omega) p)
    by_cases h5 : 5 ≤ p ^ f
    · exact (false_of_l3Eps_five (Or.inl rfl) hodd h5 (CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inl ⟨rfl, h⟩)) hzsq hz1 E hE2
        (by omega) hperf).elim
    · have hq3 : p ^ f = 3 := by
        have := hodd; rw [Nat.odd_iff] at this; omega
      obtain ⟨rfl, rfl⟩ := hthree p f hp hf hq3
      exact Or.inl h
  · have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by have := hp.two_le; omega
      exact this.trans (Nat.le_self_pow (by omega) p)
    by_cases h5 : 5 ≤ p ^ f
    · exact (false_of_l3Eps_five (Or.inr rfl) hodd h5 (CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inr ⟨rfl, h⟩)) hzsq hz1 E hE2
        (by omega) hperf).elim
    · have hq3 : p ^ f = 3 := by
        have := hodd; rw [Nat.odd_iff] at this; omega
      obtain ⟨rfl, rfl⟩ := hthree p f hp hf hq3
      exact Or.inr (Or.inl h)
  · exact (hU h).elim
  · obtain ⟨e⟩ := h7
    exact (no_q8_of_alt7 e ψ hψ).elim
  · exact Or.inr (Or.inr h)

theorem isLocBal32_of_locBal2 {K : Type} [Group K] [Finite K] (hc : center K = ⊥)
    (hLB : GLS.Prop27.LocBal2 (fun S _ => Nonempty (S ≃* K))) (B : Subgroup (MulAut K))
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 K B := by
  refine isLocBal32_of_oddCore (fun z hz => ?_) (fun H hInn t ht => ?_) B hB
  · have : z ∈ center K := Subgroup.mem_center_iff.2 hz
    rw [hc] at this
    exact Subgroup.mem_bot.1 this
  · classical
    have : Finite (MulAut K) :=
      Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
    obtain ⟨Inn, hInnDef⟩ : ∃ Inn : Subgroup (MulAut K), Inn = (MulAut.conj : K →* MulAut K).range :=
      ⟨_, rfl⟩
    have hInnH : Inn ≤ H := hInnDef ▸ hInn
    have hInnN : Inn.Normal := by
      rw [hInnDef]
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨s, rfl⟩ := hn
      exact ⟨g s, (GLS.Prop27.mul_conj_mul_inv g s).symm ▸ rfl⟩
    have hNn : (Inn.subgroupOf H).Normal := Subgroup.normal_subgroupOf
    have hiso : Nonempty (↥(Inn.subgroupOf H) ≃* K) := by
      refine ⟨(Subgroup.subgroupOfEquivOfLe hInnH).trans ?_⟩
      rw [hInnDef]
      exact (MonoidHom.ofInjective (GLS.Prop27.conj_injective_of_center_bot hc)).symm
    have hcent : centralizer ((Inn.subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊥ := by
      rw [eq_bot_iff]
      intro φ hφ
      rw [Subgroup.mem_bot]
      refine Subtype.ext ?_
      refine MulEquiv.ext fun s => ?_
      have hconj : ∀ s : K, MulAut.conj s ∈ Inn := fun s => by
        rw [hInnDef]; exact ⟨s, rfl⟩
      have hmem : ∀ s : K, (⟨MulAut.conj s, hInnH (hconj s)⟩ : ↥H) ∈ Inn.subgroupOf H :=
        fun s => hconj s
      have h1 := Subgroup.mem_centralizer_iff.mp hφ _ (hmem s)
      have h2 : (MulAut.conj s) * (φ : MulAut K) = (φ : MulAut K) * MulAut.conj s :=
        congrArg Subtype.val h1
      have h3 : MulAut.conj ((φ : MulAut K) s) = MulAut.conj s := by
        rw [← GLS.Prop27.mul_conj_mul_inv, ← h2, mul_assoc, mul_inv_cancel, mul_one]
      have h4 := GLS.Prop27.conj_injective_of_center_bot hc h3
      simpa using h4
    have hbot := hLB ↥H (Inn.subgroupOf H) hNn hiso hcent t ht
    exact (GLS.Prop27.involutionOddCore_eq_bot_iff' t).mpr hbot

section LocBal


theorem kg3_locBal {X : Type} [Group X] [Finite X] (hX : Gen4 X) {M : Subgroup X}
    (hM : IsQuasisimple ↥M) (φ : Q8 →* X) (hφ : Function.Injective φ)
    (hcent : ∀ g : Q8, ∀ m ∈ M, φ g * m = m * φ g) (ψ : Q8 →* X) (hψM : ∀ g, ψ g ∈ M)
    (hψZ : ¬ ∀ m ∈ M, ψ (QuaternionGroup.a 2) * m = m * ψ (QuaternionGroup.a 2))
    (hperf : ∀ P : Subgroup X, ⁅P, P⁆ = P → P ≤ M →
      P ≤ centralizer ({ψ (QuaternionGroup.a 2)} : Set X) → P = ⊥)
    (B : Subgroup (MulAut (↥M ⧸ center ↥M))) (hB : ∀ b ∈ B, b * b = 1) :
    IsLocBal32 (↥M ⧸ center ↥M) B := by
  classical
  have : IsSimpleGroup (↥M ⧸ center ↥M) := hM.2.1
  have hnonab := hM.2.2
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set ψM : Q8 →* ↥M := ψ.codRestrict M hψM with hψMdef
  set ψS : Q8 →* ↥M ⧸ center ↥M := π.comp ψM with hψS
  set yM : ↥M := ⟨ψ (QuaternionGroup.a 2), hψM _⟩ with hyM
  have hyc : yM ∉ center ↥M := fun h => hψZ fun m hm =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨m, hm⟩)).symm
  have hψinj : Function.Injective ψS := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hg1
    have hgc : ψM g ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 hg
    apply hyc
    rcases q8_nonid_cases g hg1 with h1 | h1
    · have : ψM g = yM := Subtype.ext (by simp [ψM, yM, h1])
      rwa [this] at hgc
    · have : ψM g * ψM g = yM := Subtype.ext (by
        simp only [ψM, yM, MonoidHom.codRestrict_apply, Subgroup.coe_mul, ← map_mul, h1])
      rw [← this]
      exact Subgroup.mul_mem _ hgc hgc
  have hψz : ψS (QuaternionGroup.a 2) = π yM := rfl
  have hperfS : ∀ P : Subgroup (↥M ⧸ center ↥M), ⁅P, P⁆ = P →
      P ≤ centralizer ({ψS (QuaternionGroup.a 2)} : Set (↥M ⧸ center ↥M)) → P = ⊥ := by
    intro P hP hPc
    refine perfect_cent_descent yM ?_ P hP ?_
    · intro M' hM' hM'c
      have hperf' : ⁅M'.map M.subtype, M'.map M.subtype⁆ = M'.map M.subtype := by
        rw [← Subgroup.map_commutator, hM']
      have hle : M'.map M.subtype ≤ centralizer ({ψ (QuaternionGroup.a 2)} : Set X) := by
        rintro _ ⟨m, hm, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hM'c hm))
      have hbot := hperf _ hperf' (Subgroup.map_subtype_le M') hle
      exact (Subgroup.map_eq_bot_iff_of_injective M' M.subtype_injective).1 hbot
    · intro m hm
      have := Subgroup.mem_centralizer_singleton_iff.1 (hPc hm)
      rw [hψz] at this
      exact this
  have hle : ∀ E : Subgroup (↥M ⧸ center ↥M), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 4 := fun E hEc hE2 =>
    CFSG.GH74.Generic.S1.card_le_four_of_quaternion_centralizer hX φ hφ hcent E
      ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact hE2 x hx⟩
  have hU : ¬ StatedClassicalModel (↥M ⧸ center ↥M) .PSU 3 2 2 := by
    intro h
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hcert := (CFSG.GH74.E2.rankCertified_SU3_four (q := 2 ^ 2) (by norm_num) hK).of_mulEquiv e.symm
    exact S1IdentRank.false_of_rankCertified_quaternion_centralizer hX φ hφ hcent (r := 3) (by norm_num)
      hcert
  have hc : center (↥M ⧸ center ↥M) = ⊥ := GLS.Prop27.center_quotient_eq_bot hM
  have hP27 := GLS.Prop27.prop27LocalBalance
  rcases kg3_S_cases rankTwoStmt_proved hnonab hle ψS hψinj hperfS hU with h | h | h
  · have hshape : CFSG.GH74.E2.ShapeL33 (↥M ⧸ center ↥M) :=
      CFSG.GH74.lieModel_of_statedClassicalModel (by decide) h
    exact isLocBal32_of_locBal2 hc (fun Y _ _ N hN he hcN => hP27.L33 Y N hN
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv he.some.symm hshape) hcN) B hB
  · have hshape : CFSG.GH74.E2.ShapeU33 (↥M ⧸ center ↥M) :=
      CFSG.GH74.lieModel_of_statedClassicalModel (by decide) h
    exact isLocBal32_of_locBal2 hc (fun Y _ _ N hN he hcN => hP27.U33 Y N hN
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv he.some.symm hshape) hcN) B hB
  · obtain ⟨e⟩ := h
    have hshape : CFSG.GH74.E2.ShapeM11 (↥M ⧸ center ↥M) :=
      CFSG.GH74.isSporadic_M11_of_mulEquiv_statedM11 e
    exact isLocBal32_of_locBal2 hc (fun Y _ _ N hN he hcN => hP27.M11 Y N hN
      ⟨he.some.trans hshape.some⟩ hcN) B hB

end LocBal

end S1Three

end CFSG.GH74.Generic.BProg.B3
