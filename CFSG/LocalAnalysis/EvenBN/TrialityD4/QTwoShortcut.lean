module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoEndgame

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem two_mul_pow_five_lt_of_two_mul_pow_ten_le {q n : ℕ} (hq : 2 ≤ q)
    (h : 2 * q ^ 10 ≤ n * q ^ 4) : 2 * q ^ 5 < n := by
  by_contra hle
  push_neg at hle
  have h1 : n * q ^ 4 ≤ 2 * q ^ 5 * q ^ 4 := Nat.mul_le_mul hle le_rfl
  have h2 : 2 * q ^ 10 = 2 * q ^ 9 * q := by ring
  have h3 : 2 * q ^ 9 * 2 ≤ 2 * q ^ 9 * q := Nat.mul_le_mul le_rfl hq
  have h4 : 0 < q ^ 9 := pow_pos (by omega) 9
  have h5 : 2 * q ^ 5 * q ^ 4 = 2 * q ^ 9 := by ring
  linarith

theorem exists_isElemAbelian_two_mul_card_le {A B : Subgroup G} {y : G}
    (hA : IsElemAbelian 2 A) (hBA : B ≤ A) (hB : 2 ≤ Nat.card B) (hy : y * y = 1)
    (hyA : ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ E ≤ centralizer ({y} : Set G) ∧
      2 * Nat.card A ≤ Nat.card E * Nat.card B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm' : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hy2 : y ^ 2 = 1 := by rw [sq]; exact hy
  by_cases hyA' : y ∈ A
  · refine ⟨A, hA, le_centralizer_of_isElemAbelian_D4 hA hyA', ?_⟩
    calc 2 * Nat.card A ≤ Nat.card B * Nat.card A := Nat.mul_le_mul hB le_rfl
      _ = Nat.card A * Nat.card B := mul_comm _ _
  ·
    obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = centralizer ({y} : Set G) ⊓ A := ⟨_, rfl⟩
    have hmemC : ∀ x, x ∈ C ↔ x ∈ centralizer ({y} : Set G) ∧ x ∈ A := fun x => by
      rw [hC, Subgroup.mem_inf]
    have hCA : C ≤ A := fun x hx => ((hmemC x).1 hx).2
    have hyC : y ∉ C := fun h => hyA' (hCA h)
    have hy1 : y ≠ 1 := fun h => hyA' (by rw [h]; exact one_mem A)
    have hcy : ∀ x ∈ C, x * y = y * x := fun x hx =>
      mem_centralizer_singleton_iff.1 ((hmemC x).1 hx).1
    have hu : ∀ b ∈ A, y * b * y⁻¹ ∈ A := by
      intro b hb
      have h1 : y * b * y⁻¹ * b⁻¹ ∈ A := hBA (hyA b hb)
      have h2 : y * b * y⁻¹ = y * b * y⁻¹ * b⁻¹ * b := by group
      rw [h2]
      exact mul_mem h1 hb
    have hmul : ∀ a ∈ A, ∀ b ∈ A,
        y * (a * b) * y⁻¹ * (a * b)⁻¹ = (y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
      intro a ha b hb
      have hab : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := hcomm' _ (inv_mem hb) _ (inv_mem ha)
      have hua : y * b * y⁻¹ * a⁻¹ = a⁻¹ * (y * b * y⁻¹) :=
        hcomm' _ (hu b hb) _ (inv_mem ha)
      calc y * (a * b) * y⁻¹ * (a * b)⁻¹
          = (y * a * y⁻¹) * (y * b * y⁻¹) * (b⁻¹ * a⁻¹) := by group
        _ = (y * a * y⁻¹) * (y * b * y⁻¹) * (a⁻¹ * b⁻¹) := by rw [hab]
        _ = (y * a * y⁻¹) * (y * b * y⁻¹ * a⁻¹) * b⁻¹ := by simp only [mul_assoc]
        _ = (y * a * y⁻¹) * (a⁻¹ * (y * b * y⁻¹)) * b⁻¹ := by rw [hua]
        _ = (y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹) := by simp only [mul_assoc]
    obtain ⟨phi, hphi⟩ : ∃ phi : A →* G,
        ∀ a : A, phi a = y * (a : G) * y⁻¹ * (a : G)⁻¹ := by
      refine ⟨MonoidHom.mk' (fun a : A => y * (a : G) * y⁻¹ * (a : G)⁻¹) fun a b => ?_,
        fun a => rfl⟩
      exact hmul a a.2 b b.2
    have hrange : phi.range ≤ B := by
      intro x hx
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
      rw [hphi]
      exact hyA a a.2
    have hKle : phi.ker.map A.subtype ≤ C := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      have h1 : y * (a : G) * y⁻¹ * (a : G)⁻¹ = 1 :=
        (hphi a).symm.trans (MonoidHom.mem_ker.1 ha)
      have h2 : y * (a : G) * y⁻¹ = (a : G) := mul_inv_eq_one.1 h1
      have h3 : y * (a : G) = (a : G) * y := mul_inv_eq_iff_eq_mul.1 h2
      exact (hmemC _).2 ⟨mem_centralizer_singleton_iff.2 h3.symm, a.2⟩
    have hKC : Nat.card phi.ker ≤ Nat.card C := by
      have hmap : Nat.card (phi.ker.map A.subtype) = Nat.card phi.ker :=
        Subgroup.card_map_of_injective A.subtype_injective
      rw [← hmap]
      exact Subgroup.card_le_of_le hKle
    have hkey : Nat.card A ≤ Nat.card C * Nat.card B := by
      calc Nat.card A = Nat.card (↥A ⧸ phi.ker) * Nat.card phi.ker :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup phi.ker
        _ = Nat.card phi.range * Nat.card phi.ker := by
            rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange phi).toEquiv]
        _ ≤ Nat.card B * Nat.card C :=
            Nat.mul_le_mul (Subgroup.card_le_of_le hrange) hKC
        _ = Nat.card C * Nat.card B := mul_comm _ _
    have hzp : ∀ w ∈ zpowers y, w = 1 ∨ w = y := by
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left
        rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, hy, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, zpow_two, hy, one_zpow, one_mul]
    have hzsq : ∀ w ∈ zpowers y, w ^ 2 = 1 := by
      intro w hw
      rcases hzp w hw with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, hy2]
    have hCz : C ⊓ zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwC, hwy⟩ := Subgroup.mem_inf.1 hw
      rcases hzp w hwy with h1 | h1
      · exact Subgroup.mem_bot.2 h1
      · rw [h1] at hwC
        exact absurd hwC hyC
    have hcomm : ∀ x ∈ C, ∀ z ∈ zpowers y, x * z = z * x := by
      intro x hx z hz
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      exact (show Commute x y from hcy x hx).zpow_right k
    have hCcomm : IsMulCommutative C :=
      ⟨⟨fun a b => Subtype.ext (hcomm' _ (hCA a.2) _ (hCA b.2))⟩⟩
    have hEcomm : IsMulCommutative (C ⊔ zpowers y : Subgroup G) :=
      isMulCommutative_sup' hcomm
    have hEcard : Nat.card (C ⊔ zpowers y : Subgroup G) = 2 * Nat.card C := by
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C (zpowers y) hcomm).1
      rw [hCz, Subgroup.card_bot, Nat.card_zpowers, orderOf_eq_prime hy2 hy1] at h1
      omega
    have hsq : ∀ x ∈ (C ⊔ zpowers y : Subgroup G), x ^ 2 = 1 := by
      intro x hx
      rw [← SetLike.mem_coe,
        (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C (zpowers y) hcomm).2,
        Set.mem_mul] at hx
      obtain ⟨c, hc, w, hw, rfl⟩ := hx
      rw [(show Commute c w from hcomm c hc w hw).mul_pow, hA.2 c (hCA hc), hzsq w hw,
        one_mul]
    have hEsub : (C ⊔ zpowers y : Subgroup G) ≤ centralizer ({y} : Set G) :=
      sup_le (fun x hx => ((hmemC x).1 hx).1)
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    refine ⟨C ⊔ zpowers y, ⟨hEcomm, hsq⟩, hEsub, ?_⟩
    rw [hEcard]
    calc 2 * Nat.card A ≤ 2 * (Nat.card C * Nat.card B) := Nat.mul_le_mul le_rfl hkey
      _ = 2 * Nat.card C * Nat.card B := by ring

namespace Setup

variable {L : Subgroup G} {f : ℕ} {t : G}

theorem false_of_commutator_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : Odd f)
    {P A B : Subgroup G} (hP : IsPGroup 2 P) (htN : t ∈ normalizer (P : Set G)) (htP : t ∉ P)
    (hSP : d.S.map L.subtype ≤ P)
    (hN : normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) =
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ⊔ P)
    (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = (2 ^ f) ^ 10) (hBA : B ≤ A)
    (hBcard : Nat.card B = (2 ^ f) ^ 4) (hPA : ∀ y ∈ P, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B) :
    False := by
  have hf1 : 1 ≤ f := by
    obtain ⟨m, hm⟩ := hf
    omega
  have hq : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hB2 : 2 ≤ Nat.card B := by
    rw [hBcard]
    calc 2 ≤ 2 ^ f := hq
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)
  have hT := h.exists_sylow_eq_sup_zpowers_of_odd d hf hP htN hSP hN
  refine h.false_of_isSylow_sup_zpowers_of_lt_card d hT htN htP (fun y hy hy2 => ?_)
  obtain ⟨E, hE, hEC, hcard⟩ :=
    exists_isElemAbelian_two_mul_card_le hA hBA hB2 hy2 (hPA y hy)
  refine ⟨E, hE, hEC, ?_⟩
  rw [hAcard, hBcard] at hcard
  exact two_mul_pow_five_lt_of_two_mul_pow_ten_le hq hcard

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
