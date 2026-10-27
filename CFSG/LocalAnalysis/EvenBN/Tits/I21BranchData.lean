module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Toolbox

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchData

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G]

theorem fusionIsSylowIn_top (S : Sylow 2 G) : fusionIsSylowIn 2 (S : Subgroup G) ⊤ :=
  ⟨le_top, S.isPGroup', fun _ _ hP hle => S.is_maximal' hP hle⟩

theorem fusionIsSylowIn_inf_normal [Finite G] (S : Sylow 2 G) {L : Subgroup G}
    (hL : L.Normal) :
    fusionIsSylowIn 2 ((S : Subgroup G) ⊓ L) L := by
  refine ⟨inf_le_right, S.isPGroup'.to_inf_left, fun P hPL hP hle => ?_⟩
  obtain ⟨c, -, hc⟩ := secTwo_exists_conj_le (fusionIsSylowIn_top S) (le_top : P ≤ ⊤) hP
  have hmap : P.map (MulAut.conj c).toMonoidHom ≤ (S : Subgroup G) ⊓ L := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hc p hp, hL.conj_mem p (hPL hp) c⟩
  have hcard : Nat.card (P.map (MulAut.conj c).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have heq : P.map (MulAut.conj c).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge (hmap.trans hle) hcard.ge
  exact le_antisymm (heq ▸ hmap) hle

theorem eq_of_le_of_two_pow [Finite G] {N S T : Subgroup G} (hSN : S ≤ N) (hS : IsPGroup 2 S)
    (hTS : T ≤ S) {e : ℕ} (hT : Nat.card T = 2 ^ e) (hN : ¬ 2 ^ (e + 1) ∣ Nat.card N) :
    S = T := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have h1 : 2 ^ k ∣ Nat.card N := hk ▸ Subgroup.card_dvd_of_le hSN
  have h2 : 2 ^ e ∣ 2 ^ k := hk ▸ hT ▸ Subgroup.card_dvd_of_le hTS
  have hek : e ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hke : k ≤ e := by
    by_contra hlt
    exact hN (dvd_trans (Nat.pow_dvd_pow 2 (not_le.mp hlt)) h1)
  refine (Subgroup.eq_of_le_of_card_ge hTS ?_).symm
  rw [hk, hT, le_antisymm hke hek]

theorem orderOf_mul_u {t u : G} (h : SecTwoHyp G t u) : orderOf (t * u) = 4 := by
  have h2 : (t * u) ^ 2 = u ^ 2 := by rw [h.commute_tu.mul_pow, h.t_sq, one_mul]
  have h4 : (t * u) ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h2, h.z_sq]
  have h1 : ¬ (t * u) ^ 2 ^ 1 = 1 := by
    rw [pow_one, h2]
    exact h.z_ne_one
  exact orderOf_eq_prime_pow h1 h4

theorem sylow_data [Finite G] (S : Sylow 2 G) {L : Subgroup G} (hL : L.Normal) {t w : G}
    (htS : t ∈ (S : Subgroup G)) (hwS : w ∈ (S : Subgroup G)) (hwL : w ∈ L)
    (hwt : w * t = t * w) {e : ℕ} (hwe : orderOf w = 2 ^ e)
    (hN : ¬ 2 ^ (e + 1) ∣ Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    fusionIsSylowIn 2 ((S : Subgroup G) ⊓ L) L ∧
      (∀ m ∈ (S : Subgroup G) ⊓ L, t * m * t⁻¹ ∈ (S : Subgroup G) ⊓ L) ∧
      fusionIsSylowIn 2 ((S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G))
        (L ⊓ centralizer ({t} : Set G)) ∧
      (S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) = zpowers w := by
  have hP : IsPGroup 2 ((S : Subgroup G) ⊓ L : Subgroup G) := S.isPGroup'.to_inf_left
  have hP' : IsPGroup 2 ((S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    hP.to_inf_left
  have hle : (S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) ≤ L ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_right _ inf_le_right
  have hwmem : w ∈ (S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) :=
    ⟨⟨hwS, hwL⟩, mem_centralizer_singleton_iff.mpr hwt⟩
  have hzle : zpowers w ≤ (S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) :=
    zpowers_le.mpr hwmem
  have hcardw : Nat.card (zpowers w) = 2 ^ e := by rw [Nat.card_zpowers, hwe]
  have heq : (S : Subgroup G) ⊓ L ⊓ centralizer ({t} : Set G) = zpowers w :=
    eq_of_le_of_two_pow hle hP' hzle hcardw hN
  refine ⟨fusionIsSylowIn_inf_normal S hL, fun m hm => ?_,
    ⟨hle, hP', fun Q hQN hQ hSQ => ?_⟩, heq⟩
  · obtain ⟨hmS, hmL⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem htS hmS) (inv_mem htS), hL.conj_mem m hmL t⟩
  · exact (eq_of_le_of_two_pow hQN hQ (hzle.trans hSQ) hcardw hN).trans heq.symm

end CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchData

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

section SectionFour

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_branch_data (h : Sec622Bar G t u x) {L : Subgroup G} (hLn : L.Normal)
    (htL : t ∉ L) (hzL : u ^ 2 ∈ L) (htzL : ∀ j : ℕ, t * (x ^ j * u ^ 2) ∉ L) :
    ∃ M : Subgroup G, fusionIsSylowIn 2 M L ∧ (∀ m ∈ M, t * m * t⁻¹ ∈ M) ∧
      fusionIsSylowIn 2 (M ⊓ centralizer ({t} : Set G)) (L ⊓ centralizer ({t} : Set G)) ∧
      ((M ⊓ centralizer ({t} : Set G) = zpowers (u ^ 2) ∧
          (Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ∨
            Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 10)) ∨
        ∃ w : G, (w = u ∨ w = t * u) ∧ M ⊓ centralizer ({t} : Set G) = zpowers w ∧
          (Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 4 ∨
            Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 20)) := by
  obtain ⟨S, hS⟩ := h.secTwo.exists_sylow_ge
  have htS : t ∈ (S : Subgroup G) := hS SecTwoHyp.t_mem_R
  have hNC : L ⊓ centralizer ({t} : Set G) ≤ centralizer ({t} : Set G) := inf_le_right
  have hNn : ∀ c ∈ centralizer ({t} : Set G), ∀ n ∈ L ⊓ centralizer ({t} : Set G),
      c * n * c⁻¹ ∈ L ⊓ centralizer ({t} : Set G) := fun c hc n hn =>
    Subgroup.mem_inf.mpr ⟨hLn.conj_mem n (Subgroup.mem_inf.mp hn).1 c,
      mul_mem (mul_mem hc (Subgroup.mem_inf.mp hn).2) (inv_mem hc)⟩
  have hzC : u ^ 2 ∈ centralizer ({t} : Set G) :=
    h.secTwo.R_le_centralizer (pow_mem SecTwoHyp.u_mem_R 2)
  have hzN : u ^ 2 ∈ L ⊓ centralizer ({t} : Set G) := Subgroup.mem_inf.mpr ⟨hzL, hzC⟩
  have hN2 : 2 ∣ Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    have := Subgroup.card_dvd_of_le (zpowers_le.mpr hzN)
    rwa [Nat.card_zpowers, h.secTwo.orderOf_z] at this
  have htN : t ∉ L ⊓ centralizer ({t} : Set G) := fun ht => htL (Subgroup.mem_inf.mp ht).1
  have htzN : ∀ j : ℕ, t * (x ^ j * u ^ 2) ∉ L ⊓ centralizer ({t} : Set G) := fun j hj =>
    htzL j (Subgroup.mem_inf.mp hj).1
  obtain ⟨w, hwR, hwN, e, hwe, hNe, hcase⟩ : ∃ w : G, w ∈ secTwoR t u ∧
      w ∈ L ⊓ centralizer ({t} : Set G) ∧ ∃ e : ℕ, orderOf w = 2 ^ e ∧
      ¬ 2 ^ (e + 1) ∣ Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      ((w = u ^ 2 ∧ (Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ∨
          Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 10)) ∨
        ((w = u ∨ w = t * u) ∧ (Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 4 ∨
          Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 20))) := by
    rcases sec622_four_one h hNC hNn hN2 htN htzN with
      ⟨-, ⟨hNe, hc⟩ | ⟨hNe, hc⟩ | ⟨hNe, hc⟩⟩ | ⟨-, ⟨hNe, hc⟩ | ⟨hNe, hc⟩ | ⟨hNe, hc⟩⟩
    · refine ⟨u ^ 2, pow_mem SecTwoHyp.u_mem_R 2, hzN, 1, ?_, ?_, Or.inl ⟨rfl, Or.inr hc⟩⟩
      · rw [h.secTwo.orderOf_z, pow_one]
      · rw [hc]; decide
    · refine ⟨u, SecTwoHyp.u_mem_R, ?_, 2, ?_, ?_, Or.inr ⟨Or.inl rfl, Or.inr hc⟩⟩
      · rw [hNe]; exact subset_closure (by simp)
      · rw [h.secTwo.orderOf_u]; rfl
      · rw [hc]; decide
    · refine ⟨t * u, mul_mem SecTwoHyp.t_mem_R SecTwoHyp.u_mem_R, ?_, 2, ?_, ?_,
        Or.inr ⟨Or.inr rfl, Or.inr hc⟩⟩
      · rw [hNe]; exact subset_closure (by simp)
      · rw [I21.BranchData.orderOf_mul_u h.secTwo]; rfl
      · rw [hc]; decide
    · refine ⟨u ^ 2, pow_mem SecTwoHyp.u_mem_R 2, hzN, 1, ?_, ?_, Or.inl ⟨rfl, Or.inl hc⟩⟩
      · rw [h.secTwo.orderOf_z, pow_one]
      · rw [hc]; decide
    · refine ⟨u, SecTwoHyp.u_mem_R, ?_, 2, ?_, ?_, Or.inr ⟨Or.inl rfl, Or.inl hc⟩⟩
      · rw [hNe]; exact mem_zpowers u
      · rw [h.secTwo.orderOf_u]; rfl
      · rw [hc]; decide
    · refine ⟨t * u, mul_mem SecTwoHyp.t_mem_R SecTwoHyp.u_mem_R, ?_, 2, ?_, ?_,
        Or.inr ⟨Or.inr rfl, Or.inl hc⟩⟩
      · rw [hNe]; exact mem_zpowers (t * u)
      · rw [I21.BranchData.orderOf_mul_u h.secTwo]; rfl
      · rw [hc]; decide
  obtain ⟨hMs, hMt, hMc, hMeq⟩ := I21.BranchData.sylow_data S hLn htS (hS hwR)
    (Subgroup.mem_inf.mp hwN).1 (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hwN).2)
    hwe hNe
  refine ⟨(S : Subgroup G) ⊓ L, hMs, hMt, hMc, ?_⟩
  rcases hcase with ⟨hw, hc⟩ | ⟨hw, hc⟩
  · exact Or.inl ⟨by rw [hMeq, hw], hc⟩
  · exact Or.inr ⟨w, hw, hMeq, hc⟩

end SectionFour

end CFSG.LocalAnalysis.EvenBN.Tits
