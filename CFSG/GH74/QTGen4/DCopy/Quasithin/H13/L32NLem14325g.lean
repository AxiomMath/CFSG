module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325e
public import CFSG.Quasithin.H13.L32NKGG22Wit
public import CFSG.Quasithin.H13.L32NLem14325f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem not_g22_F4 (hO : KGCert.KGSp6Order12096) (h1332 : Stmt13_3_2_F4) (h1352 : A6.Stmt13_5_2_F4)
    (h1381 : Stmt13_8_1_F4) (h36 : A36ForSQTK) (h39 : A39ForSQTK)
    (h6 : G112Concl6 (D.img (l32nH T V))) : False := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Hd := D.img (l32nH T V) with hHd
  have hB : ∀ γ ∈ Hd, ∀ v w, D.B (γ v) (γ w) = D.B v w := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  obtain ⟨⟨P, hPH, hP1, hPp⟩, ⟨γ₀, hγ₀H, hγ₀7, hγ₀1, hγ₀fix⟩,
    ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, ha₁7, -, ha₂7, -, hb₁7, -, hb₂7, -, ha3, ha1, hb3, hab,
      hb1, hba, hba2⟩⟩ :=
    KGCert.exists_facts hO D.B (L128A.HatU.B_isAlt D) (L128A.HatU.B_nondegenerate D) h6.1 Hd hB
      h6.2
  have hcardH : Nat.card Hd = 2 ^ 6 * 3 ^ 3 * 7 := by rw [h6.2]; norm_num
  have h49 : ¬ 7 ^ 2 ∣ Nat.card Hd := by rw [hcardH]; norm_num

  have hseven : ∀ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), X ≤ Hd → X ≠ ⊥ → ⁅X, X⁆ = X →
      7 ∣ Nat.card X := fun X hXH hX1 hXp =>
    prime_dvd_of_perfect hX1 hXp (by norm_num) (hcardH ▸ Subgroup.card_dvd_of_le hXH)

  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w ∈ D.hat V, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hb : D.hat V = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have := C.card_hatV
    rw [hb] at this
    simp at this
  obtain ⟨X, hXsub, hX1, hXp, hX60⟩ := C.exists_comp_img_F4 h1332 h1352 h1381 h36 h39 hPH hP1 hPp
    (fun X hXsub hX1 hXp hmaps => by
      have h7 := hseven X (le_of_isSubnormal hXsub) hX1 hXp
      have hγX := mem_of_subnormal_of_dvd hXsub (by norm_num) h7 h49 hγ₀H hγ₀7
      have hfix := fix_of_maps_card_four C.card_hatV (p := 7) (k := 1) (by norm_num)
        (by norm_num) (by rwa [pow_one]) (fun s hs => hmaps _ hγX s hs)
      exact hw₀0 (hγ₀fix w₀ (hfix w₀ hw₀)))
  have h7 := hseven X (le_of_isSubnormal hXsub) hX1 hXp
  have hmemX : ∀ y ∈ Hd, y ^ 7 = 1 → y ∈ X := fun y hy hy7 =>
    mem_of_subnormal_of_dvd hXsub (by norm_num) h7 h49 hy hy7

  set a := a₁ * a₂ with ha
  set b := b₁ * b₂ with hb
  have haX : a ∈ X := X.mul_mem (hmemX _ ha₁ ha₁7) (hmemX _ ha₂ ha₂7)
  have hbX : b ∈ X := X.mul_mem (hmemX _ hb₁ hb₁7) (hmemX _ hb₂ hb₂7)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcomm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set _) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right (show Commute a b from hab) k).eq).symm
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ 3 := by
      rw [← hob, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hob])
      have hbA : b ∈ Subgroup.zpowers a := (heq ▸ inf_le_left : Subgroup.zpowers b ≤ _)
        (Subgroup.mem_zpowers b)
      classical
      rw [mem_zpowers_iff_mem_range_orderOf, hoa] at hbA
      simp only [Finset.mem_image, Finset.mem_range] at hbA
      obtain ⟨k, hk, hkb⟩ := hbA
      interval_cases k
      · exact hb1 (by rw [← hkb, pow_zero])
      · exact hba (by rw [← hkb, pow_one])
      · exact hba2 (by rw [← hkb])
  have hcard9 := L32NSet14.card_sup_mul_card_inf hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at hcard9
  have hEX : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ X :=
    sup_le ((Subgroup.zpowers_le).mpr haX) ((Subgroup.zpowers_le).mpr hbX)
  have h9 : 9 ∣ Nat.card X := by
    have := Subgroup.card_dvd_of_le hEX
    rwa [hcard9] at this
  rcases hX60 with h | h
  · have := Nat.dvd_trans h7 h
    norm_num at this
  · have := Nat.dvd_trans h9 h
    norm_num at this

end Ctx14325

end L14325

end CFSG.Quasithin.H13
