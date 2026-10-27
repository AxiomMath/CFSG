module

public import CFSG.GH74.E2.BoxT5Out

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

section Aux

variable {G : Type} [Group G] [Finite G] {K A B M : Subgroup G}

theorem Setup.ne_bot_of (S : Setup K) (h : ConjOf K M) : M ≠ ⊥ := by
  intro hM
  obtain ⟨P, hPM, -, hr⟩ := S.rank_of h
  have hP : P = ⊥ := le_bot_iff.1 (hM ▸ hPM)
  have : Group.rank ↥P = 0 := by
    rw [Subgroup.rank_congr hP]
    exact Group.rank_eq_zero _
  omega

omit [Finite G] in
theorem simple_meet_odd_normal {D M : Subgroup G} (hMD : M ≤ D) (hM : IsSimpleGroup ↥M)
    (hev : ∃ a ∈ M, orderOf a = 2) (N : Subgroup ↥D) [N.Normal] (hodd : Odd (Nat.card N)) :
    ∀ a : G, ∀ ha : a ∈ M, (⟨a, hMD ha⟩ : ↥D) ∈ N → a = 1 := by
  let f : ↥M →* ↥D ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hMD)
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a₀, ha₀M, ha₀⟩ := hev
      have hmem : (⟨a₀, hMD ha₀M⟩ : ↥D) ∈ N := by
        have h0 : (⟨a₀, ha₀M⟩ : ↥M) ∈ f.ker := by rw [ht]; exact Subgroup.mem_top _
        have h1 : f ⟨a₀, ha₀M⟩ = 1 := h0
        exact (QuotientGroup.eq_one_iff (⟨a₀, hMD ha₀M⟩ : ↥D)).1 h1
      have h2 : orderOf (⟨⟨a₀, hMD ha₀M⟩, hmem⟩ : ↥N) = 2 := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact ha₀
      have h3 := orderOf_dvd_natCard (⟨⟨a₀, hMD ha₀M⟩, hmem⟩ : ↥N)
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)
  intro a ha hmem
  have : (⟨a, ha⟩ : ↥M) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  rw [hker, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem CommPair.odd_normal_bot (S : Setup K) (h : CommPair K A B) (N : Subgroup ↥(A ⊔ B))
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hAD : A ≤ A ⊔ B := le_sup_left
  have hBD : B ≤ A ⊔ B := le_sup_right
  have hsA := S.simple_of h.convA
  have hsB := S.simple_of h.convB
  obtain ⟨a0, ha0, ha02⟩ := AS16.exists_involution_of_isQuasisimple (S.quasi_of h.convA)
  obtain ⟨b0, hb0, hb02⟩ := AS16.exists_involution_of_isQuasisimple (S.quasi_of h.convB)
  have kA := simple_meet_odd_normal hAD hsA ⟨a0, ha0, ha02⟩ N hodd
  have kB := simple_meet_odd_normal hBD hsB ⟨b0, hb0, hb02⟩ N hodd
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute h.commute n.2
  have hn' : ∀ (g : ↥(A ⊔ B)), g * n * g⁻¹ ∈ N := fun g => hN.conj_mem n hn g
  have ha1 : a = 1 := by
    refine S.centerFree_of h.convA a ha fun k hk => ?_
    have hkb := h.commute k hk b hb
    let kD : ↥(A ⊔ B) := ⟨k, hAD hk⟩
    have h1 : kD * n⁻¹ * kD⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) kD
    have h2 : n * (kD * n⁻¹ * kD⁻¹) ∈ N := N.mul_mem hn h1
    have hc : a * k * a⁻¹ * k⁻¹ ∈ A :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hk) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hk)
    have heq : (⟨a * k * a⁻¹ * k⁻¹, hAD hc⟩ : ↥(A ⊔ B)) = n * (kD * n⁻¹ * kD⁻¹) := by
      apply Subtype.ext
      show a * k * a⁻¹ * k⁻¹ = (n : G) * (k * (n : G)⁻¹ * k⁻¹)
      rw [hab, mul_inv_rev]
      calc a * k * a⁻¹ * k⁻¹ = a * (k * b) * b⁻¹ * a⁻¹ * k⁻¹ := by group
        _ = a * (b * k) * b⁻¹ * a⁻¹ * k⁻¹ := by rw [← hkb]
        _ = a * b * (k * (b⁻¹ * a⁻¹) * k⁻¹) := by group
    have h3 : a * k * a⁻¹ * k⁻¹ = 1 := kA _ hc (heq ▸ h2)
    calc a * k = (a * k * a⁻¹ * k⁻¹) * (k * a) := by group
      _ = k * a := by rw [h3, one_mul]
  have hb1 : b = 1 := by
    refine S.centerFree_of h.convB b hb fun l hl => ?_
    have hal := h.commute a ha l hl
    let lD : ↥(A ⊔ B) := ⟨l, hBD hl⟩
    have h1 : lD * n⁻¹ * lD⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) lD
    have h2 : n * (lD * n⁻¹ * lD⁻¹) ∈ N := N.mul_mem hn h1
    have hc : b * l * b⁻¹ * l⁻¹ ∈ B :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hl) (Subgroup.inv_mem _ hb))
        (Subgroup.inv_mem _ hl)
    have heq : (⟨b * l * b⁻¹ * l⁻¹, hBD hc⟩ : ↥(A ⊔ B)) = n * (lD * n⁻¹ * lD⁻¹) := by
      apply Subtype.ext
      show b * l * b⁻¹ * l⁻¹ = (n : G) * (l * (n : G)⁻¹ * l⁻¹)
      rw [hab, mul_inv_rev]
      have hac : a * (b * l * b⁻¹) = (b * l * b⁻¹) * a :=
        h.commute a ha _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hl) (Subgroup.inv_mem _ hb))
      calc b * l * b⁻¹ * l⁻¹ = (a * (b * l * b⁻¹) * a⁻¹) * l⁻¹ := by rw [hac]; group
        _ = a * b * (l * (b⁻¹ * a⁻¹) * l⁻¹) := by
          have hal' : l * a⁻¹ = a⁻¹ * l := by
            have := hal
            calc l * a⁻¹ = a⁻¹ * (a * l) * a⁻¹ := by group
              _ = a⁻¹ * (l * a) * a⁻¹ := by rw [this]
              _ = a⁻¹ * l := by group
          calc (a * (b * l * b⁻¹) * a⁻¹) * l⁻¹ = a * b * l * b⁻¹ * a⁻¹ * l⁻¹ := by group
            _ = a * b * (l * (b⁻¹ * a⁻¹) * l⁻¹) := by group
    have h3 : b * l * b⁻¹ * l⁻¹ = 1 := kB _ hc (heq ▸ h2)
    calc b * l = (b * l * b⁻¹ * l⁻¹) * (l * b) := by group
      _ = l * b := by rw [h3, one_mul]
  apply Subtype.ext
  show (n : G) = 1
  rw [hab, ha1, hb1, mul_one]

theorem Setup.center_G (S : Setup K) : Subgroup.center G = ⊥ := by
  have hsimple := S.hyp.simple
  have : (Subgroup.center G).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := S.hyp.nonabelian
    have ha : a ∈ Subgroup.center G := by rw [ht]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem CommPair.normalizer_ne_top (S : Setup K) (h : CommPair K A B) :
    normalizer ((A ⊔ B : Subgroup G) : Set G) ≠ ⊤ := by
  intro htop
  have hnorm : (A ⊔ B).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have hsimple := S.hyp.simple
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A ⊔ B) with hb | ht
  · exact S.ne_bot_of h.convA (le_bot_iff.1 (hb ▸ (le_sup_left : A ≤ A ⊔ B)))
  · have hAn : A.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg : g ∈ A ⊔ B := by rw [ht]; exact Subgroup.mem_top g
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.commute hg
      have hbx := h.commute x hx b hb
      have : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
        calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
          _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [← hbx]
          _ = a * x * a⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hx) (Subgroup.inv_mem _ ha)
    have := hAn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hAb | hAt
    · exact S.ne_bot_of h.convA hAb
    · apply S.ne_bot_of h.convB
      rw [eq_bot_iff]
      intro b hb
      rw [Subgroup.mem_bot]
      have hbc : b ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hgA : g ∈ A := by rw [hAt]; exact Subgroup.mem_top g
        exact h.commute g hgA b hb
      rw [S.center_G] at hbc
      exact Subgroup.mem_bot.1 hbc

theorem CommPair.conj_normalizer (S : Setup K) (h : CommPair K A B) {n : G}
    (hn : n ∈ normalizer ((A ⊔ B : Subgroup G) : Set G)) {M : Subgroup G} (hM : M = A ∨ M = B) :
    conjugate M n = A ∨ conjugate M n = B := by
  have hM' : IsCompIn (A ⊔ B) M := by
    rcases hM with rfl | rfl
    · exact h.isCompIn_left S
    · exact h.isCompIn_right S
  have h1 := AS16.isCompIn_conj hM' n
  have h2 : conjugate (A ⊔ B) n = A ⊔ B := (AS16.conjugate_eq_self_iff _ _).2 hn
  rw [h2] at h1
  exact h.comps_of_D S h1

theorem CommPair.map_conj_normalizer (S : Setup K) (h : CommPair K A B) {n : G}
    (hn : n ∈ normalizer ((A ⊔ B : Subgroup G) : Set G)) {M : Subgroup G} (hM : M = A ∨ M = B) :
    M.map (MulAut.conj n).toMonoidHom = A ∨ M.map (MulAut.conj n).toMonoidHom = B := by
  have h1 := h.conj_normalizer S (Subgroup.inv_mem _ hn) hM
  have h2 : conjugate M n⁻¹ = M.map (MulAut.conj n).toMonoidHom := by
    simp [conjugate]
  rwa [h2] at h1

omit [Finite G] in
theorem exists_involution_pow {t : G} (h2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (h1 : t ≠ 1) :
    ∃ m : ℕ, orderOf (t ^ m) = 2 := by
  obtain ⟨k, hk⟩ := h2
  have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨a, ha, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hord
    exact h1 (orderOf_eq_one_iff.1 hord)
  refine ⟨2 ^ (a - 1), ?_⟩
  have hdvd' : 2 ^ (a - 1) ∣ orderOf t := by
    rw [hord]
    exact pow_dvd_pow 2 (Nat.sub_le a 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd', hord]
  rw [Nat.pow_div (Nat.sub_le a 1) Nat.two_pos]
  have : a - (a - 1) = 1 := by omega
  rw [this]

theorem CommPair.carry_mem_swapGrp (S : Setup K) (h : CommPair K A B) {P Q : Subgroup G}
    (hP : P = A ∨ P = B) (hQ : Q = A ∨ Q = B) {g : G} (hg : conjugate P g = Q) :
    g ∈ swapGrp A B := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · exact Or.inl ⟨hg, h.fix S hg⟩
  · exact Or.inr ⟨hg, h.swap S hg⟩
  · exact Or.inr ⟨h.symm.swap S hg, hg⟩
  · exact Or.inl ⟨h.symm.fix S hg, hg⟩

end Aux

end CFSG.GH74.E2.Box
