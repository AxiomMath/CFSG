module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SymThreeParabolic
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderSwaps

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open

variable {r s : ℕ} (i₀ : Fin r) (f₀ : Fin s)

@[expose] def threeCyc : Perm (OmegaE r s) :=
  swap (Sum.inl (i₀, false)) (Sum.inl (i₀, true)) * swap (Sum.inl (i₀, true)) (Sum.inr f₀)

theorem threeCyc_pow_three : (threeCyc i₀ f₀ : Perm (OmegaE r s)) ^ 3 = 1 := by
  have h := Offender.orderOf_swap_mul_swap (a := (Sum.inl (i₀, true) : OmegaE r s))
    (b := Sum.inl (i₀, false)) (c := Sum.inr f₀) (by simp) Sum.inl_ne_inr Sum.inl_ne_inr
  have e : (threeCyc i₀ f₀ : Perm (OmegaE r s)) =
      swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inl (i₀, false)) *
        swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) := by
    unfold threeCyc; rw [swap_comm (Sum.inl (i₀, true)) (Sum.inl (i₀, false))]
  have h' := pow_orderOf_eq_one (swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inl (i₀, false)) *
    swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀))
  rw [h] at h'
  rw [e]; exact h'

theorem threeCyc_ne_one : (threeCyc i₀ f₀ : Perm (OmegaE r s)) ≠ 1 := by
  intro h
  have := congrArg (fun g : Perm (OmegaE r s) => g (Sum.inl (i₀, false))) h
  simp [threeCyc, swap_apply_def] at this

theorem threeCyc_mem_alt : (threeCyc i₀ f₀ : Perm (OmegaE r s)) ∈ alternatingGroup (OmegaE r s) := by
  have ha' : (Sum.inl (i₀, true) : OmegaE r s) ≠ Sum.inr f₀ := Sum.inl_ne_inr
  have ha : (Sum.inl (i₀, false) : OmegaE r s) ≠ Sum.inl (i₀, true) := by simp
  rw [mem_alternatingGroup, threeCyc, map_mul, sign_swap ha, sign_swap ha']
  rfl

theorem threeCyc_mem_YStar : (threeCyc i₀ f₀ : Perm (OmegaE r s)) ∈ YStar i₀ f₀ := by
  have h1 : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ YStar i₀ f₀ := by
    apply Wr_le_YStar
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  have h2 : swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) ∈ YStar i₀ f₀ := by
    refine ⟨fun x hx => ?_, fun x hx => Or.inl ?_⟩
    · rcases hx with rfl | rfl | rfl
      · rw [swap_apply_of_ne_of_ne (by simp) Sum.inl_ne_inr]; exact Or.inl rfl
      · rw [swap_apply_left]; exact Or.inr (Or.inr rfl)
      · rw [swap_apply_right]; exact Or.inr (Or.inl rfl)
    · have h1 : x ≠ Sum.inl (i₀, true) := fun h => hx (Or.inr (Or.inl h))
      have h2 : x ≠ Sum.inr f₀ := fun h => hx (Or.inr (Or.inr h))
      exact swap_apply_of_ne_of_ne h1 h2
  exact (YStar i₀ f₀).mul_mem h1 h2

theorem threeCyc_not_mem_normalizer_Wr :
    (threeCyc i₀ f₀ : Perm (OmegaE r s)) ∉
      Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := by
  intro hN
  have ht : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ Wr r s := by
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  have h := (Subgroup.mem_normalizer_iff.1 hN _).1 ht
  have hc : (threeCyc i₀ f₀ : Perm (OmegaE r s)) *
      swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) * (threeCyc i₀ f₀)⁻¹ =
      swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) := by
    rw [← swap_apply_apply]
    simp [threeCyc, swap_apply_def]
  rw [hc] at h
  have := Wr_apply_inr h f₀
  simp at this


variable {G : Type} [Group G] [Finite G] {S M L : Subgroup G}

theorem sym3_lift (hLM : L ≤ M) (θ : ↥M →* Perm (OmegaE r s))
    (hAltL : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ l : ↥L, θ ⟨l, hLM l.2⟩ = x)
    (hcore : ∀ m : ↥M, (m : G) ∈ pCoreOf 2 M → θ m = 1)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) :
    ¬ sym3Y M i₀ f₀ θ ≤ Subgroup.normalizer (S : Set G) ∧
      ∃ y : G, y ∈ L ∧ y ∈ sym3Y M i₀ f₀ θ ∧ Odd (orderOf y) ∧ y ∉ pCoreOf 2 M := by
  classical
  obtain ⟨l, hl⟩ := hAltL _ (threeCyc_mem_alt i₀ f₀)
  set g : G := (l : G) with hg
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨b, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  set y' : ↥M := (⟨l, hLM l.2⟩ : ↥M) ^ (m * m) with hy'
  have hk : (m * m) % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h | h <;> simp [Nat.mul_mod, h]
  have hθy : θ y' = threeCyc i₀ f₀ := by
    rw [hy', map_pow, hl]
    have e : m * m = 3 * ((m * m) / 3) + 1 := by omega
    rw [e, pow_add, pow_mul, threeCyc_pow_three, one_pow, one_mul, pow_one]
  have hyG : (y' : G) = g ^ (m * m) := by
    rw [hy']; rfl
  have hyY : (y' : G) ∈ sym3Y M i₀ f₀ θ :=
    ⟨y', show θ y' ∈ YStar i₀ f₀ by rw [hθy]; exact threeCyc_mem_YStar i₀ f₀, rfl⟩
  refine ⟨fun hYN => ?_, y', ?_, hyY, ?_, ?_⟩
  · have hN : θ y' ∈ Subgroup.normalizer
        ((((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm (OmegaE r s))) : Set _) :=
      theta_mem_normalizer_W θ y' (hYN hyY)
    rw [hW, hθy] at hN
    exact threeCyc_not_mem_normalizer_Wr i₀ f₀ hN
  · rw [hyG]; exact L.pow_mem l.2 _
  · have hpow : (g ^ (m * m)) ^ (3 ^ b) = 1 := by
      rw [← pow_mul]
      have : m * m * 3 ^ b = orderOf g * m := by rw [hnm]; ring
      rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [hyG]
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hpow)
  · intro hc
    have := hcore y' hc
    rw [hθy] at this
    exact threeCyc_ne_one i₀ f₀ this


@[expose] def HasSym3Lift (S L M : Subgroup G) : Prop :=
  ∃ Y P : Subgroup G, thompsonJ S ≤ P ∧ P ≤ S ∧ P ≤ Y ∧ Y ≤ M ∧ ¬ 2 ∣ P.relIndex Y ∧
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Perm (Fin 3)) ∧ ¬ Y ≤ Subgroup.normalizer (S : Set G) ∧
    ∃ y : G, y ∈ L ∧ y ∈ Y ∧ Odd (orderOf y) ∧ y ∉ pCoreOf 2 M

theorem exists_sym3_lift (hS2 : IsPGroup 2 S) (hSM : S ≤ M) (hLM : L ≤ M)
    (θ : ↥M →* Perm (OmegaE r s)) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAltL : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ l : ↥L, θ ⟨l, hLM l.2⟩ = x)
    (hcore : ∀ m : ↥M, (m : G) ∈ pCoreOf 2 M → θ m = 1)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    HasSym3Lift S L M := by
  have hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x := fun x hx => by
    obtain ⟨l, hl⟩ := hAltL x hx
    exact ⟨⟨l, hLM l.2⟩, hl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := sym3_facts hS2 hSM θ hker hAlt hW ⟨0, hr⟩ ⟨0, hs⟩
  obtain ⟨hN, y, hy⟩ := sym3_lift ⟨0, hr⟩ ⟨0, hs⟩ hLM θ hAltL hcore hW
  exact ⟨sym3Y M ⟨0, hr⟩ ⟨0, hs⟩ θ, sym3P M θ, h1, h2, h3, Subgroup.map_subtype_le _, h4, h5, hN,
    y, hy⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
