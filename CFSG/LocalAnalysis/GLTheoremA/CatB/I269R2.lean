module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R1

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

namespace I269R

@[expose] def NoThreeSeven (G : Type) [Group G] : Prop :=
  ∀ s y : G, s ^ 3 = 1 → s ≠ 1 → orderOf y = 7 → s * y = y * s → False

@[expose] def NoNineFive (G : Type) [Group G] : Prop :=
  ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E = 9 → ∀ y : G, orderOf y = 5 →
    (∀ e ∈ E, e * y = y * e) → False

@[expose] def InnerPair (G : Type) [Group G] : Prop :=
  ∀ α β : MulAut G, α ^ 3 = 1 → β ^ 3 = 1 →
    (∃ g, MulAut.conj g = α) ∨ (∃ g, MulAut.conj g = β) ∨ (∃ g, MulAut.conj g = α * β) ∨
      (∃ g, MulAut.conj g = α * β⁻¹)

@[expose] def OuterNoFive (G : Type) [Group G] : Prop :=
  ∀ α : MulAut G, α ^ 3 = 1 → (∀ g : G, MulAut.conj g ≠ α) → ∀ y : G, orderOf y = 5 → α y = y → False

section Transport

variable {G H : Type} [Group G] [Group H]

theorem NoThreeSeven.of_mulEquiv (e : G ≃* H) (h : NoThreeSeven H) : NoThreeSeven G := by
  intro s y hs3 hs1 hy7 hc
  refine h (e s) (e y) (by rw [← map_pow, hs3, map_one])
    (fun h' => hs1 (e.injective (by rw [h', map_one]))) (by rw [MulEquiv.orderOf_eq]; exact hy7) ?_
  rw [← map_mul, ← map_mul, hc]

theorem NoNineFive.of_mulEquiv (e : G ≃* H) (h : NoNineFive H) : NoNineFive G := by
  intro E hE hcard y hy5 hc
  refine h (E.map e.toMonoidHom) (hE.map _)
    (by rw [Subgroup.card_map_of_injective e.injective, hcard]) (e y)
    (by rw [MulEquiv.orderOf_eq]; exact hy5) ?_
  rintro _ ⟨x, hx, rfl⟩
  show e x * e y = e y * e x
  rw [← map_mul, ← map_mul, hc x hx]

theorem congr_conj (e : G ≃* H) (g : G) : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem conj_of_congr (e : G ≃* H) {α : MulAut G} {g' : H} (h : MulAut.conj g' = MulAut.congr e α) :
    MulAut.conj (e.symm g') = α := by
  apply (MulAut.congr e).injective
  rw [congr_conj, MulEquiv.apply_symm_apply, h]

theorem InnerPair.of_mulEquiv (e : G ≃* H) (h : InnerPair H) : InnerPair G := by
  intro α β hα hβ
  have hα' : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  rcases h _ _ hα' hβ' with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl ⟨_, conj_of_congr e hg⟩
  · exact Or.inr (Or.inl ⟨_, conj_of_congr e hg⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, conj_of_congr e (by rw [hg, map_mul])⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, conj_of_congr e (by rw [hg, map_mul, map_inv])⟩))

theorem OuterNoFive.of_mulEquiv (e : G ≃* H) (h : OuterNoFive H) : OuterNoFive G := by
  intro α hα3 hout y hy5 hy
  refine h (MulAut.congr e α) (by rw [← map_pow, hα3, map_one]) (fun g' hg' => ?_) (e y)
    (by rw [MulEquiv.orderOf_eq]; exact hy5) ?_
  · exact hout _ (conj_of_congr e hg')
  · simp [MulAut.congr_apply, hy]

end Transport

theorem mem_center_of_conj_eq_one {G : Type} [Group G] {z : G} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut G => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem e9Solv_of_props {G : Type} [Group G] [Finite G] (hZ : Subgroup.center G = ⊥)
    (hcard : Nat.card G = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7) (h7 : NoThreeSeven G) (h5 : NoNineFive G)
    (hout3 : InnerPair G) (hout5 : OuterNoFive G) : E9Solv G := by
  classical
  intro E hE hE9
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc := mem_center_of_conj_eq_one hg
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE9]; norm_num)
  have hs : ∃ s : G, s ≠ 1 ∧ s ^ 3 = 1 ∧ MulAut.conj s ∈ E := by
    obtain ⟨α₁, hα₁1⟩ := exists_ne (1 : E)
    have hα3 : (α₁.1 : MulAut G) ^ 3 = 1 := hE.2 α₁.1 α₁.2
    have hα1 : (α₁.1 : MulAut G) ≠ 1 := fun h => hα₁1 (Subtype.ext h)
    obtain ⟨α₂, hα₂E, hα₂⟩ : ∃ α₂ ∈ E, α₂ ∉ Subgroup.zpowers (α₁.1 : MulAut G) := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hle : E ≤ Subgroup.zpowers (α₁.1 : MulAut G) := fun α hα => hcon α hα
      have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers (α₁.1 : MulAut G)) :=
        Subgroup.card_le_of_le hle
      have h2 : orderOf (α₁.1 : MulAut G) ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
      have h3 : Nat.card (Subgroup.zpowers (α₁.1 : MulAut G)) ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) h2
      omega
    have hα₂3 : α₂ ^ 3 = 1 := hE.2 α₂ hα₂E
    have hα₂1 : α₂ ≠ 1 := fun h => hα₂ (h ▸ Subgroup.one_mem _)
    have hne : α₂ ≠ (α₁.1 : MulAut G) := fun h => hα₂ (h ▸ Subgroup.mem_zpowers _)
    have hne' : α₂ ≠ (α₁.1 : MulAut G)⁻¹ := fun h =>
      hα₂ (h ▸ Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
    have key : ∀ g : G, MulAut.conj g ∈ E → MulAut.conj g ≠ 1 →
        ∃ s : G, s ≠ 1 ∧ s ^ 3 = 1 ∧ MulAut.conj s ∈ E := by
      intro g hgE hg1
      refine ⟨g, fun h => hg1 (by rw [h, map_one]), ?_, hgE⟩
      apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ hgE
    rcases hout3 α₁.1 α₂ hα3 hα₂3 with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
    · exact key g (hg ▸ α₁.2) (hg ▸ hα1)
    · exact key g (hg ▸ hα₂E) (hg ▸ hα₂1)
    · refine key g (hg ▸ E.mul_mem α₁.2 hα₂E) ?_
      rw [hg]
      intro h
      exact hne' (eq_inv_of_mul_eq_one_right h)
    · refine key g (hg ▸ E.mul_mem α₁.2 (E.inv_mem hα₂E)) ?_
      rw [hg]
      intro h
      exact hne (mul_inv_eq_one.1 h).symm
  obtain ⟨s, hs1, hs3, hsE⟩ := hs
  have hCs : ∀ x ∈ i269Fix E, s * x = x * s := by
    intro x hx
    have := (mem_i269Fix.1 hx) _ hsE
    rw [MulAut.conj_apply] at this
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x * s := by rw [this]
  have h7' : ¬ 7 ∣ Nat.card (i269Fix E) := by
    intro h
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(i269Fix E)) 7 h
    have hy' : orderOf (y : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
    exact h7 s y hs3 hs1 hy' (hCs y y.2)
  have h5' : ¬ 5 ∣ Nat.card (i269Fix E) := by
    intro h
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(i269Fix E)) 5 h
    have hy' : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
    have hyE : ∀ α ∈ E, α (y : G) = y := mem_i269Fix.1 y.2
    by_cases hin : ∀ α ∈ E, ∃ g : G, MulAut.conj g = α
    · have hinner : E ≤ (MulAut.conj : G →* MulAut G).range := fun α hα => hin α hα
      set E' : Subgroup G := E.comap (MulAut.conj : G →* MulAut G) with hE'def
      have hmap : E'.map (MulAut.conj : G →* MulAut G) = E := Subgroup.map_comap_eq_self hinner
      have hcardE' : Nat.card E' = 9 := by
        have := Subgroup.card_map_of_injective (K := E') hinj
        rw [hmap, hE9] at this
        exact this.symm
      have hE'ab : IsElemAbelian 3 E' := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · have ha : (MulAut.conj (a : G)) ∈ E := a.2
          have hb : (MulAut.conj (b : G)) ∈ E := b.2
          have hc : (MulAut.conj (a : G)) * MulAut.conj (b : G) =
              MulAut.conj (b : G) * MulAut.conj (a : G) :=
            congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
          apply Subtype.ext
          show (a : G) * b = b * a
          apply hinj
          rw [map_mul, map_mul]
          exact hc
        · apply hinj
          rw [map_pow, map_one]
          exact hE.2 _ hx
      refine h5 E' hE'ab hcardE' y hy' ?_
      intro e he
      have := hyE _ he
      rw [MulAut.conj_apply] at this
      calc e * y = (e * y * e⁻¹) * e := by group
        _ = y * e := by rw [this]
    · push Not at hin
      obtain ⟨α, hαE, hα⟩ := hin
      exact hout5 α (hE.2 α hαE) hα y hy' (hyE α hαE)
  have hdvd : Nat.card (i269Fix E) ∣ 2 ^ 12 * 3 ^ 5 := by
    have h1 : Nat.card (i269Fix E) ∣ 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 := by
      rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
    have hc7 : Nat.Coprime (Nat.card (i269Fix E)) 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7').symm
    have hc5 : Nat.Coprime (Nat.card (i269Fix E)) (5 ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5').symm
    exact hc5.dvd_of_dvd_mul_right (hc7.dvd_of_dvd_mul_right h1)
  exact isSolvable_of_card_dvd hdvd

end I269R

end CFSG.LocalAnalysis.GLTheoremA

end
