module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeShapeU33
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.L28Local

namespace TenNineOneThree

namespace L28Sq

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_isCaseTwoGroup_three (hK : IsCaseTwoGroup 3 G) : IsSimpleGroup G := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hK
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    haveI : Fact (Nat.Prime 2) := ⟨hp⟩
    have h4 : 4 ≤ Nat.card (GaloisField 2 3) := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)).isSimpleGroup
  · omega

theorem eq_one_of_comm (hK : IsCaseTwoGroup 3 G) {g : G} (hg : ∀ x : G, g * x = x * g) :
    g = 1 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 G))
  apply (l28Data_of_equiv ε₀ S).conj_injective
  ext x
  simp only [MulAut.conj_apply, map_one, MulAut.one_apply]
  rw [hg x, mul_inv_cancel_right]

theorem card_eq (hK : IsCaseTwoGroup 3 G) : Nat.card G = 504 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  rw [Nat.card_congr ε₀.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]

@[expose] def Pres (ψ : MulAut (G × G)) : Prop :=
  (∀ g : G, (ψ (g, 1)).2 = 1) ∧ ∀ g : G, (ψ (1, g)).1 = 1

@[expose] def Swap (ψ : MulAut (G × G)) : Prop :=
  (∀ g : G, (ψ (g, 1)).1 = 1) ∧ ∀ g : G, (ψ (1, g)).2 = 1

theorem fst_or_snd (hK : IsCaseTwoGroup 3 G) (ψ : MulAut (G × G)) (ι : G →* G × G)
    (hι : Function.Injective ι)
    (hn : ∀ (h : G × G) (g : G), ∃ g' : G, h * ι g * h⁻¹ = ι g') :
    (∀ g : G, (ψ (ι g)).2 = 1) ∨ (∀ g : G, (ψ (ι g)).1 = 1) := by
  classical
  haveI := isSimpleGroup_of_isCaseTwoGroup_three hK
  have hN : ∀ (h : G × G) (g : G), ∃ g' : G, h * ψ (ι g) * h⁻¹ = ψ (ι g') := by
    intro h g
    obtain ⟨g', hg'⟩ := hn (ψ.symm h) g
    refine ⟨g', ?_⟩
    rw [← hg', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  let H₁ : Subgroup G :=
    { carrier := {x | ∃ g, ψ (ι g) = (x, 1)}
      one_mem' := ⟨1, by rw [map_one, map_one, Prod.one_eq_mk]⟩
      mul_mem' := by
        rintro a b ⟨g, hg⟩ ⟨g', hg'⟩
        exact ⟨g * g', by rw [map_mul, map_mul, hg, hg', Prod.mk_mul_mk, one_mul]⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        exact ⟨g⁻¹, by rw [map_inv, map_inv, hg, Prod.inv_mk, inv_one]⟩ }
  let H₂ : Subgroup G :=
    { carrier := {x | ∃ g, ψ (ι g) = (1, x)}
      one_mem' := ⟨1, by rw [map_one, map_one, Prod.one_eq_mk]⟩
      mul_mem' := by
        rintro a b ⟨g, hg⟩ ⟨g', hg'⟩
        exact ⟨g * g', by rw [map_mul, map_mul, hg, hg', Prod.mk_mul_mk, one_mul]⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        exact ⟨g⁻¹, by rw [map_inv, map_inv, hg, Prod.inv_mk, inv_one]⟩ }
  have hH₁ : H₁.Normal := ⟨by
    rintro x ⟨g, hg⟩ y
    obtain ⟨g', hg'⟩ := hN (y, 1) g
    refine ⟨g', ?_⟩
    rw [← hg', hg]
    simp⟩
  have hH₂ : H₂.Normal := ⟨by
    rintro x ⟨g, hg⟩ y
    obtain ⟨g', hg'⟩ := hN (1, y) g
    refine ⟨g', ?_⟩
    rw [← hg', hg]
    simp⟩
  have hinj : Function.Injective (fun g => ψ (ι g)) := ψ.injective.comp hι
  have hcard := card_eq hK
  rcases hH₁.eq_bot_or_eq_top with h1 | h1
  · rcases hH₂.eq_bot_or_eq_top with h2 | h2
    ·
      exfalso
      have hall : ∀ g : G, ψ (ι g) = 1 := by
        intro g
        set n := ψ (ι g) with hn'
        have ha : ∀ x : G, n.1 * x = x * n.1 := by
          intro x
          obtain ⟨g', hg'⟩ := hN (x, 1) g⁻¹
          have hmem : n.1 * x * n.1⁻¹ * x⁻¹ ∈ H₁ := by
            refine ⟨g * g', ?_⟩
            rw [map_mul, map_mul, ← hg', map_inv, map_inv, ← hn']
            ext
            · simp [mul_assoc]
            · simp
          rw [h1, Subgroup.mem_bot] at hmem
          have hc := mul_inv_eq_one.mp hmem
          calc n.1 * x = n.1 * x * n.1⁻¹ * n.1 := by group
            _ = x * n.1 := by rw [hc]
        have hb : ∀ x : G, n.2 * x = x * n.2 := by
          intro x
          obtain ⟨g', hg'⟩ := hN (1, x) g⁻¹
          have hmem : n.2 * x * n.2⁻¹ * x⁻¹ ∈ H₂ := by
            refine ⟨g * g', ?_⟩
            rw [map_mul, map_mul, ← hg', map_inv, map_inv, ← hn']
            ext
            · simp
            · simp [mul_assoc]
          rw [h2, Subgroup.mem_bot] at hmem
          have hc := mul_inv_eq_one.mp hmem
          calc n.2 * x = n.2 * x * n.2⁻¹ * n.2 := by group
            _ = x * n.2 := by rw [hc]
        exact Prod.ext (eq_one_of_comm hK ha) (eq_one_of_comm hK hb)
      have h1all : ∀ a : G, a = 1 := fun a => hinj ((hall a).trans (hall 1).symm)
      have : Nat.card G = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h1all a).trans (h1all b).symm⟩, ⟨1⟩⟩
      omega
    ·
      right
      have hle : ∀ x : G, ∃ g, ψ (ι g) = (1, x) := fun x => (show x ∈ H₂ by rw [h2]; exact Subgroup.mem_top x)
      choose j hj using hle
      have hjinj : Function.Injective j := by
        intro a b hab
        have := congrArg Prod.snd ((hj a).symm.trans ((congrArg (fun g => ψ (ι g)) hab).trans (hj b)))
        exact this
      have hjs : Function.Surjective j := Finite.injective_iff_surjective.mp hjinj
      intro g
      obtain ⟨x, rfl⟩ := hjs g
      rw [hj]
  · left
    have hle : ∀ x : G, ∃ g, ψ (ι g) = (x, 1) := fun x => (show x ∈ H₁ by rw [h1]; exact Subgroup.mem_top x)
    choose j hj using hle
    have hjinj : Function.Injective j := by
      intro a b hab
      have := congrArg Prod.fst ((hj a).symm.trans ((congrArg (fun g => ψ (ι g)) hab).trans (hj b)))
      exact this
    have hjs : Function.Surjective j := Finite.injective_iff_surjective.mp hjinj
    intro g
    obtain ⟨x, rfl⟩ := hjs g
    rw [hj]

theorem exists_ne_one (hK : IsCaseTwoGroup 3 G) : ∃ x : G, x ≠ 1 := by
  by_contra! h
  have : Nat.card G = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
  rw [card_eq hK] at this
  norm_num at this

theorem pres_or_swap (hK : IsCaseTwoGroup 3 G) (ψ : MulAut (G × G)) : Pres ψ ∨ Swap ψ := by
  have hA := fst_or_snd hK ψ (MonoidHom.inl G G) (fun a b h => congrArg Prod.fst h)
    (fun h g => ⟨h.1 * g * h.1⁻¹, by ext <;> simp⟩)
  have hB := fst_or_snd hK ψ (MonoidHom.inr G G) (fun a b h => congrArg Prod.snd h)
    (fun h g => ⟨h.2 * g * h.2⁻¹, by ext <;> simp⟩)
  simp only [MonoidHom.inl_apply, MonoidHom.inr_apply] at hA hB
  obtain ⟨x, hx⟩ := exists_ne_one hK
  have hsplit : ∀ a b : G, ψ (a, b) = ψ (a, 1) * ψ (1, b) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  ·
    exfalso
    obtain ⟨⟨a, b⟩, hab⟩ := ψ.surjective (1, x)
    have := congrArg Prod.snd hab
    rw [hsplit, Prod.snd_mul, hA, hB, one_mul] at this
    exact hx this.symm
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hA, hB⟩
  · exfalso
    obtain ⟨⟨a, b⟩, hab⟩ := ψ.surjective (x, 1)
    have := congrArg Prod.fst hab
    rw [hsplit, Prod.fst_mul, hA, hB, one_mul] at this
    exact hx this.symm

theorem swap_mul_swap {α β : MulAut (G × G)} (hα : Swap α) (hβ : Swap β) : Pres (α * β) := by
  refine ⟨fun g => ?_, fun g => ?_⟩
  · rw [MulAut.mul_apply, show β (g, 1) = (1, (β (g, 1)).2) from Prod.ext (hβ.1 g) rfl]
    exact hα.2 _
  · rw [MulAut.mul_apply, show β (1, g) = ((β (1, g)).1, 1) from Prod.ext rfl (hβ.2 g)]
    exact hα.1 _

theorem pres_mul_swap {α β : MulAut (G × G)} (hα : Pres α) (hβ : Swap β) : Swap (α * β) := by
  refine ⟨fun g => ?_, fun g => ?_⟩
  · rw [MulAut.mul_apply, show β (g, 1) = (1, (β (g, 1)).2) from Prod.ext (hβ.1 g) rfl]
    exact hα.2 _
  · rw [MulAut.mul_apply, show β (1, g) = ((β (1, g)).1, 1) from Prod.ext rfl (hβ.2 g)]
    exact hα.1 _

theorem swap_pow_odd {ψ : MulAut (G × G)} (h : Swap ψ) (k : ℕ) : Swap (ψ ^ (2 * k + 1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, pow_two]
    exact pres_mul_swap (swap_mul_swap h h) ih

theorem pres_of_pow (hK : IsCaseTwoGroup 3 G) {ψ : MulAut (G × G)} {m : ℕ}
    (hψ : ψ ^ (3 ^ m) = 1) : Pres ψ := by
  rcases pres_or_swap hK ψ with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    have hs := swap_pow_odd h k
    rw [← hk, hψ] at hs
    obtain ⟨x, hx⟩ := exists_ne_one hK
    exact hx (hs.1 x)

section Res

variable {P : Subgroup (MulAut (G × G))} (hP : ∀ ψ ∈ P, Pres ψ)

include hP

theorem pres_left {ψ : MulAut (G × G)} (h : ψ ∈ P) (g : G) : ψ (g, 1) = ((ψ (g, 1)).1, 1) :=
  Prod.ext rfl ((hP ψ h).1 g)

theorem pres_right {ψ : MulAut (G × G)} (h : ψ ∈ P) (g : G) : ψ (1, g) = (1, (ψ (1, g)).2) :=
  Prod.ext ((hP ψ h).2 g) rfl

@[expose] noncomputable def res₁ (ψ : P) : MulAut G where
  toFun g := ((ψ : MulAut (G × G)) (g, 1)).1
  invFun g := (((ψ : MulAut (G × G))⁻¹) (g, 1)).1
  left_inv g := by
    dsimp only
    rw [← pres_left hP ψ.2 g, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  right_inv g := by
    dsimp only
    rw [← pres_left hP (P.inv_mem ψ.2) g, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  map_mul' a b := by
    rw [show ((a * b, 1) : G × G) = (a, 1) * (b, 1) by simp, map_mul, Prod.fst_mul]

@[expose] noncomputable def res₂ (ψ : P) : MulAut G where
  toFun g := ((ψ : MulAut (G × G)) (1, g)).2
  invFun g := (((ψ : MulAut (G × G))⁻¹) (1, g)).2
  left_inv g := by
    dsimp only
    rw [← pres_right hP ψ.2 g, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  right_inv g := by
    dsimp only
    rw [← pres_right hP (P.inv_mem ψ.2) g, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  map_mul' a b := by
    rw [show ((1, a * b) : G × G) = (1, a) * (1, b) by simp, map_mul, Prod.snd_mul]

theorem res₁_apply (ψ : P) (g : G) : res₁ hP ψ g = ((ψ : MulAut (G × G)) (g, 1)).1 := rfl

theorem res₂_apply (ψ : P) (g : G) : res₂ hP ψ g = ((ψ : MulAut (G × G)) (1, g)).2 := rfl

@[expose] noncomputable def resHom : P →* MulAut G × MulAut G where
  toFun ψ := (res₁ hP ψ, res₂ hP ψ)
  map_one' := by
    ext g
    · rfl
    · rfl
  map_mul' α β := by
    ext g
    · show ((α : MulAut (G × G)) ((β : MulAut (G × G)) (g, 1))).1 =
        ((α : MulAut (G × G)) (((β : MulAut (G × G)) (g, 1)).1, 1)).1
      rw [← pres_left hP β.2 g]
    · show ((α : MulAut (G × G)) ((β : MulAut (G × G)) (1, g))).2 =
        ((α : MulAut (G × G)) (1, ((β : MulAut (G × G)) (1, g)).2)).2
      rw [← pres_right hP β.2 g]

theorem resHom_injective : Function.Injective (resHom hP) := by
  intro α β h
  have h1 : ∀ g, ((α : MulAut (G × G)) (g, 1)).1 = ((β : MulAut (G × G)) (g, 1)).1 := fun g =>
    congrArg (fun f : MulAut G × MulAut G => f.1 g) h
  have h2 : ∀ g, ((α : MulAut (G × G)) (1, g)).2 = ((β : MulAut (G × G)) (1, g)).2 := fun g =>
    congrArg (fun f : MulAut G × MulAut G => f.2 g) h
  apply Subtype.ext
  ext ⟨a, b⟩
  · rw [show ((a, b) : G × G) = (a, 1) * (1, b) by simp, map_mul, map_mul, Prod.fst_mul,
      Prod.fst_mul, (hP _ α.2).2 b, (hP _ β.2).2 b, h1]
  · rw [show ((a, b) : G × G) = (a, 1) * (1, b) by simp, map_mul, map_mul, Prod.snd_mul,
      Prod.snd_mul, (hP _ α.2).1 a, (hP _ β.2).1 a, h2]

theorem resHom_conj {s : G × G} (hs : MulAut.conj s ∈ P) :
    resHom hP ⟨MulAut.conj s, hs⟩ = (MulAut.conj s.1, MulAut.conj s.2) := by
  ext g
  · simp [resHom, res₁_apply, MulAut.conj_apply]
  · simp [resHom, res₂_apply, MulAut.conj_apply]

end Res

theorem mem_inn_of_comm (hK : IsCaseTwoGroup 3 G) (S : Sylow 3 G) {α : MulAut G}
    (h : ∀ a ∈ (S : Subgroup G), α * MulAut.conj a = MulAut.conj a * α) :
    α ∈ (S : Subgroup G).map (MulAut.conj : G →* MulAut G) := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  have hD := l28Data_of_equiv ε₀ S
  have hfix : ∀ x ∈ (S : Subgroup G), α x = x := by
    intro x hx
    apply hD.conj_injective
    ext y
    have h1 := congrArg (fun β : MulAut G => β (α.symm y)) (h x hx)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    rw [MulAut.conj_apply, MulAut.conj_apply, h1]
  obtain ⟨t, ht, rfl⟩ := hD.aut α hfix
  exact ⟨t, ht, rfl⟩

theorem card_inn (hK : IsCaseTwoGroup 3 G) (S : Sylow 3 G) :
    Nat.card ((S : Subgroup G).map (MulAut.conj : G →* MulAut G)) = 9 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  have hD := l28Data_of_equiv ε₀ S
  rw [Subgroup.card_map_of_injective hD.conj_injective, hD.card_eq]

theorem card_cube_le (hK : IsCaseTwoGroup 3 G) (S : Sylow 3 G) :
    Nat.card {y : MulAut G // y ∈ (S : Subgroup G).map (MulAut.conj : G →* MulAut G) ∧
      y ^ 3 = 1} ≤ 3 := by
  classical
  set I := (S : Subgroup G).map (MulAut.conj : G →* MulAut G)
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  have hD := l28Data_of_equiv ε₀ S
  obtain ⟨s0, hs0S, hs0⟩ := exists_orderOf_nine_of_isCaseTwoGroup hK S
  have hgen : Subgroup.zpowers (MulAut.conj s0) = I := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨s0, hs0S, rfl⟩
    · rw [Nat.card_zpowers, orderOf_injective _ hD.conj_injective, hs0, card_inn hK S]
  haveI : IsCyclic I := hgen ▸ inferInstance
  haveI : Fintype I := Fintype.ofFinite I
  have hcyc := IsCyclic.card_pow_eq_one_le (α := I) (n := 3) (by norm_num)
  have he : {y : MulAut G // y ∈ I ∧ y ^ 3 = 1} ≃ {z : I // z ^ 3 = 1} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext y.2.2⟩
      invFun := fun z => ⟨z.1.1, z.1.2, by simpa using congrArg Subtype.val z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcyc

theorem card_center_le_three {X : Type} [Group X] [Finite X] (hX : Nat.card X = 27)
    (hnc : ¬ ∀ a b : X, a * b = b * a) : Nat.card (Subgroup.center X) ≤ 3 := by
  have hdvd : Nat.card (Subgroup.center X) ∣ 27 := hX ▸ Subgroup.card_subgroup_dvd_card _
  have hd : Nat.card (Subgroup.center X) ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h
  · omega
  · omega
  · exfalso
    apply hnc
    have hq : Nat.card (X ⧸ Subgroup.center X) = 3 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
      rw [hX, h] at this
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (X ⧸ Subgroup.center X) := isCyclic_of_prime_card hq
    have := commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center X))
      (by rw [QuotientGroup.ker_mk'])
    exact fun a b => this a b
  · exfalso
    apply hnc
    have htop : Subgroup.center X = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hX])
    intro a b
    have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem finite_mulAut : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem shapeProd_core (hK : IsCaseTwoGroup 3 G) (S₁ S₂ : Sylow 3 G)
    {Q : Subgroup (MulAut G × MulAut G)} (hQ : IsPGroup 3 Q)
    (h₁ : ∀ a ∈ (S₁ : Subgroup G), (MulAut.conj a, (1 : MulAut G)) ∈ Q)
    (h₂ : ∀ b ∈ (S₂ : Subgroup G), ((1 : MulAut G), MulAut.conj b) ∈ Q) : ShapeProd Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut G) := finite_mulAut
  set I₁ := (S₁ : Subgroup G).map (MulAut.conj : G →* MulAut G) with hI₁
  set I₂ := (S₂ : Subgroup G).map (MulAut.conj : G →* MulAut G) with hI₂
  set I := I₁.prod I₂ with hI
  have hIQ : I ≤ Q := by
    rintro ⟨x, y⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    have := Q.mul_mem (h₁ a ha) (h₂ b hb)
    simpa using this
  have hIcard : Nat.card I = 81 := by
    rw [hI, Nat.card_congr (Subgroup.prodEquiv I₁ I₂).toEquiv, Nat.card_prod, card_inn hK S₁,
      card_inn hK S₂]
  have hcube : ∀ E : Subgroup (MulAut G × MulAut G), E ≤ I → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 9 := by
    intro E hEI hE3
    let f : E → {y : MulAut G // y ∈ I₁ ∧ y ^ 3 = 1} × {y : MulAut G // y ∈ I₂ ∧ y ^ 3 = 1} :=
      fun x => (⟨x.1.1, (hEI x.2).1, by simpa using congrArg Prod.fst (hE3 x.1 x.2)⟩,
        ⟨x.1.2, (hEI x.2).2, by simpa using congrArg Prod.snd (hE3 x.1 x.2)⟩)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact Prod.ext (congrArg (fun q => q.1.1) hxy) (congrArg (fun q => q.2.1) hxy)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at this
    calc Nat.card E ≤ _ := this
      _ ≤ 3 * 3 := Nat.mul_le_mul (card_cube_le hK S₁) (card_cube_le hK S₂)
      _ = 9 := rfl
  set Q₁ := Q.map (MonoidHom.fst (MulAut G) (MulAut G)) with hQ₁def
  set Q₂ := Q.map (MonoidHom.snd (MulAut G) (MulAut G)) with hQ₂def
  have hQ₁27 : Nat.card Q₁ ≤ 27 := kFactL28AutThree G hK Q₁ (hQ.map _)
  have hQ₂27 : Nat.card Q₂ ≤ 27 := kFactL28AutThree G hK Q₂ (hQ.map _)
  have hQle : Q ≤ Q₁.prod Q₂ := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hprodcard : Nat.card (Q₁.prod Q₂) = Nat.card Q₁ * Nat.card Q₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv Q₁ Q₂).toEquiv, Nat.card_prod]
  have hQ729 : Nat.card Q ≤ 729 := by
    calc Nat.card Q ≤ Nat.card (Q₁.prod Q₂) := Subgroup.card_le_of_le hQle
      _ = Nat.card Q₁ * Nat.card Q₂ := hprodcard
      _ ≤ 27 * 27 := Nat.mul_le_mul hQ₁27 hQ₂27
      _ = 729 := rfl
  have h81 : 81 ∣ Nat.card Q := hIcard ▸ Subgroup.card_dvd_of_le hIQ
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hk' : k = 4 ∨ k = 5 ∨ k = 6 := by
    have h1 : 3 ^ 4 ∣ 3 ^ k := by rw [← hk]; simpa using h81
    have h2 : 3 ^ k ≤ 3 ^ 6 := by rw [← hk]; simpa using hQ729
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    omega
  have hnc : I ≠ Q → ¬ ∀ a b : Q, a * b = b * a := by
    intro hne hcomm
    obtain ⟨x, hxQ, hxI⟩ : ∃ x ∈ Q, x ∉ I := by
      by_contra! h
      exact hne (le_antisymm hIQ h)
    apply hxI
    refine Subgroup.mem_prod.mpr ⟨mem_inn_of_comm hK S₁ fun a ha => ?_,
      mem_inn_of_comm hK S₂ fun b hb => ?_⟩
    · have := congrArg (fun z : Q => (z : MulAut G × MulAut G).1) (hcomm ⟨x, hxQ⟩ ⟨_, h₁ a ha⟩)
      simpa using this
    · have := congrArg (fun z : Q => (z : MulAut G × MulAut G).2) (hcomm ⟨x, hxQ⟩ ⟨_, h₂ b hb⟩)
      simpa using this
  have hne : 81 < Nat.card Q → I ≠ Q := fun hlt h => by
    rw [← h, hIcard] at hlt
    exact lt_irrefl _ hlt
  rcases hk' with rfl | rfl | rfl
  ·
    have hQI : I = Q := Subgroup.eq_of_le_of_card_ge hIQ (by rw [hk, hIcard]; norm_num)
    refine Or.inr (Or.inl ⟨by rw [hk]; norm_num, ?_⟩)
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    have hmap := hcube (E.map Q.subtype) (by
        intro y hy
        rw [hQI]
        exact Subgroup.map_subtype_le E hy)
      (by
        rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hE.2 x hx))
    rw [Subgroup.card_map_of_injective Q.subtype_injective] at hmap
    calc Nat.card E ≤ 9 := hmap
      _ = 3 ^ 2 := by norm_num
  ·
    refine Or.inl ⟨hnc (hne (by rw [hk]; norm_num)),
      CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_⟩
    set E' := E.map Q.subtype with hE'def
    have hE'Q : E' ≤ Q := Subgroup.map_subtype_le E
    have hE'card : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective Q.subtype_injective
    have hrel : I.relIndex Q = 3 := by
      have := Subgroup.relIndex_mul_card (H := I) (K := Q)
      rw [inf_of_le_left hIQ, hIcard, hk] at this
      omega
    have hrel' : I.relIndex E' ≤ 3 :=
      hrel ▸ Subgroup.relIndex_le_of_le_right hE'Q (by rw [hrel]; norm_num)
    have hcap : Nat.card (I ⊓ E' : Subgroup _) ≤ 9 := hcube _ inf_le_left (by
      rintro x ⟨-, y, hy, rfl⟩
      simpa using congrArg Subtype.val (hE.2 y hy))
    have hEcard := Subgroup.relIndex_mul_card (H := I) (K := E')
    rw [hE'card] at hEcard
    calc Nat.card E = I.relIndex E' * Nat.card (I ⊓ E' : Subgroup _) := hEcard.symm
      _ ≤ 3 * 9 := Nat.mul_le_mul hrel' hcap
      _ = 3 ^ 3 := by norm_num
  ·
    have hQ₁₂ : Nat.card Q₁ = 27 ∧ Nat.card Q₂ = 27 := by
      have h := Subgroup.card_le_of_le hQle
      rw [hprodcard, hk] at h
      constructor
      · refine le_antisymm hQ₁27 ?_
        by_contra! hlt
        have : Nat.card Q₁ * Nat.card Q₂ < 27 * 27 :=
          Nat.mul_lt_mul_of_lt_of_le hlt hQ₂27 (by norm_num)
        omega
      · refine le_antisymm hQ₂27 ?_
        by_contra! hlt
        have : Nat.card Q₁ * Nat.card Q₂ < 27 * 27 :=
          Nat.mul_lt_mul_of_le_of_lt hQ₁27 hlt (by norm_num)
        omega
    have hQprod : Q = Q₁.prod Q₂ := Subgroup.eq_of_le_of_card_ge hQle (by
      rw [hprodcard, hQ₁₂.1, hQ₁₂.2, hk]; norm_num)
    have hge : Q₁.prod Q₂ ≤ Q := le_of_eq hQprod.symm
    have hncQ₁ : ¬ ∀ a b : Q₁, a * b = b * a := by
      intro hcomm
      obtain ⟨α, hαQ, hαI⟩ : ∃ α ∈ Q₁, α ∉ I₁ := by
        by_contra! h
        have := Subgroup.card_le_of_le (show Q₁ ≤ I₁ from h)
        rw [hQ₁₂.1, card_inn hK S₁] at this
        norm_num at this
      apply hαI
      refine mem_inn_of_comm hK S₁ fun a ha => ?_
      have hmem : MulAut.conj a ∈ Q₁ := ⟨_, h₁ a ha, rfl⟩
      simpa using congrArg Subtype.val (hcomm ⟨α, hαQ⟩ ⟨_, hmem⟩)
    have hncQ₂ : ¬ ∀ a b : Q₂, a * b = b * a := by
      intro hcomm
      obtain ⟨α, hαQ, hαI⟩ : ∃ α ∈ Q₂, α ∉ I₂ := by
        by_contra! h
        have := Subgroup.card_le_of_le (show Q₂ ≤ I₂ from h)
        rw [hQ₁₂.2, card_inn hK S₂] at this
        norm_num at this
      apply hαI
      refine mem_inn_of_comm hK S₂ fun b hb => ?_
      have hmem : MulAut.conj b ∈ Q₂ := ⟨_, h₂ b hb, rfl⟩
      simpa using congrArg Subtype.val (hcomm ⟨α, hαQ⟩ ⟨_, hmem⟩)
    refine Or.inr (Or.inr ⟨by rw [hk]; norm_num, ?_⟩)
    have hm₁ : ∀ z : Q, (z : MulAut G × MulAut G).1 ∈ Q₁ := fun z => ⟨z, z.2, rfl⟩
    have hm₂ : ∀ z : Q, (z : MulAut G × MulAut G).2 ∈ Q₂ := fun z => ⟨z, z.2, rfl⟩
    have hc₁ : ∀ z : Q, z ∈ Subgroup.center Q →
        (⟨(z : MulAut G × MulAut G).1, hm₁ z⟩ : Q₁) ∈ Subgroup.center Q₁ := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro γ
      have hγ : ((γ : MulAut G), (1 : MulAut G)) ∈ Q := hge ⟨γ.2, Q₂.one_mem⟩
      have := Subgroup.mem_center_iff.mp hz ⟨_, hγ⟩
      apply Subtype.ext
      simpa using congrArg (fun w : Q => (w : MulAut G × MulAut G).1) this
    have hc₂ : ∀ z : Q, z ∈ Subgroup.center Q →
        (⟨(z : MulAut G × MulAut G).2, hm₂ z⟩ : Q₂) ∈ Subgroup.center Q₂ := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro γ
      have hγ : ((1 : MulAut G), (γ : MulAut G)) ∈ Q := hge ⟨Q₁.one_mem, γ.2⟩
      have := Subgroup.mem_center_iff.mp hz ⟨_, hγ⟩
      apply Subtype.ext
      simpa using congrArg (fun w : Q => (w : MulAut G × MulAut G).2) this
    let f : Subgroup.center Q → Subgroup.center Q₁ × Subgroup.center Q₂ := fun z =>
      (⟨_, hc₁ z.1 z.2⟩, ⟨_, hc₂ z.1 z.2⟩)
    have hf : Function.Injective f := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (congrArg (fun q => ((q.1 : Q₁) : MulAut G)) hzw)
        (congrArg (fun q => ((q.2 : Q₂) : MulAut G)) hzw)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at this
    calc Nat.card (Subgroup.center Q) ≤ _ := this
      _ ≤ 3 * 3 := Nat.mul_le_mul (card_center_le_three hQ₁₂.1 hncQ₁)
          (card_center_le_three hQ₁₂.2 hncQ₂)
      _ = 9 := rfl

theorem card_le_nine (hK : IsCaseTwoGroup 3 G) {H : Subgroup G} (hH : IsPGroup 3 H) :
    Nat.card H ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : 3 ^ k ∣ 504 := hk ▸ card_eq hK ▸ Subgroup.card_subgroup_dvd_card H
  have hk2 : k ≤ 2 := by
    by_contra! h
    have : 3 ^ 3 ∣ 504 := (Nat.pow_dvd_pow 3 h).trans hdvd
    norm_num at this
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem card_sylow_of_card {X : Type} [Group X] [Finite X] (hX : Nat.card X = 3 ^ 4 * 3136)
    (S : Sylow 3 X) : Nat.card (S : Subgroup X) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : Nat.factorization (Nat.card X) 3 = 4 := by
    rw [hX, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [Sylow.card_eq_multiplicity, hf]
  norm_num

end L28Sq

open L28Sq in
theorem kFactCaseIThreeShapeProd : KFactCaseIThreeShapeProd := by
  classical
  intro B _ _ Kb _ T hT ⟨S, hST⟩ hKb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hKb
  set G := (TauCeti.CFSGIndex.lie d).Group
  have hG : IsCaseTwoGroup 3 G := ⟨d, Or.inl ⟨rfl, hd⟩, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite G := Finite.of_injective (fun g : G => e.symm (g, 1)) fun a b h => by
    simpa using congrArg Prod.fst (e.symm.injective h)
  set φ := (MulAut.conjNormal (H := Kb)).comp T.subtype with hφ
  have hR : IsPGroup 3 φ.range := hT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  set c : MulAut Kb ≃* MulAut (G × G) := MulAut.congr e with hc
  set R' := φ.range.map c.toMonoidHom with hR'def
  have hR' : IsPGroup 3 R' := hR.map _
  have hpres : ∀ ψ ∈ R', Pres ψ := by
    intro ψ hψ
    obtain ⟨m, hm⟩ := hR' ⟨ψ, hψ⟩
    exact pres_of_pow hG (m := m) (by simpa using congrArg Subtype.val hm)
  set Q := (resHom hpres).range with hQdef
  have hQ : IsPGroup 3 Q := hR'.of_surjective (resHom hpres).rangeRestrict
    (resHom hpres).rangeRestrict_surjective
  set S' := (S : Subgroup Kb).map e.toMonoidHom with hS'def
  have hS'card : Nat.card S' = 81 := by
    rw [hS'def, Subgroup.card_map_of_injective e.injective]
    exact card_sylow_of_card (by rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_eq hG]; norm_num) S
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map _
  set T₁ := S'.map (MonoidHom.fst G G)
  set T₂ := S'.map (MonoidHom.snd G G)
  have hT₁ : Nat.card T₁ ≤ 9 := card_le_nine hG (hS'p.map _)
  have hT₂ : Nat.card T₂ ≤ 9 := card_le_nine hG (hS'p.map _)
  have hS'le : S' ≤ T₁.prod T₂ := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hpc : Nat.card (T₁.prod T₂) = Nat.card T₁ * Nat.card T₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv T₁ T₂).toEquiv, Nat.card_prod]
  have h81 : 81 ≤ Nat.card T₁ * Nat.card T₂ := hpc ▸ hS'card ▸ Subgroup.card_le_of_le hS'le
  have hT₁9 : Nat.card T₁ = 9 := by
    refine le_antisymm hT₁ ?_
    by_contra! hlt
    have : Nat.card T₁ * Nat.card T₂ < 9 * 9 := Nat.mul_lt_mul_of_lt_of_le hlt hT₂ (by norm_num)
    omega
  have hT₂9 : Nat.card T₂ = 9 := by
    refine le_antisymm hT₂ ?_
    by_contra! hlt
    have : Nat.card T₁ * Nat.card T₂ < 9 * 9 := Nat.mul_lt_mul_of_le_of_lt hT₁ hlt (by norm_num)
    omega
  have hS'eq : S' = T₁.prod T₂ := Subgroup.eq_of_le_of_card_ge hS'le (by
    rw [hpc, hT₁9, hT₂9, hS'card])
  have hfac : Nat.factorization (Nat.card G) 3 = 2 := by
    rw [card_eq hG, show (504 : ℕ) = 3 ^ 2 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let S₁ : Sylow 3 G := Sylow.ofCard T₁ (by rw [hT₁9, hfac]; norm_num)
  let S₂ : Sylow 3 G := Sylow.ofCard T₂ (by rw [hT₂9, hfac]; norm_num)
  have hinn : ∀ x ∈ S', MulAut.conj x ∈ R' := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨φ ⟨s, hST ⟨s, hs, rfl⟩⟩, ⟨_, rfl⟩, ?_⟩
    have hcs : ∀ z : Kb, MulAut.conjNormal (s : B) z = s * z * s⁻¹ := fun z =>
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    refine MulEquiv.ext fun y => ?_
    show e (MulAut.conjNormal (s : B) (e.symm y)) = e s * y * (e s)⁻¹
    rw [hcs, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hQ₁ : ∀ a ∈ (S₁ : Subgroup G), (MulAut.conj a, (1 : MulAut G)) ∈ Q := by
    intro a ha
    have hx : ((a, 1) : G × G) ∈ S' := hS'eq ▸ ⟨ha, T₂.one_mem⟩
    refine ⟨⟨_, hinn _ hx⟩, ?_⟩
    rw [resHom_conj]
    simp
  have hQ₂ : ∀ b ∈ (S₂ : Subgroup G), ((1 : MulAut G), MulAut.conj b) ∈ Q := by
    intro b hb
    have hx : ((1, b) : G × G) ∈ S' := hS'eq ▸ ⟨T₁.one_mem, hb⟩
    refine ⟨⟨_, hinn _ hx⟩, ?_⟩
    rw [resHom_conj]
    simp
  have hcore := shapeProd_core hG S₁ S₂ hQ hQ₁ hQ₂
  have e₁ := QuotientGroup.quotientKerEquivRange φ
  have e₂ := φ.range.equivMapOfInjective c.toMonoidHom c.injective
  have e₃ := MonoidHom.ofInjective (resHom_injective hpres)
  exact shapeProd_congr (e₁.trans (e₂.trans e₃)).symm hcore

theorem kFactCaseIThreeShape :
    KFactCaseIThreeShape :=
  kFactCaseIThreeShape_of_prod kFactCaseIThreeShapeProd

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
