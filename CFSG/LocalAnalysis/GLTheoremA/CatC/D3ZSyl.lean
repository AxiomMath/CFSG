module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FAlg

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open scoped Pointwise

theorem d3z_map_eq_of_forall_mem {G : Type*} [Group G] [Finite G] (S : Subgroup G) (α : MulAut G)
    (h : ∀ y ∈ S, α y ∈ S) : S.map α.toMonoidHom = S :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (by rw [Subgroup.card_map_of_injective α.injective])

theorem exists_stable_sylow_in {G : Type*} [Group G] [Finite G] (α : MulAut G) (hα : α ^ 3 = 1)
    (P : Subgroup G) (hPα : ∀ x ∈ P, α x ∈ P) (S₀ : Sylow 3 G) (hS₀ : (S₀ : Subgroup G) ≤ P) :
    ∃ S : Sylow 3 G, (S : Subgroup G) ≤ P ∧ (S : Subgroup G).map α.toMonoidHom = S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPmap : P.map α.toMonoidHom = P := d3z_map_eq_of_forall_mem P α hPα
  let αP : MulAut ↥P :=
    (MulEquiv.subgroupMap (α : G ≃* G) P).trans (MulEquiv.subgroupCongr hPmap)
  have hαP : ∀ x : ↥P, ((αP x : ↥P) : G) = α x := fun x => rfl
  have hαPn : ∀ (n : ℕ) (x : ↥P), (((αP ^ n) x : ↥P) : G) = (α ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hαP]
  have hαP3 : αP ^ 3 = 1 := by
    ext x
    rw [hαPn, hα]; rfl
  have hbot : IsElemAbelian 3 (⊥ : Subgroup ↥P) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha := Subgroup.mem_bot.1 a.2
      have hb := Subgroup.mem_bot.1 b.2
      apply Subtype.ext
      simp [ha, hb]
    · rw [Subgroup.mem_bot.1 hx]; simp
  obtain ⟨T, -, hT⟩ := exists_stable_sylow_fixing αP hαP3 ⊥ hbot
    (fun a ha => by rw [Subgroup.mem_bot.1 ha]; exact map_one _)
  have hTc : Nat.card (T : Subgroup ↥P) = 3 ^ (Nat.card ↥P).factorization 3 :=
    Sylow.card_eq_multiplicity T
  have hS0 : Nat.card (S₀ : Subgroup G) = 3 ^ (Nat.card G).factorization 3 :=
    Sylow.card_eq_multiplicity S₀
  have hT' : Nat.card ((S₀.subtype hS₀ : Sylow 3 ↥P) : Subgroup ↥P) =
      3 ^ (Nat.card ↥P).factorization 3 := Sylow.card_eq_multiplicity _
  have hT'S : Nat.card ((S₀.subtype hS₀ : Sylow 3 ↥P) : Subgroup ↥P) = Nat.card (S₀ : Subgroup G) := by
    rw [Sylow.coe_subtype]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀).toEquiv
  have hv : (Nat.card ↥P).factorization 3 = (Nat.card G).factorization 3 := by
    have := hT'.symm.trans (hT'S.trans hS0)
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  have hQ : Nat.card ((T : Subgroup ↥P).map P.subtype) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hTc, hv]
  refine ⟨Sylow.ofCard _ hQ, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _
  · rw [Sylow.coe_ofCard, Subgroup.map_map]
    have e : α.toMonoidHom.comp P.subtype = P.subtype.comp αP.toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, hT]

theorem normalizer_le_of_sylow {G : Type*} [Group G] [Finite G] (P : Subgroup G) (S₀ S₁ : Sylow 3 G)
    (h₀ : (S₀ : Subgroup G) ≤ P) (h₁ : (S₁ : Subgroup G) ≤ P)
    (hN : Subgroup.normalizer ((S₀ : Subgroup G) : Set G) ≤ P) :
    Subgroup.normalizer ((S₁ : Subgroup G) : Set G) ≤ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq ↥P (S₀.subtype h₀) (S₁.subtype h₁)
  rw [Sylow.smul_subtype h₀ p] at hp
  have hS := Sylow.subtype_injective hp
  have hS' : (S₁ : Subgroup G) = MulAut.conj (p : G) • (S₀ : Subgroup G) := by
    rw [← hS]; rfl
  have hmem : ∀ u : G, u ∈ (S₁ : Subgroup G) ↔ (p : G)⁻¹ * u * (p : G) ∈ (S₀ : Subgroup G) := by
    intro u
    rw [hS', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_inv_apply]
  intro x hx
  have hxS := Subgroup.mem_normalizer_iff.1 hx
  have hconj : (p : G)⁻¹ * x * (p : G) ∈ Subgroup.normalizer ((S₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e : ((p : G)⁻¹ * x * (p : G)) * h * ((p : G)⁻¹ * x * (p : G))⁻¹ =
        (p : G)⁻¹ * (x * ((p : G) * h * (p : G)⁻¹) * x⁻¹) * (p : G) := by group
    have e1 : (p : G)⁻¹ * ((p : G) * h * (p : G)⁻¹) * (p : G) = h := by group
    rw [e]
    calc h ∈ (S₀ : Subgroup G) ↔ (p : G)⁻¹ * ((p : G) * h * (p : G)⁻¹) * (p : G) ∈ (S₀ : Subgroup G) := by
          rw [e1]
      _ ↔ (p : G) * h * (p : G)⁻¹ ∈ (S₁ : Subgroup G) := (hmem _).symm
      _ ↔ x * ((p : G) * h * (p : G)⁻¹) * x⁻¹ ∈ (S₁ : Subgroup G) := hxS _
      _ ↔ _ := hmem _
  have hxP : (p : G) * ((p : G)⁻¹ * x * (p : G)) * (p : G)⁻¹ ∈ P :=
    mul_mem (mul_mem p.2 (hN hconj)) (inv_mem p.2)
  simpa [mul_assoc] using hxP


theorem map_conj_stable {G : Type*} [Group G] [Finite G] (α : MulAut G) (S : Subgroup G)
    (hS : S.map α.toMonoidHom = S) (c : G)
    (hc : c⁻¹ * α c ∈ Subgroup.normalizer (S : Set G)) :
    (S.map (MulAut.conj c).toMonoidHom).map α.toMonoidHom = S.map (MulAut.conj c).toMonoidHom := by
  refine d3z_map_eq_of_forall_mem _ α ?_
  rintro _ ⟨s, hs, rfl⟩
  have hαs : α s ∈ S := by
    have := Subgroup.mem_map_of_mem α.toMonoidHom hs
    rwa [hS] at this
  have h1 : (c⁻¹ * α c) * α s * (c⁻¹ * α c)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hc (α s)).1 hαs
  refine ⟨_, h1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem map_conj_stable_inner {G : Type*} [Group G] [Finite G] (y c : G) (S : Subgroup G)
    (hc : c⁻¹ * y * c ∈ Subgroup.normalizer (S : Set G)) :
    (S.map (MulAut.conj c).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      S.map (MulAut.conj c).toMonoidHom := by
  refine d3z_map_eq_of_forall_mem _ (MulAut.conj y) ?_
  rintro _ ⟨s, hs, rfl⟩
  have h1 : (c⁻¹ * y * c) * s * (c⁻¹ * y * c)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hc s).1 hs
  refine ⟨_, h1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

end CFSG.LocalAnalysis.GLTheoremA
