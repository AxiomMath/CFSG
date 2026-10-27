module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section Comp

@[expose] def NoNormalTwo (Γ : Type*) [Group Γ] : Prop :=
  ∀ N : Subgroup Γ, N.Normal → IsPGroup 2 ↥N → N = ⊥

theorem map_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

variable {Γ : Type*} [Group Γ]

theorem isComponent_map_conj {L : Subgroup Γ} (hL : CFSG.IsComponent L) (g : Γ) :
    CFSG.IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
  ⟨isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ (MulAut.conj g).injective) hL.1,
    hL.2.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective⟩

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    Nontrivial Q := by
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2.1
  exact (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial

theorem isComponent_toGW {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    CFSG.GorensteinWalter.IsComponentOf L ⊤ :=
  ⟨le_top, hL.2.subgroupOf, nontrivial_of_isQuasisimple hL.1, Group.isPerfect_def.mp hL.1.1,
    hL.1.2.1⟩

variable [Finite Γ]

theorem isComponent_commute_of_ne {L₁ L₂ : Subgroup Γ} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) {a b : Γ} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    a * b = b * a := by
  have h := CFSG.GorensteinWalter.component_commute_of_ne (isComponent_toGW h₁)
    (isComponent_toGW h₂) hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact ((Subgroup.mem_centralizer_iff.mp (h ha)) b hb).symm

omit [Finite Γ] in
theorem exists_pow_eq_one_of_mem_closure {S : Set Γ} (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (h2 : ∀ a ∈ S, ∃ k : ℕ, a ^ 2 ^ k = 1) {x : Γ} (hx : x ∈ Subgroup.closure S) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hS : S ⊆ (Subgroup.centralizer S : Set Γ) := fun a ha b hb => hcomm b hb a ha
  have hcl : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr hS
    have h2 := Subgroup.closure_le_centralizer_centralizer S
    exact ((Subgroup.mem_centralizer_iff.mp (h2 hx)) y (h1 hy)).symm
  let P : Subgroup Γ :=
    { carrier := {x | x ∈ Subgroup.closure S ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨Subgroup.mul_mem _ ha hb, k + l, ?_⟩
        have hab : Commute a b := hcl a ha b hb
        rw [hab.mul_pow, pow_add, pow_mul, hk, one_pow, mul_comm (2 ^ k), pow_mul, hl, one_pow,
          mul_one]
      one_mem' := ⟨Subgroup.one_mem _, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨Subgroup.inv_mem _ ha, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hle : Subgroup.closure S ≤ P :=
    (Subgroup.closure_le P).mpr fun a ha => ⟨Subgroup.subset_closure ha, h2 a ha⟩
  exact (hle hx).2


theorem eq_one_of_central_two (hO : NoNormalTwo Γ) {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    {z : Γ} (hzL : z ∈ L) (hzc : ∀ l ∈ L, l * z = z * l) {k : ℕ} (hz : z ^ 2 ^ k = 1) :
    z = 1 := by
  set S : Set Γ := {w | ∃ g : Γ, w = g * z * g⁻¹} with hS
  have hcent : ∀ g : Γ, (g * z * g⁻¹) ∈ L.map (MulAut.conj g).toMonoidHom ∧
      ∀ l ∈ L.map (MulAut.conj g).toMonoidHom, l * (g * z * g⁻¹) = (g * z * g⁻¹) * l := by
    intro g
    refine ⟨⟨z, hzL, by simp [MulAut.conj_apply]⟩, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hzc l hl
    calc g * l * g⁻¹ * (g * z * g⁻¹) = g * (l * z) * g⁻¹ := by group
      _ = g * (z * l) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * (g * l * g⁻¹) := by group
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    by_cases hgh : L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj h).toMonoidHom
    · exact (hcent h).2 _ (hgh ▸ (hcent g).1)
    · exact isComponent_commute_of_ne (isComponent_map_conj hL g) (isComponent_map_conj hL h) hgh
        (hcent g).1 (hcent h).1
  have h2 : ∀ a ∈ S, ∃ k : ℕ, a ^ 2 ^ k = 1 := by
    rintro _ ⟨g, rfl⟩
    refine ⟨k, ?_⟩
    have := conj_pow (a := g) (b := z) (i := 2 ^ k)
    rw [hz] at this
    simpa using this
  have hsub : Subgroup.normalClosure ({z} : Set Γ) ≤ Subgroup.closure S := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hax
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact Subgroup.subset_closure ⟨c, hc.symm⟩
  have hpg : IsPGroup 2 ↥(Subgroup.normalClosure ({z} : Set Γ)) := by
    intro x
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_closure hcomm h2 (hsub x.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hbot := hO _ inferInstance hpg
  have hz1 : z ∈ Subgroup.normalClosure ({z} : Set Γ) := Subgroup.subset_normalClosure rfl
  rw [hbot] at hz1
  exact hz1

theorem even_card_of_isComponent {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    Even (Nat.card ↥L) := by
  have := nontrivial_of_isQuasisimple hL.1
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hsolv := CFSG.Milestones.odd_order_solvable hodd
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥L)
  exact hlt.ne (Group.isPerfect_def.mp hL.1.1)

theorem false_of_two_central (hO : NoNormalTwo Γ) {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    (h2 : ∀ l ∈ L, (∃ k : ℕ, l ^ 2 ^ k = 1) → ∀ m ∈ L, m * l = l * m) : False := by
  have hev := even_iff_two_dvd.mp (even_card_of_isComponent hL)
  have : Fintype ↥L := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at hev)
  have hx2 : (x : Γ) ^ 2 ^ 1 = 1 := by
    have : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  have hxc : ∀ l ∈ L, l * (x : Γ) = (x : Γ) * l := fun l hl => h2 x x.2 ⟨1, hx2⟩ l hl
  have h1 := eq_one_of_central_two hO hL x.2 hxc hx2
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

end Comp

end CFSG.CGT.PushingUpLit.CGT6
