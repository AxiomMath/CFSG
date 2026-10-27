module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Index3
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.NativeMonomial
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open scoped Pointwise

abbrev G23 : Type := ↥(adjointGroup ReeTag.G2.tag (ZMod 3))

abbrev fixedGroup {G : Type*} [Group G] (α : MulAut G) : Subgroup G :=
  α.toMonoidHom.eqLocus (MonoidHom.id G)

theorem mem_conj_smul_iff {G : Type*} [Group G] (y : G) (H : Subgroup G) (z : G) :
    z ∈ (MulAut.conj y • H : Subgroup G) ↔ y⁻¹ * z * y ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have : (MulAut.conj y)⁻¹ = MulAut.conj y⁻¹ := (map_inv MulAut.conj y).symm
  rw [this, MulAut.smul_def, MulAut.conj_apply]
  simp

@[expose] def G23Pinned (α : MulAut G23) : Prop :=
  ∃ (u s : Fin 3 → G23) (g₀ : G23),
    (∀ i, α (u i) = u i ∧ u i * u i = 1 ∧ u i ≠ 1) ∧
    (∀ i, α (s i) = s i ∧ s i * s i = 1) ∧
    (∀ i j, s i * s j = s j * s i) ∧
    Nat.card (Subgroup.closure (Set.range s)) = 8 ∧
    (∀ i, g₀ * s i * g₀⁻¹ ∈ Subgroup.closure (Set.range s)) ∧
    Subgroup.closure (Set.range u ∪ Set.range fun i => g₀ * u i * g₀⁻¹) = ⊤

theorem G23Pinned.of_conj {α β : MulAut G23} (ψ : MulAut G23) (h : ψ * α * ψ⁻¹ = β)
    (hβ : G23Pinned β) : G23Pinned α := by
  obtain ⟨u, s, g₀, hu, hs, hsc, hs8, hg₀, hgen⟩ := hβ
  have hαψ : ∀ x, α (ψ⁻¹ x) = ψ⁻¹ (β x) := by
    intro x
    have hx := congrArg (fun γ : MulAut G23 => ψ⁻¹ (γ x)) h
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at hx
    exact hx
  have hmap : ∀ T : Subgroup G23, (T.map ψ⁻¹.toMonoidHom).map ψ.toMonoidHom = T := by
    intro T
    rw [Subgroup.map_map]
    have : ψ.toMonoidHom.comp ψ⁻¹.toMonoidHom = MonoidHom.id G23 := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  refine ⟨fun i => ψ⁻¹ (u i), fun i => ψ⁻¹ (s i), ψ⁻¹ g₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨h1, h2, h3⟩ := hu i
    refine ⟨by rw [hαψ, h1], ?_, ?_⟩
    · rw [← map_mul, h2, map_one]
    · intro h4
      have h4' : ψ⁻¹ (u i) = 1 := h4
      exact h3 (ψ⁻¹.injective (h4'.trans (map_one ψ⁻¹).symm))
  · intro i
    obtain ⟨h1, h2⟩ := hs i
    refine ⟨by rw [hαψ, h1], ?_⟩
    rw [← map_mul, h2, map_one]
  · intro i j
    rw [← map_mul, ← map_mul, hsc i j]
  · have hc : Subgroup.closure (Set.range fun i => ψ⁻¹ (s i)) =
        (Subgroup.closure (Set.range s)).map ψ⁻¹.toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [hc]
    rw [← hs8]
    exact (Nat.card_congr
      ((Subgroup.closure (Set.range s)).equivMapOfInjective ψ⁻¹.toMonoidHom
        ψ⁻¹.injective).toEquiv).symm
  · intro i
    have hc : Subgroup.closure (Set.range fun i => ψ⁻¹ (s i)) =
        (Subgroup.closure (Set.range s)).map ψ⁻¹.toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [hc]
    refine ⟨g₀ * s i * g₀⁻¹, hg₀ i, ?_⟩
    simp
  · have hc : Subgroup.closure (Set.range (fun i => ψ⁻¹ (u i)) ∪
        Set.range fun i => ψ⁻¹ g₀ * ψ⁻¹ (u i) * (ψ⁻¹ g₀)⁻¹) =
        (Subgroup.closure (Set.range u ∪ Set.range fun i => g₀ * u i * g₀⁻¹)).map
          ψ⁻¹.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
      congr 2
      ext i
      simp
    rw [hc, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 ψ⁻¹.surjective

theorem generation_of_pinned {α : MulAut G23} (hfix : Nat.card (fixedGroup α) = 1512)
    (hp : G23Pinned α) {Y : Subgroup G23} (hYα : Y ≤ fixedGroup α) [hperf : Group.IsPerfect ↥Y]
    (hY : Nat.card Y = 504) {S : Subgroup G23} (hSY : S ≤ Y) (hS : Nat.card S = 8) :
    ∃ g ∈ Subgroup.normalizer (S : Set G23), Y ⊔ Y.map (MulAut.conj g).toMonoidHom = ⊤ := by
  classical
  obtain ⟨u, s, g₀, hu, hs, -, hs8, hg₀, hgen⟩ := hp
  set M : Subgroup G23 := fixedGroup α with hM
  have hperf' : Group.IsPerfect ↥(Y.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYα).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYα).symm.surjective
  have hcardYM : Nat.card ↥(Y.subgroupOf M) = 504 := by
    rw [← hY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYα).toEquiv
  have hidx : (Y.subgroupOf M).index = 3 := by
    have h1 := Subgroup.card_mul_index (Y.subgroupOf M)
    rw [hcardYM, hfix] at h1
    omega
  have hinv : ∀ x : G23, α x = x → x * x = 1 → x ∈ Y := by
    intro x hx hxx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · have hxM : x ∈ M := hx
      have hord : orderOf (⟨x, hxM⟩ : M) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine orderOf_eq_prime (p := 2) ?_ ?_
        · apply Subtype.ext
          show x ^ 2 = 1
          rw [pow_two]
          exact hxx
        · intro h
          apply hx1
          simpa using congrArg Subtype.val h
      exact mem_of_perfect_index_three (Y := Y.subgroupOf M) hidx
        (x := ⟨x, hxM⟩) (by rw [hord]; norm_num)
  set S₀ : Subgroup G23 := Subgroup.closure (Set.range s) with hS₀
  have hS₀Y : S₀ ≤ Y := by
    rw [hS₀, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hinv _ (hs i).1 (hs i).2
  have huY : ∀ i, u i ∈ Y := fun i => hinv _ (hu i).1 (hu i).2.1
  have hg₀le : ∀ h ∈ S₀, g₀ * h * g₀⁻¹ ∈ S₀ := by
    have hle : S₀ ≤ S₀.comap (MulAut.conj g₀).toMonoidHom := by
      rw [hS₀, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hg₀ i
    intro h hh
    exact hle hh
  have hfinS₀ : Finite ↥S₀ := Nat.finite_of_card_ne_zero (by rw [hs8]; norm_num)
  have hfinY : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have hg₀iff : ∀ h : G23, h ∈ S₀ ↔ g₀ * h * g₀⁻¹ ∈ S₀ := by
    have hmapeq : S₀.map (MulAut.conj g₀).toMonoidHom = S₀ := by
      refine Subgroup.eq_of_le_of_card_ge (H := S₀.map (MulAut.conj g₀).toMonoidHom) ?_ ?_
      · rintro _ ⟨h, hh, rfl⟩
        exact hg₀le h hh
      · exact (Nat.card_congr (S₀.equivMapOfInjective (MulAut.conj g₀).toMonoidHom
          (MulAut.conj g₀).injective).toEquiv).le
    intro h
    constructor
    · exact hg₀le h
    · intro hh
      have hh2 : g₀ * h * g₀⁻¹ ∈ S₀.map (MulAut.conj g₀).toMonoidHom := by
        rw [hmapeq]
        exact hh
      obtain ⟨h', hh', hh'e⟩ := hh2
      have : h' = h := (MulAut.conj g₀).injective (by simpa [MulAut.conj_apply] using hh'e)
      rw [← this]
      exact hh'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card ↥Y).factorization 2 = 3 := by
    rw [hY]
    have h504 : (504 : ℕ) = 2 ^ 3 * 63 := by norm_num
    rw [h504, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 63)]
  have hcardS : Nat.card ↥(S.subgroupOf Y) = 2 ^ (Nat.card ↥Y).factorization 2 := by
    rw [hfac]
    have h1 : Nat.card ↥(S.subgroupOf Y) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
    rw [h1, hS]
    norm_num
  have hcardS₀ : Nat.card ↥(S₀.subgroupOf Y) = 2 ^ (Nat.card ↥Y).factorization 2 := by
    rw [hfac]
    have h1 : Nat.card ↥(S₀.subgroupOf Y) = Nat.card S₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀Y).toEquiv
    rw [h1, hs8]
    norm_num
  let PS : Sylow 2 ↥Y := Sylow.ofCard (S.subgroupOf Y) hcardS
  let PT : Sylow 2 ↥Y := Sylow.ofCard (S₀.subgroupOf Y) hcardS₀
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥Y PT PS
  have hcoe : (MulAut.conj y • (PT : Subgroup ↥Y) : Subgroup ↥Y) = (PS : Subgroup ↥Y) := by
    have h1 := Sylow.coe_subgroup_smul (g := y) (P := PT)
    rw [hy] at h1
    exact h1.symm
  have hyiff' : ∀ z : ↥Y, z ∈ (PS : Subgroup ↥Y) ↔ y⁻¹ * z * y ∈ (PT : Subgroup ↥Y) := by
    intro z
    rw [← hcoe]
    exact mem_conj_smul_iff y _ z
  have hyiff : ∀ h : G23, h ∈ S ↔ ((y : G23)⁻¹ * h * y) ∈ S₀ := by
    intro h
    constructor
    · intro hh
      exact (hyiff' ⟨h, hSY hh⟩).1 hh
    · intro hh
      have hhY : (y : G23)⁻¹ * h * y ∈ Y := hS₀Y hh
      have hhY' : h ∈ Y := by
        have := Y.mul_mem (Y.mul_mem y.2 hhY) (Y.inv_mem y.2)
        simpa [mul_assoc] using this
      exact (hyiff' ⟨h, hhY'⟩).2 hh
  refine ⟨(y : G23) * g₀ * (y : G23)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 := hyiff h
    have e2 := hyiff ((y : G23) * g₀ * (y : G23)⁻¹ * h * ((y : G23) * g₀ * (y : G23)⁻¹)⁻¹)
    have e3 := hg₀iff ((y : G23)⁻¹ * h * y)
    have e4 : (y : G23)⁻¹ * ((y : G23) * g₀ * (y : G23)⁻¹ * h *
        ((y : G23) * g₀ * (y : G23)⁻¹)⁻¹) * y = g₀ * ((y : G23)⁻¹ * h * y) * g₀⁻¹ := by
      group
    rw [e4] at e2
    rw [e1, e2]
    exact e3
  ·
    set H : Subgroup G23 := Y ⊔ Y.map (MulAut.conj ((y : G23) * g₀ * (y : G23)⁻¹)).toMonoidHom
      with hH
    have hcomap : ⊤ ≤ H.comap (MulAut.conj (y : G23)).toMonoidHom := by
      rw [← hgen, Subgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · show (y : G23) * u i * (y : G23)⁻¹ ∈ H
        exact Subgroup.mem_sup_left (Y.mul_mem (Y.mul_mem y.2 (huY i)) (Y.inv_mem y.2))
      · show (y : G23) * (g₀ * u i * g₀⁻¹) * (y : G23)⁻¹ ∈ H
        refine Subgroup.mem_sup_right ⟨(y : G23) * u i * (y : G23)⁻¹,
          Y.mul_mem (Y.mul_mem y.2 (huY i)) (Y.inv_mem y.2), ?_⟩
        show (y : G23) * g₀ * (y : G23)⁻¹ * ((y : G23) * u i * (y : G23)⁻¹) *
          ((y : G23) * g₀ * (y : G23)⁻¹)⁻¹ = (y : G23) * (g₀ * u i * g₀⁻¹) * (y : G23)⁻¹
        group
    rw [eq_top_iff]
    intro z _
    have hz : (MulAut.conj (y : G23)).toMonoidHom ((y : G23)⁻¹ * z * y) ∈ H :=
      hcomap (Subgroup.mem_top _)
    have : (MulAut.conj (y : G23)).toMonoidHom ((y : G23)⁻¹ * z * y) = z := by
      simp [MulAut.conj_apply]
      group
    rw [this] at hz
    exact hz

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
