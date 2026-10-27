module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathModel
public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Wreath

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Open
open Fin.NatCast
open scoped commutatorElement

namespace WMod

private def decEqWMod : DecidableEq WMod := WMod.equivProd.decidableEq
attribute [local instance 2000] decEqWMod
private instance : Fintype WMod := Fintype.ofEquiv (Fin 4 × Fin 4 × Fin 2) WMod.equivProd.symm
private instance (B : Subgroup WMod) : Finite B :=
  Finite.of_injective (Subtype.val : B → WMod) Subtype.val_injective

private def baseSub : Subgroup WMod where
  carrier := {m | m.i = 0}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change (g * h).i = 0
    rw [show (g * h).i = g.i + h.i from rfl, hg, hh, add_zero]
  inv_mem' := by
    intro g hg
    change (g⁻¹).i = 0
    rw [show (g⁻¹).i = g.i from rfl, hg]

private theorem closure_pair_eq_baseSub : closure ({wx₁, wx₂} : Set WMod) = baseSub := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> rfl
  · intro m hm
    rw [WMod.eq_pow_mul m]
    have hi : m.i.val = 0 := by rw [hm]; rfl
    rw [hi, pow_zero, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

private def baseSubEquiv : baseSub ≃ Fin 4 × Fin 4 where
  toFun m := (m.1.a, m.1.b)
  invFun p := ⟨⟨p.1, p.2, 0⟩, rfl⟩
  left_inv m := by
    apply Subtype.ext
    obtain ⟨⟨a, b, i⟩, hi⟩ := m
    have hi' : i = 0 := hi
    subst hi'
    rfl
  right_inv p := by cases p; rfl

private theorem card_baseSub : Nat.card baseSub = 16 := by
  rw [Nat.card_congr baseSubEquiv]
  simp [Nat.card_eq_fintype_card]

private def diagSub : Subgroup WMod where
  carrier := {m | m.a = m.b ∧ m.i = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨a, b, i⟩ := g
    obtain ⟨c, d, k⟩ := h
    obtain ⟨ha, hi⟩ := hg
    obtain ⟨hb, hk⟩ := hh
    decide +revert
  inv_mem' := by
    intro g hg
    obtain ⟨a, b, i⟩ := g
    obtain ⟨ha, hi⟩ := hg
    decide +revert

private theorem center_cond (a b : Fin 4) (i : Fin 2) :
    (⟨a, b, i⟩ : WMod) * wx₁ = wx₁ * ⟨a, b, i⟩ →
    (⟨a, b, i⟩ : WMod) * wlam = wlam * ⟨a, b, i⟩ → a = b ∧ i = 0 := by
  decide +revert

private theorem pow_wx₁wx₂_fin (k : Fin 4) :
    (wx₁ * wx₂) ^ k.val = (⟨k, k, 0⟩ : WMod) := by
  fin_cases k <;> decide

private theorem center_eq_diagSub : center WMod = diagSub := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, b, i⟩ := m
    have h1 : (⟨a, b, i⟩ : WMod) * wx₁ = wx₁ * ⟨a, b, i⟩ :=
      (Subgroup.mem_center_iff.mp hm wx₁).symm
    have h2 : (⟨a, b, i⟩ : WMod) * wlam = wlam * ⟨a, b, i⟩ :=
      (Subgroup.mem_center_iff.mp hm wlam).symm
    exact center_cond a b i h1 h2
  · intro m hm
    obtain ⟨a, b, i⟩ := m
    obtain ⟨ha, hi⟩ := hm
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, d, k⟩ := g
    decide +revert

private def diagEquiv : diagSub ≃ Fin 4 where
  toFun m := m.1.a
  invFun a := ⟨⟨a, a, 0⟩, ⟨rfl, rfl⟩⟩
  left_inv m := by
    apply Subtype.ext
    obtain ⟨⟨a, b, i⟩, ha, hi⟩ := m
    have ha' : a = b := ha
    have hi' : i = 0 := hi
    subst ha'
    subst hi'
    rfl
  right_inv a := rfl

private theorem diagSub_eq_zpowers : diagSub = zpowers (wx₁ * wx₂) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, b, i⟩ := m
    obtain ⟨ha, hi⟩ := hm
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(b.val : ℤ), ?_⟩
    rw [zpow_natCast, pow_wx₁wx₂_fin]
    have ha' : a = b := ha
    have hi' : i = 0 := hi
    rw [← ha', hi']
  · rw [Subgroup.zpowers_le]
    exact ⟨rfl, rfl⟩

private theorem center_eq_zpowers : center WMod = zpowers (wx₁ * wx₂) := by
  rw [center_eq_diagSub, diagSub_eq_zpowers]

private theorem card_zpowers_wx₁wx₂ : Nat.card (zpowers (wx₁ * wx₂)) = 4 := by
  rw [← diagSub_eq_zpowers, Nat.card_congr diagEquiv]
  simp [Nat.card_eq_fintype_card]

private def antiSub : Subgroup WMod where
  carrier := {m | m.a = -m.b ∧ m.i = 0}
  one_mem' := by decide
  mul_mem' := by
    intro g h hg hh
    obtain ⟨a, b, i⟩ := g
    obtain ⟨c, d, k⟩ := h
    obtain ⟨ha, hi⟩ := hg
    obtain ⟨hb, hk⟩ := hh
    decide +revert
  inv_mem' := by
    intro g hg
    obtain ⟨a, b, i⟩ := g
    obtain ⟨ha, hi⟩ := hg
    decide +revert

private theorem pow_anti_fin (k : Fin 4) :
    (wx₁⁻¹ * wx₂) ^ k.val = (⟨-k, k, 0⟩ : WMod) := by
  fin_cases k <;> decide

private theorem anti_pow_four : (wx₁⁻¹ * wx₂) ^ 4 = 1 := by decide

private theorem pow_anti (n : ℕ) :
    (wx₁⁻¹ * wx₂) ^ n = (⟨-(n : Fin 4), (n : Fin 4), 0⟩ : WMod) := by
  rw [← CFSG.GF2Type.Aschbacher1976Full.Z4Q8.pow_mod_four anti_pow_four n]
  exact pow_anti_fin (n : Fin 4)

private theorem antiSub_eq_zpowers : antiSub = zpowers (wx₁⁻¹ * wx₂) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, b, i⟩ := m
    obtain ⟨ha, hi⟩ := hm
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(b.val : ℤ), ?_⟩
    rw [zpow_natCast, pow_anti_fin]
    have ha' : a = -b := ha
    have hi' : i = 0 := hi
    rw [← ha', hi']
  · rw [Subgroup.zpowers_le]
    exact ⟨rfl, rfl⟩

private theorem mem_antiSub {m : WMod} : m ∈ antiSub ↔ m.a = -m.b ∧ m.i = 0 := Iff.rfl

private theorem commutator_mem_anti (g₁ g₂ : WMod) : ⁅g₁, g₂⁆ ∈ antiSub := by
  obtain ⟨a, b, i⟩ := g₁
  obtain ⟨c, d, k⟩ := g₂
  rw [commutatorElement_def, mem_antiSub]
  decide +revert

private theorem commutator_top_eq_antiSub : ⁅(⊤ : Subgroup WMod), ⊤⁆ = antiSub := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact commutator_mem_anti g₁ g₂
  · rw [antiSub_eq_zpowers, Subgroup.zpowers_le]
    have hg : wx₁⁻¹ * wx₂ = ⁅wlam, wx₁⁆ := by decide
    rw [hg]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem card_zpowers_anti : Nat.card (zpowers (wx₁⁻¹ * wx₂)) = 4 := by
  rw [Nat.card_zpowers]
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  constructor
  · decide
  · intro m hm4 hm0
    rw [pow_anti]
    intro h
    have h' : (⟨-(m : Fin 4), (m : Fin 4), 0⟩ : WMod) = (⟨0, 0, 0⟩ : WMod) := by
      rw [show (1 : WMod) = ⟨0, 0, 0⟩ from rfl] at h
      exact h
    have hb : (m : Fin 4) = 0 := by simpa using congrArg WMod.b h'
    have hdvd : 4 ∣ m := Fin.natCast_eq_zero.mp hb
    have := Nat.le_of_dvd hm0 hdvd
    omega

private theorem cent_1_inj (p q c d : Fin 4) (k : Fin 2) (c' d' : Fin 4) (k' : Fin 2) :
    (⟨c, d, k⟩ : WMod) * (⟨p, q, 1⟩ : WMod) = (⟨p, q, 1⟩ : WMod) * ⟨c, d, k⟩ →
    (⟨c', d', k'⟩ : WMod) * (⟨p, q, 1⟩ : WMod) = (⟨p, q, 1⟩ : WMod) * ⟨c', d', k'⟩ →
    c = c' → k = k' → d = d' := by
  decide +revert

private theorem card_centralizer_of_cent_1 (p q : Fin 4) :
    Nat.card (Subgroup.centralizer ({(⟨p, q, 1⟩ : WMod)} : Set WMod)) ≤ 8 := by
  let f : Subgroup.centralizer ({(⟨p, q, 1⟩ : WMod)} : Set WMod) → Fin 4 × Fin 2 :=
    fun x => (x.1.a, x.1.i)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨⟨c, d, k⟩, hx⟩ := x
    obtain ⟨⟨c', d', k'⟩, hy⟩ := y
    have h1 : c = c' := congrArg Prod.fst hxy
    have h2 : k = k' := congrArg Prod.snd hxy
    have hx' : (⟨c, d, k⟩ : WMod) * (⟨p, q, 1⟩ : WMod) = (⟨p, q, 1⟩ : WMod) * ⟨c, d, k⟩ :=
      ((Subgroup.mem_centralizer_iff.mp hx) (⟨p, q, 1⟩ : WMod) (by simp)).symm
    have hy' : (⟨c', d', k'⟩ : WMod) * (⟨p, q, 1⟩ : WMod) =
        (⟨p, q, 1⟩ : WMod) * ⟨c', d', k'⟩ :=
      ((Subgroup.mem_centralizer_iff.mp hy) (⟨p, q, 1⟩ : WMod) (by simp)).symm
    have h3 : d = d' := cent_1_inj p q c d k c' d' k' hx' hy' h1 h2
    apply Subtype.ext
    change (⟨c, d, k⟩ : WMod) = ⟨c', d', k'⟩
    rw [h1, h2, h3]
  calc Nat.card (Subgroup.centralizer ({(⟨p, q, 1⟩ : WMod)} : Set WMod))
      ≤ Nat.card (Fin 4 × Fin 2) := Nat.card_le_card_of_injective f hf
    _ = 8 := by simp [Nat.card_eq_fintype_card]

private theorem card_centralizer_of_i_one (m : WMod) (hm : m.i = 1) :
    Nat.card (Subgroup.centralizer ({m} : Set WMod)) ≤ 8 := by
  obtain ⟨p, q, i⟩ := m
  have hi : i = 1 := hm
  rw [hi]
  exact card_centralizer_of_cent_1 p q

private theorem abelian_card_le (B : Subgroup WMod) [IsMulCommutative B] :
    Nat.card B ≤ 16 := by
  by_cases hB : B ≤ baseSub
  · calc Nat.card B ≤ Nat.card baseSub := Subgroup.card_le_of_le hB
      _ = 16 := card_baseSub
  · have hB' : ¬ (B : Set WMod) ⊆ (baseSub : Set WMod) := hB
    obtain ⟨m, hmB, hm⟩ := Set.not_subset.mp hB'
    have hmi : m.i = 1 := Fin.eq_one_of_ne_zero m.i hm
    have hle : B ≤ Subgroup.centralizer ({m} : Set WMod) :=
      (Subgroup.le_centralizer B).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmB))
    calc Nat.card B ≤ Nat.card (Subgroup.centralizer ({m} : Set WMod)) :=
          Subgroup.card_le_of_le hle
      _ ≤ 8 := card_centralizer_of_i_one m hmi
      _ ≤ 16 := by norm_num

private theorem abelian_eq_baseSub (B : Subgroup WMod) [IsMulCommutative B]
    (hcard : Nat.card B = 16) : B = baseSub := by
  have hle : B ≤ baseSub := by
    by_contra hB
    have hB' : ¬ (B : Set WMod) ⊆ (baseSub : Set WMod) := hB
    obtain ⟨m, hmB, hm⟩ := Set.not_subset.mp hB'
    have hmi : m.i = 1 := Fin.eq_one_of_ne_zero m.i hm
    have hle' : B ≤ Subgroup.centralizer ({m} : Set WMod) :=
      (Subgroup.le_centralizer B).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmB))
    have : Nat.card B ≤ 8 := (Subgroup.card_le_of_le hle').trans (card_centralizer_of_i_one m hmi)
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_baseSub, hcard]))

end WMod

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

private theorem baseGrp_eq_map_baseSub (φ : WMod →* G) (h1 : φ WMod.wx₁ = x₁)
    (h2 : φ WMod.wx₂ = x₂) : baseGrp x₁ x₂ = WMod.baseSub.map φ := by
  rw [baseGrp, ← WMod.closure_pair_eq_baseSub, MonoidHom.map_closure, Set.image_pair, h1, h2]

private theorem comap_centralizer_map (φ : WMod →* G) (hinj : Function.Injective φ)
    (H : Subgroup WMod) :
    (Subgroup.centralizer ((H.map φ : Subgroup G) : Set G)).comap φ =
      Subgroup.centralizer (H : Set WMod) := by
  ext m
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    apply hinj
    rw [map_mul, map_mul]
    exact h (φ k) (Subgroup.mem_map_of_mem φ hk)
  · intro h g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← map_mul, ← map_mul, h k hk]

private theorem eq_of_comap_eq {E F : Subgroup G} (φ : WMod →* G)
    (hE : E ≤ φ.range) (hF : F ≤ φ.range) (h : E.comap φ = F.comap φ) : E = F := by
  rw [← Subgroup.map_comap_eq_self hE, h, Subgroup.map_comap_eq_self hF]

private theorem isMulCommutative_comap (φ : WMod →* G) (hinj : Function.Injective φ)
    (A : Subgroup G) (h : IsMulCommutative A) : IsMulCommutative (A.comap φ) := by
  rw [isMulCommutative_iff] at h ⊢
  intro x y
  apply Subtype.ext
  show x.1 * y.1 = y.1 * x.1
  apply hinj
  rw [map_mul, map_mul]
  exact congrArg Subtype.val (h ⟨φ x.1, x.2⟩ ⟨φ y.1, y.2⟩)

private theorem card_comap_eq (φ : WMod →* G) (hinj : Function.Injective φ) (A : Subgroup G)
    (hA' : A ≤ φ.range) : Nat.card A = Nat.card (A.comap φ) := by
  conv_lhs => rw [← Subgroup.map_comap_eq_self hA']
  rw [Subgroup.card_map_of_injective (K := A.comap φ) (f := φ) hinj]

private theorem card_le_sixteen_of_le (φ : WMod →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = wreathGrp x₁ x₂ lam) (A : Subgroup G)
    (hA : A ≤ wreathGrp x₁ x₂ lam) (hcomm : IsMulCommutative A) : Nat.card A ≤ 16 := by
  have hA' : A ≤ φ.range := by rw [hrange]; exact hA
  have hBcomm : IsMulCommutative (A.comap φ) := isMulCommutative_comap φ hinj A hcomm
  rw [card_comap_eq φ hinj A hA']
  exact WMod.abelian_card_le (A.comap φ)

private theorem eq_baseGrp_of_card (φ : WMod →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = wreathGrp x₁ x₂ lam) (h1 : φ WMod.wx₁ = x₁) (h2 : φ WMod.wx₂ = x₂)
    (A : Subgroup G) (hA : A ≤ wreathGrp x₁ x₂ lam) (hcomm : IsMulCommutative A)
    (hcard : Nat.card A = 16) : A = baseGrp x₁ x₂ := by
  have hA' : A ≤ φ.range := by rw [hrange]; exact hA
  have hBcomm : IsMulCommutative (A.comap φ) := isMulCommutative_comap φ hinj A hcomm
  have hcard' : Nat.card (A.comap φ) = 16 := by
    rw [← card_comap_eq φ hinj A hA', hcard]
  have hB : A.comap φ = WMod.baseSub := WMod.abelian_eq_baseSub (A.comap φ) hcard'
  rw [← Subgroup.map_comap_eq_self hA', hB, ← baseGrp_eq_map_baseSub φ h1 h2]

theorem WreathRel.baseGrp_eq (h : WreathRel x₁ x₂ lam) :
    IsMulCommutative (baseGrp x₁ x₂) ∧ baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ ∧
      Nat.card (baseGrp x₁ x₂) = 16 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  have hpair : ({x₁, x₂} : Set G).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact h.comm
    · exact h.comm.symm
    · exact absurd rfl hab
  refine ⟨?_, ?_, ?_⟩
  · rw [baseGrp]
    exact isMulCommutative_closure hpair
  · rw [baseGrp, Subgroup.zpowers_eq_closure x₁, Subgroup.zpowers_eq_closure x₂,
      ← Subgroup.closure_union]
    rfl
  · rw [baseGrp_eq_map_baseSub φ h1 h2,
      Subgroup.card_map_of_injective (K := WMod.baseSub) (f := φ) hinj, WMod.card_baseSub]

theorem WreathRel.center_eq (h : WreathRel x₁ x₂ lam) :
    wreathGrp x₁ x₂ lam ⊓ centralizer (wreathGrp x₁ x₂ lam : Set G) = zpowers (x₁ * x₂) ∧
      Nat.card (zpowers (x₁ * x₂)) = 4 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  have hzp : (zpowers (WMod.wx₁ * WMod.wx₂)).map φ = zpowers (x₁ * x₂) := by
    rw [MonoidHom.map_zpowers, map_mul, h1, h2]
  constructor
  · apply eq_of_comap_eq φ
    · rw [hrange]; exact inf_le_left
    · rw [← hzp]; exact Subgroup.map_le_range φ _
    · have hcr : (wreathGrp x₁ x₂ lam).comap φ = ⊤ := by
        rw [← hrange]
        ext m
        simp [Subgroup.mem_comap]
      rw [Subgroup.comap_inf, hcr, ← hrange, ← Subgroup.map_top (f := φ),
        comap_centralizer_map φ hinj (⊤ : Subgroup WMod), Subgroup.coe_top,
        Subgroup.centralizer_univ, WMod.center_eq_zpowers, ← hzp,
        Subgroup.comap_map_eq_self_of_injective hinj]
      simp
  · rw [← hzp, Subgroup.card_map_of_injective (f := φ) hinj]
    exact WMod.card_zpowers_wx₁wx₂

theorem WreathRel.commutator_eq (h : WreathRel x₁ x₂ lam) :
    ⁅wreathGrp x₁ x₂ lam, wreathGrp x₁ x₂ lam⁆ = zpowers (x₁⁻¹ * x₂) ∧
      Nat.card (zpowers (x₁⁻¹ * x₂)) = 4 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  have hzp : (zpowers (WMod.wx₁⁻¹ * WMod.wx₂)).map φ = zpowers (x₁⁻¹ * x₂) := by
    rw [MonoidHom.map_zpowers, map_mul, map_inv, h1, h2]
  constructor
  · rw [← hrange, ← Subgroup.map_top (f := φ),
      ← Subgroup.map_commutator (H₁ := (⊤ : Subgroup WMod)) (H₂ := ⊤) (f := φ),
      WMod.commutator_top_eq_antiSub, WMod.antiSub_eq_zpowers, hzp]
  · rw [← hzp, Subgroup.card_map_of_injective (f := φ) hinj]
    exact WMod.card_zpowers_anti

theorem WreathRel.card_le_sixteen (h : WreathRel x₁ x₂ lam) {A : Subgroup G}
    (hA : A ≤ wreathGrp x₁ x₂ lam) (hcomm : IsMulCommutative A) : Nat.card A ≤ 16 := by
  obtain ⟨φ, hinj, hrange, -, -, -⟩ := h.exists_embedding
  exact card_le_sixteen_of_le φ hinj hrange A hA hcomm

theorem WreathRel.eq_baseGrp_of_card_sixteen (h : WreathRel x₁ x₂ lam) {A : Subgroup G}
    (hA : A ≤ wreathGrp x₁ x₂ lam) (hcomm : IsMulCommutative A) (hcard : Nat.card A = 16) :
    A = baseGrp x₁ x₂ := by
  obtain ⟨φ, hinj, hrange, h1, h2, -⟩ := h.exists_embedding
  exact eq_baseGrp_of_card φ hinj hrange h1 h2 A hA hcomm hcard

end CFSG.OddStandard.SmallF3.HarrisU33
