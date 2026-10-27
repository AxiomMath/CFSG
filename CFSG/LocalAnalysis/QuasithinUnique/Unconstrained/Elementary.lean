module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_5

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Elementary

variable {G : Type*} [Group G]

theorem mem_closure_pair_of_involutions {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {w : G} (hw : w ∈ Subgroup.closure ({a, b} : Set G)) :
    w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  have hba : b * a = a * b := hab.symm
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, h1, h2, hba, mul_assoc]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hai, hbi, mul_inv_rev, hba]

theorem closure_pair_eq_of_mem {a b w : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hw : w ∈ Subgroup.closure ({a, b} : Set G)) (hw1 : w ≠ 1)
    (hwa : w ≠ a) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.closure ({a, w} : Set G) := by
  have hmem : a ∈ Subgroup.closure ({a, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwmem : w ∈ Subgroup.closure ({a, w} : Set G) := Subgroup.subset_closure (by simp)
  rcases mem_closure_pair_of_involutions ha hb hab hw with h | h | h | h
  · exact absurd h hw1
  · exact absurd h hwa
  · rw [h]
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | hv
      · exact hmem
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        have : v = a * (a * v) := by rw [← mul_assoc, ha, one_mul]
        rw [this, ← h]
        exact Subgroup.mul_mem _ hmem hwmem
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | hv
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        rw [h]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))

theorem card_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := by
  have hset : ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext w
    constructor
    · intro hw
      rcases mem_closure_pair_of_involutions ha hb hab hw with h | h | h | h <;> simp [h]
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  have h1 : (1 : G) ≠ a * b := by
    intro h
    apply hne
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [← h, one_mul]
  have h2 : a ≠ a * b := by
    intro h
    apply hb1
    calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
      _ = a⁻¹ * a := by rw [← h]
      _ = 1 := inv_mul_cancel a
  have h3 : b ≠ a * b := by
    intro h
    apply ha1
    calc a = (a * b) * b⁻¹ := by rw [mul_inv_cancel_right]
      _ = b * b⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel b
  have hcard : Nat.card (Subgroup.closure ({a, b} : Set G)) =
      Set.ncard ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) :=
    Nat.card_coe_set_eq _
  rw [hcard, hset]
  rw [Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, h1]),
    Set.ncard_insert_of_notMem (by simp [hne, h2]),
    Set.ncard_insert_of_notMem (by simp [h3]), Set.ncard_singleton]

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {w : G}
    (hw : w ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = w := by
  rw [Subgroup.sup_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    have h := hAB a₂ ha₂ b₁ hb₁
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have h := hAB a ha b hb
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h]

theorem mem_zpowers_involution {t w : G} (ht : t * t = 1) (hw : w ∈ Subgroup.zpowers t) :
    w = 1 ∨ w = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ht, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one]

theorem normalizer_zpowers_eq_centralizer {t : G} (ht : t * t = 1) :
    Subgroup.normalizer (Subgroup.zpowers t : Set G) = Subgroup.centralizer ({t} : Set G) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    rcases mem_zpowers_involution ht hmem with h | h
    · have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      rw [this]; simp
    · calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h]
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hcomm : Commute g t := hg
    have hk : ∀ k : ℤ, g * t ^ k = t ^ k * g := fun k => (hcomm.zpow_right k).eq
    refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : g * t ^ k * g⁻¹ = t ^ k := by rw [hk k]; group
      rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro hw
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : w = t ^ k := by
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = g⁻¹ * t ^ k * g := by rw [← hk']
          _ = g⁻¹ * (t ^ k * g) := by group
          _ = g⁻¹ * (g * t ^ k) := by rw [hk k]
          _ = t ^ k := by group
      rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card (CFSG.conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem inf_centralizer_ne_bot_of_normalizes [Finite G] {S A : Subgroup G} (hS : IsPGroup 2 S)
    (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G)) (hA1 : A ≠ ⊥) :
    A ⊓ Subgroup.centralizer (S : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  have hn : (A.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr hSA
  have hA1' : A.subgroupOf S ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro b hb
    have : (⟨b, hAS hb⟩ : S) ∈ A.subgroupOf S := Subgroup.mem_subgroupOf.mpr hb
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hA1'
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  obtain ⟨hyA, hyZ⟩ := y.2
  intro h'
  apply hy1
  have hyZ' : (y : S) ∈ Subgroup.center S := hyZ
  have hmem : ((y : S) : G) ∈ A ⊓ Subgroup.centralizer (S : Set G) :=
    ⟨Subgroup.mem_subgroupOf.mp hyA, Subgroup.mem_centralizer_iff.mpr fun g hg => by
      have := Subgroup.mem_center_iff.mp hyZ' ⟨g, hg⟩
      exact congrArg Subtype.val this⟩
  rw [h', Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

theorem inv_conj_mem_centerOf {S : Subgroup G} {y w : G}
    (hy : y ∈ Subgroup.normalizer (S : Set G)) (hw : w ∈ centerOf S) :
    y⁻¹ * w * y ∈ centerOf S := by
  have hyN := Subgroup.mem_normalizer_iff.mp hy
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun s hs' => ?_⟩
  · have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
    exact (hyN (y⁻¹ * w * y)).mpr (by rw [e]; exact hw.1)
  · have hs'' : y * s * y⁻¹ ∈ S := (hyN s).mp hs'
    have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hs''
    calc s * (y⁻¹ * w * y) = y⁻¹ * ((y * s * y⁻¹) * w) * y := by group
      _ = y⁻¹ * (w * (y * s * y⁻¹)) * y := by rw [hc]
      _ = y⁻¹ * w * y * s := by group

theorem exists_involution_center_decomp [Finite G] {S SC : Subgroup G} {zK x : G}
    (hS2 : IsPGroup 2 S) (hSC : SC ≤ S) (hSCn : S ≤ Subgroup.normalizer (SC : Set G))
    (hSC1 : SC ≠ ⊥) (hx : x ∈ Subgroup.normalizer (S : Set G))
    (hSCx : SC ⊓ CFSG.conjugate SC x = ⊥) (hzK2 : zK * zK = 1) (hzKZ : zK ∈ centerOf S)
    (hdec : centerOf S = Subgroup.zpowers zK ⊔ (centerOf S ⊓ SC)) :
    ∃ t ∈ SC, t ≠ 1 ∧ t * t = 1 ∧ t ∈ centerOf S ∧ centerOf S = Subgroup.closure {t, zK} := by
  have hZC : centerOf S ⊓ SC ≠ ⊥ := by
    intro hbot
    apply inf_centralizer_ne_bot_of_normalizes hS2 hSC hSCn hSC1
    rw [eq_bot_iff]
    intro c hc
    have : c ∈ centerOf S ⊓ SC := ⟨⟨hSC hc.1, hc.2⟩, hc.1⟩
    rw [hbot] at this
    exact this
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZC
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcomS : ∀ w ∈ centerOf S, ∀ s ∈ S, s * w = w * s := fun w hw s hs =>
    Subgroup.mem_centralizer_iff.mp hw.2 s hs
  have hcommAB : ∀ a ∈ Subgroup.zpowers zK, ∀ b ∈ centerOf S ⊓ SC, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_involution hzK2 ha with rfl | rfl
    · simp
    · exact (hcomS _ hzKZ b hb.1.1).symm
  have key : ∀ c ∈ centerOf S ⊓ SC, c ≠ 1 → ∃ b ∈ centerOf S ⊓ SC, x⁻¹ * c * x = zK * b := by
    intro c hc hc1
    have hcx : x⁻¹ * c * x ∈ centerOf S := inv_conj_mem_centerOf hx hc.1
    rw [hdec] at hcx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcommAB hcx
    rcases mem_zpowers_involution hzK2 ha with rfl | rfl
    · exfalso
      apply hc1
      have hmemC : x⁻¹ * c * x ∈ CFSG.conjugate SC x := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hc.2
      have hmemSC : x⁻¹ * c * x ∈ SC := by rw [← hab]; simpa using hb.2
      have : x⁻¹ * c * x ∈ SC ⊓ CFSG.conjugate SC x := ⟨hmemSC, hmemC⟩
      rw [hSCx, Subgroup.mem_bot] at this
      calc c = x * (x⁻¹ * c * x) * x⁻¹ := by group
        _ = 1 := by rw [this]; group
    · exact ⟨b, hb, hab.symm⟩
  have hmul : ∀ c₁ ∈ centerOf S ⊓ SC, c₁ ≠ 1 → ∀ c₂ ∈ centerOf S ⊓ SC, c₂ ≠ 1 → c₁ * c₂ = 1 := by
    intro c₁ hc₁ h₁ c₂ hc₂ h₂
    obtain ⟨b₁, hb₁, e₁⟩ := key c₁ hc₁ h₁
    obtain ⟨b₂, hb₂, e₂⟩ := key c₂ hc₂ h₂
    have hb₁z : b₁ * zK = zK * b₁ := hcomS zK hzKZ b₁ hb₁.1.1
    have hprod : x⁻¹ * (c₁ * c₂) * x = b₁ * b₂ := by
      calc x⁻¹ * (c₁ * c₂) * x = (x⁻¹ * c₁ * x) * (x⁻¹ * c₂ * x) := by group
        _ = (zK * b₁) * (zK * b₂) := by rw [e₁, e₂]
        _ = zK * (b₁ * zK) * b₂ := by group
        _ = zK * (zK * b₁) * b₂ := by rw [hb₁z]
        _ = (zK * zK) * b₁ * b₂ := by group
        _ = b₁ * b₂ := by rw [hzK2, one_mul]
    have hmemSC : x⁻¹ * (c₁ * c₂) * x ∈ SC := by
      rw [hprod]; exact SC.mul_mem hb₁.2 hb₂.2
    have hmemC : x⁻¹ * (c₁ * c₂) * x ∈ CFSG.conjugate SC x := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using SC.mul_mem hc₁.2 hc₂.2
    have hm : x⁻¹ * (c₁ * c₂) * x ∈ SC ⊓ CFSG.conjugate SC x := ⟨hmemSC, hmemC⟩
    rw [hSCx, Subgroup.mem_bot] at hm
    calc c₁ * c₂ = x * (x⁻¹ * (c₁ * c₂) * x) * x⁻¹ := by group
      _ = 1 := by rw [hm]; group
  have ht2 : t * t = 1 := hmul t ht ht1' t ht ht1'
  have hZCeq : ∀ c ∈ centerOf S ⊓ SC, c = 1 ∨ c = t := by
    intro c hc
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · right
      have h := hmul t ht ht1' c hc hc1
      calc c = t * (t * c) := by rw [← mul_assoc, ht2, one_mul]
        _ = t := by rw [h, mul_one]
  refine ⟨t, ht.2, ht1', ht2, ht.1, le_antisymm ?_ ?_⟩
  · intro w hw
    rw [hdec] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcommAB hw
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases mem_zpowers_involution hzK2 ha with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
    · rcases hZCeq b hb with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | hw
    · exact ht.1
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact hzKZ

end Elementary

end CFSG.QuasithinUnique
