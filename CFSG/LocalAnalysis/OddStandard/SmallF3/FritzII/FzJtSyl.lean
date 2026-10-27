module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36Zc
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

section Syl
variable [Finite G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

theorem fzJt_mem_normalizer_pair {y x : G} (h : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) :
    y ∈ Subgroup.normalizer ({x, x⁻¹} : Set G) := by
  have hxy : y * x * y⁻¹ ∈ ({x, x⁻¹} : Set G) := by
    rcases h with h | h <;> simp [h]
  have hxi : y * x⁻¹ * y⁻¹ ∈ ({x, x⁻¹} : Set G) := by
    have h2 : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [h2]; rcases h with h | h <;> simp [h]
  have hyi : y⁻¹ * x * y ∈ ({x, x⁻¹} : Set G) := by
    rcases h with h | h
    · left
      calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [h]
        _ = x := by group
    · right
      have h2 : y⁻¹ * x⁻¹ * y = x := by
        calc y⁻¹ * x⁻¹ * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [h]
          _ = x := by group
      calc y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y)⁻¹ := by group
        _ = x⁻¹ := by rw [h2]
  have hyii : y⁻¹ * x⁻¹ * y ∈ ({x, x⁻¹} : Set G) := by
    rcases h with h | h
    · right
      have h3 : y⁻¹ * x * y = x := by
        calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [h]
          _ = x := by group
      calc y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
        _ = x⁻¹ := by rw [h3]
    · left
      calc y⁻¹ * x⁻¹ * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [h]
        _ = x := by group
  rw [Subgroup.mem_set_normalizer_iff]
  intro z
  constructor
  · intro hz
    rcases (by simpa using hz : z = x ∨ z = x⁻¹) with rfl | rfl
    · exact hxy
    · exact hxi
  · intro hz
    have hz' : y * z * y⁻¹ = x ∨ y * z * y⁻¹ = x⁻¹ := by simpa using hz
    have hzt : y⁻¹ * (y * z * y⁻¹) * y ∈ ({x, x⁻¹} : Set G) := by
      rcases hz' with hzx | hzx
      · simpa [hzx] using hyi
      · simpa [hzx] using hyii
    rw [show z = y⁻¹ * (y * z * y⁻¹) * y by group]
    exact hzt

theorem fzR3_conj (hq3 : IsQ8Pair ((x₁ * x₂)⁻¹ * t) a₃₂) {a : G} (ha : a ∈ fzR3 t x₁ x₂ a₃₂) :
    (∀ p ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G), p * a * p⁻¹ = a ∨ p * a * p⁻¹ = a⁻¹) ∧
    (a = 1 ∨ a = ((x₁ * x₂)⁻¹ * t) ^ 2 ∨ ∃ p ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G),
      p * a * p⁻¹ = a⁻¹) := by
  have hr : a ∈ (q8Hom hq3).range := by rw [fz_q8_range hq3]; exact ha
  obtain ⟨q, rfl⟩ := hr
  have h1 : q8Hom hq3 (QuaternionGroup.a 1) = (x₁ * x₂)⁻¹ * t := by
    change zmod4Pow ((x₁ * x₂)⁻¹ * t) (1 : ZMod 4) = (x₁ * x₂)⁻¹ * t
    rw [zmod4Pow, show (1 : ZMod 4).val = 1 from rfl, pow_one]
  have h0 : q8Hom hq3 (QuaternionGroup.xa 0) = a₃₂ := by
    change a₃₂ * zmod4Pow ((x₁ * x₂)⁻¹ * t) (0 : ZMod 4) = a₃₂
    rw [zmod4Pow_zero, mul_one]
  have h2 : q8Hom hq3 (QuaternionGroup.a 2) = ((x₁ * x₂)⁻¹ * t) ^ 2 := by
    change zmod4Pow ((x₁ * x₂)⁻¹ * t) (2 : ZMod 4) = ((x₁ * x₂)⁻¹ * t) ^ 2
    rw [zmod4Pow, show (2 : ZMod 4).val = 2 from rfl]
  have D1 : ∀ p r : QuaternionGroup 2, p * r * p⁻¹ = r ∨ p * r * p⁻¹ = r⁻¹ := by decide
  have D2 : ∀ r : QuaternionGroup 2, r = 1 ∨ r = QuaternionGroup.a 2 ∨
      QuaternionGroup.a 1 * r * (QuaternionGroup.a 1)⁻¹ = r⁻¹ ∨
      QuaternionGroup.xa 0 * r * (QuaternionGroup.xa 0)⁻¹ = r⁻¹ := by decide
  have img : ∀ p r : QuaternionGroup 2, q8Hom hq3 p * q8Hom hq3 r * (q8Hom hq3 p)⁻¹ =
      q8Hom hq3 (p * r * p⁻¹) := fun p r => by rw [map_mul, map_mul, map_inv]
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    have key : ∀ e : QuaternionGroup 2, q8Hom hq3 e = p →
        p * q8Hom hq3 q * p⁻¹ = q8Hom hq3 q ∨ p * q8Hom hq3 q * p⁻¹ = (q8Hom hq3 q)⁻¹ := by
      intro e he
      have hi := img e q
      rw [he] at hi
      rw [hi]
      rcases D1 e q with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (map_inv _ _)
    rcases hp with hp | hp
    · exact key _ (h1.trans hp.symm)
    · exact key _ (h0.trans hp.symm)
  · rcases D2 q with h | h | h | h
    · left; rw [h, map_one]
    · right; left; rw [h, h2]
    · right; right; refine ⟨_, Set.mem_insert _ _, ?_⟩
      have hi := img (QuaternionGroup.a 1) q
      rw [h1, h, map_inv] at hi; exact hi
    · right; right; refine ⟨_, Set.mem_insert_of_mem _ rfl, ?_⟩
      have hi := img (QuaternionGroup.xa 0) q
      rw [h0, h, map_inv] at hi; exact hi

theorem fzl_extremal_R3 (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (hT : FzSylow T₂)
    {a : G} (ha : a ∈ fzR3 t x₁ x₂ a₃₂) (ha2 : a ^ 2 ≠ 1) :
    IsSylowOf 2 (T₂ ⊓ centralizer ({a} : Set G)) (centralizer ({a} : Set G)) := by
  have hS : IsSylowOf 2 T₂ ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [isSylowOf_iff]
    exact ⟨le_top, hT.1, by simpa using hT.2⟩
  have hR3T : fzR3 t x₁ x₂ a₃₂ ≤ T₂ := by
    rw [fzR3, hsh.gen, closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl <;> exact subset_closure (by simp)
  have haT : a ∈ T₂ := hR3T ha
  have hq3 := hsh.quat₃
  obtain ⟨hconj, htri⟩ := fzR3_conj hq3 ha
  have hcomm : ∀ u : G, Commute u ((x₁ * x₂)⁻¹ * t) → Commute u a₃₂ → u * a * u⁻¹ = a := by
    intro u h1 h2
    have hle : fzR3 t x₁ x₂ a₃₂ ≤ centralizer ({u} : Set G) := by
      rw [fzR3, closure_le]
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr h1.eq.symm
      · exact mem_centralizer_singleton_iff.mpr h2.eq.symm
    have := mem_centralizer_singleton_iff.mp (hle ha)
    rw [← this]; group
  have hN : T₂ ≤ Subgroup.normalizer ({a, a⁻¹} : Set G) := by
    rw [hsh.gen, closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fzJt_mem_normalizer_pair (Or.inl (hcomm _ (hsh.comm₁₃ _ (by simp) _ (by simp))
        (hsh.comm₁₃ _ (by simp) _ (by simp))))
    · exact fzJt_mem_normalizer_pair (Or.inl (hcomm _ (hsh.comm₁₃ _ (by simp) _ (by simp))
        (hsh.comm₁₃ _ (by simp) _ (by simp))))
    · exact fzJt_mem_normalizer_pair (Or.inl (hcomm _ (hsh.comm₂₃ _ (by simp) _ (by simp))
        (hsh.comm₂₃ _ (by simp) _ (by simp))))
    · exact fzJt_mem_normalizer_pair (Or.inl (hcomm _ (hsh.comm₂₃ _ (by simp) _ (by simp))
        (hsh.comm₂₃ _ (by simp) _ (by simp))))
    · exact fzJt_mem_normalizer_pair (hconj _ (Set.mem_insert _ _))
    · exact fzJt_mem_normalizer_pair (hconj _ (Set.mem_insert_of_mem _ rfl))
    · exact fzJt_mem_normalizer_pair (Or.inl (hcomm _ hsh.lam_comm₃.1 hsh.lam_comm₃.2))
  obtain ⟨b, hbmem, hb⟩ : ∃ b ∈ ({(x₁ * x₂)⁻¹ * t, a₃₂} : Set G), b * a * b⁻¹ = a⁻¹ := by
    rcases htri with h | h | h
    · exact absurd (by rw [h, one_pow]) ha2
    · exfalso; apply ha2
      rw [h, ← pow_mul]
      exact hq3.1
    · exact h
  have hbT : b ∈ T₂ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbmem
    rcases hbmem with rfl | rfl
    · exact hR3T (subset_closure (by simp))
    · exact hR3T (subset_closure (by simp))
  refine CFSG.ComponentClassification.GHarris.isSylowOf_of_card_le hS haT ?_
  intro g hgT
  set w := g⁻¹ * a * g
  set Cx : Subgroup G := T₂ ⊓ centralizer ({a} : Set G)
  set Cw : Subgroup G := T₂ ⊓ centralizer ({w} : Set G)
  have hCxle : Cx ≤ T₂ := inf_le_left
  have hCwle : Cw ≤ T₂ := inf_le_left
  have hw2 : w ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have h1 : g⁻¹ * a ^ 2 * g = 1 := by rw [← fzJt_conj_sq]; exact h
    calc a ^ 2 = g * (g⁻¹ * a ^ 2 * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hncw : ¬ T₂ ≤ Cw := by
    intro hle
    have hc : ∀ u ∈ T₂, u * w = w * u := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mp (mem_inf.mp (hle hu)).2
    exact hw2 (fzl_center_sq hsh hgT hc)
  have hmul : Cw.relIndex T₂ * Nat.card Cw = Nat.card T₂ := by
    have h := Subgroup.relIndex_mul_card (H := Cw) (K := T₂)
    rwa [inf_eq_left.mpr hCwle] at h
  have hrel : Cw.relIndex T₂ ≠ 1 := fun h1 => hncw (Subgroup.relIndex_eq_one.mp h1)
  have hrel0 : Cw.relIndex T₂ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact absurd hmul (by rw [hsh.card]; norm_num)
  have hi : Nat.card Cw ≤ 256 := by
    rw [hsh.card] at hmul
    have h2 : 2 ≤ Cw.relIndex T₂ := by omega
    have hb : Nat.card Cw * 2 ≤ 512 := by
      calc Nat.card Cw * 2 ≤ Nat.card Cw * Cw.relIndex T₂ := Nat.mul_le_mul_left _ h2
        _ = 2 ^ 9 := by rw [mul_comm]; exact hmul
        _ = 512 := by norm_num
    omega
  have hsurj : Function.Surjective
      (Sum.elim (fun c : Cx => (⟨c.1, hCxle c.2⟩ : T₂))
                (fun c : Cx => (⟨b * c.1, T₂.mul_mem hbT (hCxle c.2)⟩ : T₂))) := by
    rintro ⟨y, hy⟩
    have hy' : y * a * y⁻¹ ∈ ({a, a⁻¹} : Set G) :=
      (Subgroup.mem_set_normalizer_iff.mp (hN hy) a).mp (by simp)
    have hy'' : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a⁻¹ := by simpa using hy'
    rcases hy'' with hya | hya
    · have hyc : y ∈ centralizer ({a} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc y * a = (y * a * y⁻¹) * y := by group
            _ = a * y := by rw [hya])
      exact ⟨Sum.inl ⟨y, mem_inf.mpr ⟨hy, hyc⟩⟩, rfl⟩
    · have hinvb : b⁻¹ * a⁻¹ * b = a := by
        calc b⁻¹ * a⁻¹ * b = b⁻¹ * (b * a * b⁻¹) * b := by rw [hb]
          _ = a := by group
      have hc : b⁻¹ * y ∈ Cx := by
        refine mem_inf.mpr ⟨T₂.mul_mem (T₂.inv_mem hbT) hy, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc b⁻¹ * y * a = b⁻¹ * (y * a * y⁻¹) * y := by group
          _ = b⁻¹ * a⁻¹ * y := by rw [hya]
          _ = (b⁻¹ * a⁻¹ * b) * (b⁻¹ * y) := by group
          _ = a * (b⁻¹ * y) := by rw [hinvb]
      exact ⟨Sum.inr ⟨b⁻¹ * y, hc⟩, by
        apply Subtype.ext
        show b * (b⁻¹ * y) = y
        group⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_sum, hsh.card] at h
  have : 256 ≤ Nat.card Cx := by omega
  exact le_trans hi this

end Syl


theorem fzSylR3_holds : FzSylR3 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2
  refine fzl_extremal_R3 hset.shape hset.sylow ha ?_
  rw [ha2]; exact (orderOf_eq_prime_iff.mp (fz_orderOf_z hset.ctx.toCtx0)).2


end CFSG.OddStandard.SmallF3.FritzII
