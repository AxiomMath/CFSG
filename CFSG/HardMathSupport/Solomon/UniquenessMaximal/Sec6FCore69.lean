module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DSylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem closure_elemAbelian {S : Set G} (h3 : ∀ s ∈ S, s ^ 3 = 1)
    (hc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : IsElemAbelian 3 (Subgroup.closure S) := by
  have h1 : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, x * s = s * x := by
    intro x hx s hs
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hc y hy s hs
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx => exact (show Commute x s from hx).inv_left
  have h2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs => exact h1 x hx s hs
    | one => simp
    | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    | inv y _ hy => exact (show Commute x y from hy).inv_right
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h3 s hs
  | one => simp
  | mul x y hx hy hx3 hy3 =>
    rw [(show Commute x y from h2 x hx y hy).mul_pow, hx3, hy3, one_mul]
  | inv x _ hx3 => rw [inv_pow, hx3, inv_one]

theorem comm_of_isMulCommutative {T : Subgroup G} (hT : IsMulCommutative T) :
    ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hT.is_comm.comm (⟨a, ha⟩ : T) ⟨b, hb⟩)

theorem mem_of_cube_centralizes {B : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hSC : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B) {c : G} (hc3 : c ^ 3 = 1)
    (hc : ∀ b ∈ B, c * b = b * c) : c ∈ B := by
  have hB := comm_of_isMulCommutative hBel.1
  have hE := closure_elemAbelian (S := (B : Set G) ∪ {c}) ?_ ?_
  · have hle : B ≤ Subgroup.closure ((B : Set G) ∪ {c}) := fun x hx =>
      Subgroup.subset_closure (Or.inl hx)
    have := hSC _ hE hle
    rw [← this]
    exact Subgroup.subset_closure (Or.inr rfl)
  · rintro s (hs | hs)
    · exact hBel.2 s hs
    · rw [Set.mem_singleton_iff.1 hs]; exact hc3
  · rintro s (hs | hs) t (ht | ht)
    · exact hB s hs t ht
    · rw [Set.mem_singleton_iff.1 ht]; exact (hc s hs).symm
    · rw [Set.mem_singleton_iff.1 hs]; exact hc t ht
    · rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht]

theorem card_abelian_le {R₁ Z T : Subgroup G} (hR₁c : Nat.card R₁ = 3 ^ 5)
    (hZR : Z ≤ R₁) (hZc : Nat.card Z = 3) (hZcent : ∀ z ∈ Z, ∀ r ∈ R₁, z * r = r * z)
    (hZcenter : ∀ z ∈ R₁, (∀ r ∈ R₁, z * r = r * z) → z ∈ Z)
    (hcomm : ∀ a ∈ R₁, ∀ c ∈ R₁, a * c * a⁻¹ * c⁻¹ ∈ Z)
    (hTR : T ≤ R₁) (hT : IsMulCommutative T) : Nat.card T ≤ 27 := by
  by_contra hlt
  push Not at hlt
  have hTc := comm_of_isMulCommutative hT
  have hdvd : ∀ K : Subgroup G, K ≤ R₁ → ∃ i ≤ 5, Nat.card K = 3 ^ i := fun K hK =>
    (Nat.dvd_prime_pow Nat.prime_three).1 (hR₁c ▸ Subgroup.card_dvd_of_le hK)
  by_cases hg : ∃ g ∈ R₁, g ∉ T
  · obtain ⟨g, hgR, hgT⟩ := hg
    set K := T ⊔ Subgroup.zpowers g with hK
    have hKR : K ≤ R₁ := sup_le hTR ((Subgroup.zpowers_le).2 hgR)
    have hgK : g ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
    have hTK : T ≤ K := le_sup_left
    have hlt2 : Nat.card T < Nat.card K := by
      by_contra h
      exact hgT ((Subgroup.eq_of_le_of_card_ge hTK (not_lt.1 h)) ▸ hgK)
    obtain ⟨i, hi, hTi⟩ := hdvd T hTR
    obtain ⟨j, hj, hKj⟩ := hdvd K hKR
    have hi4 : 3 < i := by
      by_contra h
      have : i ≤ 3 := not_lt.1 h
      have : 3 ^ i ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have hij : i < j := by
      rw [hTi, hKj] at hlt2
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt2
    have hj5 : j = 5 := by omega
    have hKR1 : K = R₁ :=
      Subgroup.eq_of_le_of_card_ge hKR (by rw [hR₁c, hKj, hj5])
    let φ : T →* Z :=
      { toFun := fun a => ⟨a * g * a⁻¹ * g⁻¹, hcomm _ (hTR a.2) _ hgR⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hz : (b : G) * g * (b : G)⁻¹ * g⁻¹ ∈ Z := hcomm _ (hTR b.2) _ hgR
          have hw : (a : G) * g * (a : G)⁻¹ * g⁻¹ ∈ Z := hcomm _ (hTR a.2) _ hgR
          have h1 := hZcent _ hz _ (hTR a.2)
          have h2 := hZcent _ hz _ (hZR hw)
          show (a * b : G) * g * ((a * b : G))⁻¹ * g⁻¹ =
            ((a : G) * g * (a : G)⁻¹ * g⁻¹) * ((b : G) * g * (b : G)⁻¹ * g⁻¹)
          calc (a * b : G) * g * ((a * b : G))⁻¹ * g⁻¹
              = (a : G) * ((b : G) * g * (b : G)⁻¹ * g⁻¹) * (g * (a : G)⁻¹ * g⁻¹) := by group
            _ = ((b : G) * g * (b : G)⁻¹ * g⁻¹) * (a : G) * (g * (a : G)⁻¹ * g⁻¹) := by rw [h1]
            _ = ((b : G) * g * (b : G)⁻¹ * g⁻¹) * ((a : G) * g * (a : G)⁻¹ * g⁻¹) := by group
            _ = _ := h2 }
    have hker : ∀ x ∈ φ.ker, ((x : T) : G) ∈ Z := by
      intro x hx
      have h1 : (x : G) * g * (x : G)⁻¹ * g⁻¹ = 1 := congrArg Subtype.val hx
      have hxg : (x : G) * g = g * x := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
      have hxT : T ≤ Subgroup.centralizer {(x : G)} := fun t ht => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hTc _ x.2 t ht
      have hxg' : Subgroup.zpowers g ≤ Subgroup.centralizer {(x : G)} :=
        Subgroup.zpowers_le.2 (by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.1 hh]
          exact hxg)
      refine hZcenter _ (hTR x.2) fun r hr => ?_
      rw [← hKR1] at hr
      have := sup_le hxT hxg' hr
      rw [Subgroup.mem_centralizer_iff] at this
      exact this _ rfl
    have hker' : φ.ker.map T.subtype ≤ Z := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have hc1 : Nat.card φ.ker ≤ 3 := by
      calc Nat.card φ.ker = Nat.card (φ.ker.map T.subtype) :=
            (Subgroup.card_map_of_injective T.subtype_injective).symm
        _ ≤ Nat.card Z := Subgroup.card_le_of_le hker'
        _ = 3 := hZc
    have hc2 : Nat.card φ.range ≤ 3 := (Subgroup.card_le_card_group _).trans hZc.le
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h
    have : Nat.card T ≤ 3 * 3 := h ▸ Nat.mul_le_mul hc1 hc2
    omega
  · push Not at hg
    have : R₁ ≤ Z := fun x hx =>
      hZcenter x hx fun r hr => hTc x (hg x hx) r (hg r hr)
    have := Subgroup.card_le_of_le this
    rw [hR₁c, hZc] at this
    omega

theorem core69 {B R₁ R₂ Z : Subgroup G}
    (hBc : Nat.card B = 81) (hBel : IsElemAbelian 3 B)
    (hSC : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B)
    (hR₁c : Nat.card R₁ = 3 ^ 5) (hR₁exp : ∀ g ∈ R₁, g ^ 3 = 1)
    (hZR : Z ≤ R₁) (hZc : Nat.card Z = 3) (hZcent : ∀ z ∈ Z, ∀ r ∈ R₁, z * r = r * z)
    (hZcenter : ∀ z ∈ R₁, (∀ r ∈ R₁, z * r = r * z) → z ∈ Z)
    (hcomm : ∀ a ∈ R₁, ∀ c ∈ R₁, a * c * a⁻¹ * c⁻¹ ∈ Z)
    (hR₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₂ = r₂ * r₁) (hR₁R₂ : R₁ ⊓ R₂ = Z)
    (hBR : ∀ b ∈ B, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, b = r₁ * r₂)
    (hBR₂ : B ≤ Subgroup.normalizer (R₂ : Set G))
    (hBcard : Nat.card ↥(B ⊓ R₂) = 3)
    (h66 : ∀ B₁ : Subgroup G, B₁ ≤ R₁ → B₁ ≤ Subgroup.normalizer (B : Set G) →
      Nat.card ↥⁅B₁, B⁆ ≤ 3 → (Subgroup.centralizer (B : Set G)).relIndex B₁ ≤ 3) : False := by
  have hB := comm_of_isMulCommutative hBel.1
  have hZR₂ : Z ≤ R₂ := (hR₁R₂.ge).trans inf_le_right
  have hR₂pos : 0 < Nat.card R₂ := Nat.card_pos
  have hZB : Z ≤ B := by
    intro z hz
    refine mem_of_cube_centralizes hBel hSC (hR₁exp z (hZR hz)) fun b hb => ?_
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := hBR b hb
    rw [← mul_assoc, hZcent z hz r1 hr1, mul_assoc, hR₂ z (hZR hz) r2 hr2, ← mul_assoc]
  set B₁ : Subgroup G := (B ⊔ R₂) ⊓ R₁ with hB₁
  have hB₁R₁ : B₁ ≤ R₁ := inf_le_right
  have hBR₂le : B ⊔ R₂ ≤ Subgroup.normalizer (R₂ : Set G) :=
    sup_le hBR₂ Subgroup.le_normalizer
  have hcardBR : Nat.card ↥(B ⊔ R₂) = 27 * Nat.card R₂ := by
    have h := card_sup_mul_card_inf hBR₂
    rw [sup_comm R₂ B, inf_comm R₂ B, hBcard, hBc] at h
    omega
  have hsupeq : B ⊔ R₂ = B₁ ⊔ R₂ := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      intro b hb
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := hBR b hb
      have hr1' : r1 ∈ B₁ := by
        refine ⟨?_, hr1⟩
        have : r1 = (r1 * r2) * r2⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.inv_mem _
          (Subgroup.mem_sup_right hr2))
      exact Subgroup.mul_mem_sup hr1' hr2
    · exact sup_le inf_le_left le_sup_right
  have hZB₁ : Z ≤ B₁ := le_inf (hZB.trans le_sup_left) hZR
  have hB₁R₂ : B₁ ⊓ R₂ = Z := by
    apply le_antisymm
    · calc B₁ ⊓ R₂ ≤ R₁ ⊓ R₂ := inf_le_inf_right _ hB₁R₁
        _ = Z := hR₁R₂
    · exact le_inf hZB₁ hZR₂
  have hB₁N : B₁ ≤ Subgroup.normalizer (R₂ : Set G) := inf_le_left.trans hBR₂le
  have hcardB₁ : Nat.card B₁ = 81 := by
    have h := card_sup_mul_card_inf hB₁N
    rw [sup_comm R₂ B₁, inf_comm R₂ B₁, ← hsupeq, hB₁R₂, hZc, hcardBR] at h
    have h' : Nat.card R₂ * 81 = Nat.card R₂ * Nat.card B₁ := by linarith
    exact (Nat.eq_of_mul_eq_mul_left hR₂pos h').symm
  have hcomm4 : ∀ y ∈ B₁, ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ Z := by
    intro y hy b hb
    have hyR := hB₁R₁ hy
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := hBR b hb
    have h : r2 * y⁻¹ = y⁻¹ * r2 := (hR₂ y⁻¹ (Subgroup.inv_mem _ hyR) r2 hr2).symm
    have e : y * (r1 * r2) * y⁻¹ * (r1 * r2)⁻¹ = y * r1 * y⁻¹ * r1⁻¹ := by
      calc y * (r1 * r2) * y⁻¹ * (r1 * r2)⁻¹
          = y * r1 * (r2 * y⁻¹) * r2⁻¹ * r1⁻¹ := by group
        _ = y * r1 * (y⁻¹ * r2) * r2⁻¹ * r1⁻¹ := by rw [h]
        _ = y * r1 * y⁻¹ * r1⁻¹ := by group
    rw [e]
    exact hcomm y hyR r1 hr1
  have hcommle : ⁅B₁, B⁆ ≤ Z := Subgroup.commutator_le.2 fun y hy b hb => hcomm4 y hy b hb
  have hconj : ∀ y ∈ B₁, ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    have : y * b * y⁻¹ = (y * b * y⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact Subgroup.mul_mem _ (hZB (hcomm4 y hy b hb)) hb
  have hB₁NB : B₁ ≤ Subgroup.normalizer (B : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj y hy h hh, fun hh => ?_⟩
    have := hconj y⁻¹ (Subgroup.inv_mem _ hy) _ hh
    simpa [mul_assoc] using this
  have hri := h66 B₁ hB₁R₁ hB₁NB ((Subgroup.card_le_of_le hcommle).trans hZc.le)
  have hCle : Subgroup.centralizer (B : Set G) ⊓ B₁ ≤ B := by
    rintro c ⟨hcC, hcB₁⟩
    refine mem_of_cube_centralizes hBel hSC (hR₁exp c (hB₁R₁ hcB₁)) fun b hb => ?_
    exact ((Subgroup.mem_centralizer_iff.1 hcC) b hb).symm
  set S : Subgroup G := B ⊓ B₁ with hSdef
  have hSB : S ≤ B := inf_le_left
  have hSR₁ : S ≤ R₁ := inf_le_right.trans hB₁R₁
  have hS27 : 27 ≤ Nat.card S := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (B : Set G)) (K := B₁)
    rw [hcardB₁] at h
    have h2 : 81 ≤ 3 * Nat.card ↥(Subgroup.centralizer (B : Set G) ⊓ B₁) := by
      rw [← h]; exact Nat.mul_le_mul_right _ hri
    have h3 : Nat.card ↥(Subgroup.centralizer (B : Set G) ⊓ B₁) ≤ Nat.card S :=
      Subgroup.card_le_of_le (le_inf hCle inf_le_right)
    omega
  have hScomm : IsMulCommutative S := ⟨⟨fun a b => Subtype.ext
    (hB a (hSB a.2) b (hSB b.2))⟩⟩
  have hSle := card_abelian_le hR₁c hZR hZc hZcent hZcenter hcomm hSR₁ hScomm
  have hS : Nat.card S = 27 := le_antisymm hSle hS27
  have hZS : Z ≤ S := le_inf hZB hZB₁
  have hCS : ∀ c ∈ R₁, (∀ s ∈ S, c * s = s * c) → c ∈ S := by
    intro c hc hcs
    by_contra hcS
    have hel := closure_elemAbelian (S := (S : Set G) ∪ {c}) ?_ ?_
    · have hTR : Subgroup.closure ((S : Set G) ∪ {c}) ≤ R₁ := by
        rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · exact hSR₁ hx
        · rw [Set.mem_singleton_iff.1 hx]; exact hc
      have hST : S ≤ Subgroup.closure ((S : Set G) ∪ {c}) := fun x hx =>
        Subgroup.subset_closure (Or.inl hx)
      have hcT : c ∈ Subgroup.closure ((S : Set G) ∪ {c}) := Subgroup.subset_closure (Or.inr rfl)
      have hlt : Nat.card S < Nat.card (Subgroup.closure ((S : Set G) ∪ {c})) := by
        by_contra h
        exact hcS ((Subgroup.eq_of_le_of_card_ge hST (not_lt.1 h)) ▸ hcT)
      have := card_abelian_le hR₁c hZR hZc hZcent hZcenter hcomm hTR hel.1
      omega
    · rintro s (hs | hs)
      · exact hR₁exp s (hSR₁ hs)
      · rw [Set.mem_singleton_iff.1 hs]; exact hR₁exp c hc
    · have hSc := comm_of_isMulCommutative hScomm
      rintro s (hs | hs) t (ht | ht)
      · exact hSc s hs t ht
      · rw [Set.mem_singleton_iff.1 ht]; exact (hcs s hs).symm
      · rw [Set.mem_singleton_iff.1 hs]; exact hcs t ht
      · rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht]
  have hBS : B ≤ S ⊔ R₂ := by
    intro b hb
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := hBR b hb
    have hr1S : r1 ∈ S := by
      refine hCS r1 hr1 fun s hs => ?_
      have h1 := hB s (hSB hs) _ hb
      have h2 := hR₂ s (hSR₁ hs) r2 hr2
      have h3 : s * r1 * r2 = r1 * s * r2 := by
        calc s * r1 * r2 = s * (r1 * r2) := by rw [mul_assoc]
          _ = (r1 * r2) * s := h1
          _ = r1 * (r2 * s) := by rw [mul_assoc]
          _ = r1 * (s * r2) := by rw [h2]
          _ = r1 * s * r2 := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    exact Subgroup.mul_mem_sup hr1S hr2
  have hSR₂ : S ⊓ R₂ = Z := by
    apply le_antisymm
    · calc S ⊓ R₂ ≤ R₁ ⊓ R₂ := inf_le_inf_right _ hSR₁
        _ = Z := hR₁R₂
    · exact le_inf hZS hZR₂
  have hSN : S ≤ Subgroup.normalizer (R₂ : Set G) := hSB.trans hBR₂
  have h := card_sup_mul_card_inf hSN
  rw [sup_comm R₂ S, inf_comm R₂ S, hSR₂, hZc, hS] at h
  have hle := Subgroup.card_le_of_le (sup_le hBS le_sup_right : B ⊔ R₂ ≤ S ⊔ R₂)
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
