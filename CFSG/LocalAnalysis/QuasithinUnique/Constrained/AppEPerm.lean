module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Act
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Klein

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sl2_isSimpleGroup {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hq : Fintype.card F = 2 ^ n) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hq
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup

omit [Finite G] in
theorem normal_le_or_eq_lin2 {L : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 2 ≤ n)
    (hlin : IsLin2Type L n) {W : Subgroup G} (hWL : W ≤ L)
    (hnorm : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) : W ≤ blockQ L ∨ W = L := by
  classical
  obtain ⟨F, hF, hFfin, hcard, α, hα, hαk, -⟩ := hlin
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := sl2_isSimpleGroup hn hcard
  set W' : Subgroup ↥L := W.subgroupOf L with hW'
  have hnormal : W'.Normal := ⟨fun w hw g => by
    rw [hW', Subgroup.mem_subgroupOf] at hw ⊢
    show ((g * w * g⁻¹ : ↥L) : G) ∈ W
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hnorm _ g.2 _ hw⟩
  have : (W'.map α).Normal := Subgroup.Normal.map hnormal α hα
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map α) with h | h
  · left
    intro w hw
    have hwL : w ∈ L := hWL hw
    have h1 : α ⟨w, hwL⟩ = 1 := by
      have : α ⟨w, hwL⟩ ∈ W'.map α := ⟨⟨w, hwL⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    have h2 : (⟨w, hwL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk]; exact h1
    exact (C56.mem_blockQ_iff _).2 h2
  · right
    refine le_antisymm hWL fun l hl => ?_
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    have hq : IsPGroup 2 (↥L ⧸ W') := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have : α g ∈ W'.map α := by rw [h]; trivial
      obtain ⟨w, hw, hwg⟩ := this
      have hp : (w⁻¹ * g) ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwg, inv_mul_cancel]
      rw [hαk] at hp
      obtain ⟨k, hk⟩ := hP2 ⟨w⁻¹ * g, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (w⁻¹ * g) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hq1 : (QuotientGroup.mk (w⁻¹ * g) : ↥L ⧸ W') = QuotientGroup.mk g := by
        rw [QuotientGroup.eq]
        have := hnormal.conj_mem w hw g⁻¹
        simpa [mul_assoc] using this
      rw [← hq1, ← QuotientGroup.mk_pow, hk']
      rfl
    have htop := hL.1 W' hq
    have : (⟨l, hl⟩ : ↥L) ∈ W' := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem mem_blockQ_of_comm_lin2 {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hlin : IsLin2Type L n)
    {a : G} (ha : a ∈ L) (h : ∀ y ∈ L, a * y * a⁻¹ * y⁻¹ ∈ blockQ L) : a ∈ blockQ L := by
  classical
  obtain ⟨F, hF, hFfin, hcard, α, hα, hαk, -⟩ := hlin
  have hcard' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard'
  have hc : α ⟨a, ha⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hα z
    have hy : y.1 ∈ L := y.2
    have h1 := h y hy
    have h2 : (⟨a * y * a⁻¹ * y⁻¹, L.mul_mem (L.mul_mem (L.mul_mem ha hy) (L.inv_mem ha)) (L.inv_mem hy)⟩ :
        ↥L) ∈ CFSG.pCore 2 ↥L := (C56.mem_blockQ_iff _).1 h1
    rw [← hαk, MonoidHom.mem_ker] at h2
    have h3 : α ⟨a, ha⟩ * α y * (α ⟨a, ha⟩)⁻¹ * (α y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    calc α y * α ⟨a, ha⟩ = (α ⟨a, ha⟩ * α y * (α ⟨a, ha⟩)⁻¹ * (α y)⁻¹) * (α y * α ⟨a, ha⟩) := by
          rw [h3, one_mul]
      _ = α ⟨a, ha⟩ * α y := by group
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo] at hc
  have h1 : α ⟨a, ha⟩ = 1 := Subgroup.mem_bot.1 hc
  have h2 : (⟨a, ha⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact h1
  exact (C56.mem_blockQ_iff _).2 h2

omit [Finite G] in
theorem three_dvd_card_lin2 {L : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n) :
    3 ∣ Nat.card ↥L := by
  obtain ⟨F, hF, hFfin, hcard, α, hα, -, -⟩ := hlin
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ∣ Nat.card ↥L :=
    Subgroup.card_dvd_of_surjective hα
  have hcard' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard'] at h1
  refine Dvd.dvd.trans ?_ h1
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have := Nat.sub_dvd_pow_sub_pow 4 1 n
  simpa using this

theorem conjR_cases_generic {L L₂ N : Subgroup G} (hcomm : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a)
    (hNK : N ≤ L ⊔ L₂) (hNn : L ⊔ L₂ ≤ normalizer (N : Set G))
    (hcard : Nat.card ↥N = Nat.card ↥L) (hcard₂ : Nat.card ↥L₂ = Nat.card ↥L)
    (h1 : ∀ W : Subgroup G, W ≤ L → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W ≤ blockQ L ∨ W = L)
    (h2 : ∀ W : Subgroup G, W ≤ L₂ → (∀ l ∈ L₂, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W ≤ blockQ L₂ ∨ W = L₂)
    (c1 : ∀ a ∈ L, (∀ y ∈ L, a * y * a⁻¹ * y⁻¹ ∈ blockQ L) → a ∈ blockQ L)
    (c2 : ∀ a ∈ L₂, (∀ y ∈ L₂, a * y * a⁻¹ * y⁻¹ ∈ blockQ L₂) → a ∈ blockQ L₂)
    (h3 : 3 ∣ Nat.card ↥L) : N = L ∨ N = L₂ := by
  classical
  have hLK : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂K : L₂ ≤ L ⊔ L₂ := le_sup_right
  have hnL : ∀ l ∈ L, ∀ w ∈ N ⊓ L, l * w * l⁻¹ ∈ N ⊓ L := by
    intro l hl w hw
    refine ⟨?_, L.mul_mem (L.mul_mem hl hw.2) (L.inv_mem hl)⟩
    exact (Subgroup.mem_normalizer_iff.1 (hNn (hLK hl)) w).1 hw.1
  have hnL₂ : ∀ l ∈ L₂, ∀ w ∈ N ⊓ L₂, l * w * l⁻¹ ∈ N ⊓ L₂ := by
    intro l hl w hw
    refine ⟨?_, L₂.mul_mem (L₂.mul_mem hl hw.2) (L₂.inv_mem hl)⟩
    exact (Subgroup.mem_normalizer_iff.1 (hNn (hL₂K hl)) w).1 hw.1
  have e1 := h1 (N ⊓ L) inf_le_right hnL
  have e2 := h2 (N ⊓ L₂) inf_le_right hnL₂
  rcases e1 with e1 | e1
  swap
  · left
    have hLN : L ≤ N := by rw [← e1]; exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hLN hcard.le).symm
  rcases e2 with e2 | e2
  swap
  · right
    have hLN : L₂ ≤ N := by rw [← e2]; exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hLN (by rw [hcard, hcard₂])).symm
  exfalso
  have hLN : L ≤ normalizer (L₂ : Set G) :=
    C5.le_normalizer_of_commute (fun u hu a ha => hcomm u hu a ha)
  have hpow : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    have hxK : x ∈ L ⊔ L₂ := hNK hx
    have hxK' : x ∈ ((L ⊔ L₂ : Subgroup G) : Set G) := hxK
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L L₂ hLN] at hxK'
    obtain ⟨a, ha, b, hb, hab⟩ := hxK'
    have hab' : a * b = x := hab
    have haQ : a ∈ blockQ L := by
      refine c1 a ha fun y hy => ?_
      have hby : b * y = y * b := (hcomm y hy b hb).symm
      have e : x * y * x⁻¹ * y⁻¹ = a * y * a⁻¹ * y⁻¹ := by
        rw [← hab']
        calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ * y⁻¹ := by group
          _ = a * (y * b) * b⁻¹ * a⁻¹ * y⁻¹ := by rw [hby]
          _ = a * y * a⁻¹ * y⁻¹ := by group
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have h3 : y * x⁻¹ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hNn (hLK hy)) x⁻¹).1 (N.inv_mem hx)
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [this]
        exact mul_mem hx h3
      have hmemL : a * y * a⁻¹ * y⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem ha hy) (L.inv_mem ha)) (L.inv_mem hy)
      rw [e] at hmem
      exact e1 ⟨hmem, hmemL⟩
    have hbQ : b ∈ blockQ L₂ := by
      refine c2 b hb fun y hy => ?_
      have hay : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a :=
        hcomm a ha _ (mul_mem (mul_mem hb hy) (inv_mem hb))
      have e : x * y * x⁻¹ * y⁻¹ = b * y * b⁻¹ * y⁻¹ := by
        rw [← hab']
        calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y * b⁻¹) * a⁻¹ * y⁻¹ := by group
          _ = (b * y * b⁻¹) * a * a⁻¹ * y⁻¹ := by rw [hay]
          _ = b * y * b⁻¹ * y⁻¹ := by group
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have h3 : y * x⁻¹ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hNn (hL₂K hy)) x⁻¹).1 (N.inv_mem hx)
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [this]
        exact mul_mem hx h3
      have hmemL : b * y * b⁻¹ * y⁻¹ ∈ L₂ :=
        L₂.mul_mem (L₂.mul_mem (L₂.mul_mem hb hy) (L₂.inv_mem hb)) (L₂.inv_mem hy)
      rw [e] at hmem
      exact e2 ⟨hmem, hmemL⟩
    obtain ⟨k₁, hk₁⟩ := C1.blockQ_isPGroup L ⟨a, haQ⟩
    obtain ⟨k₂, hk₂⟩ := C1.blockQ_isPGroup L₂ ⟨b, hbQ⟩
    have hk₁' : a ^ (2 ^ k₁) = 1 := congrArg Subtype.val hk₁
    have hk₂' : b ^ (2 ^ k₂) = 1 := congrArg Subtype.val hk₂
    refine ⟨k₁ + k₂, ?_⟩
    have hc : Commute a b := hcomm a ha b hb
    rw [← hab', hc.mul_pow, pow_add, pow_mul, pow_mul', hk₁', hk₂']
    simp
  have hN2 : IsPGroup 2 ↥N := by
    intro g
    obtain ⟨k, hk⟩ := hpow g.1 g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hN2
  rw [← hcard, hn] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end CFSG.QuasithinUnique.AppE
