module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma43
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

namespace EndB

theorem card_closure_pair_le {G : Type*} [Group G] [Finite G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : a * b = b * a) : Nat.card ↥(closure ({a, b} : Set G)) ≤ 4 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  have hsub : ((closure ({a, b} : Set G) : Subgroup G) : Set G) ⊆ {1, a, b, a * b} := by
    intro x hx
    rcases mem_closure_pair ha hb hab hx with h | h | h | h <;> simp [h]
  refine (Set.ncard_le_ncard hsub).trans ?_
  have h1 := Set.ncard_insert_le (1 : G) ({a, b, a * b} : Set G)
  have h2 := Set.ncard_insert_le a ({b, a * b} : Set G)
  have h3 := Set.ncard_insert_le b ({a * b} : Set G)
  have h4 := Set.ncard_singleton (a * b)
  omega

theorem card_zpowers_sup_le {G : Type*} [Group G] [Finite G] {a γ : G} (ha : a ^ 2 = 1)
    (haγ : a * γ = γ * a) (hγ : γ ^ 4 = 1) : Nat.card ↥(zpowers a ⊔ zpowers γ) ≤ 8 := by
  have hn : ∀ k ∈ zpowers γ, a * k * a⁻¹ ∈ zpowers γ := by
    intro k hk
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    rw [show a * γ ^ n * a⁻¹ = γ ^ n by
      rw [((Commute.zpow_right (show Commute a γ from haγ) n)).eq, mul_inv_cancel_right]]
    exact zpow_mem (mem_zpowers γ) n
  have hu2 : a ^ 2 ∈ zpowers γ := by rw [ha]; exact one_mem _
  have hγ4 : Nat.card ↥(zpowers γ) ≤ 4 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hγ)
  rw [sup_comm]
  by_cases haz : a ∈ zpowers γ
  · rw [sup_of_le_left (zpowers_le.mpr haz)]
    omega
  · rw [card_sup_zpowers hn hu2 haz]
    omega

theorem comm_conj_iff {G : Type*} [Group G] (d g a : G) :
    a * g = g * a ↔ (d⁻¹ * a * d) * (d⁻¹ * g * d) = (d⁻¹ * g * d) * (d⁻¹ * a * d) := by
  constructor
  · intro h
    calc d⁻¹ * a * d * (d⁻¹ * g * d) = d⁻¹ * (a * g) * d := by group
      _ = d⁻¹ * (g * a) * d := by rw [h]
      _ = d⁻¹ * g * d * (d⁻¹ * a * d) := by group
  · intro h
    calc a * g = d * (d⁻¹ * a * d * (d⁻¹ * g * d)) * d⁻¹ := by group
      _ = d * (d⁻¹ * g * d * (d⁻¹ * a * d)) * d⁻¹ := by rw [h]
      _ = g * a := by group

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

theorem card_centralizer_le_of_not_mem_T (hs : Setting46e t L p f S w z V i j)
    (hw2 : orderOf w = 2) (hT64 : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64)
    (hS128 : Nat.card S ≤ 128) {τ : X} (hτS : τ ∈ S)
    (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    Nat.card ↥(S ⊓ centralizer {τ}) ≤ 16 := by
  have hu : w ^ (orderOf w / 2) = w := by rw [hw2, show 2 / 2 = 1 from rfl, pow_one]
  have hτS1 : τ ∈ HarrisLit.S1 t L S :=
    hs.setup.mem_S1_iff.mpr ⟨hτS, by rw [hτ2]; exact one_mem _⟩
  have hτT1 : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) := by rw [hu]; exact hτT
  obtain ⟨hrel, -, hcent, -⟩ := hs.setup.lemma43c hτS1 hτT1 hτ2
  rw [hu] at hrel hcent
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hs.lemma45.isSylowOf_T.le.trans inf_le_left
  have h8 : Nat.card ↥((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {τ}) ≤ 8 := by
    rcases hcent with h | ⟨γ, hγT, hγ2, h⟩ <;> rw [h]
    · have hzt : t * z = z * t :=
        (mem_centralizer_singleton_iff.mp (hTt (mem_sup_left (mem_sup_right
          hs.setup.z_mem)))).symm
      exact (card_closure_pair_le ht2 hz2 hzt).trans (by norm_num)
    · have htγ : t * γ = γ * t := (mem_centralizer_singleton_iff.mp (hTt hγT)).symm
      have hγ4 : γ ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hγ2, hz2]
      exact card_zpowers_sup_le ht2 htγ hγ4
  have hS1 : HarrisLit.S1 t L S = S := by
    refine Subgroup.eq_of_le_of_card_ge hs.setup.S1_le ?_
    have h1 := Subgroup.relIndex_mul_card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (HarrisLit.S1 t L S)
    have hle : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ HarrisLit.S1 t L S := by
      have := hs.setup.T1_le_S1
      rwa [hu] at this
    rw [hrel, inf_of_le_left hle, hT64] at h1
    omega
  rw [hS1] at hrel
  have hrel' : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (S ⊓ centralizer {τ}) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hrel]; norm_num)).trans hrel.le
  have h1 := Subgroup.relIndex_mul_card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (S ⊓ centralizer {τ})
  rw [show (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ (S ⊓ centralizer {τ}) =
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {τ} by
    rw [← inf_assoc, inf_of_le_left hs.setup.T_le]] at h1
  rw [← h1]
  calc _ ≤ 2 * 8 := Nat.mul_le_mul hrel' h8
    _ = 16 := by norm_num

theorem false_of_conj_t_twoPart (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    (hw2 : orderOf w = 2) (hT64 : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64)
    (hS128 : Nat.card S ≤ 128) {c : X}
    (hβc : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({c * t * c⁻¹} : Set X))
    {R : Subgroup X} (hRle : R ≤ centralizer ({c * t * c⁻¹} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (hR2 : IsPGroup 2 R)
    (hRcard : Nat.card R = twoPart (centralizer ({c * t * c⁻¹} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
    (h16 : 16 < Nat.card R) (h64 : Nat.card R < 64) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set C := centralizer ({c * t * c⁻¹} : Set X) ⊓ centralizer {β} with hC
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβC : β ∈ C := mem_inf.mpr ⟨hβc, mem_centralizer_singleton_iff.mpr rfl⟩
  have hβR : β ∈ R := by
    by_contra hβR
    have hn : ∀ k ∈ R, β * k * β⁻¹ ∈ R := by
      intro k hk
      rw [show β * k = k * β from (mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hk)).2).symm,
        mul_inv_cancel_right]
      exact hk
    have hc := card_sup_zpowers hn (by rw [hβ2]; exact one_mem _) hβR
    obtain ⟨m, hm⟩ := hR2.exists_card_eq
    have hp : IsPGroup 2 ↥(R ⊔ zpowers β) := IsPGroup.of_card (n := m + 1) (by rw [hc, hm]; ring)
    have hle := card_le_twoPart hp (sup_le hRle (zpowers_le.mpr hβC))
    rw [hc, ← hRcard] at hle
    omega
  set H := centralizer ({t} : Set X) with hH
  have hR'H : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ H := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).1
    rw [hH, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * r * c * t = c⁻¹ * (r * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * r) * c := by rw [h1]
      _ = t * (c⁻¹ * r * c) := by group
  obtain ⟨S', hS', hR'S'⟩ := exists_isSylowOf_ge (hR2.map _) hR'H
  obtain ⟨k, hkH, hk⟩ := hs.sylow.exists_mem_conj hS'
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hkH
  set d := c * k with hd
  have hdS : ∀ r ∈ R, d⁻¹ * r * d ∈ S := by
    intro r hr
    have h1 : c⁻¹ * r * c ∈ S' := hR'S' ⟨r, hr, by simp⟩
    have h2 := (hk _).mp h1
    rwa [show k⁻¹ * (c⁻¹ * r * c) * k = d⁻¹ * r * d by rw [hd]; group] at h2
  have hdt : d⁻¹ * (c * t * c⁻¹) * d = t := by
    rw [hd, show (c * k)⁻¹ * (c * t * c⁻¹) * (c * k) = k⁻¹ * (t * k) by group, ← hkt]
    group
  set τ := d⁻¹ * β * d with hτ
  have hτS : τ ∈ S := hdS β hβR
  have hτ2 : τ ^ 2 = 1 := by
    rw [hτ, sq, show d⁻¹ * β * d * (d⁻¹ * β * d) = d⁻¹ * (β * β) * d by group, ← sq, hβ2]
    group
  have hconj : ∀ (g a b : X), a * g = g * a ↔ (d⁻¹ * a * d) * (d⁻¹ * g * d) =
      (d⁻¹ * g * d) * (d⁻¹ * a * d) := fun g a _ => comm_conj_iff d g a
  have hcardC : Nat.card ↥C = Nat.card ↥(H ⊓ centralizer {τ}) := by
    refine card_eq_of_conj_iff d fun x => ?_
    rw [hC, hH, mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, hconj _ x x, hdt,
      hconj β x x]
  by_cases hτT : τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  ·
    obtain ⟨m, hmH, hmX⟩ := hs.setup.exists_conj_mem_X hKF hτT hτ2
    have hTle : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ H ⊓ centralizer {m * τ * m⁻¹} := by
      refine le_inf (hs.lemma45.isSylowOf_T.le.trans inf_le_left) fun y hy => ?_
      have := mem_centralizer_iff.mp (mem_inf.mp (hs.setup.X_le_center_T hmX)).2 y hy
      exact mem_centralizer_singleton_iff.mpr this
    have hcard' : Nat.card ↥(H ⊓ centralizer {m * τ * m⁻¹}) =
        Nat.card ↥(H ⊓ centralizer {τ}) := by
      refine card_eq_of_conj_iff m fun x => ?_
      have hmt : m⁻¹ * t * m = t := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hmH, inv_mul_cancel_left]
      have hmτ : m⁻¹ * (m * τ * m⁻¹) * m = τ := by group
      rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, comm_conj_iff m t x,
        hmt, comm_conj_iff m (m * τ * m⁻¹) x, hmτ]
    have h1 := card_le_twoPart (hs.lemma45.isSylowOf_T.isPGroup) hTle
    rw [twoPart, hcard', ← hcardC, ← twoPart, hC, ← hRcard, hT64] at h1
    omega
  ·
    have h1 := card_centralizer_le_of_not_mem_T hs hw2 hT64 hS128 hτS hτT hτ2
    have hle : R.map (MulAut.conj d⁻¹).toMonoidHom ≤ S ⊓ centralizer {τ} := by
      rintro _ ⟨r, hr, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine mem_inf.mpr ⟨hdS r hr, mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).2
      exact (hconj β r r).mp h2
    have h2 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective] at h2
    omega

end EndB

end CFSG.ComponentClassification.HarrisLit
