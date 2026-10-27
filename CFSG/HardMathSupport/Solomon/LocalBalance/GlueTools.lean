module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]


theorem pRank_eq_of_card [Finite G] {p k : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k := by
  have hbdd : BddAbove {k' | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k'} := by
    refine ⟨k, fun k' ⟨F, hFE, _, hF⟩ => ?_⟩
    have hd : p ^ k' ∣ p ^ k := hF ▸ hcard ▸ Subgroup.card_dvd_of_le hFE
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd
  refine le_antisymm (csSup_le' fun k' ⟨F, hFE, _, hF⟩ => ?_) (le_csSup hbdd ⟨E, le_rfl, hE, hcard⟩)
  have hd : p ^ k' ∣ p ^ k := hF ▸ hcard ▸ Subgroup.card_dvd_of_le hFE
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd

theorem commutator_le_gLAPPrimeCore_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {X L L' : Subgroup G}
    (hL : GLAPComponent p X L) (hL' : GLAPComponent p X L') (hne : L ≠ L') :
    ⁅L, L'⁆ ≤ GLAPPrimeCoreOf p X := by
  have _ := hp
  have hbar : barX p X L ≠ barX p X L' := fun h => hne (glaPComponent_uniqueAux hL hL' h)
  have hcomm : ⁅barX p X L, barX p X L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 hL'.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  refine Subgroup.commutator_le.2 fun ℓ hℓ u hu => ?_
  have hℓX : ℓ ∈ X := hL.1 hℓ
  have huX : u ∈ X := hL'.1 hu
  have hℓbar : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨ℓ, hℓX⟩ ∈ barX p X L :=
    ⟨⟨ℓ, hℓX⟩, (Subgroup.mem_subgroupOf).2 hℓ, rfl⟩
  have hubar : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨u, huX⟩ ∈ barX p X L' :=
    ⟨⟨u, huX⟩, (Subgroup.mem_subgroupOf).2 hu, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (hcen hℓbar) _ hubar
  rw [commutatorElement_def]
  have hxX : ℓ * u * ℓ⁻¹ * u⁻¹ ∈ X :=
    by exact X.mul_mem (X.mul_mem (X.mul_mem hℓX huX) (X.inv_mem hℓX)) (X.inv_mem huX)
  refine ⟨⟨_, hxX⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
  have h2 : (⟨ℓ * u * ℓ⁻¹ * u⁻¹, hxX⟩ : ↥X) =
      ⟨ℓ, hℓX⟩ * ⟨u, huX⟩ * ⟨ℓ, hℓX⟩⁻¹ * ⟨u, huX⟩⁻¹ := rfl
  show QuotientGroup.mk' (GLAPPrimeCore p ↥X) _ = 1
  rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv]
  set a := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨ℓ, hℓX⟩
  set b := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨u, huX⟩
  rw [← h1]
  group

theorem mem_oPrimePOf_of_forall_comm [Finite G] {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hx : x ∈ L) (hc : ∀ y ∈ L, x * y = y * x) : x ∈ oPrimePOf p L := by
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨x, hx⟩ ∈ CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L)
  refine mem_pCore_of_forall_comm_aux hp fun w => ?_
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) w
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc ℓ ℓ.2).symm

theorem gLBConj_centralizer_singleton_of_commute {b g : G} (h : g * b = b * g) :
    GLBConj g (Subgroup.centralizer ({b} : Set G)) = Subgroup.centralizer ({b} : Set G) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have h1 : b * (g * y * g⁻¹) = g * (b * y) * g⁻¹ := by
    calc b * (g * y * g⁻¹) = (b * g) * y * g⁻¹ := by group
      _ = g * (b * y) * g⁻¹ := by rw [← h]; group
  have h2 : g * y * g⁻¹ * b = g * (y * b) * g⁻¹ := by
    calc g * y * g⁻¹ * b = g * y * (g⁻¹ * b) := by group
      _ = g * (y * b) * g⁻¹ := by
        have : g⁻¹ * b = b * g⁻¹ := by
          calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * b) * g⁻¹ := by rw [h]
            _ = b * g⁻¹ := by group
        rw [this]; group
  rw [h1, h2]
  constructor
  · intro h; simpa using h
  · intro h; rw [h]

theorem le_normalizer_gLBConj_iff {B L : Subgroup G} (hB : IsMulCommutative B) {g : G} (hg : g ∈ B) :
    B ≤ Subgroup.normalizer (GLBConj g L : Set G) ↔ B ≤ Subgroup.normalizer (L : Set G) := by
  have hcomm : ∀ b ∈ B, g * b * g⁻¹ = b := fun b hb => by
    have := congrArg Subtype.val (hB.is_comm.comm ⟨g, hg⟩ ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this]; group
  rw [normalizer_gLBConj]
  constructor
  · intro h b hb
    have := h hb
    rw [mem_gLBConj, hcomm b hb] at this
    exact this
  · intro h b hb
    rw [mem_gLBConj, hcomm b hb]
    exact h hb

theorem card_sup_zpowers_of_pow_three_eq_one {H : Subgroup G} {w : G} (hw3 : w ^ 3 = 1)
    (hwH : w ∉ H) (hc : ∀ h ∈ H, h * w = w * h) :
    Nat.card ↥(H ⊔ Subgroup.zpowers w) = 3 * Nat.card H := by
  have hw1 : w ≠ 1 := fun h => hwH (h ▸ H.one_mem)
  have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hord]
  have hprime : (Nat.card (Subgroup.zpowers w)).Prime := hcard ▸ Nat.prime_three
  have hdisj : Disjoint H (Subgroup.zpowers w) := by
    rw [disjoint_iff]
    have : Fact (Nat.card (Subgroup.zpowers w)).Prime := ⟨hprime⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w)) with hb | hb
    · refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
      have : (⟨u, hu.2⟩ : Subgroup.zpowers w) ∈
          (H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w) := Subgroup.mem_subgroupOf.2 hu
      rw [hb, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exfalso
      have : (⟨w, Subgroup.mem_zpowers w⟩ : Subgroup.zpowers w) ∈
          (H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w) := by rw [hb]; trivial
      exact hwH (Subgroup.mem_subgroupOf.1 this).1
  let f : H →* G := H.subtype
  let g' : Subgroup.zpowers w →* G := (Subgroup.zpowers w).subtype
  have hcomm : ∀ (m : H) (n : Subgroup.zpowers w), Commute (f m) (g' n) := by
    intro m n
    obtain ⟨k, hk⟩ := n.2
    show (m : G) * (n : G) = (n : G) * m
    rw [← hk]
    exact ((Commute.zpow_right (hc m m.2 : (m : G) * w = w * m) k)).eq
  have hinj : Function.Injective (MonoidHom.noncommCoprod f g' hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, (Subgroup.zpowers w).subtype_injective, ?_⟩
    simpa [f, g'] using hdisj
  have hrange : (MonoidHom.noncommCoprod f g' hcomm).range = H ⊔ Subgroup.zpowers w := by
    rw [MonoidHom.noncommCoprod_range]
    simp [f, g']
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hcard, mul_comm]

theorem exists_isElemAbelian_card_three_of_independent {x y z : G}
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    (hzxy : z ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers z) = 3 ^ 3 := by
  have hord : ∀ {w : G}, w ^ 3 = 1 → ∀ u ∈ Subgroup.zpowers w, u ^ 3 = 1 := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hel : ∀ {w : G}, w ^ 3 = 1 → IsElemAbelian 3 (Subgroup.zpowers w) :=
    fun hw => ⟨inferInstance, hord hw⟩
  have hcent : ∀ {a b : G}, a * b = b * a →
      Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro a b hab u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).symm.eq
  have hHz : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer (Subgroup.zpowers z : Set G) :=
    sup_le (hcent hxz) (hcent hyz)
  have hcard3 : ∀ {w : G}, w ^ 3 = 1 → w ≠ 1 → Nat.card (Subgroup.zpowers w) = 3 := fun hw hw1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime hw hw1]
  refine ⟨isElemAbelian_sup_of_commute
    (isElemAbelian_sup_of_commute (hel hx) (hel hy) (hcent hxy)) (hel hz) hHz, ?_⟩
  have h9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
    rw [card_sup_zpowers_of_pow_three_eq_one hy hyx
      (fun h hh => (Subgroup.mem_centralizer_iff.1 (hcent hxy hh) y
        (Subgroup.mem_zpowers y)).symm), hcard3 hx hx1]
  rw [card_sup_zpowers_of_pow_three_eq_one hz hzxy
    (fun h hh => (Subgroup.mem_centralizer_iff.1 (hHz hh) z (Subgroup.mem_zpowers z)).symm), h9]
  norm_num

end CFSG.HardMathSupport.Solomon.LocalBalance
