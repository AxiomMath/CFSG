module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerLinearField
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem card_eq_two_mul_card_of_isCompl {z : V} (hz : z ≠ 0) {W : Submodule (ZMod 2) V}
    (hzW : IsCompl (Submodule.span (ZMod 2) {z}) W) : Nat.card V = 2 * Nat.card W := by
  rw [← Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hzW).toEquiv, Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Submodule.span (ZMod 2) {z}),
    finrank_span_singleton hz, Nat.card_zmod, pow_one]

theorem card_eq_mul_card_stabilizer_of_transitive {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hYtrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ y ∈ Y, y v = w) {z : V} (hz : z ≠ 0) :
    Nat.card Y = (Nat.card V - 1) * Nat.card (MulAction.stabilizer Y z) := by
  have horbit : MulAction.orbit Y z = ({0} : Set V)ᶜ := by
    ext v
    rw [MulAction.mem_orbit_iff, Set.mem_compl_singleton_iff]
    constructor
    · rintro ⟨y, rfl⟩ h
      exact hz ((y : V ≃ₗ[ZMod 2] V).injective (h.trans (map_zero _).symm))
    · intro hv
      obtain ⟨y, hy, rfl⟩ := hYtrans z v hz hv
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← Subgroup.card_mul_index (MulAction.stabilizer Y z), MulAction.index_stabilizer, horbit,
    Set.ncard_compl, Set.ncard_singleton, mul_comm]

theorem add_five_le_two_pow {n : ℕ} (hn : 3 ≤ n) : n + 5 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m _ ih => rw [pow_succ]; omega

theorem card_eq_twentyOne_of_oddTransitive {q n : ℕ} (hq : q = 2 ^ n) (hn : 2 ≤ n) {z : V}
    (hz : z ≠ 0) {W : Submodule (ZMod 2) V} (hzW : IsCompl (Submodule.span (ZMod 2) {z}) W)
    (hW : Nat.card W = q) {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hYodd : Odd (Nat.card Y))
    (hYtrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ y ∈ Y, y v = w) {C₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hC₀Y : C₀ ≤ Y) (hC₀cyc : IsCyclic C₀) (hC₀card : Nat.card C₀ = q - 1)
    (hC₀z : ∀ c ∈ C₀, c z = z)
    (hC₀reg : ∀ w ∈ W, w ≠ 0 → ∀ w' ∈ W, w' ≠ 0 → ∃! c, c ∈ C₀ ∧ c w = w') :
    q = 4 ∧ Nat.card Y = 21 := by
  have := finite_linearEquiv_zmod_two (V := V)
  have hq4 : 4 ≤ q := hq ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hV : Nat.card V = 2 * q := by rw [card_eq_two_mul_card_of_isCompl hz hzW, hW]
  have hrank : Module.finrank (ZMod 2) V = n + 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod, hq, ← pow_succ'] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hYodd
  have hYne : Y ≠ ⊥ := by
    rintro rfl
    rw [le_bot_iff.mp hC₀Y, Subgroup.card_bot] at hC₀card
    omega
  obtain ⟨P, -, hPne, hPcomm, hPnorm⟩ :=
    CFSG.LinearGroups.exists_abelian_normalized_of_isSolvable Y hYne
  have hfree : ∀ x ∈ P, ∀ v : V, v ≠ 0 → x v = v → x = 1 := fun x hx _ hv hxv =>
    eq_one_of_mem_of_apply_eq_self hPcomm hPnorm hYtrans hx hv hxv
  obtain ⟨⟨x, hxP⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hC₀comm : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a := by
    intro a ha b hb
    have := hC₀cyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hC₀trans : ∀ w ∈ W, w ≠ 0 → ∀ w' ∈ W, w' ≠ 0 → ∃ c ∈ C₀, c w = w' :=
    fun w hw hw0 w' hw' hw'0 => (hC₀reg w hw hw0 w' hw' hw'0).exists
  have hfaith : ∀ c ∈ C₀, c * x = x * c → c = 1 := fun c hc hcx =>
    eq_one_of_commute_of_fixedPointFree hz hzW hC₀comm hC₀z hC₀trans
      (fun v hv => by_contra fun h => hx1' (hfree x hxP v h hv)) hc hcx
  have hPcard := card_add_one_le_card_of_conj_injective hPnorm hC₀Y hxP hx1' hfaith
  have hPtrans : ∀ v : V, v ≠ 0 → ∃ x ∈ P, x z = v := fun v hv =>
    exists_mem_apply_eq_of_card_le hfree (by omega) hz hv
  have hstab : Nat.card (MulAction.stabilizer Y z) ≤ n + 1 :=
    hrank ▸ card_stabilizer_le_finrank hPcomm hPnorm hz hPtrans
  have hC₀stab : Nat.card C₀ ≤ Nat.card (MulAction.stabilizer Y z) := by
    refine Nat.card_le_card_of_injective
      (fun c => ⟨⟨c, hC₀Y c.2⟩, (MulAction.mem_stabilizer_iff).mpr (hC₀z c c.2)⟩) ?_
    intro c₁ c₂ h
    exact Subtype.ext
      (congrArg (fun y : MulAction.stabilizer Y z => ((y : Y) : V ≃ₗ[ZMod 2] V)) h)
  have hcard := card_eq_mul_card_stabilizer_of_transitive hYtrans hz
  have hn2 : n = 2 := by
    by_contra hne
    have := add_five_le_two_pow (n := n) (by omega)
    omega
  subst hn2
  norm_num at hq
  subst hq
  refine ⟨rfl, ?_⟩
  rw [hcard, hV]
  have : Nat.card (MulAction.stabilizer Y z) = 3 := by omega
  rw [this]

end CFSG.ProperTwoGeneratedCore.Assembly
