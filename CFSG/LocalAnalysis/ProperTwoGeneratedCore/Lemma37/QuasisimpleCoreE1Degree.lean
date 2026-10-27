module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv

theorem nonempty_mulEquiv_alternatingGroup_nine_of_index {X : Type*} [Group X] [Finite X]
    (hX : IsSimpleGroup X) {B : Subgroup X} (hB : B.index = 9) (hcard : Nat.card X = 181440) :
    Nonempty (X ≃* alternatingGroup (Fin 9)) := by
  classical
  have hBne : B ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hB
    omega
  have hcore : B.normalCore = ⊥ := by
    rcases B.normalCore_normal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · exact absurd (le_antisymm le_top (htop.symm ▸ B.normalCore_le)) hBne
  have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ B)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← B.normalCore_eq_ker]
    exact hcore
  have : Fintype (X ⧸ B) := Fintype.ofFinite _
  have hcosets : Fintype.card (X ⧸ B) = 9 := by
    rw [← Nat.card_eq_fintype_card, ← B.index_eq_card, hB]
  let φ : X →* Perm (Fin 9) := (permCongrHom (Fintype.equivFinOfCardEq hcosets)).toMonoidHom.comp
    (MulAction.toPermHom X (X ⧸ B))
  have hφ : Function.Injective φ :=
    (permCongrHom (Fintype.equivFinOfCardEq hcosets)).injective.comp hinj
  let e : X ≃* φ.range := MulEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y hxy => hφ (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  have hidx : φ.range.index = 2 := by
    have hmul := φ.range.index_mul_card
    rw [← Nat.card_congr e.toEquiv, hcard, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hmul
    have h9 : Nat.factorial 9 = 362880 := by decide
    omega
  exact ⟨e.trans (MulEquiv.subgroupCongr (Perm.eq_alternatingGroup_of_index_eq_two hidx))⟩

theorem eq_nine_of_dvd_nine_hundred_forty_five {n : ℕ} (hdvd : n ∣ 945) (hmod : n % 8 = 1)
    (hle : n ≤ 55) (hlt : 1 < n) : n = 9 := by
  have key : ∀ k < 56, k ∣ 945 → k % 8 = 1 → 1 < k → k = 9 := by decide
  exact key n (by omega) hdvd hmod hlt

theorem card_modEq_one_of_dvd_card_orbit {G α : Type*} [Group G] [MulAction G α] [Finite α]
    {k : ℕ} {a : α} (ha : ∀ g : G, g • a = a)
    (hk : ∀ b : α, b ≠ a → k ∣ Nat.card (MulAction.orbit G b)) :
    Nat.card α ≡ 1 [MOD k] := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  set a' : MulAction.orbitRel.Quotient G α := Quotient.mk'' a
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' G α), Nat.card_sigma,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a')]
  have h1 : Nat.card a'.orbit = 1 := by
    rw [MulAction.orbitRel.Quotient.orbit_mk]
    have horbit : MulAction.orbit G a = {a} := by
      ext b
      rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨g, hg⟩ => by rw [← hg, ha], fun hb => ⟨1, by rw [hb, one_smul]⟩⟩
    rw [horbit, Nat.card_unique]
  have h2 : k ∣ ∑ ω ∈ Finset.univ.erase a', Nat.card ω.orbit := by
    refine Finset.dvd_sum fun ω hω => ?_
    induction ω using Quotient.inductionOn' with
    | h b =>
      rw [MulAction.orbitRel.Quotient.orbit_mk]
      exact hk b fun hb => (Finset.mem_erase.mp hω).1 (by rw [hb])
  obtain ⟨c, hc⟩ := h2
  rw [h1, hc, Nat.ModEq, Nat.add_mul_mod_self_left]

theorem card_le_sixteen_of_pow_eight {P : Type*} [Group P] [Finite P]
    (hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions P)
    (h8 : ∀ p : P, p ^ 8 = 1) : Nat.card P ≤ 16 := by
  have hp : IsPGroup 2 P := fun p => ⟨3, by rw [show 2 ^ 3 = 8 by norm_num]; exact h8 p⟩
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hp hrank with
    hc | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
    have hdvd : orderOf g ∣ 8 := orderOf_dvd_of_pow_eq_one (h8 g)
    rw [hg] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have h1 : orderOf (e (QuaternionGroup.a 1)) = 2 * 2 ^ n := by
      rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
    have h2 : orderOf (e (QuaternionGroup.a 1)) ∣ 8 := orderOf_dvd_of_pow_eq_one (h8 _)
    have hcard : Nat.card P = 4 * 2 ^ n := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [h1] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem smul_mk_eq_mk_iff {G : Type*} [Group G] (H : Subgroup G) (c g : G) :
    c • (g : G ⧸ H) = g ↔ g⁻¹ * c * g ∈ H := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  have : ((c * g)⁻¹ * g)⁻¹ = g⁻¹ * c * g := by group
  rw [this]

theorem card_eq_index_mul_card_of_existsUnique {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (C : G → Prop) (hC : ∀ c g, C c → C (g * c * g⁻¹))
    (hfix : ∀ c, C c → ∃! ω : G ⧸ H, c • ω = ω) :
    Nat.card {c // C c} = H.index * Nat.card {c // C c ∧ c ∈ H} := by
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  let f : {c // C c} → G ⧸ H := fun c => (hfix c.1 c.2).choose
  have hf : ∀ (c : {c // C c}) (ω : G ⧸ H), c.1 • ω = ω ↔ f c = ω := fun c ω =>
    ⟨fun h => ((hfix c.1 c.2).choose_spec.2 ω h).symm,
      fun h => h ▸ (hfix c.1 c.2).choose_spec.1⟩
  have hfiber : ∀ ω : G ⧸ H, Nat.card {c : {c // C c} // f c = ω} =
      Nat.card {c // C c ∧ c ∈ H} := by
    intro ω
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    refine Nat.card_congr
      { toFun := fun c => ⟨g⁻¹ * c.1.1 * g, by simpa using hC c.1.1 g⁻¹ c.1.2,
          (smul_mk_eq_mk_iff H _ g).mp ((hf c.1 _).mpr c.2)⟩
        invFun := fun c => ⟨⟨g * c.1 * g⁻¹, hC c.1 g c.2.1⟩, (hf _ _).mp
          ((smul_mk_eq_mk_iff H _ g).mpr (by simpa [mul_assoc] using c.2.2))⟩
        left_inv := fun c => by
          ext
          simp [mul_assoc]
        right_inv := fun c => by
          ext
          simp [mul_assoc] }
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma,
    Finset.sum_congr rfl fun ω _ => hfiber ω, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    H.index_eq_card, Nat.card_eq_fintype_card (α := G ⧸ H)]

theorem smul_eq_self_of_commute_of_existsUnique {G α : Type*} [Group G] [MulAction G α]
    {c d : G} (hc : ∃! ω : α, c • ω = ω) (hcd : c * d = d * c) {ω : α} (hω : c • ω = ω) :
    d • ω = ω :=
  hc.unique (by rw [smul_smul, hcd, mul_smul, hω]) hω

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
