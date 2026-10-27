module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.InvariantsAut

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

theorem card_inf_le_card_mul_of_coord {X A : Type*} [Group X] [Finite X] [AddCommGroup A]
    [Finite A] {x : A → X} {H N P : Subgroup X} {c : X → A} (hc : ∀ a, ∀ n ∈ N, c (x a * n) = a)
    (hx : ∀ a a', x (a + a') = x a * x a') (hxN : ∀ a, x a ∈ normalizer (N : Set X))
    (hH : ∀ g ∈ H, ∃ a, ∃ n ∈ N, x a * n = g) (T : Set A) (hT : ∀ g ∈ H ⊓ P, c g ∈ T) :
    Nat.card ↥(H ⊓ P) ≤ Nat.card T * Nat.card ↥(N ⊓ P) := by
  have hx0 : x 0 = 1 := map_zero_of_add hx
  have hadd : ∀ g ∈ H, ∀ g' ∈ H, c (g * g') = c g + c g' := fun g hg g' hg' =>
    TrialityD4Data.coord_mul_eq_add hc (fun a a' => by rw [hx, inv_mul_cancel]; exact one_mem _)
      hxN (hH g hg) (hH g' hg')
  have hc1 : c 1 = 0 := by
    have := hc 0 1 (one_mem _)
    rwa [hx0, one_mul] at this
  let ψ : ↥(H ⊓ P) →* Multiplicative A :=
    { toFun := fun g => Multiplicative.ofAdd (c g)
      map_one' := by
        change Multiplicative.ofAdd (c 1) = 1
        rw [hc1, ofAdd_zero]
      map_mul' := fun g g' => by
        change Multiplicative.ofAdd (c ((g : X) * g')) = _
        rw [hadd _ (mem_inf.1 g.2).1 _ (mem_inf.1 g'.2).1]
        rfl }
  have hcard := TrialityD4Data.card_eq_card_range_mul_card_ker ψ
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(N ⊓ P) := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨((g : ↥(H ⊓ P)) : X), ?_, (mem_inf.1 (g : ↥(H ⊓ P)).2).2⟩) ?_
    · obtain ⟨a, n, hn, hg⟩ := hH _ (mem_inf.1 (g : ↥(H ⊓ P)).2).1
      have h0 : c ((g : ↥(H ⊓ P)) : X) = 0 := ofAdd_eq_one.1 (MonoidHom.mem_ker.1 g.2)
      rw [← hg, hc a n hn] at h0
      rw [← hg, h0, hx0, one_mul]
      exact hn
    · intro g g' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  have hrange : Nat.card ψ.range ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective
      (fun y => ⟨Multiplicative.toAdd (y : Multiplicative A), ?_⟩) ?_
    · obtain ⟨g, hg⟩ := y.2
      rw [← hg]
      exact hT _ g.2
    · intro y y' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
  rw [hcard]
  exact Nat.mul_le_mul hrange hker

theorem coord_conj_eq {X A : Type*} [Group X] [AddCommGroup A]
    {x : A → X} {H N : Subgroup X} {c : X → A} (hc : ∀ a, ∀ n ∈ N, c (x a * n) = a)
    (hx : ∀ a a', x (a + a') = x a * x a') (hxN : ∀ a, x a ∈ normalizer (N : Set X))
    (hH : ∀ g ∈ H, ∃ a, ∃ n ∈ N, x a * n = g) (hNH : N ≤ H) {s y : X} (hy : y ∈ H)
    (hsy : ⁅s, y⁆ ∈ N) : c (s * y * s⁻¹) = c y := by
  have hx0 : x 0 = 1 := map_zero_of_add hx
  have hcN : c ⁅s, y⁆ = 0 := by
    have := hc 0 _ hsy
    rwa [hx0, one_mul] at this
  rw [conj_eq_commutatorElement_mul, TrialityD4Data.coord_mul_eq_add hc
    (fun a a' => by rw [hx, inv_mul_cancel]; exact one_mem _) hxN (hH _ (hNH hsy)) (hH _ hy),
    hcN, zero_add]

theorem inv_mul_mul_mem_range_conj {X : Type*} [Group X] {a x : MulAut X}
    (hx : x ∈ (MulAut.conj : X →* MulAut X).range) :
    a⁻¹ * x * a ∈ (MulAut.conj : X →* MulAut X).range := by
  have h := (mulAutConj_range_normal (G := X)).conj_mem _ hx a⁻¹
  rwa [inv_inv] at h

theorem inv_mul_mul_not_mem_range_conj {X : Type*} [Group X] {a x : MulAut X}
    (hx : x ∉ (MulAut.conj : X →* MulAut X).range) :
    a⁻¹ * x * a ∉ (MulAut.conj : X →* MulAut X).range := fun h => hx (by
  have h2 := (mulAutConj_range_normal (G := X)).conj_mem _ h a
  rwa [show a * (a⁻¹ * x * a) * a⁻¹ = x by group] at h2)

theorem card_le_two_pow_pRank {G : Type*} [Group G] [Finite G] {E H : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 _ x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE2
  rw [hn]
  exact Nat.pow_le_pow_right two_pos (CFSG.SectionRank.le_pRank one_lt_two hEH hE hn)

theorem isMulCommutative_map {G H : Type*} [Group G] [Group H] {A : Subgroup G}
    (hA : IsMulCommutative A) (φ : G →* H) : IsMulCommutative (A.map φ) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
  change (a : H) * b = b * a
  rw [← hxa, ← hyb, ← map_mul, ← map_mul]
  exact congrArg (fun z : A => φ z) (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)

open SymplecticFourRankThompson in
theorem omegaOneOf_map_props {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (A : Subgroup Q) [IsMulCommutative A] :
    CFSG.Open.IsElemAbelian 2 ((omegaOneOf A).map Q.subtype) ∧
      (omegaOneOf A).map Q.subtype ≤ A.map Q.subtype ∧
      2 ^ Group.rank A ≤ Nat.card ((omegaOneOf A).map Q.subtype) := by
  refine ⟨CFSG.SectionRank.isElemAbelian_map ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩ _,
    map_mono (omegaOneOf_le A), ?_⟩
  · have h := congrArg Subtype.val (mul_comm' (⟨_, a.2.1⟩ : A) ⟨_, b.2.1⟩)
    exact h
  · rw [sq]
    exact hx.2
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact two_pow_rank_le_card_omegaOneOf A (hQ.to_subgroup A)

open SymplecticFourRankThompson in
theorem iSup_eq_and_rankThompson_eq_of_forall {G : Type*} [Group G] [Finite G]
    {Q R₀ : Subgroup G} {r : ℕ} (hQ : IsPGroup 2 Q) (hrQ : CFSG.Open.pRank 2 Q = r)
    (hkey : ∀ B : Subgroup G, B ≤ Q → IsMulCommutative B → r ≤ CFSG.Open.pRank 2 B → B ≤ R₀)
    (hgen : R₀ ≤ ⨆ (E : Subgroup G) (_ : E ≤ Q ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ r), E) :
    (⨆ (A : Subgroup G) (_ : A ≤ Q ∧ IsMulCommutative A ∧
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 Q), A) = R₀ ∧
      (CFSG.LocalAnalysis.rankThompson ↥Q).map Q.subtype = R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEr : ∀ E : Subgroup G, E ≤ Q → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 2 ^ r →
      CFSG.Open.pRank 2 E = r := fun E hEQ hE hc =>
    le_antisymm (hrQ ▸ CFSG.SectionRank.pRank_mono one_lt_two hEQ)
      (CFSG.SectionRank.le_pRank one_lt_two le_rfl hE hc)
  refine ⟨le_antisymm (iSup₂_le fun A hA => hkey A hA.1 hA.2.1 (by rw [hA.2.2, hrQ]))
    (hgen.trans (iSup₂_le fun E hE => le_iSup₂_of_le E ⟨hE.1, hE.2.1.1,
      by rw [hEr E hE.1 hE.2.1 hE.2.2, hrQ]⟩ le_rfl)), ?_⟩
  have hrank_le : ∀ A : Subgroup Q, IsMulCommutative A → Group.rank A ≤ r := fun A hA => by
    obtain ⟨hΩe, -, hΩc⟩ := omegaOneOf_map_props hQ A
    have h2 := card_le_two_pow_pRank (H := Q) (map_subtype_le _) hΩe
    rw [hrQ] at h2
    exact (Nat.pow_le_pow_iff_right one_lt_two).1 (hΩc.trans h2)
  have hsub : ∀ E : Subgroup G, E ≤ Q → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 2 ^ r →
      IsMulCommutative (E.subgroupOf Q) ∧ Group.rank (E.subgroupOf Q) = r := by
    intro E hEQ hE hcE
    have := hE.1
    have hc : IsMulCommutative (E.subgroupOf Q) := ⟨⟨fun a b => by
      have h := congrArg Subtype.val (mul_comm' (⟨_, a.2⟩ : E) ⟨_, b.2⟩)
      exact Subtype.ext (Subtype.ext h)⟩⟩
    refine ⟨hc, ?_⟩
    have h := two_pow_rank_eq_card_of_elementary (E.subgroupOf Q) fun x hx => by
      have := hE.2 _ hx
      rw [sq] at this
      exact Subtype.ext this
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv, hcE] at h
    exact Nat.pow_right_injective le_rfl h
  obtain ⟨E₀, hE₀Q, hE₀, hcE₀⟩ := CFSG.SectionRank.exists_pRank one_lt_two Q
  rw [hrQ] at hcE₀
  obtain ⟨hE₀c, hE₀r⟩ := hsub E₀ hE₀Q hE₀ hcE₀
  have hmax : CFSG.LocalAnalysis.maxAbelianRank ↥Q = r := by
    refine le_antisymm (csSup_le ⟨r, _, hE₀c, hE₀r⟩ ?_) (le_csSup ⟨r, ?_⟩ ⟨_, hE₀c, hE₀r⟩)
    · rintro _ ⟨A, hA, rfl⟩
      exact hrank_le A hA
    · rintro _ ⟨A, hA, rfl⟩
      exact hrank_le A hA
  apply le_antisymm
  · rw [CFSG.LocalAnalysis.rankThompson, map_le_iff_le_comap]
    refine sSup_le fun A ⟨hA, hrA⟩ => ?_
    rw [← map_le_iff_le_comap]
    obtain ⟨hΩe, hΩA, hΩc⟩ := omegaOneOf_map_props hQ A
    refine hkey _ (map_subtype_le _) (isMulCommutative_map hA _) ?_
    have hΩ2 : IsPGroup 2 ((omegaOneOf A).map Q.subtype) := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hΩe.2 _ x.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hΩ2
    have h1 := CFSG.SectionRank.le_pRank one_lt_two hΩA hΩe hn
    rw [hrA, hmax, hn] at hΩc
    have := (Nat.pow_le_pow_iff_right one_lt_two).1 hΩc
    omega
  · refine hgen.trans (iSup₂_le fun E ⟨hEQ, hE, hcE⟩ => ?_)
    obtain ⟨hc, hr⟩ := hsub E hEQ hE hcE
    rw [← map_subgroupOf_eq_of_le hEQ]
    exact map_mono (le_sSup ⟨hc, by rw [hr, hmax]⟩)

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem nfc_φ_pow (k : ℕ) {g : X} (hg : g ∈ d.S) :
    d.nfc ((d.φ ^ k) g) = d.powCo (2 ^ k) (d.nfc g) := by
  conv_lhs => rw [← d.nf_nfc hg]
  rw [d.φ_pow_nf, nfc_nf]

theorem nfc_x₂_mul {a : d.Γ₀} {n : X} (hn : n ∈ d.F) : (d.nfc (d.x₂ a * n)).2.1 = a := by
  obtain ⟨a₃, a₄, a₅, a₆, rfl⟩ := d.mem_F_coords hn
  rw [show d.x₂ a * d.nf (0, 0, a₃, a₄, a₅, a₆) = d.nf (0, a, a₃, a₄, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, one_mul, mul_assoc], nfc_nf]

theorem nfc_x₃_mul {a : d.Γ} {n : X} (hn : n ∈ d.W) : (d.nfc (d.x₃ a * n)).2.2.1 = a := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hn
  rw [show d.x₃ a * d.nf (0, 0, 0, a₄, a₅, a₆) = d.nf (0, 0, a, a₄, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul, mul_assoc], nfc_nf]

theorem nfc_x₄_mul {a : d.Γ} {n : X} (hn : n ∈ d.Y) : (d.nfc (d.x₄ a * n)).2.2.2.1 = a := by
  obtain ⟨a₅, a₆, rfl⟩ := d.mem_Y_coords hn
  rw [show d.x₄ a * d.nf (0, 0, 0, 0, a₅, a₆) = d.nf (0, 0, 0, a, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, one_mul, mul_assoc], nfc_nf]

theorem nfc_x₅_mul {a : d.Γ₀} {n : X} (hn : n ∈ d.V) : (d.nfc (d.x₅ a * n)).2.2.2.2.1 = a := by
  obtain ⟨a₆, rfl⟩ := hn
  rw [show d.x₅ a * d.x₆ a₆ = d.nf (0, 0, 0, 0, a, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, one_mul], nfc_nf]

theorem nfc_x₆_mul {a : d.Γ₀} {n : X} (hn : n ∈ (⊥ : Subgroup X)) :
    (d.nfc (d.x₆ a * n)).2.2.2.2.2 = a := by
  rw [mem_bot.1 hn, mul_one, ← d.nf_x₆, nfc_nf]

theorem mem_V_iff_bot {g : X} : g ∈ d.V → ∃ a, ∃ n ∈ (⊥ : Subgroup X), d.x₆ a * n = g := by
  rintro ⟨a, rfl⟩
  exact ⟨a, 1, one_mem _, mul_one _⟩

@[expose] def fixConj (s : X) (k : ℕ) : Subgroup X :=
  (MulAut.conj s * d.φ ^ k).toMonoidHom.eqLocus (MonoidHom.id X)

theorem mem_fixConj {s : X} {k : ℕ} {g : X} : g ∈ d.fixConj s k ↔ s * (d.φ ^ k) g * s⁻¹ = g :=
  Iff.rfl

theorem coord_pow_eq_of_fixed {A : Type*} [Field A] {x : A → X} {H N : Subgroup X} {c : X → A}
    (hc : ∀ a, ∀ n ∈ N, c (x a * n) = a) (hx : ∀ a a', x (a + a') = x a * x a')
    (hxN : ∀ a, x a ∈ normalizer (N : Set X)) (hH : ∀ g ∈ H, ∃ a, ∃ n ∈ N, x a * n = g)
    (hNH : N ≤ H) (hHS : H ≤ d.S) (hSH : ⁅d.S, H⁆ ≤ N) {k : ℕ}
    (hφH : ∀ g ∈ H, (d.φ ^ k) g ∈ H) (hcφ : ∀ g ∈ d.S, c ((d.φ ^ k) g) = c g ^ 2 ^ k)
    {s g : X} (hs : s ∈ d.S) (hg : g ∈ H) (hfix : g ∈ d.fixConj s k) : c g ^ 2 ^ k = c g := by
  have h1 := coord_conj_eq hc hx hxN hH hNH (hφH g hg)
    (hSH (commutator_mem_commutator hs (hφH g hg)))
  rw [d.mem_fixConj.1 hfix] at h1
  rw [← hcφ g (hHS hg), h1]

theorem card_inf_fixConj_le {A : Type*} [Field A] [Finite A] {x : A → X} {H N : Subgroup X}
    {c : X → A} (hc : ∀ a, ∀ n ∈ N, c (x a * n) = a) (hx : ∀ a a', x (a + a') = x a * x a')
    (hxN : ∀ a, x a ∈ normalizer (N : Set X)) (hH : ∀ g ∈ H, ∃ a, ∃ n ∈ N, x a * n = g)
    (hNH : N ≤ H) (hHS : H ≤ d.S) (hSH : ⁅d.S, H⁆ ≤ N) {k : ℕ}
    (hφH : ∀ g ∈ H, (d.φ ^ k) g ∈ H) (hcφ : ∀ g ∈ d.S, c ((d.φ ^ k) g) = c g ^ 2 ^ k)
    {s : X} (hs : s ∈ d.S) {P : Subgroup X} (hP : P ≤ d.fixConj s k) :
    Nat.card ↥(H ⊓ P) ≤ Nat.card {a : A // a ^ 2 ^ k = a} * Nat.card ↥(N ⊓ P) := by
  have := d.finite
  exact card_inf_le_card_mul_of_coord hc hx hxN hH {a | a ^ 2 ^ k = a} fun g hg =>
    d.coord_pow_eq_of_fixed hc hx hxN hH hNH hHS hSH hφH hcφ hs (mem_inf.1 hg).1
      (hP (mem_inf.1 hg).2)

section Counts

variable {s : X} (hs : s ∈ d.S) (k : ℕ) {P : Subgroup X} (hP : P ≤ d.fixConj s k)
include hs hP

theorem card_V_inf_le : Nat.card ↥(d.V ⊓ P) ≤ Nat.card {a : d.Γ₀ // a ^ 2 ^ k = a} := by
  have h := d.card_inf_fixConj_le (x := d.x₆) (H := d.V) (N := ⊥)
    (c := fun g => (d.nfc g).2.2.2.2.2) (fun _ _ hn => d.nfc_x₆_mul hn) d.x₆_add
    (fun a => le_normalizer_bot_subgroup _ (mem_top (d.x₆ a))) (fun g hg => d.mem_V_iff_bot hg)
    bot_le d.V_le_S (by rw [d.commutator_S_V]) (fun g hg => d.φ_pow_mem_rootChain k 1 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP
  rwa [bot_inf_eq, card_bot, mul_one] at h

theorem card_Y_inf_le :
    Nat.card ↥(d.Y ⊓ P) ≤ Nat.card {a : d.Γ₀ // a ^ 2 ^ k = a} * Nat.card ↥(d.V ⊓ P) :=
  d.card_inf_fixConj_le (x := d.x₅) (H := d.Y) (N := d.V)
    (c := fun g => (d.nfc g).2.2.2.2.1) (fun _ _ hn => d.nfc_x₅_mul hn) d.x₅_add
    (fun a => d.S_le_normalizer_V (d.U₅_le_S (d.x₅_mem_U₅ a))) (fun g hg => d.mem_Y_iff.1 hg)
    d.V_le_Y d.Y_le_S d.commutator_S_Y (fun g hg => d.φ_pow_mem_rootChain k 2 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP

theorem card_W_inf_le :
    Nat.card ↥(d.W ⊓ P) ≤ Nat.card {a : d.Γ // a ^ 2 ^ k = a} * Nat.card ↥(d.Y ⊓ P) :=
  d.card_inf_fixConj_le (x := d.x₄) (H := d.W) (N := d.Y)
    (c := fun g => (d.nfc g).2.2.2.1) (fun _ _ hn => d.nfc_x₄_mul hn) d.x₄_add
    (fun a => d.S_le_normalizer_Y (d.U₄_le_S (d.x₄_mem_U₄ a))) (fun g hg => d.mem_W_iff.1 hg)
    d.Y_le_W d.W_le_S d.commutator_S_W (fun g hg => d.φ_pow_mem_rootChain k 3 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP

theorem card_F_inf_le :
    Nat.card ↥(d.F ⊓ P) ≤ Nat.card {a : d.Γ // a ^ 2 ^ k = a} * Nat.card ↥(d.W ⊓ P) :=
  d.card_inf_fixConj_le (x := d.x₃) (H := d.F) (N := d.W)
    (c := fun g => (d.nfc g).2.2.1) (fun _ _ hn => d.nfc_x₃_mul hn) d.x₃_add
    (fun a => d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ a))) (fun g hg => d.mem_F_iff.1 hg)
    d.W_le_F d.F_le_S d.commutator_S_F (fun g hg => d.φ_pow_mem_rootChain k 4 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP

theorem card_D_inf_le :
    Nat.card ↥(d.D ⊓ P) ≤ Nat.card {a : d.Γ₀ // a ^ 2 ^ k = a} * Nat.card ↥(d.F ⊓ P) :=
  d.card_inf_fixConj_le (x := d.x₂) (H := d.D) (N := d.F)
    (c := fun g => (d.nfc g).2.1) (fun _ _ hn => d.nfc_x₂_mul hn) d.x₂_add
    (fun a => d.S_le_normalizer_F (d.U₂_le_S (d.x₂_mem_U₂ a))) (fun g hg => d.mem_D_iff.1 hg)
    d.F_le_D d.D_le_S d.commutator_S_D (fun g hg => d.φ_pow_mem_rootChain k 5 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP

theorem card_S_inf_le :
    Nat.card ↥(d.S ⊓ P) ≤ Nat.card {a : d.Γ // a ^ 2 ^ k = a} * Nat.card ↥(d.D ⊓ P) :=
  d.card_inf_fixConj_le (x := d.x₁) (H := d.S) (N := d.D)
    (c := fun g => (d.nfc g).1) (fun _ _ hn => d.nfc_x₁_mul hn) d.x₁_add
    (fun a => d.S_le_normalizer_D (d.U₁_le_S (d.x₁_mem_U₁ a))) (fun g hg => d.mem_S_iff.1 hg)
    d.D_le_S le_rfl (d.commutator_S_S.trans d.F_le_D) (fun g hg => d.φ_pow_mem_rootChain k 6 hg)
    (fun g hg => by simp only [d.nfc_φ_pow k hg]; rfl) hs hP

end Counts

theorem card_fixed_Γ {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) :
    Nat.card {a : d.Γ // a ^ 2 ^ (3 * e) = a} = 2 ^ (3 * e) :=
  card_fixed_pow_two_pow (by omega) (by rw [d.card_Γ, hq, ← pow_mul, ← pow_mul]; ring_nf)

theorem card_fixed_Γ₀ {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) :
    Nat.card {a : d.Γ₀ // a ^ 2 ^ (3 * e) = a} = 2 ^ e := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => d.pow_three_e_eq_iff hq x)]
  exact card_fixed_pow_two_pow he (by rw [d.card_Γ₀, hq, ← pow_mul, mul_comm])

theorem card_W_inf_fixConj_le {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {s : X} (hs : s ∈ d.S) :
    Nat.card ↥(d.W ⊓ d.fixConj s (3 * e)) ≤ 2 ^ (5 * e) := by
  have hV := d.card_V_inf_le hs (3 * e) le_rfl
  have hY := d.card_Y_inf_le hs (3 * e) le_rfl
  have hW := d.card_W_inf_le hs (3 * e) le_rfl
  rw [d.card_fixed_Γ₀ he hq] at hV hY
  rw [d.card_fixed_Γ he hq] at hW
  calc Nat.card ↥(d.W ⊓ d.fixConj s (3 * e)) ≤ 2 ^ (3 * e) * (2 ^ e * 2 ^ e) :=
        hW.trans (Nat.mul_le_mul_left _ (hY.trans (Nat.mul_le_mul_left _ hV)))
    _ = 2 ^ (5 * e) := by rw [← pow_add, ← pow_add]; ring_nf

theorem card_D_inf_fixConj_le {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {s : X} (hs : s ∈ d.S) :
    Nat.card ↥(d.D ⊓ d.fixConj s (3 * e)) ≤ 2 ^ (9 * e) := by
  have hW := d.card_W_inf_fixConj_le he hq hs
  have hF := d.card_F_inf_le hs (3 * e) le_rfl
  have hD := d.card_D_inf_le hs (3 * e) le_rfl
  rw [d.card_fixed_Γ he hq] at hF
  rw [d.card_fixed_Γ₀ he hq] at hD
  calc Nat.card ↥(d.D ⊓ d.fixConj s (3 * e)) ≤ 2 ^ e * (2 ^ (3 * e) * 2 ^ (5 * e)) :=
        hD.trans (Nat.mul_le_mul_left _ (hF.trans (Nat.mul_le_mul_left _ hW)))
    _ = 2 ^ (9 * e) := by rw [← pow_add, ← pow_add]; ring_nf

theorem card_le_of_le_fixConj_of_not_le {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {s : X}
    (hs : s ∈ d.S) {E : Subgroup X} (hES : E ≤ d.S) (hEP : E ≤ d.fixConj s (3 * e))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) (hED : ¬ E ≤ d.D) :
    Nat.card E ≤ 2 ^ (8 * e) := by
  have := d.finite
  obtain ⟨x₀, hx₀E, hx₀D⟩ := Set.not_subset.1 hED
  have hs₀ : (d.nfc x₀).1 ≠ 0 := fun h0 => hx₀D (d.mem_D_of_nfc_fst (hES hx₀E) h0)
  obtain ⟨g₀, hg₀, hx₀⟩ := d.eq_x₁_mul_of_mem_S (hES hx₀E)
  have hDW : d.D ⊓ E ≤ d.W ⊓ d.fixConj s (3 * e) := by
    rintro n ⟨hnD, hnE⟩
    refine ⟨(d.mem_W_of_commute_x₁_mul hs₀ hg₀ hnD ?_ (hsq n hnE)).1, hEP hnE⟩
    rw [← hx₀]
    exact hcomm _ hx₀E _ hnE
  have h1 := d.card_S_inf_le hs (3 * e) hEP
  rw [inf_eq_right.2 hES, d.card_fixed_Γ he hq] at h1
  calc Nat.card E ≤ 2 ^ (3 * e) * 2 ^ (5 * e) :=
        h1.trans (Nat.mul_le_mul_left _ ((Subgroup.card_le_of_le hDW).trans
          (d.card_W_inf_fixConj_le he hq hs)))
    _ = 2 ^ (8 * e) := by rw [← pow_add]; ring_nf

theorem card_le_of_le_fixConj {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {s : X}
    (hs : s ∈ d.S) {E : Subgroup X} (hES : E ≤ d.S) (hEP : E ≤ d.fixConj s (3 * e))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ (9 * e) := by
  have := d.finite
  by_cases hED : E ≤ d.D
  · exact (Subgroup.card_le_of_le (le_inf hED hEP)).trans (d.card_D_inf_fixConj_le he hq hs)
  · exact (d.card_le_of_le_fixConj_of_not_le he hq hs hES hEP hcomm hsq hED).trans
      (Nat.pow_le_pow_right two_pos (by omega))

theorem card_lt_of_le_fixConj_one {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {E : Subgroup X}
    (hES : E ≤ d.S) (hEP : E ≤ d.fixConj 1 (3 * e)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E < 2 ^ (9 * e) := by
  have := d.finite
  by_cases hED : E ≤ d.D
  · refine lt_of_le_of_ne ((Subgroup.card_le_of_le (le_inf hED hEP)).trans
      (d.card_D_inf_fixConj_le he hq (one_mem _))) fun heq => ?_
    have hE : E = d.D ⊓ d.fixConj 1 (3 * e) := Subgroup.eq_of_le_of_card_ge (le_inf hED hEP)
      (by rw [heq]; exact d.card_D_inf_fixConj_le he hq (one_mem _))
    have hfix : ∀ g, (d.φ ^ (3 * e)) g = g → g ∈ d.fixConj 1 (3 * e) := fun g hg => by
      rw [d.mem_fixConj, hg, one_mul, inv_one, mul_one]
    have h2 : d.x₂ 1 ∈ E := hE ▸ ⟨d.x₂_mem_D 1, hfix _ (by rw [d.φ_pow_x₂, one_pow])⟩
    have h5 : d.x₅ 1 ∈ E := hE ▸ ⟨d.F_le_D (d.x₅_mem_F 1), hfix _ (by rw [d.φ_pow_x₅, one_pow])⟩
    have hc := d.comm₂₅ 1 1
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ h2 _ h5), mul_one, eq_comm,
      d.x₆_eq_one_iff] at hc
    exact one_ne_zero hc
  · exact (d.card_le_of_le_fixConj_of_not_le he hq (one_mem _) hES hEP hcomm hsq hED).trans_lt
      (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem exists_conj_mul_φ_pow_pow (g : X) (k n : ℕ) :
    ∃ g' : X, (MulAut.conj g * d.φ ^ k) ^ n = MulAut.conj g' * d.φ ^ (k * n) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨g', hg'⟩ := ih
    refine ⟨g' * (d.φ ^ (k * n)) g, ?_⟩
    rw [pow_succ, hg', map_mul, ← mulAut_mul_conj_mul_inv (d.φ ^ (k * n)) g,
      show k * (n + 1) = k * n + k by ring, pow_add]
    group

include d in
theorem commutatorElement_mem_range_conj (α β : MulAut X) :
    ⁅α, β⁆ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨g, a, rfl⟩ := d.aut_eq α
  obtain ⟨h, b, rfl⟩ := d.aut_eq β
  have e1 : MulAut.conj g * d.φ ^ a * (MulAut.conj h * d.φ ^ b) =
      MulAut.conj (g * (d.φ ^ a) h) * d.φ ^ (a + b) := by
    rw [map_mul, ← mulAut_mul_conj_mul_inv (d.φ ^ a) h, pow_add]
    group
  have e2 : MulAut.conj h * d.φ ^ b * (MulAut.conj g * d.φ ^ a) =
      MulAut.conj (h * (d.φ ^ b) g) * d.φ ^ (a + b) := by
    rw [map_mul, ← mulAut_mul_conj_mul_inv (d.φ ^ b) g, add_comm a b, pow_add]
    group
  refine ⟨g * (d.φ ^ a) h * (h * (d.φ ^ b) g)⁻¹, ?_⟩
  rw [commutatorElement_def, show MulAut.conj g * d.φ ^ a * (MulAut.conj h * d.φ ^ b) *
      (MulAut.conj g * d.φ ^ a)⁻¹ * (MulAut.conj h * d.φ ^ b)⁻¹ =
      (MulAut.conj g * d.φ ^ a * (MulAut.conj h * d.φ ^ b)) *
        (MulAut.conj h * d.φ ^ b * (MulAut.conj g * d.φ ^ a))⁻¹ by group, e1, e2, map_mul,
    map_inv]
  group

theorem even_and_exists_eq_conj_mul {f : ℕ} (hq : q = 2 ^ f) {β : MulAut X}
    (hβ : β ∉ (MulAut.conj : X →* MulAut X).range)
    (hβ2 : β ^ 2 ∈ (MulAut.conj : X →* MulAut X).range) :
    Even f ∧ ∃ g : X, β = MulAut.conj g * d.φ ^ (3 * f / 2) := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq β
  obtain ⟨g', hg'⟩ := d.exists_conj_mul_φ_pow_pow g k 2
  rw [hg'] at hβ2
  obtain ⟨h, hh⟩ := hβ2
  have h2k : d.φ ^ (k * 2) = MulAut.conj (g'⁻¹ * h) := by
    rw [map_mul, map_inv, hh]
    group
  have h2k1 := d.φ_pow_eq_conj _ _ h2k
  have hk1 : d.φ ^ k ≠ 1 := fun h1 => hβ ⟨g, by rw [h1, mul_one]⟩
  have hord := d.orderOf_φ_eq_three_mul hq
  have hdvd : 3 * f ∣ k * 2 := hord ▸ orderOf_dvd_of_pow_eq_one h2k1
  have hndvd : ¬ 3 * f ∣ k := fun h => hk1 (orderOf_dvd_iff_pow_eq_one.1 (hord ▸ h))
  have hf : Even f := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hndvd ((Nat.coprime_two_right.2 (Nat.odd_mul.2 ⟨by decide, hodd⟩)).dvd_of_dvd_mul_right
      hdvd)
  obtain ⟨e, rfl⟩ := hf
  refine ⟨⟨e, rfl⟩, g, ?_⟩
  have h3e : 3 * e ∣ k := by
    have : 3 * e * 2 ∣ k * 2 := by
      rw [show 3 * e * 2 = 3 * (e + e) by ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right two_pos this
  obtain ⟨m, rfl⟩ := h3e
  have hm : Odd m := by
    by_contra hm
    rw [Nat.not_odd_iff_even] at hm
    obtain ⟨j, rfl⟩ := hm
    exact hndvd ⟨j, by ring⟩
  obtain ⟨j, rfl⟩ := hm
  have h6 : d.φ ^ (3 * (e + e)) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  rw [show 3 * (e + e) / 2 = 3 * e by omega,
    show 3 * e * (2 * j + 1) = 3 * (e + e) * j + 3 * e by ring, pow_add, pow_mul, h6, one_pow,
    one_mul]

include d in
theorem mem_range_conj_of_pow_eq_one {f : ℕ} (hq : q = 2 ^ f) (hf : Odd f) {α : MulAut X}
    {m : ℕ} (h : α ^ 2 ^ m = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  obtain ⟨g', hg'⟩ := d.exists_conj_mul_φ_pow_pow g k (2 ^ m)
  rw [hg'] at h
  have h1 : d.φ ^ (k * 2 ^ m) = MulAut.conj g'⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h
  have h2 := d.φ_pow_eq_conj _ _ h1
  have hord := d.orderOf_φ_eq_three_mul hq
  have hdvd : 3 * f ∣ k * 2 ^ m := hord ▸ orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (3 * f) (2 ^ m) :=
    (Nat.coprime_two_right.2 (Nat.odd_mul.2 ⟨by decide, hf⟩)).pow_right m
  have hk : d.φ ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hcop.dvd_of_dvd_mul_right hdvd)
  exact ⟨g, by rw [hk, mul_one]⟩

include d in
theorem isCyclic_quotient_range_conj [(MulAut.conj : X →* MulAut X).range.Normal] :
    IsCyclic (MulAut X ⧸ (MulAut.conj : X →* MulAut X).range) := by
  refine isCyclic_of_surjective ((QuotientGroup.mk' _).comp (zpowers d.φ).subtype) fun y => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  refine ⟨⟨d.φ ^ k, npow_mem_zpowers _ _⟩, ?_⟩
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq]
  refine ⟨((d.φ ^ k)⁻¹) g, ?_⟩
  rw [← mulAut_mul_conj_mul_inv, inv_inv]
  group

section Sylow

variable {e : ℕ} (hq : q = 2 ^ (2 * e))
include hq

theorem orderOf_φ_pow_three_mul :
    orderOf (d.φ ^ (3 * e)) = 2 ∧ d.φ ^ (3 * e) ∉ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨h1, h2, -⟩ := d.yamada_3_13_1 (f := 2 * e) ⟨e, by ring⟩ hq
  rw [show 3 * (2 * e) / 2 = 3 * e by omega] at h1 h2
  exact ⟨h1, h2⟩

omit hq in
theorem zpowers_φ_pow_le_normalizer (k : ℕ) :
    zpowers (d.φ ^ k) ≤ normalizer ((d.S.map MulAut.conj : Subgroup (MulAut X)) :
      Set (MulAut X)) := by
  have := d.finite
  rw [zpowers_le]
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨g, hg, rfl⟩ := hn
  exact ⟨(d.φ ^ k) g, d.φ_pow_mem_rootChain k 6 hg, (mulAut_mul_conj_mul_inv _ g).symm⟩

theorem mem_sup_zpowers_φ_pow {x : MulAut X}
    (hx : x ∈ d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e))) :
    ∃ s ∈ d.S, x = MulAut.conj s ∨ x = MulAut.conj s * d.φ ^ (3 * e) := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (d.zpowers_φ_pow_le_normalizer (3 * e)), Set.mem_mul] at hx
  obtain ⟨_, ⟨s, hs, rfl⟩, z, hz, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have hk : (d.φ ^ (3 * e)) ^ k = (d.φ ^ (3 * e)) ^ (k % 2) := by
    rw [← zpow_mod_orderOf, (d.orderOf_φ_pow_three_mul hq).1]
    norm_cast
  refine ⟨s, hs, ?_⟩
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero, mul_one]
  · right
    rw [hk, h1, zpow_one]

theorem sup_zpowers_φ_pow_inf_range :
    (d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e))) ⊓ (MulAut.conj : X →* MulAut X).range =
      d.S.map MulAut.conj := by
  refine le_antisymm (fun x ⟨hxP, hxi⟩ => ?_)
    (le_inf le_sup_left (map_le_range _ _))
  obtain ⟨s, hs, rfl | rfl⟩ := d.mem_sup_zpowers_φ_pow hq hxP
  · exact ⟨s, hs, rfl⟩
  · exfalso
    obtain ⟨g, hg⟩ := hxi
    refine (d.orderOf_φ_pow_three_mul hq).2 ⟨s⁻¹ * g, ?_⟩
    rw [map_mul, hg, map_inv]
    group

theorem isPGroup_sup_zpowers_φ_pow :
    IsPGroup 2 ↥(d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 ↥(d.S.map (MulAut.conj : X →* MulAut X)) := by
    obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
    rw [← hP]
    exact P.isPGroup'.map _
  have hz : IsPGroup 2 ↥(zpowers (d.φ ^ (3 * e))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, (d.orderOf_φ_pow_three_mul hq).1,
      pow_one])
  exact hS.to_sup_of_normal_left' hz (d.zpowers_φ_pow_le_normalizer (3 * e))

theorem isSylowOf_sup_zpowers_φ_pow :
    CFSG.ABGLocalTools.IsSylowOf 2 (d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e)))
      ((MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := d.finite
  have := mulAutConj_range_normal (G := X)
  have hsup : (MulAut.conj : X →* MulAut X).range ⊔
      (d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e))) =
      (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)) := by
    rw [← sup_assoc, sup_eq_left.2 (map_le_range _ _)]
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sup_le_sup_right (map_le_range _ _) _, d.isPGroup_sup_zpowers_φ_pow hq, ?_⟩
  rw [← hsup, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal,
    ← Subgroup.inf_relIndex_right, d.sup_zpowers_φ_pow_inf_range hq,
    MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ d.mulAutConj_injective,
    Subgroup.relIndex_top_right]
  exact d.not_two_dvd_index_S

theorem exists_conj_le_sup_zpowers {R : Subgroup (MulAut X)} (hR : IsPGroup 2 R)
    (hRA : R ≤ (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e))) :
    ∃ a ∈ (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)),
      ∀ x ∈ R, a⁻¹ * x * a ∈ d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := d.finite
  obtain ⟨T₀, hT₀⟩ := (d.isSylowOf_sup_zpowers_φ_pow hq).exists_sylow_eq_subgroupOf
  obtain ⟨T, hT⟩ := (hR.comap_subtype
    (K := (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)))).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    ↥((MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e))) T₀ T
  refine ⟨a, a.2, fun x hx => ?_⟩
  have h1 : (⟨x, hRA hx⟩ : ↥((MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)))) ∈
      (T : Subgroup _) := hT hx
  rw [← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hT₀,
    Subgroup.mem_subgroupOf] at h1
  convert h1 using 1
  simp [MulAut.smul_def]

end Sylow

theorem comap_conj_props {k : ℕ} {s : X} {E : Subgroup (MulAut X)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hES : E ≤ d.S.map MulAut.conj)
    (hc : ∀ x ∈ E, x * (MulAut.conj s * d.φ ^ k) = MulAut.conj s * d.φ ^ k * x) :
    Nat.card ↥(E.comap (MulAut.conj : X →* MulAut X)) = Nat.card E ∧
      E.comap (MulAut.conj : X →* MulAut X) ≤ d.S ∧
      E.comap (MulAut.conj : X →* MulAut X) ≤ d.fixConj s k ∧
      (∀ x ∈ E.comap (MulAut.conj : X →* MulAut X),
        ∀ y ∈ E.comap (MulAut.conj : X →* MulAut X), x * y = y * x) ∧
      ∀ x ∈ E.comap (MulAut.conj : X →* MulAut X), x * x = 1 := by
  refine ⟨?_, fun g hg => ?_, fun g hg => ?_, fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [← Subgroup.card_map_of_injective d.mulAutConj_injective,
      Subgroup.map_comap_eq_self (hES.trans (map_le_range _ _))]
  · obtain ⟨g', hg', hgg'⟩ := hES hg
    rw [← d.mulAutConj_injective hgg']
    exact hg'
  · have h2 : MulAut.conj ((MulAut.conj s * d.φ ^ k) g) = MulAut.conj g := by
      rw [← mulAut_mul_conj_mul_inv, ← hc _ hg, mul_inv_cancel_right]
    exact d.mulAutConj_injective h2
  · refine d.mulAutConj_injective ?_
    rw [map_mul, map_mul]
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨_, hx⟩ : E) ⟨_, hy⟩)
  · exact d.mulAutConj_injective (by rw [map_mul, map_one, ← sq]; exact hE.2 _ hx)

theorem card_le_of_commute_conj_mul_φ_pow {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) {s : X}
    (hs : s ∈ d.S) {E : Subgroup (MulAut X)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hES : E ≤ d.S.map MulAut.conj)
    (hc : ∀ x ∈ E, x * (MulAut.conj s * d.φ ^ (3 * e)) = MulAut.conj s * d.φ ^ (3 * e) * x) :
    Nat.card E ≤ 2 ^ (9 * e) := by
  obtain ⟨hcard, hS, hP, hcomm, hsq⟩ := d.comap_conj_props hE hES hc
  rw [← hcard]
  exact d.card_le_of_le_fixConj he hq hs hS hP hcomm hsq

theorem card_lt_of_commute_φ_pow {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e))
    {E : Subgroup (MulAut X)} (hE : CFSG.Open.IsElemAbelian 2 E) (hES : E ≤ d.S.map MulAut.conj)
    (hc : ∀ x ∈ E, x * d.φ ^ (3 * e) = d.φ ^ (3 * e) * x) : Nat.card E < 2 ^ (9 * e) := by
  obtain ⟨hcard, hS, hP, hcomm, hsq⟩ := d.comap_conj_props (s := 1) hE hES fun x hx => by
    rw [map_one, one_mul]
    exact hc x hx
  rw [← hcard]
  exact d.card_lt_of_le_fixConj_one he hq hS hP hcomm hsq

include d in
theorem one_le_and_eq_two_pow_two_mul {e : ℕ} (hq : q = 2 ^ (e + e)) :
    1 ≤ e ∧ q = 2 ^ (2 * e) := by
  refine ⟨?_, by rw [hq, two_mul]⟩
  have h2 := d.two_le_q
  by_contra h0
  rw [hq, show e = 0 by omega] at h2
  norm_num at h2

include d in
theorem card_le_of_isElemAbelian_aut {f : ℕ} (hq : q = 2 ^ f) {E : Subgroup (MulAut X)}
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ q ^ 5 ∧ (q ^ 5 ≤ Nat.card E → E ≤ (MulAut.conj : X →* MulAut X).range) := by
  have := d.finite
  have := mulAutConj_range_normal (G := X)
  by_cases hEi : E ≤ (MulAut.conj : X →* MulAut X).range
  · refine ⟨?_, fun _ => hEi⟩
    have hcard : Nat.card ↥(E.comap (MulAut.conj : X →* MulAut X)) = Nat.card E := by
      rw [← Subgroup.card_map_of_injective d.mulAutConj_injective, Subgroup.map_comap_eq_self hEi]
    rw [← hcard]
    have := hE.1
    refine d.card_le_of_isElemAbelian ⟨⟨⟨fun a b => Subtype.ext (d.mulAutConj_injective ?_)⟩⟩,
      fun x hx => d.mulAutConj_injective ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (mul_comm' (⟨_, a.2⟩ : E) ⟨_, b.2⟩)
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  obtain ⟨y, hyE, hyi⟩ := Set.not_subset.1 hEi
  have hsqi : ∀ x ∈ E, x ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := fun x hx => by
    rw [hE.2 x hx]
    exact one_mem _
  obtain ⟨⟨e, rfl⟩, -⟩ := d.even_and_exists_eq_conj_mul hq hyi (hsqi y hyE)
  obtain ⟨he, hq'⟩ := d.one_le_and_eq_two_pow_two_mul hq
  have h3 : 3 * (e + e) / 2 = 3 * e := by omega
  have hEA : E ≤ (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)) := by
    intro x hx
    by_cases hxi : x ∈ (MulAut.conj : X →* MulAut X).range
    · exact mem_sup_left hxi
    · obtain ⟨-, g', hg'⟩ := d.even_and_exists_eq_conj_mul hq hxi (hsqi x hx)
      rw [hg', h3]
      exact mul_mem_sup ⟨g', rfl⟩ (mem_zpowers _)
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 _ x.2)⟩
  obtain ⟨a, -, ha⟩ := d.exists_conj_le_sup_zpowers hq' hE2 hEA
  obtain ⟨s, hs, hy' | hy'⟩ := d.mem_sup_zpowers_φ_pow hq' (ha y hyE)
  · exact absurd ⟨s, hy'.symm⟩ (inv_mul_mul_not_mem_range_conj hyi)
  obtain ⟨hord, -, hset, -⟩ := d.yamada_3_13_1 (f := 2 * e) ⟨e, two_mul e⟩ hq'
  rw [show 3 * (2 * e) / 2 = 3 * e by omega] at hord hset
  have hφ₀ : d.φ ^ (3 * e) * d.φ ^ (3 * e) = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
  have hφ₀inv : (d.φ ^ (3 * e))⁻¹ = d.φ ^ (3 * e) := inv_eq_of_mul_eq_one_right hφ₀
  have hmem : a⁻¹ * y * a ∈ {β : MulAut X |
      (∃ s ∈ d.S, β = d.φ ^ (3 * e) * MulAut.conj s) ∧ orderOf β = 2} := by
    refine ⟨⟨(d.φ ^ (3 * e)) s, d.φ_pow_mem_rootChain _ 6 hs, ?_⟩, ?_⟩
    · rw [hy', ← mulAut_mul_conj_mul_inv, hφ₀inv]
      calc MulAut.conj s * d.φ ^ (3 * e) =
            d.φ ^ (3 * e) * d.φ ^ (3 * e) * MulAut.conj s * d.φ ^ (3 * e) := by rw [hφ₀, one_mul]
        _ = _ := by group
    · refine orderOf_eq_prime ?_ fun h1 => inv_mul_mul_not_mem_range_conj hyi (h1 ▸ one_mem _)
      rw [show (a⁻¹ * y * a) ^ 2 = a⁻¹ * y ^ 2 * a by rw [sq, sq]; group, hE.2 y hyE]
      group
  rw [hset] at hmem
  obtain ⟨t, ht, hyt⟩ := hmem
  have hconjP : MulAut.conj t ∈ d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e)) :=
    mem_sup_left ⟨t, ht, rfl⟩
  have hb : ∀ x ∈ E, (a * (MulAut.conj t)⁻¹)⁻¹ * x * (a * (MulAut.conj t)⁻¹) ∈
      d.S.map MulAut.conj ⊔ zpowers (d.φ ^ (3 * e)) := fun x hx => by
    rw [show (a * (MulAut.conj t)⁻¹)⁻¹ * x * (a * (MulAut.conj t)⁻¹) =
      MulAut.conj t * (a⁻¹ * x * a) * (MulAut.conj t)⁻¹ by group]
    exact mul_mem (mul_mem hconjP (ha x hx)) (inv_mem hconjP)
  set b := a * (MulAut.conj t)⁻¹ with hbdef
  have hby : b⁻¹ * y * b = d.φ ^ (3 * e) := by
    rw [hbdef, show (a * (MulAut.conj t)⁻¹)⁻¹ * y * (a * (MulAut.conj t)⁻¹) =
      MulAut.conj t * (a⁻¹ * y * a) * (MulAut.conj t)⁻¹ by group, hyt]
    group
  have hcb : ∀ x, (MulAut.conj b⁻¹).toMonoidHom x = b⁻¹ * x * b := fun x => by simp
  have hE' := CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj b⁻¹).toMonoidHom
  have hE'P : E.map (MulAut.conj b⁻¹).toMonoidHom ⊓ (MulAut.conj : X →* MulAut X).range ≤
      d.S.map MulAut.conj := by
    rw [← d.sup_zpowers_φ_pow_inf_range hq']
    refine inf_le_inf_right _ ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hcb]
    exact hb x hx
  have hE'el : CFSG.Open.IsElemAbelian 2
      (E.map (MulAut.conj b⁻¹).toMonoidHom ⊓ (MulAut.conj : X →* MulAut X).range) := by
    have := hE'.1
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => hE'.2 x (mem_inf.1 hx).1⟩
    have h := congrArg Subtype.val
      (mul_comm' (⟨u, (mem_inf.1 u.2).1⟩ : E.map (MulAut.conj b⁻¹).toMonoidHom)
        ⟨v, (mem_inf.1 v.2).1⟩)
    exact Subtype.ext h
  have hφE : d.φ ^ (3 * e) ∈ E.map (MulAut.conj b⁻¹).toMonoidHom := hby ▸ ⟨y, hyE, hcb y⟩
  have hc : ∀ x ∈ E.map (MulAut.conj b⁻¹).toMonoidHom ⊓ (MulAut.conj : X →* MulAut X).range,
      x * d.φ ^ (3 * e) = d.φ ^ (3 * e) * x := by
    intro x hx
    have := hE'.1
    exact congrArg Subtype.val (mul_comm' (⟨x, (mem_inf.1 hx).1⟩ :
      E.map (MulAut.conj b⁻¹).toMonoidHom) ⟨_, hφE⟩)
  have hlt := d.card_lt_of_commute_φ_pow he hq' hE'el hE'P hc
  have := d.isCyclic_quotient_range_conj
  have h2 := SymplecticFourRankThompson.card_le_two_mul_card_inf
    (MulAut.conj : X →* MulAut X).range (E.map (MulAut.conj b⁻¹).toMonoidHom) fun x hx => by
      rw [← sq]
      exact hE'.2 x hx
  rw [card_map_of_injective (MulAut.conj b⁻¹).injective] at h2
  have hlt' : Nat.card E < q ^ 5 := by
    calc Nat.card E < 2 * 2 ^ (9 * e) := h2.trans_lt (by omega)
      _ ≤ q ^ 5 := by
          rw [hq', ← pow_mul, ← pow_succ']
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨hlt'.le, fun h => absurd h (not_le.2 hlt')⟩

include d in
theorem le_range_conj_of_isMulCommutative {f : ℕ} (hq : q = 2 ^ f) {V E : Subgroup (MulAut X)}
    (hV2 : IsPGroup 2 V) (hV : IsMulCommutative V) (hEV : E ≤ V)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : q ^ 5 ≤ Nat.card E) :
    V ≤ (MulAut.conj : X →* MulAut X).range := by
  classical
  have := d.finite
  have hEi := (d.card_le_of_isElemAbelian_aut hq hE).2 hcard
  by_contra hVi
  obtain ⟨v, hvV, hvi⟩ := Set.not_subset.1 hVi
  obtain ⟨m, hm⟩ := hV2 ⟨v, hvV⟩
  have hex : ∃ n, v ^ 2 ^ n ∈ (MulAut.conj : X →* MulAut X).range := ⟨m, by
    rw [show v ^ 2 ^ m = 1 from congrArg Subtype.val hm]
    exact one_mem _⟩
  have hn₀ := Nat.find_spec hex
  have hn₀0 : Nat.find hex ≠ 0 := fun h => hvi (by rwa [h, pow_zero, pow_one] at hn₀)
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hβi : v ^ 2 ^ n ∉ (MulAut.conj : X →* MulAut X).range :=
    Nat.find_min hex (by omega : n < Nat.find hex)
  have hβ2 : (v ^ 2 ^ n) ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
    rw [← pow_mul, ← pow_succ]
    rwa [hn] at hn₀
  have hβV : v ^ 2 ^ n ∈ V := pow_mem hvV _
  obtain ⟨⟨e, rfl⟩, g, hg⟩ := d.even_and_exists_eq_conj_mul hq hβi hβ2
  obtain ⟨he, hq'⟩ := d.one_le_and_eq_two_pow_two_mul hq
  rw [show 3 * (e + e) / 2 = 3 * e by omega] at hg
  have hRV : E ⊔ zpowers (v ^ 2 ^ n) ≤ V := sup_le hEV (zpowers_le.2 hβV)
  have hRA : E ⊔ zpowers (v ^ 2 ^ n) ≤
      (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)) :=
    sup_le (hEi.trans le_sup_left) (zpowers_le.2 (by
      rw [hg]
      exact mul_mem_sup ⟨g, rfl⟩ (mem_zpowers _)))
  obtain ⟨a, -, ha⟩ := d.exists_conj_le_sup_zpowers hq' (hV2.to_le hRV) hRA
  have hca : ∀ x, (MulAut.conj a⁻¹).toMonoidHom x = a⁻¹ * x * a := fun x => by simp
  obtain ⟨s, hs, hβ' | hβ'⟩ := d.mem_sup_zpowers_φ_pow hq' (ha _ (mem_sup_right (mem_zpowers _)))
  · exact absurd ⟨s, hβ'.symm⟩ (inv_mul_mul_not_mem_range_conj hβi)
  have hE'S : E.map (MulAut.conj a⁻¹).toMonoidHom ≤ d.S.map MulAut.conj := by
    rw [← d.sup_zpowers_φ_pow_inf_range hq']
    rintro _ ⟨x, hx, rfl⟩
    rw [hca]
    exact ⟨ha x (mem_sup_left hx), inv_mul_mul_mem_range_conj (hEi hx)⟩
  have hc : ∀ x ∈ E.map (MulAut.conj a⁻¹).toMonoidHom,
      x * (MulAut.conj s * d.φ ^ (3 * e)) = MulAut.conj s * d.φ ^ (3 * e) * x := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hca, ← hβ']
    have hxβ : x * v ^ 2 ^ n = v ^ 2 ^ n * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hEV hx⟩ : V) ⟨_, hβV⟩)
    calc a⁻¹ * x * a * (a⁻¹ * v ^ 2 ^ n * a) = a⁻¹ * (x * v ^ 2 ^ n) * a := by group
      _ = a⁻¹ * (v ^ 2 ^ n * x) * a := by rw [hxβ]
      _ = a⁻¹ * v ^ 2 ^ n * a * (a⁻¹ * x * a) := by group
  have hb := d.card_le_of_commute_conj_mul_φ_pow he hq' hs
    (CFSG.SectionRank.isElemAbelian_map hE _) hE'S hc
  rw [card_map_of_injective (MulAut.conj a⁻¹).injective] at hb
  have hlt : 2 ^ (9 * e) < q ^ 5 := by
    rw [hq', ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem inf_range_conj_eq_of_isPGroup {Q : Subgroup (MulAut X)} (hQ : IsPGroup 2 Q)
    (hSQ : d.S.map MulAut.conj ≤ Q) :
    Q ⊓ (MulAut.conj : X →* MulAut X).range = d.S.map MulAut.conj := by
  refine le_antisymm ?_ (le_inf hSQ (map_le_range _ _))
  have hT2 : IsPGroup 2 ↥((Q ⊓ (MulAut.conj : X →* MulAut X).range).comap MulAut.conj) :=
    (hQ.to_le inf_le_left).comap_of_injective _ d.mulAutConj_injective
  have hST : d.S ≤ (Q ⊓ (MulAut.conj : X →* MulAut X).range).comap MulAut.conj :=
    fun x hx => ⟨hSQ ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hTS := P.is_maximal' hT2 (hP ▸ hST)
  rw [hP] at hTS
  rintro x ⟨hxQ, g, rfl⟩
  exact ⟨g, hTS ▸ (⟨hxQ, ⟨g, rfl⟩⟩ :
    g ∈ (Q ⊓ (MulAut.conj : X →* MulAut X).range).comap MulAut.conj), rfl⟩

theorem S_le_sup_eU : d.S ≤ d.eU₁Y ⊔ d.eU₂U₃V ⊔ d.eW := by
  rw [S, sixClosure, closure_le]
  rintro g (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
  · have h := mem_range_tripleHom d.x₁_add d.x₅_add d.x₆_add d.commute₁₅ d.commute₁₆
      d.commute₅₆ a 0 0
    rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one] at h
    exact mem_sup_left (mem_sup_left h)
  · have h := mem_range_tripleHom d.x₂_add d.x₃_add d.x₆_add d.commute₂₃ d.commute₂₆
      d.commute₃₆ a 0 0
    rw [d.x₃_zero, d.x₆_zero, mul_one, mul_one] at h
    exact mem_sup_left (mem_sup_right h)
  · have h := mem_range_tripleHom d.x₂_add d.x₃_add d.x₆_add d.commute₂₃ d.commute₂₆
      d.commute₃₆ 0 a 0
    rw [d.x₂_zero, d.x₆_zero, one_mul, mul_one] at h
    exact mem_sup_left (mem_sup_right h)
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ a 0 0
    rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one] at h
    exact mem_sup_right h
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ 0 a 0
    rw [d.x₄_zero, d.x₆_zero, one_mul, mul_one] at h
    exact mem_sup_right h
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ 0 0 a
    rw [d.x₄_zero, d.x₅_zero, one_mul, one_mul] at h
    exact mem_sup_right h

theorem yamada_3_14 [Finite X] {f : ℕ} (hq : q = 2 ^ f) {Q : Subgroup (MulAut X)}
    (hQ : IsPGroup 2 Q) (hSQ : d.S.map MulAut.conj ≤ Q) :
    (∀ V : Subgroup (MulAut X), V ≤ Q → IsMulCommutative V → 5 * f ≤ CFSG.Open.pRank 2 V →
        V ≤ d.S.map MulAut.conj) ∧
      CFSG.Open.pRank 2 Q = 5 * f ∧
      (⨆ (A : Subgroup (MulAut X)) (_ : A ≤ Q ∧ IsMulCommutative A ∧
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 Q), A) = d.S.map MulAut.conj ∧
      (CFSG.LocalAnalysis.rankThompson ↥Q).map Q.subtype = d.S.map MulAut.conj := by
  have hq5 : q ^ 5 = 2 ^ (5 * f) := by rw [hq, ← pow_mul, mul_comm]
  have hkey : ∀ V : Subgroup (MulAut X), V ≤ Q → IsMulCommutative V →
      5 * f ≤ CFSG.Open.pRank 2 V → V ≤ d.S.map MulAut.conj := by
    intro V hVQ hV hrV
    obtain ⟨E, hEV, hE, hcE⟩ := CFSG.SectionRank.exists_pRank one_lt_two V
    have hVi := d.le_range_conj_of_isMulCommutative hq (hQ.to_le hVQ) hV hEV hE (by
      rw [hcE, hq5]
      exact Nat.pow_le_pow_right two_pos hrV)
    rw [← d.inf_range_conj_eq_of_isPGroup hQ hSQ]
    exact le_inf hVQ hVi
  have hW := CFSG.SectionRank.isElemAbelian_map d.isElemAbelian_eW (MulAut.conj : X →* MulAut X)
  have hcW : Nat.card ↥(d.eW.map (MulAut.conj : X →* MulAut X)) = 2 ^ (5 * f) := by
    rw [card_map_of_injective d.mulAutConj_injective, d.card_eW, hq5]
  have hWQ : d.eW.map (MulAut.conj : X →* MulAut X) ≤ Q := (map_mono d.eU_le_S.2.2).trans hSQ
  have hrQ : CFSG.Open.pRank 2 Q = 5 * f := by
    refine le_antisymm (CFSG.SectionRank.pRank_le one_lt_two fun E _ hE => ?_)
      (CFSG.SectionRank.le_pRank one_lt_two hWQ hW hcW)
    rw [← hq5]
    exact (d.card_le_of_isElemAbelian_aut hq hE).1
  have hgen : d.S.map MulAut.conj ≤ ⨆ (E : Subgroup (MulAut X)) (_ : E ≤ Q ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (5 * f)), E := by
    have hmem : ∀ E : Subgroup X, E ≤ d.S → CFSG.Open.IsElemAbelian 2 E → Nat.card E = q ^ 5 →
        E.map (MulAut.conj : X →* MulAut X) ≤ ⨆ (E : Subgroup (MulAut X)) (_ : E ≤ Q ∧
          CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (5 * f)), E := fun E hES hE hc =>
      le_iSup₂_of_le (E.map MulAut.conj) ⟨(map_mono hES).trans hSQ,
        CFSG.SectionRank.isElemAbelian_map hE _,
        by rw [card_map_of_injective d.mulAutConj_injective, hc, hq5]⟩ le_rfl
    refine (map_mono d.S_le_sup_eU).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (sup_le (hmem _ d.eU_le_S.1 d.isElemAbelian_eU₁Y d.card_eU₁Y)
      (hmem _ d.eU_le_S.2.1 d.isElemAbelian_eU₂U₃V d.card_eU₂U₃V))
      (hmem _ d.eU_le_S.2.2 d.isElemAbelian_eW d.card_eW)
  obtain ⟨h1, h2⟩ := iSup_eq_and_rankThompson_eq_of_forall hQ hrQ hkey hgen
  exact ⟨hkey, hrQ, h1, h2⟩

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
