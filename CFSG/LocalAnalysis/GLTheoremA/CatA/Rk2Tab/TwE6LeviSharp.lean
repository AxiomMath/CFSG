module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwistSwapRank
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517A
public import CFSG.GroupTheory.ProjectiveElemAbelianRank
public import CFSG.LieType.SeitzGeneration.OrthHyperExSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviChar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviSubsys
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA

noncomputable section

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA CFSG.RankThree.E6
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.SeitzReduction.TwistedE6Pilot


abbrev e6NodeGroup (F : Type) [Field F]
    (S : Set (Fin Tag.E6.rank)) : Subgroup (ModGL Tag.E6 F) :=
  subsystemGroup Tag.E6 F S

abbrev e6TwGroup (F : Type) [Field F]
    (S : Set (Fin TwistTag.E6.tag.rank)) :
    Subgroup (ModGL TwistTag.E6.tag F) :=
  subsystemGroup TwistTag.E6.tag F S

private theorem one_le_exponent_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ n := by
  have h2 : 1 ≤ n * 2 :=
    CFSG.SeitzReduction.LinearPilot.one_le_of_card_eq_two_pow (K := F) (f := n * 2)
      (by rw [hF, pow_mul])
  omega

private theorem charP_two_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 :=
  CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hn hF

private theorem dvd_card_sub_one_of_dvd_two_pow_add_one {F : Type} [Field F] [Finite F]
    {n p : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    p ∣ Nat.card F - 1 := by
  rw [hF]
  exact CFSG.LieType.SeitzGeneration.dvd_sq_sub_one_of_dvd_add_one hpq

theorem projective_rank_bound_of_dvd_card_sub_one {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hrF : p ∣ Nat.card F - 1) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} := by
  intro V _ _ _ R hR hcomm hpow
  exact CFSG.GroupTheory.card_le_pow_finrank_sub_one_mul_card_scalar hp hp2 hrF R hR hcomm hpow

private noncomputable def twistEndE6 {F : Type} [Field F] (σ : F →+* F) :
    ModGL Tag.E6 F →* ModGL Tag.E6 F :=
  { toFun := fun g => twistHom TwistTag.E6 F σ g
    map_one' := map_one _
    map_mul' := map_mul _ }

private theorem twistEndE6_generators {F : Type} [Field F] (σ : F →+* F) :
    (∀ (i : Fin Tag.E6.rank) (c : F),
      twistEndE6 σ (xUnit Tag.E6 F i c) =
        xUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c)) ∧
    (∀ (i : Fin Tag.E6.rank) (c : F),
      twistEndE6 σ (yUnit Tag.E6 F i c) =
        yUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c)) := by
  refine ⟨?_, ?_⟩ <;> intro i c
  · exact twistHom_xUnit TwistTag.E6 F σ i c
  · exact twistHom_yUnit TwistTag.E6 F σ i c

private noncomputable def twistEndTw {F : Type} [Field F] (σ : F →+* F) :
    ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag F :=
  twistHom TwistTag.E6 F σ

private theorem twistEndTw_generators {F : Type} [Field F] (σ : F →+* F) :
    (∀ (i : Fin TwistTag.E6.tag.rank) (c : F),
      twistEndTw σ (xUnit TwistTag.E6.tag F i c) =
        xUnit TwistTag.E6.tag F (TwistTag.E6.perm i) (σ c)) ∧
    (∀ (i : Fin TwistTag.E6.tag.rank) (c : F),
      twistEndTw σ (yUnit TwistTag.E6.tag F i c) =
        yUnit TwistTag.E6.tag F (TwistTag.E6.perm i) (σ c)) := by
  refine ⟨?_, ?_⟩ <;> intro i c
  · exact twistHom_xUnit TwistTag.E6 F σ i c
  · exact twistHom_yUnit TwistTag.E6 F σ i c

abbrev twE6Node0 : Set (Fin TwistTag.E6.tag.rank) := {e6Index 0}

abbrev twE6Node5 : Set (Fin TwistTag.E6.tag.rank) := {e6Index 5}

abbrev twE6Node1 : Set (Fin TwistTag.E6.tag.rank) := {e6Index 1}

abbrev twE6Node3 : Set (Fin TwistTag.E6.tag.rank) := {e6Index 3}

private theorem mapsTo_subsystemGroup_of_mapsTo {K : Type} [Field K]
    (φ : ModGL Tag.E6 K →* ModGL Tag.E6 K) (σ : K →+* K)
    (hx : ∀ (i : Fin Tag.E6.rank) (c : K),
      φ (xUnit Tag.E6 K i c) =
        xUnit Tag.E6 K (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c))
    (hy : ∀ (i : Fin Tag.E6.rank) (c : K),
      φ (yUnit Tag.E6 K i c) =
        yUnit Tag.E6 K (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c))
    {S T : Set (Fin Tag.E6.rank)}
    (h : ∀ i ∈ S, (TwistTag.E6.perm i : Fin Tag.E6.rank) ∈ T)
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K S) :
    φ g ∈ subsystemGroup Tag.E6 K T := by
  have hgen : {x : ModGL Tag.E6 K | ∃ i ∈ S, ∃ c : K,
      x = xUnit Tag.E6 K i c ∨ x = yUnit Tag.E6 K i c} ⊆
      Subgroup.comap φ (subsystemGroup Tag.E6 K T) := by
    rintro g ⟨i, hi, c, rfl | rfl⟩
    · change xUnit Tag.E6 K i c ∈ Subgroup.comap φ (subsystemGroup Tag.E6 K T)
      rw [Subgroup.mem_comap, hx i c]
      exact xUnit_mem_subsystemGroup (h i hi) (σ c)
    · change yUnit Tag.E6 K i c ∈ Subgroup.comap φ (subsystemGroup Tag.E6 K T)
      rw [Subgroup.mem_comap, hy i c]
      exact yUnit_mem_subsystemGroup (h i hi) (σ c)
  rw [subsystemGroup] at hg
  exact (Subgroup.closure_le (Subgroup.comap φ (subsystemGroup Tag.E6 K T))).2 hgen hg

theorem twE6A2A1_le_sup {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 3}) :
    E ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) ⊔
      (e6NodeGroup F support13 ⊔ e6NodeGroup F support56) := by
  refine hE.trans ?_
  change subsystemGroup Tag.E6 F {i : Fin Tag.E6.rank | i.val ≠ 3} ≤
    e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) ⊔
      (e6NodeGroup F support13 ⊔ e6NodeGroup F support56)
  rw [← CFSG.StandardType.F4Rest.subsystemGroup_union,
    ← CFSG.StandardType.F4Rest.subsystemGroup_union]
  refine CFSG.StandardType.F4Rest.subsystemGroup_mono ?_
  intro i hi
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hi ⊢
  fin_cases i <;> simp [support13, support56] at hi ⊢ <;> decide

private theorem A2A1_comm_N1_N2 {F : Type} [Field F] :
    ∀ x ∈ e6NodeGroup F support13, ∀ y ∈ e6NodeGroup F support56, Commute x y :=
  fun x hx y hy => commute_Q₁_Q₂ hx hy

private theorem A2A1_comm_L1_N1 {F : Type} [Field F] :
    ∀ x ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)),
      ∀ y ∈ e6NodeGroup F support13, Commute x y := by
  have h := commute_subsystemGroup (τ := Tag.E6) (K := F)
    (A := ({e6Index 1} : Set (Fin Tag.E6.rank))) (B := support13) ?_
  · intro x hx y hy
    exact h x hx y hy
  · intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    rw [mem_support13] at hb
    rcases hb with rfl | rfl
    · exact e6_pair_support 1 0 (by decide) (by decide +kernel)
    · exact e6_pair_support 1 2 (by decide) (by decide +kernel)

private theorem A2A1_comm_L1_N2 {F : Type} [Field F] :
    ∀ x ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)),
      ∀ y ∈ e6NodeGroup F support56, Commute x y := by
  have h := commute_subsystemGroup (τ := Tag.E6) (K := F)
    (A := ({e6Index 1} : Set (Fin Tag.E6.rank))) (B := support56) ?_
  · intro x hx y hy
    exact h x hx y hy
  · intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    rw [mem_support56] at hb
    rcases hb with rfl | rfl
    · exact e6_pair_support 1 4 (by decide) (by decide +kernel)
    · exact e6_pair_support 1 5 (by decide) (by decide +kernel)

private theorem A2A1_comm_L1_N {F : Type} [Field F] :
    ∀ x ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)),
      ∀ y ∈ e6NodeGroup F support13 ⊔ e6NodeGroup F support56, Commute x y := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => (A2A1_comm_N1_N2 a ha b hb).eq) hy
  exact (A2A1_comm_L1_N1 x hx a ha).mul_right (A2A1_comm_L1_N2 x hx b hb)

private theorem A2A1_inf_L1_N_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2] :
    e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) ⊓
      (e6NodeGroup F support13 ⊔ e6NodeGroup F support56) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxT : x ∈ e6TwGroup F ({e6Index 1} : Set (Fin TwistTag.E6.tag.rank)) := by
    have hxL1 : x ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) := hx.1
    change x ∈ subsystemGroup Tag.E6 F ({e6Index 1} : Set (Fin Tag.E6.rank)) at hxL1 ⊢
    exact hxL1
  exact eq_one_of_mem_subsystemGroup_singleton_of_centralizes (F := F)
    (i := (e6Index 1 : Fin TwistTag.E6.tag.rank)) hxT
    (fun y hy => by
      change y ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) at hy
      exact (A2A1_comm_L1_N y hy x hx.2).symm)

private theorem A2A1_N1_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ G : Subgroup (ModGL Tag.E6 F), G ≤ e6NodeGroup F support13 →
      IsElemAbelian p G → Nat.card G ≤ p ^ 2 := by
  intro G hG hGel
  exact card_le_pow_two_subsystemGroup_e6pair (F := F) hp hp2
    (i := e6Index 0) (j := e6Index 2)
    (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hG hGel

private theorem A2A1_L1_bound {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}) :
    ∀ G : Subgroup (ModGL Tag.E6 F), G ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) →
      IsElemAbelian p G → Nat.card G ≤ p ^ 1 := by
  intro G hG hGel
  exact card_le_pow_one_subsystemGroup_e6node (F := F) (n := n) hF hp hp2 hPRL
    (e6Index 1) hG hGel

private theorem A2A1_twist_N1 {F : Type} [Field F] [Finite F] (σ : F →+* F)
    {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφx : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (xUnit Tag.E6 F i c) =
        xUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c))
    (hφy : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (yUnit Tag.E6 F i c) =
        yUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c)) :
    ∀ x ∈ e6NodeGroup F support13, φ x ∈ e6NodeGroup F support56 := by
  have hmap : ∀ i ∈ (support13 : Set (Fin Tag.E6.rank)),
      (TwistTag.E6.perm i : Fin Tag.E6.rank) ∈ support56 := by
    intro i hi
    rw [mem_support13] at hi
    rcases hi with rfl | rfl
    · have hp' : (TwistTag.E6.perm (e6Index 0) : Fin Tag.E6.rank) = e6Index 5 := by
        apply Fin.ext
        decide
      rw [hp']
      exact (mem_support56 (e6Index 5)).2 (Or.inr rfl)
    · have hp' : (TwistTag.E6.perm (e6Index 2) : Fin Tag.E6.rank) = e6Index 4 := by
        apply Fin.ext
        decide
      rw [hp']
      exact (mem_support56 (e6Index 4)).2 (Or.inl rfl)
  intro x hx
  exact mapsTo_subsystemGroup_of_mapsTo φ σ hφx hφy hmap hx

private theorem A2A1_twist_N2 {F : Type} [Field F] [Finite F] (σ : F →+* F)
    {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφx : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (xUnit Tag.E6 F i c) =
        xUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c))
    (hφy : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (yUnit Tag.E6 F i c) =
        yUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c)) :
    ∀ x ∈ e6NodeGroup F support56, φ x ∈ e6NodeGroup F support13 := by
  have hmap : ∀ i ∈ (support56 : Set (Fin Tag.E6.rank)),
      (TwistTag.E6.perm i : Fin Tag.E6.rank) ∈ support13 := by
    intro i hi
    rw [mem_support56] at hi
    rcases hi with rfl | rfl
    · have hp' : (TwistTag.E6.perm (e6Index 4) : Fin Tag.E6.rank) = e6Index 2 := by
        apply Fin.ext
        decide
      rw [hp']
      exact (mem_support13 (e6Index 2)).2 (Or.inr rfl)
    · have hp' : (TwistTag.E6.perm (e6Index 5) : Fin Tag.E6.rank) = e6Index 0 := by
        apply Fin.ext
        decide
      rw [hp']
      exact (mem_support13 (e6Index 0)).2 (Or.inl rfl)
  intro x hx
  exact mapsTo_subsystemGroup_of_mapsTo φ σ hφx hφy hmap hx

private theorem A2A1_twist_N {F : Type} [Field F] [Finite F] (σ : F →+* F)
    {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφN1 : ∀ x ∈ e6NodeGroup F support13, φ x ∈ e6NodeGroup F support56)
    (hφN2 : ∀ x ∈ e6NodeGroup F support56, φ x ∈ e6NodeGroup F support13) :
    ∀ x ∈ e6NodeGroup F support13 ⊔ e6NodeGroup F support56,
      φ x ∈ e6NodeGroup F support13 ⊔ e6NodeGroup F support56 := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => (A2A1_comm_N1_N2 a ha b hb).eq) hx
  rw [map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hφN1 a ha))
    (Subgroup.mem_sup_left (hφN2 b hb))

private theorem A2A1_twist_L1 {F : Type} [Field F] [Finite F] (σ : F →+* F)
    {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφx : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (xUnit Tag.E6 F i c) =
        xUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c))
    (hφy : ∀ (i : Fin Tag.E6.rank) (c : F),
      φ (yUnit Tag.E6 F i c) =
        yUnit Tag.E6 F (TwistTag.E6.perm i : Fin Tag.E6.rank) (σ c)) :
    ∀ y ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)),
      φ y ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) := by
  have hmap : ∀ i ∈ ({e6Index 1} : Set (Fin Tag.E6.rank)),
      (TwistTag.E6.perm i : Fin Tag.E6.rank) ∈ ({e6Index 1} : Set (Fin Tag.E6.rank)) := by
    intro i hi
    simp only [Set.mem_singleton_iff] at hi ⊢
    rw [hi]
    exact show (TwistTag.E6.perm (e6Index 1) : Fin Tag.E6.rank) = e6Index 1 from by
      apply Fin.ext
      decide
  intro y hy
  exact mapsTo_subsystemGroup_of_mapsTo φ σ hφx hφy hmap hy

private theorem A2A1_swap_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφN1 : ∀ x ∈ e6NodeGroup F support13, φ x ∈ e6NodeGroup F support56)
    (hφN2 : ∀ x ∈ e6NodeGroup F support56, φ x ∈ e6NodeGroup F support13)
    (hN1 : ∀ G : Subgroup (ModGL Tag.E6 F), G ≤ e6NodeGroup F support13 →
      IsElemAbelian p G → Nat.card G ≤ p ^ 2)
    : ∀ G : Subgroup (ModGL Tag.E6 F),
      G ≤ e6NodeGroup F support13 ⊔ e6NodeGroup F support56 →
      IsElemAbelian p G →
      (∀ e ∈ G, φ e = e) → Nat.card G ≤ p ^ 2 := by
  intro G hG hGel hGfix
  refine card_le_of_le_sup_of_swap (G := ModGL Tag.E6 F) (p := p) (k := 2) hp
    (X := e6NodeGroup F support13) (Y := e6NodeGroup F support56)
    A2A1_comm_N1_N2 ?_ φ hφN1 hφN2 hN1 hG hGel hGfix
  have hdvd : Nat.card ↥(e6NodeGroup F support13 ⊓ e6NodeGroup F support56) ∣ 3 :=
    card_inf_A2_A2_dvd_three (F := F)
  have h3 : p ≠ 3 := by omega
  intro hd
  rcases (Nat.dvd_prime Nat.prime_three).1 (hd.trans hdvd) with h | h
  · exact hp.ne_one h
  · exact h3 h

private theorem A2A1_fixed_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) {φ : ModGL Tag.E6 F →* ModGL Tag.E6 F}
    (hφN : ∀ x ∈ e6NodeGroup F support13 ⊔ e6NodeGroup F support56,
      φ x ∈ e6NodeGroup F support13 ⊔ e6NodeGroup F support56)
    (hφL1 : ∀ y ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)),
      φ y ∈ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)))
    (hN : ∀ G : Subgroup (ModGL Tag.E6 F),
      G ≤ e6NodeGroup F support13 ⊔ e6NodeGroup F support56 →
      IsElemAbelian p G → (∀ e ∈ G, φ e = e) → Nat.card G ≤ p ^ 2)
    (hL1 : ∀ G : Subgroup (ModGL Tag.E6 F),
      G ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) →
      IsElemAbelian p G → (∀ e ∈ G, φ e = e) → Nat.card G ≤ p ^ 1)
    {G : Subgroup (ModGL Tag.E6 F)}
    (hG : G ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) ⊔
      (e6NodeGroup F support13 ⊔ e6NodeGroup F support56))
    (hGel : IsElemAbelian p G)
    (hGfix : ∀ e ∈ G, φ e = e) : Nat.card G ≤ p ^ (2 + 1) := by
  have hinf : ¬ p ∣ Nat.card ↥
      ((e6NodeGroup F support13 ⊔ e6NodeGroup F support56) ⊓
        e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank))) := by
    rw [inf_comm, A2A1_inf_L1_N_eq_bot, Subgroup.card_bot]
    exact hp.not_dvd_one
  exact card_le_of_le_sup_of_fixed (G := ModGL Tag.E6 F) (p := p) (k₁ := 2) (k₂ := 1) hp
    (X := e6NodeGroup F support13 ⊔ e6NodeGroup F support56)
    (W := e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)))
    (fun a ha b hb => (A2A1_comm_L1_N b hb a ha).symm) hinf φ hφN hφL1 hN hL1
    (by rwa [sup_comm]) hGel hGfix

private theorem A2A1_core
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 1 ≤ n := one_le_exponent_of_card_sq hF
  haveI : CharP F 2 := charP_two_of_card_sq hn hF
  have hrF : p ∣ Nat.card F - 1 := dvd_card_sub_one_of_dvd_two_pow_add_one hF hpq
  have hPRL := projective_rank_bound_of_dvd_card_sub_one hp hp2 hrF
  have hsub : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 3} :=
    le_subsystemGroup_of_le_graphFixedParabolicLevi_A2A1 hF σ hσ hp hp2 hpq hE hEel
  let E' : Subgroup (ModGL Tag.E6 F) := E
  let φ : ModGL Tag.E6 F →* ModGL Tag.E6 F := twistEndE6 σ.toRingHom
  have hE'el : IsElemAbelian p E' := hEel
  obtain ⟨hφx, hφy⟩ := twistEndE6_generators σ.toRingHom
  have hfix : ∀ e ∈ E', φ e = e := by
    intro e he
    exact ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom)).1
        (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
          (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
            (J := twE6MaxA2A1) (hE he)))).2
  have hE1 : E' ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) ⊔
      (e6NodeGroup F support13 ⊔ e6NodeGroup F support56) :=
    twE6A2A1_le_sup (F := F) hsub
  have hN1 := A2A1_twist_N1 (F := F) σ (φ := φ) hφx hφy
  have hN2 := A2A1_twist_N2 (F := F) σ (φ := φ) hφx hφy
  have hN := A2A1_twist_N (F := F) σ (φ := φ) hN1 hN2
  have hL1 := A2A1_twist_L1 (F := F) σ (φ := φ) hφx hφy
  have hN_bound := A2A1_swap_bound (F := F) hp hp5 (φ := φ) hN1 hN2
    (A2A1_N1_bound (F := F) hp hp2)
  have hL1_bound := A2A1_L1_bound (F := F) hF hp hp2 hPRL
  have hL1_fixed : ∀ G : Subgroup (ModGL Tag.E6 F),
      G ≤ e6NodeGroup F ({e6Index 1} : Set (Fin Tag.E6.rank)) →
      IsElemAbelian p G → (∀ e ∈ G, φ e = e) → Nat.card G ≤ p ^ 1 :=
    fun G hG hGel _ => hL1_bound G hG hGel
  have hE0 := A2A1_fixed_bound (F := F) hp (φ := φ) (G := E') hN hL1
    hN_bound hL1_fixed hE1 hE'el hfix
  calc Nat.card E = Nat.card E' := rfl
    _ ≤ p ^ (2 + 1) := hE0
    _ ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num)

theorem card_le_pow_four_graphFixedParabolicLevi_A2A1
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 :=
  A2A1_core hF σ hσ hp hp5 hpq hE hEel

private theorem eq_one_of_mem_sup_of_commute_of_centralizes {G : Type} [Group G]
    {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hA : ∀ x ∈ A, (∀ a ∈ A, Commute x a) → x = 1)
    (hB : ∀ x ∈ B, (∀ b ∈ B, Commute x b) → x = 1)
    {x : G} (hx : x ∈ A ⊔ B) (hcA : ∀ a ∈ A, Commute x a)
    (hcB : ∀ b ∈ B, Commute x b) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => (hcomm a ha b hb).eq) hx
  have haZ : ∀ a' ∈ A, Commute a a' := by
    intro a' ha'
    have h1 : Commute (a * b) a' := hcA a' ha'
    have h2 : Commute b a' := (hcomm a' ha' b hb).symm
    have hab : a * b = b * a := (hcomm a ha b hb).eq
    have h3 : b⁻¹ * (a * b) = a := by
      rw [hab]
      group
    rw [← h3]
    exact h2.inv_left.mul_left h1
  have hbZ : ∀ b' ∈ B, Commute b b' := by
    intro b' hb'
    have h1 : Commute (a * b) b' := hcB b' hb'
    have h2 : Commute a⁻¹ b' := (hcomm a ha b' hb').inv_left
    have h3 : b = a⁻¹ * (a * b) := by group
    rw [h3]
    exact h2.mul_left h1
  rw [hA a ha haZ, hB b hb hbZ, mul_one]


private theorem inf_eq_bot_of_commute_of_center_trivial {G : Type} [Group G]
    {X W L0 L5 : Subgroup G} (hXsup : X = L0 ⊔ L5)
    (hcomm05 : ∀ a ∈ L0, ∀ b ∈ L5, Commute a b)
    (hcommXW : ∀ a ∈ X, ∀ b ∈ W, Commute a b)
    (hL0 : ∀ z ∈ L0, (∀ a ∈ L0, Commute z a) → z = 1)
    (hL5 : ∀ z ∈ L5, (∀ b ∈ L5, Commute z b) → z = 1) :
    X ⊓ W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxW : x ∈ W := hx.2
  have hx05 : x ∈ L0 ⊔ L5 := by
    rw [← hXsup]
    exact hx.1
  have hcA : ∀ a ∈ L0, Commute x a := fun a ha =>
    (hcommXW a (by rw [hXsup]; exact Subgroup.mem_sup_left ha) x hxW).symm
  have hcB : ∀ b ∈ L5, Commute x b := fun b hb =>
    (hcommXW b (by rw [hXsup]; exact Subgroup.mem_sup_right hb) x hxW).symm
  have hx1 : x = 1 :=
    eq_one_of_mem_sup_of_commute_of_centralizes hcomm05 hL0 hL5 hx05 hcA hcB
  rw [hx1]
  exact Subgroup.mem_bot.2 rfl



private theorem A1A2_perm_0 {F : Type} [Field F] :
    ∀ i ∈ (twE6Node0 : Set (Fin TwistTag.E6.tag.rank)),
      (TwistTag.E6.perm i : Fin TwistTag.E6.tag.rank) ∈ twE6Node5 := by
  intro i hi
  change i ∈ ({(e6Index 0 : Fin TwistTag.E6.tag.rank)} :
    Set (Fin TwistTag.E6.tag.rank)) at hi
  change (TwistTag.E6.perm i) ∈ ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} :
    Set (Fin TwistTag.E6.tag.rank))
  change i = (e6Index 0 : Fin TwistTag.E6.tag.rank) at hi
  subst hi
  change (TwistTag.E6.perm (e6Index 0) : Fin TwistTag.E6.tag.rank) = e6Index 5
  apply Fin.ext
  decide

private theorem A1A2_perm_5 {F : Type} [Field F] :
    ∀ i ∈ (twE6Node5 : Set (Fin TwistTag.E6.tag.rank)),
      (TwistTag.E6.perm i : Fin TwistTag.E6.tag.rank) ∈ twE6Node0 := by
  intro i hi
  change i ∈ ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} :
    Set (Fin TwistTag.E6.tag.rank)) at hi
  change (TwistTag.E6.perm i) ∈ ({(e6Index 0 : Fin TwistTag.E6.tag.rank)} :
    Set (Fin TwistTag.E6.tag.rank))
  change i = (e6Index 5 : Fin TwistTag.E6.tag.rank) at hi
  subst hi
  change (TwistTag.E6.perm (e6Index 5) : Fin TwistTag.E6.tag.rank) = e6Index 0
  apply Fin.ext
  decide

private theorem A1A2_perm_05 {F : Type} [Field F] :
    ∀ i ∈ (twE6Node0 ∪ twE6Node5),
      (TwistTag.E6.perm i : Fin TwistTag.E6.tag.rank) ∈ twE6Node0 ∪ twE6Node5 := by
  intro i hi
  change i ∈ (({(e6Index 0 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank))) at hi
  change (TwistTag.E6.perm i) ∈
    (({(e6Index 0 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)))
  rw [Set.mem_union] at hi ⊢
  rcases hi with hi | hi
  · change i = (e6Index 0 : Fin TwistTag.E6.tag.rank) at hi
    subst hi
    exact Or.inr (by
      change (TwistTag.E6.perm (e6Index 0) : Fin TwistTag.E6.tag.rank) = e6Index 5
      apply Fin.ext
      decide)
  · change i = (e6Index 5 : Fin TwistTag.E6.tag.rank) at hi
    subst hi
    exact Or.inl (by
      change (TwistTag.E6.perm (e6Index 5) : Fin TwistTag.E6.tag.rank) = e6Index 0
      apply Fin.ext
      decide)

private theorem A1A2_perm_13 {F : Type} [Field F] :
    ∀ i ∈ (twE6Node1 ∪ twE6Node3),
      (TwistTag.E6.perm i : Fin TwistTag.E6.tag.rank) ∈ twE6Node1 ∪ twE6Node3 := by
  intro i hi
  change i ∈ (({(e6Index 1 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 3 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank))) at hi
  change (TwistTag.E6.perm i) ∈
    (({(e6Index 1 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 3 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)))
  rw [Set.mem_union] at hi ⊢
  rcases hi with hi | hi
  · change i = (e6Index 1 : Fin TwistTag.E6.tag.rank) at hi
    subst hi
    exact Or.inl (by
      change (TwistTag.E6.perm (e6Index 1) : Fin TwistTag.E6.tag.rank) = e6Index 1
      apply Fin.ext
      decide)
  · change i = (e6Index 3 : Fin TwistTag.E6.tag.rank) at hi
    subst hi
    exact Or.inr (by
      change (TwistTag.E6.perm (e6Index 3) : Fin TwistTag.E6.tag.rank) = e6Index 3
      apply Fin.ext
      decide)

private theorem A1A2_twist_image {F : Type} [Field F] (σ : F →+* F)
    {S T : Set (Fin TwistTag.E6.tag.rank)}
    (h : ∀ i ∈ S, (TwistTag.E6.perm i : Fin TwistTag.E6.tag.rank) ∈ T) :
    ∀ x ∈ e6TwGroup F S, twistEndTw σ x ∈ e6TwGroup F T := by
  intro x hx
  have himg : (TwistTag.E6.perm '' S) ⊆ T := by
    rintro i ⟨a, ha, rfl⟩
    exact h a ha
  exact CFSG.StandardType.F4Rest.subsystemGroup_mono himg
    (twistHom_mem_subsystemGroup_image (σ := σ) (S := S) hx)

private theorem A1A2_twist_L0 {F : Type} [Field F] (σ : F →+* F) :
    ∀ x ∈ e6TwGroup F twE6Node0, twistEndTw σ x ∈ e6TwGroup F twE6Node5 :=
  A1A2_twist_image σ (A1A2_perm_0 (F := F))

private theorem A1A2_twist_L5 {F : Type} [Field F] (σ : F →+* F) :
    ∀ x ∈ e6TwGroup F twE6Node5, twistEndTw σ x ∈ e6TwGroup F twE6Node0 :=
  A1A2_twist_image σ (A1A2_perm_5 (F := F))

private theorem A1A2_twist_X {F : Type} [Field F] (σ : F →+* F) :
    ∀ x ∈ e6TwGroup F (twE6Node0 ∪ twE6Node5),
      twistEndTw σ x ∈ e6TwGroup F (twE6Node0 ∪ twE6Node5) :=
  A1A2_twist_image σ (A1A2_perm_05 (F := F))

private theorem A1A2_twist_W {F : Type} [Field F] (σ : F →+* F) :
    ∀ x ∈ e6TwGroup F (twE6Node1 ∪ twE6Node3),
      twistEndTw σ x ∈ e6TwGroup F (twE6Node1 ∪ twE6Node3) :=
  A1A2_twist_image σ (A1A2_perm_13 (F := F))

private theorem A1A2_comm05 {F : Type} [Field F] :
    ∀ a ∈ e6TwGroup F twE6Node0, ∀ b ∈ e6TwGroup F twE6Node5, Commute a b := by
  have h := commute_subsystemGroup (τ := TwistTag.E6.tag) (K := F)
    (A := twE6Node0) (B := twE6Node5) ?_
  · intro a ha b hb
    exact h a ha b hb
  · intro a ha b hb
    change a ∈ ({(e6Index 0 : Fin TwistTag.E6.tag.rank)} :
      Set (Fin TwistTag.E6.tag.rank)) at ha
    change b ∈ ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} :
      Set (Fin TwistTag.E6.tag.rank)) at hb
    change a = (e6Index 0 : Fin TwistTag.E6.tag.rank) at ha
    change b = (e6Index 5 : Fin TwistTag.E6.tag.rank) at hb
    subst ha
    subst hb
    exact e6_pair_support 0 5 (by decide) (by decide +kernel)

private theorem A1A2_commXW {F : Type} [Field F] :
    ∀ a ∈ e6TwGroup F (twE6Node0 ∪ twE6Node5),
      ∀ b ∈ e6TwGroup F (twE6Node1 ∪ twE6Node3), Commute a b := by
  change ∀ a ∈ subsystemGroup TwistTag.E6.tag F
      (({e6Index 0} : Set (Fin TwistTag.E6.tag.rank)) ∪
        ({e6Index 5} : Set (Fin TwistTag.E6.tag.rank))),
    ∀ b ∈ subsystemGroup TwistTag.E6.tag F
      (({e6Index 1} : Set (Fin TwistTag.E6.tag.rank)) ∪
        ({e6Index 3} : Set (Fin TwistTag.E6.tag.rank))), Commute a b
  refine commute_subsystemGroup ?_
  intro a ha b hb
  change a ∈ (({e6Index 0} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({e6Index 5} : Set (Fin TwistTag.E6.tag.rank))) at ha
  change b ∈ (({e6Index 1} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({e6Index 3} : Set (Fin TwistTag.E6.tag.rank))) at hb
  simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact e6_pair_support 0 1 (by decide) (by decide +kernel)
  · exact e6_pair_support 0 3 (by decide) (by decide +kernel)
  · exact e6_pair_support 5 1 (by decide) (by decide +kernel)
  · exact e6_pair_support 5 3 (by decide) (by decide +kernel)

private theorem A1A2_Xsup {F : Type} [Field F] :
    e6TwGroup F (twE6Node0 ∪ twE6Node5) = e6TwGroup F twE6Node0 ⊔ e6TwGroup F twE6Node5 := by
  change subsystemGroup TwistTag.E6.tag F
      (({e6Index 0} : Set (Fin TwistTag.E6.tag.rank)) ∪
        ({e6Index 5} : Set (Fin TwistTag.E6.tag.rank))) = _
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union]

private theorem A1A2_inf05 {F : Type} [Field F] [Finite F] [CharP F 2] :
    e6TwGroup F twE6Node0 ⊓ e6TwGroup F twE6Node5 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact eq_one_of_mem_subsystemGroup_singleton_of_centralizes (F := F) (i := e6Index 0)
    hx.1 (fun y hy => (A1A2_comm05 y hy x hx.2).symm)

private theorem A1A2_infXW {F : Type} [Field F] [Finite F] [CharP F 2] :
    e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊓ e6TwGroup F (twE6Node1 ∪ twE6Node3) = ⊥ :=
  inf_eq_bot_of_commute_of_center_trivial A1A2_Xsup A1A2_comm05 A1A2_commXW
    (fun z hz hzc => eq_one_of_mem_subsystemGroup_singleton_of_centralizes
      (F := F) (i := e6Index 0) hz hzc)
    (fun z hz hzc => eq_one_of_mem_subsystemGroup_singleton_of_centralizes
      (F := F) (i := e6Index 5) hz hzc)

private theorem A1A2_subset {F : Type} [Field F] :
    ({i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} : Set _) ⊆
      (twE6Node0 ∪ twE6Node5) ∪ (twE6Node1 ∪ twE6Node3) := by
  intro i hi
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 3 ∨ i.val = 5 := by
    have h2 := hi.1
    have h4 := hi.2
    have hlt : i.val < 6 := i.isLt
    omega
  change i ∈ ((({(e6Index 0 : Fin TwistTag.E6.tag.rank)} :
      Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 5 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank))) ∪
    (({(e6Index 1 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank)) ∪
    ({(e6Index 3 : Fin TwistTag.E6.tag.rank)} : Set (Fin TwistTag.E6.tag.rank))))
  rcases hv with h | h | h | h
  · have hi0 : i = (e6Index 0 : Fin TwistTag.E6.tag.rank) :=
      Fin.ext (by simpa [e6Index] using h)
    rw [hi0]
    exact Or.inl (Or.inl (Set.mem_singleton _))
  · have hi1 : i = (e6Index 1 : Fin TwistTag.E6.tag.rank) :=
      Fin.ext (by simpa [e6Index] using h)
    rw [hi1]
    exact Or.inr (Or.inl (Set.mem_singleton _))
  · have hi3 : i = (e6Index 3 : Fin TwistTag.E6.tag.rank) :=
      Fin.ext (by simpa [e6Index] using h)
    rw [hi3]
    exact Or.inr (Or.inr (Set.mem_singleton _))
  · have hi5 : i = (e6Index 5 : Fin TwistTag.E6.tag.rank) :=
      Fin.ext (by simpa [e6Index] using h)
    rw [hi5]
    exact Or.inl (Or.inr (Set.mem_singleton _))

theorem twE6A1A2_le_sup {F : Type} [Field F] [Finite F]
    {E : Subgroup (ModGL TwistTag.E6.tag F)} :
    E ⊓ subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank |
        i.val ≠ 2 ∧ i.val ≠ 4} ≤
      e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊔ e6TwGroup F (twE6Node1 ∪ twE6Node3) := by
  refine inf_le_right.trans ?_
  change subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank |
      i.val ≠ 2 ∧ i.val ≠ 4} ≤
    e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊔ e6TwGroup F (twE6Node1 ∪ twE6Node3)
  rw [← CFSG.StandardType.F4Rest.subsystemGroup_union]
  exact CFSG.StandardType.F4Rest.subsystemGroup_mono (A1A2_subset (F := F))

private theorem A1A2_L0_bound {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}) :
    ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F twE6Node0 →
      IsElemAbelian p G → Nat.card G ≤ p ^ 1 := by
  intro G hG hGel
  change G ≤ subsystemGroup TwistTag.E6.tag F
    ({e6Index 0} : Set (Fin TwistTag.E6.tag.rank)) at hG
  exact card_le_pow_one_subsystemGroup_e6node (F := F) (n := n) hF hp hp2 hPRL
    (e6Index 0) hG hGel

private theorem A1A2_X_swap_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    {σ : F →+* F} (hp : p.Prime)
    (hL0 : ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F twE6Node0 →
      IsElemAbelian p G → Nat.card G ≤ p ^ 1) :
    ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F (twE6Node0 ∪ twE6Node5) →
      IsElemAbelian p G → (∀ e ∈ G, twistEndTw σ e = e) → Nat.card G ≤ p ^ 1 := by
  intro G hG hGel hGfix
  have hG05 : G ≤ e6TwGroup F twE6Node0 ⊔ e6TwGroup F twE6Node5 := by
    rwa [A1A2_Xsup] at hG
  have hinf : ¬ p ∣ Nat.card ↥(e6TwGroup F twE6Node0 ⊓ e6TwGroup F twE6Node5) := by
    rw [A1A2_inf05, Subgroup.card_bot]
    exact hp.not_dvd_one
  exact card_le_of_le_sup_of_swap (G := ModGL TwistTag.E6.tag F) (p := p) (k := 1) hp
    (X := e6TwGroup F twE6Node0) (Y := e6TwGroup F twE6Node5) A1A2_comm05 hinf
    (twistEndTw σ) (A1A2_twist_L0 σ) (A1A2_twist_L5 σ) hL0 hG05 hGel hGfix

private theorem A1A2_W_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F (twE6Node1 ∪ twE6Node3) →
      IsElemAbelian p G → Nat.card G ≤ p ^ 2 := by
  intro G hG hGel
  change G ≤ subsystemGroup TwistTag.E6.tag F
    ({e6Index 1, e6Index 3} : Set (Fin TwistTag.E6.tag.rank)) at hG
  exact card_le_pow_two_subsystemGroup_e6pair (F := F) hp hp2
    (i := e6Index 1) (j := e6Index 3)
    (by intro h; have := congrArg Fin.val h; simp [e6Index] at this)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hG hGel

private theorem A1A2_fixed_bound {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    {σ : F →+* F} (hp : p.Prime)
    (hX : ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F (twE6Node0 ∪ twE6Node5) →
      IsElemAbelian p G → (∀ e ∈ G, twistEndTw σ e = e) → Nat.card G ≤ p ^ 1)
    (hW : ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F (twE6Node1 ∪ twE6Node3) →
      IsElemAbelian p G → Nat.card G ≤ p ^ 2)
    {G : Subgroup (ModGL TwistTag.E6.tag F)}
    (hG : G ≤ e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊔ e6TwGroup F (twE6Node1 ∪ twE6Node3))
    (hGel : IsElemAbelian p G)
    (hGfix : ∀ e ∈ G, twistEndTw σ e = e) : Nat.card G ≤ p ^ (1 + 2) := by
  have hW' : ∀ G : Subgroup (ModGL TwistTag.E6.tag F), G ≤ e6TwGroup F (twE6Node1 ∪ twE6Node3) →
      IsElemAbelian p G → (∀ e ∈ G, twistEndTw σ e = e) → Nat.card G ≤ p ^ 2 :=
    fun G hG hGel _ => hW G hG hGel
  have hinf : ¬ p ∣ Nat.card ↥
      (e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊓ e6TwGroup F (twE6Node1 ∪ twE6Node3)) := by
    rw [A1A2_infXW, Subgroup.card_bot]
    exact hp.not_dvd_one
  exact card_le_of_le_sup_of_fixed (G := ModGL TwistTag.E6.tag F) (p := p)
    (k₁ := 1) (k₂ := 2) hp (X := e6TwGroup F (twE6Node0 ∪ twE6Node5))
    (W := e6TwGroup F (twE6Node1 ∪ twE6Node3)) A1A2_commXW hinf (twistEndTw σ)
    (A1A2_twist_X σ) (A1A2_twist_W σ) hX hW' hG hGel hGfix

private theorem A1A2_core
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 1 ≤ n := one_le_exponent_of_card_sq hF
  haveI : CharP F 2 := charP_two_of_card_sq hn hF
  have hrF : p ∣ Nat.card F - 1 := dvd_card_sub_one_of_dvd_two_pow_add_one hF hpq
  have hPRL := projective_rank_bound_of_dvd_card_sub_one hp hp2 hrF
  have hbound := card_le_mul_card_inf_subsystemGroup_A1A2 (F := F) (n := n) hF σ hσ
    hp hp2 hpq hE hEel
  let φ : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag F := twistEndTw σ.toRingHom
  obtain ⟨hφx, hφy⟩ := twistEndTw_generators σ.toRingHom
  have hfix : ∀ e ∈ E, φ e = e := by
    intro e he
    exact ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom)).1
        (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
          (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
            (J := twE6MaxA1A2) (hE he)))).2
  let E0 : Subgroup (ModGL TwistTag.E6.tag F) :=
    E ⊓ subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank |
      i.val ≠ 2 ∧ i.val ≠ 4}
  have hbound' : Nat.card E ≤ p * Nat.card E0 := hbound
  have hE0el : IsElemAbelian p E0 := hEel.mono inf_le_left
  have hE0fix : ∀ e ∈ E0, φ e = e := fun e he => hfix e he.1
  have hE0XW : E0 ≤ e6TwGroup F (twE6Node0 ∪ twE6Node5) ⊔ e6TwGroup F (twE6Node1 ∪ twE6Node3) :=
    twE6A1A2_le_sup
  have hXbound := A1A2_X_swap_bound (F := F) (σ := σ.toRingHom) hp
    (A1A2_L0_bound (F := F) hF hp hp2 hPRL)
  have hWbound := A1A2_W_bound (F := F) hp hp2
  have hE0bound := A1A2_fixed_bound (F := F) (σ := σ.toRingHom) hp hXbound hWbound
    hE0XW hE0el hE0fix
  calc Nat.card E ≤ p * Nat.card E0 := hbound'
    _ ≤ p * p ^ (1 + 2) := Nat.mul_le_mul_left p hE0bound
    _ = p ^ 4 := by ring

theorem card_le_pow_four_graphFixedParabolicLevi_A1A2
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 :=
  A1A2_core hF σ hσ hp hp5 hpq hE hEel





private theorem D4_subset_setD :
    ({i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} :
      Set (Fin TwistTag.E6.tag.rank)) ⊆
      (CFSG.LieType.Chevalley.C2E6Std.setD : Set (Fin TwistTag.E6.tag.rank)) := by
  intro i hi
  by_contra h
  have h' := (CFSG.LieType.Chevalley.C2E6Std.not_mem_setD_iff
    (i : Fin Tag.E6.rank)).1 h
  rcases h' with h0 | h5
  · exact hi.1 (by simpa [CFSG.LieType.Chevalley.C2E6Std.i6] using congrArg Fin.val h0)
  · exact hi.2 (by simpa [CFSG.LieType.Chevalley.C2E6Std.i6] using congrArg Fin.val h5)

private theorem D4_fixed_le_omegaMinus {F : Type} [Field F] {σ : F →+* F}
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ twE6MaxD4) :
    E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5} ≤
      CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi σ := by
  rw [CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi]
  refine le_inf ?_ ?_
  · exact inf_le_right.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono D4_subset_setD)
  · exact (inf_le_left.trans hE).trans
      (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F) (σ := σ) (J := twE6MaxD4))

theorem omegaMinusLevi_isQuasisimple_model {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hn : 1 ≤ n) :
    CFSG.Open.IsQuasisimple
        (CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)) ∧
      Subgroup.center (CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)) = ⊥ ∧
      StatedClassicalModel
        ((CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)) ⧸
          Subgroup.center (CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)))
        .POmegaMinus 4 2 n := by
  let H := CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)
  have hmodel : LieModel H .POmegaMinus 4 2 n :=
    CFSG.SeitzReduction.TwistedE6Pilot.lieModel_omegaMinusLevi hn hF hσ
  haveI hsimple : IsSimpleGroup H :=
    CFSG.SeitzReduction.TwistedE6Pilot.isSimpleGroup_omegaMinusLevi hn hF hσ
  haveI hperf : Group.IsPerfect H :=
    CFSG.SeitzReduction.TwistedE6Pilot.isPerfect_omegaMinusLevi hn hF hσ
  have hnc : ¬ IsMulCommutative H := Group.IsPerfect.not_isMulCommutative H
  have hnab : ∃ a b : H, a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  obtain ⟨hqs, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := H) hnab
  have hqOpen : CFSG.Open.IsQuasisimple H :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mp hqs
  refine ⟨hqOpen, hZ, ?_⟩
  let e : (H ⧸ Subgroup.center H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
    (hmodel.statedClassicalModel (by decide))

theorem pRank_omegaMinusLevi_le_three {F : Type} [Field F] [Finite F] {n p : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p
      (⊤ : Subgroup (CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F))) ≤ 3 := by
  have hn : 1 ≤ n := one_le_exponent_of_card_sq hF
  obtain ⟨hqOpen, _hZ, hSCM⟩ := omegaMinusLevi_isQuasisimple_model hF σ hσ hn
  have hT : LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_pomegaMinus
    (K := CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)) hT hqOpen
    hSCM (r := p) hp hp2
  rw [hpr]
  obtain ⟨hS1, hP2⟩ := bad_pRank_or_out_aux2 hpq
  have hP4 : eP (2 ^ n) p ∣ 4 := hP2.trans (by norm_num)
  unfold rkOmMinus
  rw [hS1]
  simp [hP4]

private theorem D4_core
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 1 ≤ n := one_le_exponent_of_card_sq hF
  haveI : CharP F 2 := charP_two_of_card_sq hn hF
  have hbound :=
    card_le_mul_card_inf_subsystemGroup_D4 (F := F) (n := n) hF σ hσ hp hp2 hpq hE hEel
  let E' : Subgroup (ModGL TwistTag.E6.tag F) :=
    E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5}
  have hE'el : IsElemAbelian p E' := hEel.mono inf_le_left
  have hE'le : E' ≤ CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F) :=
    D4_fixed_le_omegaMinus hE
  have hpr3 := pRank_omegaMinusLevi_le_three hF σ hσ hp hp2 hpq
  let A : Subgroup (CFSG.SeitzReduction.TwistedE6Pilot.omegaMinusLevi (σ : F →+* F)) :=
    E'.subgroupOf _
  have hAel : IsElemAbelian p A := hE'el.comap (Subgroup.subtype_injective _)
  have hAcard : Nat.card A = Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'le).toEquiv
  have hA3 : Nat.card A ≤ p ^ 3 :=
    (CFSG.RankThree.OddKernel.card_le_pow_pRank_of_le hp hAel le_top).trans
      (Nat.pow_le_pow_right hp.pos hpr3)
  calc Nat.card E ≤ p * Nat.card E' := hbound
    _ = p * Nat.card A := by rw [hAcard]
    _ ≤ p * p ^ 3 := Nat.mul_le_mul_left p hA3
    _ = p ^ 4 := by ring

theorem card_le_pow_four_graphFixedParabolicLevi_D4
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 :=
  D4_core hF σ hσ hp hp5 hpq hE hEel

theorem card_le_pow_four_graphFixedParabolicLevi_of_not_subset
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) (hJ : J ≠ Set.univ) (hJA : ¬ J ⊆ twE6MaxA5)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  rcases subset_maximalSet_of_ne_univ hJ with h | h | h | h
  · exact absurd h hJA
  · exact card_le_pow_four_graphFixedParabolicLevi_A2A1 hF σ hσ hp hp5 hpq
      (hE.trans (graphFixedParabolicLevi_mono h)) hEel
  · exact card_le_pow_four_graphFixedParabolicLevi_A1A2 hF σ hσ hp hp5 hpq
      (hE.trans (graphFixedParabolicLevi_mono h)) hEel
  · exact card_le_pow_four_graphFixedParabolicLevi_D4 hF σ hσ hp hp5 hpq
      (hE.trans (graphFixedParabolicLevi_mono h)) hEel

end

end CFSG.LocalAnalysis.GLTheoremA
