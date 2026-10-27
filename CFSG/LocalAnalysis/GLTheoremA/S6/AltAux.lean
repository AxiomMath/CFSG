module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
import CFSG.Quasithin.H13.A7SectionRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def GenByPElts (p : ℕ) {G : Type*} [Group G] (I : Subgroup G) : Prop :=
  I ≤ Subgroup.closure {g : G | g ∈ I ∧ IsPGroup p (Subgroup.zpowers g)}

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem isPGroup_zpowers_iff_exists_pow {y : G} :
    IsPGroup p (Subgroup.zpowers y) ↔ ∃ m : ℕ, y ^ p ^ m = 1 := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h ⟨y, Subgroup.mem_zpowers y⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  · rintro ⟨m, hm⟩ ⟨_, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨m, Subtype.ext ?_⟩
    show (y ^ k) ^ p ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]

theorem le_commutator_of_genByPElts (hp : p.Prime) (hp2 : p ≠ 2) {I C : Subgroup G}
    (hC : IsPGroup 2 C) (hIC : I ≤ Subgroup.normalizer (C : Set G)) (hgen : GenByPElts p I) :
    (⁅I, C⁆ : Subgroup G) ≤ ⁅(⁅I, C⁆ : Subgroup G), I⁆ := by
  classical
  set N : Subgroup G := ⁅(⁅I, C⁆ : Subgroup G), I⁆ with hN
  have hj : ∀ j ∈ I, IsPGroup p (Subgroup.zpowers j) → ⁅C, Subgroup.zpowers j⁆ ≤ N := by
    intro j hjI hjp
    have h1 := commutator_commutator_eq_of_isPGroup hp hjp hC hp2
      (Subgroup.zpowers_le.2 (hIC hjI))
    have hjI' : Subgroup.zpowers j ≤ I := Subgroup.zpowers_le.2 hjI
    have h2 : (⁅C, Subgroup.zpowers j⁆ : Subgroup G) ≤ ⁅I, C⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono hjI' le_rfl
    rw [← h1]
    exact Subgroup.commutator_mono h2 hjI'
  set S : Set G := {x : G | ∃ c ∈ C, ∃ j ∈ I, IsPGroup p (Subgroup.zpowers j) ∧ x = ⁅c, j⁆} with hS
  set P : Subgroup G := Subgroup.closure S with hP
  have hPN : P ≤ N := by
    rw [hP, Subgroup.closure_le]
    rintro _ ⟨c, hc, j, hjI, hjp, rfl⟩
    exact hj j hjI hjp (Subgroup.commutator_mem_commutator hc (Subgroup.mem_zpowers j))
  have hSconj : ∀ a ∈ I, ∀ x ∈ S, a * x * a⁻¹ ∈ S := by
    rintro a ha _ ⟨c, hc, j, hjI, hjp, rfl⟩
    refine ⟨a * c * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hIC ha) c).1 hc, a * j * a⁻¹,
      I.mul_mem (I.mul_mem ha hjI) (I.inv_mem ha), ?_, ?_⟩
    · obtain ⟨m, hm⟩ := isPGroup_zpowers_iff_exists_pow.1 hjp
      refine isPGroup_zpowers_iff_exists_pow.2 ⟨m, ?_⟩
      have : (a * j * a⁻¹) ^ p ^ m = a * j ^ p ^ m * a⁻¹ := by simp [conj_pow]
      rw [this, hm]
      simp
    · simp only [commutatorElement_def]
      group
  have hPconj : ∀ a ∈ I, ∀ x ∈ P, a * x * a⁻¹ ∈ P := by
    intro a ha x hx
    refine Subgroup.closure_induction (p := fun x _ => a * x * a⁻¹ ∈ P)
      (fun x hx => Subgroup.subset_closure (hSconj a ha x hx)) (by simp) (fun x y _ _ hx hy => ?_)
      (fun x _ hx => ?_) hx
    · have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [this]
      exact P.mul_mem hx hy
    · have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [this]
      exact P.inv_mem hx
  have hcl : Subgroup.closure {g : G | g ∈ I ∧ IsPGroup p (Subgroup.zpowers g)} ≤ I :=
    (Subgroup.closure_le I).2 fun g hg => hg.1
  have hmain : ∀ g ∈ I, ∀ c ∈ C, ⁅g, c⁆ ∈ P := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ c ∈ C, ⁅g, c⁆ ∈ P) ?_ ?_ ?_ ?_ (hgen hg)
    · rintro g ⟨hgI, hgp⟩ c hc
      have : ⁅c, g⁆ ∈ P := Subgroup.subset_closure ⟨c, hc, g, hgI, hgp, rfl⟩
      rw [← commutatorElement_inv]
      exact P.inv_mem this
    · intro c _
      simp
    · intro g₁ g₂ hg₁ hg₂ ih₁ ih₂ c hc
      have e : ⁅g₁ * g₂, c⁆ = g₁ * ⁅g₂, c⁆ * g₁⁻¹ * ⁅g₁, c⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact P.mul_mem (hPconj g₁ (hcl hg₁) _ (ih₂ c hc)) (ih₁ c hc)
    · intro g hg ih c hc
      have e : ⁅g⁻¹, c⁆ = g⁻¹ * (⁅g, c⁆)⁻¹ * g⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hPconj g⁻¹ (I.inv_mem (hcl hg)) _ (P.inv_mem (ih c hc))
  rw [Subgroup.commutator_le]
  intro g hg c hc
  exact hPN (hmain g hg c hc)

theorem le_of_commutator_subnormal {K X S I : Subgroup G} (hKX : IsSubnormal K X) (hIK : I ≤ K)
    (hSX : S ≤ X) (hS : S ≤ ⁅S, I⁆) : S ≤ K := by
  induction hKX with
  | refl H => exact hSX
  | @step H M K' hHM hn _ ih =>
    have hSM : S ≤ M := ih (hIK.trans hHM) hSX
    refine hS.trans (Subgroup.commutator_le.2 fun s hs i hi => ?_)
    have h1 := hn.conj_mem (⟨i, hHM (hIK hi)⟩ : ↥M) (Subgroup.mem_subgroupOf.2 (hIK hi))
      (⟨s, hSM hs⟩ : ↥M)
    have h2 : s * i * s⁻¹ ∈ H := Subgroup.mem_subgroupOf.1 h1
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (hIK hi))

theorem exists_invariant_twoGroup (hp : p.Prime) (hp2 : p ≠ 2) {O B : Subgroup G}
    (hB : IsPGroup p B) (hBO : B ≤ Subgroup.normalizer (O : Set G))
    (hcop : Nat.Coprime p (Nat.card ↥O)) (hev : ¬ Odd (Nat.card ↥O)) :
    ∃ U : Subgroup G, U ≤ O ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  classical
  haveI := Fact.mk hp
  have hV2 : 2 ∣ Nat.card ↥O := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  have hnd : ¬ p ∣ Nat.card ↥O := (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
  let f : B →* MulAut O := O.normalizerMonoidHom.comp (Subgroup.inclusion hBO)
  let _ : MulDistribMulAction B O := MulDistribMulAction.compHom O f
  have hcard : Nat.card (Sylow 2 O) ∣ Nat.card O :=
    (Sylow.card_dvd_index (default : Sylow 2 O)).trans (Subgroup.index_dvd_card _)
  have hnd' : ¬ p ∣ Nat.card (Sylow 2 O) := fun h => hnd (h.trans hcard)
  have hfix : (MulAction.fixedPoints B (Sylow 2 O)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hmod := hB.card_modEq_card_fixedPoints (Sylow 2 O)
    rw [hne] at hmod
    have h0 : Nat.card (↥(∅ : Set (Sylow 2 O))) = 0 := by simp
    rw [h0] at hmod
    exact hnd' ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨Q, hQ⟩ := hfix
  rw [MulAction.mem_fixedPoints] at hQ
  refine ⟨(Q : Subgroup O).map O.subtype, Subgroup.map_subtype_le _, ?_, Q.isPGroup'.map O.subtype, ?_⟩
  · intro h
    exact Q.ne_bot_of_dvd_card hV2
      ((Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup O) O.subtype_injective).1 h)
  · have hfwd : ∀ x ∈ B, ∀ y ∈ (Q : Subgroup O).map O.subtype,
        x * y * x⁻¹ ∈ (Q : Subgroup O).map O.subtype := by
      intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := hy
      have h1 := Subgroup.smul_mem_pointwise_smul s (⟨x, hx⟩ : B) (Q : Subgroup O) hs
      rw [← Sylow.pointwise_smul_def, hQ] at h1
      exact ⟨_, h1, rfl⟩
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨fun hy => hfwd x hx y hy, fun hy => ?_⟩
    have := hfwd x⁻¹ (B.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem exists_gen_of_index (hp : p.Prime) {D A : Subgroup G} (hD : Nat.card ↥D = p ^ 2)
    (hAD : A ≤ D) (hi : (A.subgroupOf D).index = p) :
    ∃ a : G, a ∈ A ∧ a ≠ 1 ∧ A = Subgroup.zpowers a := by
  have h1 := (A.subgroupOf D).card_mul_index
  rw [hi, hD] at h1
  have hAcard : Nat.card ↥A = p := by
    have h2 : Nat.card ↥(A.subgroupOf D) = p := by
      have : Nat.card ↥(A.subgroupOf D) * p = p * p := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    rw [← h2]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv).symm
  have hne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    exact hp.one_lt.ne hAcard
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hao : orderOf (a : G) = p := by
    have hd : orderOf (a : G) ∣ p := by
      rw [← hAcard, Subgroup.orderOf_coe a]
      exact orderOf_dvd_natCard a
    have hne1 : orderOf (a : G) ≠ 1 := fun h => ha (Subtype.ext (orderOf_eq_one_iff.1 h))
    exact ((Nat.dvd_prime hp).1 hd).resolve_left hne1
  refine ⟨a, a.2, fun h => ha (Subtype.ext h), ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 a.2) ?_).symm
  rw [Nat.card_zpowers, hao, hAcard]

theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian p (A ⊔ B) :=
  CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hA hB fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm

theorem exists_mul_of_mem_sup_of_le_normalizer {A N : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) {y : G} (hy : y ∈ A ⊔ N) :
    ∃ a ∈ A, ∃ n ∈ N, y = a * n := by
  rw [Subgroup.sup_eq_closure] at hy
  refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, ∃ n ∈ N, y = a * n) ?_ ?_ ?_ ?_ hy
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, N.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  · exact ⟨1, A.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
  · rintro y z - - ⟨a, ha, n, hn, rfl⟩ ⟨a', ha', n', hn', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * n * a') * n', N.mul_mem ?_ hn', by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha')) n).1 hn
    simpa using this
  · rintro y - ⟨a, ha, n, hn, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, a * n⁻¹ * a⁻¹, ?_, by group⟩
    exact (Subgroup.mem_normalizer_iff.1 (hA ha) n⁻¹).1 (N.inv_mem hn)

theorem permOfMod_of_mem {L : Subgroup G} {n : ℕ} (e : PQuot p L ≃* ↥(alternatingGroup (Fin n)))
    {y : G} (hy : y ∈ L) :
    permOfMod p L n e y =
      ((e (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : PQuot p L) : ↥(alternatingGroup (Fin n))) :
        Equiv.Perm (Fin n)) := by
  unfold permOfMod
  rw [dif_pos hy]

theorem exists_elemAbelian_blocks {M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpM : p ≤ M) :
    ∃ (E₀ : Subgroup ↥(alternatingGroup (Fin M))) (c₀ : ↥(alternatingGroup (Fin M))),
      IsElemAbelian p E₀ ∧ Nat.card ↥E₀ = p ^ (M / p) ∧ c₀ ∈ E₀ ∧
      ((c₀ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).cycleType = {p} ∧
      (2 ≤ M / p → ∃ c₁ ∈ E₀, ((c₁ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).cycleType = {p} ∧
        Equiv.Perm.Disjoint (c₀ : Equiv.Perm (Fin M)) (c₁ : Equiv.Perm (Fin M))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hex : ∀ j : ℕ, ∃ τ : ↥(alternatingGroup (Fin M)), (j + 1) * p ≤ M →
      (((τ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).cycleType = {p} ∧ τ ^ p = 1 ∧
        (∀ x : Fin M, x.val < j * p ∨ j * p + p ≤ x.val →
          ((τ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)) x = x) ∧
        ∃ x : Fin M, x.val = j * p ∧ ((τ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)) x ≠ x) := by
    intro j
    by_cases hj : (j + 1) * p ≤ M
    · obtain ⟨hpow, hfix, hmove⟩ :=
        CFSG.Quasithin.H13.A7.blockCycle_spec (n := M) (p := p) j hj hp.two_le
      have hsign : Equiv.Perm.sign ((finRotate p).extendDomain
          (CFSG.Quasithin.H13.A7.blockEquiv j hj)) = 1 := by
        rw [Equiv.Perm.sign_extendDomain, sign_finRotate]
        obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
        have : p - 1 = 2 * r := by omega
        rw [this, pow_mul]
        simp
      refine ⟨⟨_, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, fun _ => ⟨?_, ?_, hfix, _, rfl, hmove⟩⟩
      · show ((finRotate p).extendDomain (CFSG.Quasithin.H13.A7.blockEquiv j hj)).cycleType = {p}
        rw [Equiv.Perm.cycleType_extendDomain]
        exact cycleType_finRotate_of_le hp.two_le
      · exact Subtype.ext hpow
    · exact ⟨1, fun h => absurd h hj⟩
  choose τ hτ using hex
  have key : ∀ j : ℕ, j ≤ M / p → ∃ E : Subgroup ↥(alternatingGroup (Fin M)), IsElemAbelian p E ∧
      Nat.card ↥E = p ^ j ∧
      (∀ g ∈ E, ∀ x : Fin M, j * p ≤ x.val → ((g : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)) x = x) ∧
      ∀ i, i < j → τ i ∈ E := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⊥, CFSG.SectionRank.isElemAbelian_bot p, by simp, ?_, fun i hi => absurd hi (by omega)⟩
      intro g hg x _
      rw [Subgroup.mem_bot.1 hg]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨E, hEel, hEcard, hEfix, hEmem⟩ := ih (by omega)
      have hjM : (j + 1) * p ≤ M := (Nat.le_div_iff_mul_le hp.pos).1 hj
      have hj1 : (j + 1) * p = j * p + p := by ring
      obtain ⟨hcyc, hpow, hfix, x₀, hx₀, hmove⟩ := hτ j hjM
      have hcomm : ∀ g ∈ E, ∀ w ∈ Subgroup.zpowers (τ j), g * w = w * g := by
        intro g hg w hw
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have hd : Equiv.Perm.Disjoint (g : Equiv.Perm (Fin M)) ((τ j ^ m : ↥(alternatingGroup (Fin M))) :
            Equiv.Perm (Fin M)) := by
          intro x
          by_cases hx : j * p ≤ x.val
          · exact Or.inl (hEfix g hg x hx)
          · right
            rw [SubgroupClass.coe_zpow]
            exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hfix x (Or.inl (by omega))) m
        exact Subtype.ext hd.commute.eq
      have hzel : IsElemAbelian p (Subgroup.zpowers (τ j)) :=
        ⟨inferInstance, fun g hg => by
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]⟩
      have hτ1 : τ j ≠ 1 := by
        intro h1
        apply hmove
        rw [h1]
        rfl
      have hτo : orderOf (τ j) = p := orderOf_eq_prime hpow hτ1
      have hτE : τ j ∉ E := fun h => hmove (hEfix _ h x₀ (by omega))
      have hnorm : Subgroup.zpowers (τ j) ≤ Subgroup.normalizer (E : Set ↥(alternatingGroup (Fin M))) :=
        Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun g hg => (hcomm g hg (τ j) (Subgroup.mem_zpowers _))))
      have hinf : E ⊓ Subgroup.zpowers (τ j) = ⊥ := by
        have hd : Nat.card ↥(E ⊓ Subgroup.zpowers (τ j)) ∣ p := by
          rw [← hτo, ← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hp).1 hd with h1 | h1
        · exact Subgroup.card_eq_one.1 h1
        · exfalso
          have : E ⊓ Subgroup.zpowers (τ j) = Subgroup.zpowers (τ j) :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hτo])
          have hmem : τ j ∈ E ⊓ Subgroup.zpowers (τ j) := by
            rw [this]
            exact Subgroup.mem_zpowers _
          exact hτE hmem.1
      have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hτo, hEcard] at hcard
      refine ⟨E ⊔ Subgroup.zpowers (τ j), isElemAbelian_sup_of_commute hEel hzel hcomm,
        by rw [hcard, pow_succ], ?_, ?_⟩
      · intro g hg x hx
        obtain ⟨e, he, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
          (A := E) (N := Subgroup.zpowers (τ j))
          (Subgroup.centralizer_le_normalizer _
            |>.trans' (fun g hg => Subgroup.mem_centralizer_iff.2 fun w hw =>
              (hcomm g hg w hw).symm) : E ≤ Subgroup.normalizer ((Subgroup.zpowers (τ j) : Subgroup _) : Set _)) hg
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have h1 : ((τ j ^ m : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)) x = x := by
          rw [SubgroupClass.coe_zpow]
          exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hfix x (Or.inr (by omega))) m
        show ((e : Equiv.Perm (Fin M)) * ((τ j ^ m : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M))) x = x
        rw [Equiv.Perm.mul_apply, h1]
        exact hEfix e he x (by omega)
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact Subgroup.mem_sup_left (hEmem i h)
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨E, hEel, hEcard, -, hEmem⟩ := key (M / p) le_rfl
  have hk1 : 1 ≤ M / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have h0 : (0 + 1) * p ≤ M := by omega
  refine ⟨E, τ 0, hEel, hEcard, hEmem 0 (by omega), (hτ 0 h0).1, fun h2 => ?_⟩
  have h1 : (1 + 1) * p ≤ M := by
    have := (Nat.le_div_iff_mul_le hp.pos).1 h2
    omega
  refine ⟨τ 1, hEmem 1 (by omega), (hτ 1 h1).1, ?_⟩
  intro x
  by_cases hx : x.val < p
  · right
    exact (hτ 1 h1).2.2.1 x (Or.inl (by omega))
  · left
    exact (hτ 0 h0).2.2.1 x (Or.inr (by omega))

theorem exists_elemAbelian_pCycle {M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpM : p ≤ M)
    (σ : ↥(alternatingGroup (Fin M)))
    (hσ : ((σ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).cycleType = {p}) :
    ∃ E : Subgroup ↥(alternatingGroup (Fin M)), IsElemAbelian p E ∧ Nat.card ↥E = p ^ (M / p) ∧
      σ ∈ E ∧ (2 ≤ M / p → ∃ τ ∈ E,
        ((τ : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)).cycleType = {p} ∧
          Equiv.Perm.Disjoint (σ : Equiv.Perm (Fin M)) (τ : Equiv.Perm (Fin M))) := by
  classical
  obtain ⟨E₀, c₀, hE₀, hcard, hc₀E, hc₀, hex⟩ := exists_elemAbelian_blocks hp hp2 hpM
  obtain ⟨g, hg⟩ : ∃ g : Equiv.Perm (Fin M),
      g * (c₀ : Equiv.Perm (Fin M)) * g⁻¹ = (σ : Equiv.Perm (Fin M)) :=
    isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc₀.trans hσ.symm))
  have hφ : ∀ a : ↥(alternatingGroup (Fin M)),
      ((MulAut.conjNormal g a : ↥(alternatingGroup (Fin M))) : Equiv.Perm (Fin M)) =
        g * (a : Equiv.Perm (Fin M)) * g⁻¹ := fun a => MulAut.conjNormal_apply g a
  refine ⟨E₀.map (MulAut.conjNormal g : MulAut ↥(alternatingGroup (Fin M))).toMonoidHom,
    CFSG.SectionRank.isElemAbelian_map hE₀ _, ?_, ⟨c₀, hc₀E, Subtype.ext ((hφ c₀).trans hg)⟩, ?_⟩
  · rw [← hcard]
    exact Subgroup.card_map_of_injective
      (MulAut.conjNormal g : MulAut ↥(alternatingGroup (Fin M))).injective
  · intro h2
    obtain ⟨c₁, hc₁E, hc₁, hd⟩ := hex h2
    refine ⟨MulAut.conjNormal g c₁, ⟨c₁, hc₁E, rfl⟩, ?_, ?_⟩
    · rw [hφ, Equiv.Perm.cycleType_conj]
      exact hc₁
    · rw [hφ, ← hg]
      exact hd.conj g

theorem exists_lift_elemAbelian (hp : p.Prime) {L : Subgroup G} {n : ℕ}
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) {Ebar : Subgroup ↥(alternatingGroup (Fin n))}
    (hE : IsElemAbelian p Ebar) {y : G} (hyL : y ∈ L) (hyo : orderOf y = p)
    (hy : e (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : PQuot p L) ∈ Ebar) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian p E ∧ y ∈ E ∧ Nat.card ↥E = Nat.card ↥Ebar ∧
      ∀ σ ∈ Ebar, ∃ z ∈ E, permOfMod p L n e z = ((σ : ↥(alternatingGroup (Fin n))) :
        Equiv.Perm (Fin n)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, hπ⟩ : ∃ π : ↥L →* PQuot p L, π = QuotientGroup.mk' (GLAPPrimeCore p ↥L) := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Subgroup ↥L, O = GLAPPrimeCore p ↥L := ⟨_, rfl⟩
  have hOcop : Nat.Coprime p (Nat.card O) := by
    rw [hO]; exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥L
  have hker : ∀ x : ↥L, π x = 1 → x ∈ O := fun x hx => by
    rw [hO]; rw [hπ] at hx; exact (QuotientGroup.eq_one_iff x).1 hx
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Subgroup (PQuot p L), Eb = Ebar.map e.symm.toMonoidHom := ⟨_, rfl⟩
  have hEbcard : Nat.card Eb = Nat.card Ebar := by
    rw [hEb]; exact Subgroup.card_map_of_injective e.symm.injective
  have hEbel : IsElemAbelian p Eb := by
    rw [hEb]; exact CFSG.SectionRank.isElemAbelian_map hE _
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hEbel
  obtain ⟨Mhat, hMhat⟩ : ∃ Mhat : Subgroup ↥L, Mhat = Eb.comap π := ⟨_, rfl⟩
  have hMhatcard : Nat.card Mhat = Nat.card O * p ^ k := by
    rw [hMhat, ← hk, hπ, hO]
    exact QuotientGroup.card_preimage_mk (GLAPPrimeCore p ↥L) (Eb : Set (PQuot p L))
  have hy₀ : (⟨y, hyL⟩ : ↥L) ∈ Mhat := by
    rw [hMhat, Subgroup.mem_comap, hπ, hEb]
    exact ⟨_, hy, by simp⟩
  have hy₀p : ((⟨y, hyL⟩ : ↥L) : ↥L) ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hzp : IsPGroup p (Subgroup.zpowers (⟨⟨y, hyL⟩, hy₀⟩ : ↥Mhat)) := by
    refine isPGroup_zpowers_iff_exists_pow.2 ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hy₀p
  obtain ⟨P0, hP0⟩ := hzp.exists_le_sylow
  have hP0card : Nat.card P0 = p ^ k := by
    rw [P0.card_eq_multiplicity, hMhatcard,
      Nat.factorization_mul Nat.card_pos.ne' (pow_pos hp.pos k).ne', Nat.factorization_pow]
    have h0 : (Nat.card O).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => hp.one_lt.ne' (hOcop.eq_one_of_dvd h)
    simp [h0, hp.factorization_self]
  obtain ⟨Pm, hPm⟩ : ∃ Pm : Subgroup ↥L, Pm = (P0 : Subgroup ↥Mhat).map Mhat.subtype := ⟨_, rfl⟩
  have hPmcard : Nat.card Pm = p ^ k := by
    rw [hPm, Subgroup.card_map_of_injective Mhat.subtype_injective]; exact hP0card
  have hPmp : IsPGroup p Pm := by rw [hPm]; exact P0.isPGroup'.map Mhat.subtype
  have hPmle : Pm ≤ Mhat := by rw [hPm]; exact Subgroup.map_subtype_le _
  have hPmπ : ∀ x ∈ Pm, π x ∈ Eb := fun x hx => by
    have := hPmle hx; rw [hMhat] at this; exact this
  have hinj : ∀ x ∈ Pm, π x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ O := hker x h1
    obtain ⟨m, hm⟩ := hPmp ⟨x, hx⟩
    have hm' : x ^ (p ^ m) = 1 := congrArg Subtype.val hm
    have h2 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h3 : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have h4 : orderOf x ∣ Nat.gcd (p ^ m) (Nat.card O) := Nat.dvd_gcd h2 h3
    rw [(Nat.Coprime.pow_left m hOcop)] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have hcomm : ∀ x ∈ Pm, ∀ w ∈ Pm, x * w = w * x := by
    intro x hx w hw
    have hc : π x * π w = π w * π x :=
      congrArg Subtype.val (hEbel.1.is_comm.comm ⟨π x, hPmπ x hx⟩ ⟨π w, hPmπ w hw⟩)
    have := hinj (x * w * (w * x)⁻¹) (mul_mem (mul_mem hx hw) (inv_mem (mul_mem hw hx)))
      (by rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hexp : ∀ x ∈ Pm, x ^ p = 1 := fun x hx =>
    hinj (x ^ p) (pow_mem hx p) (by rw [map_pow]; exact hEbel.2 _ (hPmπ x hx))
  have hPmel : IsElemAbelian p Pm :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hexp⟩
  have himg : Pm.map π = Eb := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩; exact hPmπ x hx
    · have hinjπ : Function.Injective (π.subgroupMap Pm) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have h1 : π (x : ↥L) = 1 := congrArg Subtype.val hx
        exact Subgroup.mem_bot.2 (Subtype.ext (hinj x x.2 h1))
      have : Nat.card (Pm.map π) = Nat.card Pm :=
        (Nat.card_congr (Equiv.ofBijective (π.subgroupMap Pm)
          ⟨hinjπ, π.subgroupMap_surjective Pm⟩)).symm
      rw [this, hPmcard, hk]
  refine ⟨Pm.map L.subtype, Subgroup.map_subtype_le _, CFSG.SectionRank.isElemAbelian_map hPmel _,
    ⟨⟨y, hyL⟩, ?_, rfl⟩, ?_, ?_⟩
  · rw [hPm]
    exact ⟨⟨⟨y, hyL⟩, hy₀⟩, hP0 (Subgroup.mem_zpowers _), rfl⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hPmcard, ← hk, hEbcard]
  · intro σ hσ
    have hmem : e.symm σ ∈ Pm.map π := by
      rw [himg, hEb]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx, hxσ⟩ := hmem
    refine ⟨(x : G), ⟨x, hx, rfl⟩, ?_⟩
    rw [permOfMod_of_mem e x.2]
    have : (QuotientGroup.mk (⟨(x : G), x.2⟩ : ↥L) : PQuot p L) = e.symm σ := by
      rw [← hxσ, hπ]; rfl
    rw [this, e.apply_symm_apply]

theorem isBmax_of_pRank_le (hp : p.Prime) {B B' : Subgroup G} (hB : GLAIsBmax p B)
    (hB' : IsElemAbelian p B') (hrank : CFSG.Open.pRank p B ≤ CFSG.Open.pRank p B')
    (hU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B' ≤ Subgroup.normalizer (U : Set G)) :
    GLAIsBmax p B' := by
  obtain ⟨U, hU0, hU2, hB'U⟩ := hU
  obtain ⟨k', hk'⟩ := exists_card_eq_pow_of_isElemAbelian hp hB'
  have hle : Nat.card ↥B' ≤ p ^ GLATwoLocalRank p G :=
    card_le_pow_glaTwoLocalRank hp hB' hU0 hU2 hB'U
  have hm : GLATwoLocalRank p G ≤ CFSG.Open.pRank p B :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1
  have hpB' : CFSG.Open.pRank p B' ≤ k' := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEel => ?_
    rw [← hk']
    exact Subgroup.card_le_of_le hE
  have hge : p ^ GLATwoLocalRank p G ≤ Nat.card ↥B' := by
    rw [hk']
    exact Nat.pow_le_pow_right hp.pos (hm.trans (hrank.trans hpB'))
  exact ⟨hB', le_antisymm hle hge, U, hU0, hU2, hB'U⟩

end CFSG.LocalAnalysis.GLTheoremA
