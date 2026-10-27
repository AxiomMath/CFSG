module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma72
public import CFSG.Quasithin.H13.A7SectionRank
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def preMod (p : ℕ) (L : Subgroup G) (H : Subgroup (PQuot p L)) : Subgroup G :=
  (H.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥L))).map L.subtype

@[expose] def modOf (p : ℕ) (L : Subgroup G) (y : G) (hy : y ∈ L) : PQuot p L :=
  QuotientGroup.mk (⟨y, hy⟩ : ↥L)

@[expose] def altFixSub {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n)))
    (Ω : Set (Fin n)) : Subgroup Q :=
  (fixingSubgroup (alternatingGroup (Fin n)) Ω).comap e.toMonoidHom

@[expose] def permOfQ {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (q : Q) :
    Equiv.Perm (Fin n) :=
  ((e q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))

theorem permOfQ_mul {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (a b : Q) :
    permOfQ e (a * b) = permOfQ e a * permOfQ e b := by
  simp [permOfQ]

theorem permOfQ_inv {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (a : Q) :
    permOfQ e a⁻¹ = (permOfQ e a)⁻¹ := by
  simp [permOfQ]

theorem permOfQ_one {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) :
    permOfQ e 1 = 1 := by
  simp [permOfQ]

theorem mem_altFixSub_iff {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n)))
    (Ω : Set (Fin n)) {q : Q} : q ∈ altFixSub e Ω ↔ ∀ i ∈ Ω, permOfQ e q i = i := by
  unfold altFixSub
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  exact Iff.rfl

theorem permOfQ_zpow {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (a : Q) (k : ℤ) :
    permOfQ e (a ^ k) = (permOfQ e a) ^ k := by
  simp [permOfQ]

theorem permOfQ_injective {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) :
    Function.Injective (permOfQ e) := fun _ _ h => e.injective (Subtype.ext h)

theorem zpowers_inf_altFixSub_support {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (yb : Q) :
    Subgroup.zpowers yb ⊓ altFixSub e ((permOfQ e yb).support : Set (Fin n)) = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro z ⟨hz, hzf⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  apply permOfQ_injective e
  rw [permOfQ_zpow] at *
  rw [permOfQ_one]
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ (permOfQ e yb).support
  · have := (mem_altFixSub_iff e _).1 hzf i (Finset.mem_coe.2 hi)
    rw [permOfQ_zpow] at this
    simpa using this
  · simpa using Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (Equiv.Perm.notMem_support.1 hi) k

theorem exists_finset_movedLetters {Q : Type} [Group Q] {n k : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n)))
    {H : Subgroup Q} (h : MovesExactly e H k) :
    ∃ Ω : Finset (Fin n), (Ω : Set (Fin n)) = movedLettersOf e H ∧ Ω.card = k := by
  classical
  refine ⟨(Set.toFinite (movedLettersOf e H)).toFinset, Set.Finite.coe_toFinset _, ?_⟩
  unfold MovesExactly at h
  rw [← h, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]

structure FourGroupData {Q : Type} [Group Q] {n : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin n))) (yb : Q)
    (Tb : Subgroup Q) : Prop where
  elemAb : IsElemAbelian 2 Tb
  card_four : Nat.card ↥Tb = 4
  yb_cyc : (((e yb : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))).cycleType = {3}
  yb_norm : yb ∈ Subgroup.normalizer (Tb : Set Q)
  moves_four : MovesExactly e Tb 4
  supp_sub : ∀ i : Fin n, (((e yb : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) i ≠ i) →
    i ∈ movedLettersOf e Tb
  trans : ∀ a ∈ movedLettersOf e Tb, ∀ b ∈ movedLettersOf e Tb, ∃ t ∈ Tb, permOfQ e t a = b

theorem l73_card_B (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n ≤ 11) :
    Nat.card ↥B = 3 ^ 4 := by
  have h4 := pow_four_le_card_of_bmax hc (IsSStarMax.bmax hB)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime (IsSStarMax.bmax hB).1
  have hrk : CFSG.Open.pRank 3 B = k :=
    pRank_eq_of_isElemAbelian_altSetup hc.prime.one_lt (IsSStarMax.bmax hB).1 hk
  have h1 := S.rank_B
  rw [hrk] at h1
  have h2 : n / 3 + 1 ≤ 4 := by omega
  have hk4 : k ≤ 4 := by omega
  have hk4' : 4 ≤ k := by
    rw [hk] at h4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  rw [hk, show k = 4 by omega]

theorem l73_card_B_mul {B : Subgroup G} {x : G} {L : Subgroup G} (hB : IsSStarMax 3 B x L)
    (hdir : IsDirectZpowersInf B x L) : Nat.card ↥B = 3 * Nat.card ↥(B ⊓ L : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hB).2.1
  have hxo : orderOf x = 3 := orderOf_eq_prime (hBel.2 x hxB) hx1
  have hzB : Subgroup.zpowers x ≤ B := (Subgroup.zpowers_le).2 hxB
  have hN : (B ⊓ L : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hBel (hzB hd) hg.1)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [← hdir.1, hdir.2, Subgroup.card_bot, Nat.card_zpowers, hxo] at h1
  simpa using h1

theorem l73_card_BL (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n ≤ 11) :
    Nat.card ↥(B ⊓ L : Subgroup G) = 3 ^ 3 := by
  have h1 := l73_card_B hc hB S hn
  have h2 := l73_card_B_mul hB S.B_eq
  rw [h1] at h2
  omega

private theorem y5x_lt_three_pow_pred {a : ℕ} (ha : 2 ≤ a) : a < 3 ^ (a - 1) := by
  have key : ∀ k : ℕ, k + 3 ≤ 3 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
  have := key k
  have e : k + 2 - 1 = k + 1 := by omega
  rw [e]
  omega

theorem elemAbelian_sameCycle {n : ℕ} {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card ↥E = 3 ^ (n / 3)) {g : Equiv.Perm (Fin n)} (hg : g ∈ E) {x : Fin n}
    (hx : g x ≠ x) : ∀ h ∈ E, g.SameCycle x (h x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ y ∈ E, y ^ 3 = 1 := hE.2
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : IsPGroup 3 E := fun y => ⟨1, Subtype.ext (by simpa using hpow y y.2)⟩
  set O := MulAction.orbit E x with hO
  obtain ⟨a, ha⟩ := hE2.card_orbit x
  rw [← hO] at ha
  have hsm : ∀ (k : E) (y : Fin n), k • y = (k : Equiv.Perm (Fin n)) y := fun _ _ => rfl
  have hgO : g x ∈ O := ⟨⟨g, hg⟩, rfl⟩
  have hO2 : 2 ≤ Nat.card O := by
    have hsub : ({x, g x} : Set (Fin n)) ⊆ O := by
      intro y hy
      rcases hy with rfl | rfl
      · exact MulAction.mem_orbit_self y
      · exact hgO
    have h := Set.ncard_le_ncard hsub (Set.toFinite O)
    rw [Set.ncard_pair hx.symm] at h
    rwa [Nat.card_coe_set_eq]
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at ha
      omega
    · exact h
  set Of : Finset (Fin n) := (Set.toFinite O).toFinset with hOf
  have hOfcard : Of.card = 3 ^ a := by
    rw [hOf, ← Set.ncard_eq_toFinset_card O, ← Nat.card_coe_set_eq, ha]
  have hle : 3 ^ a ≤ n := by
    have := Finset.card_le_univ Of
    rw [Fintype.card_fin, hOfcard] at this
    exact this
  set K : Subgroup (Equiv.Perm (Fin n)) := (MulAction.stabilizer E x).map E.subtype with hK
  have hKcard : Nat.card K = Nat.card (MulAction.stabilizer E x) :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩
    exact hcomm u u.2 v v.2
  have hKpow : ∀ a ∈ K, a ^ 3 = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hpow u u.2
  have hKfix : ∀ k ∈ K, ∀ y ∈ Of, k y = y := by
    rintro _ ⟨u, hu, rfl⟩ y hy
    have hu' : (u : Equiv.Perm (Fin n)) x = x := hu
    rw [hOf, Set.Finite.mem_toFinset] at hy
    obtain ⟨j, rfl⟩ := hy
    show (u : Equiv.Perm (Fin n)) ((j : Equiv.Perm (Fin n)) x) = (j : Equiv.Perm (Fin n)) x
    rw [← Equiv.Perm.mul_apply, hcomm u u.2 j j.2, Equiv.Perm.mul_apply, hu']
  have hEcard : Nat.card E = Nat.card (MulAction.stabilizer E x) * 3 ^ a := by
    rw [← Subgroup.card_mul_index (MulAction.stabilizer E x), MulAction.index_stabilizer,
      ← hO, ← Nat.card_coe_set_eq, ha]
  have hXc : (Of)ᶜ.card = n - 3 ^ a := by
    rw [Finset.card_compl, Fintype.card_fin, hOfcard]
  have hKbound : Nat.card K ≤ 3 ^ ((n - 3 ^ a) / 3) :=
    CFSG.Quasithin.H13.A7.card_le_pow_of_fixes (p := 3) (n - 3 ^ a) (Of)ᶜ hXc K hKcomm hKpow
      (fun k hk y hy => hKfix k hk y (by simpa using hy))
  have hineq : 3 ^ (n / 3) ≤ 3 ^ ((n - 3 ^ a) / 3 + a) := by
    calc 3 ^ (n / 3) = Nat.card E := hcard.symm
      _ = Nat.card K * 3 ^ a := by rw [hEcard, hKcard]
      _ ≤ 3 ^ ((n - 3 ^ a) / 3) * 3 ^ a := Nat.mul_le_mul_right _ hKbound
      _ = 3 ^ ((n - 3 ^ a) / 3 + a) := (pow_add _ _ _).symm
  have harith : n / 3 ≤ (n - 3 ^ a) / 3 + a := (Nat.pow_le_pow_iff_right (by norm_num)).1 hineq
  have ha_one : a = 1 := by
    by_contra hne
    have ha2 : 2 ≤ a := by omega
    have hlt := y5x_lt_three_pow_pred ha2
    have h3 : 3 ^ a = 3 * 3 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hO3 : Nat.card O = 3 := by rw [ha, ha_one]; norm_num
  have hg3 : ∀ y : Fin n, g (g (g y)) = y := by
    intro y
    have := congrArg (fun p : Equiv.Perm (Fin n) => p y) (hpow g hg)
    simpa [pow_three, Equiv.Perm.mul_apply] using this
  have hgx2 : g (g x) ≠ x := by
    intro h
    have h2 : g (g (g x)) = g x := by rw [h]
    exact hx (h2.symm.trans (hg3 x))
  have hgx12 : g x ≠ g (g x) := by
    intro h
    exact hx (g.injective h).symm
  have hcard3 : ({x, g x, g (g x)} : Set (Fin n)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hgx2]), Set.ncard_pair hgx12]
  have hsub3 : ({x, g x, g (g x)} : Set (Fin n)) ⊆ O := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact hgO
    · exact ⟨⟨g * g, E.mul_mem hg hg⟩, rfl⟩
  have hthree : ({x, g x, g (g x)} : Set (Fin n)) = O :=
    Set.eq_of_subset_of_ncard_le hsub3 (by rw [hcard3, ← Nat.card_coe_set_eq, hO3]) (Set.toFinite _)
  intro h hh
  have hmem : h x ∈ ({x, g x, g (g x)} : Set (Fin n)) := by
    rw [hthree]
    exact ⟨⟨h, hh⟩, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h1 | h1
  · rw [h1]
    try exact Equiv.Perm.SameCycle.refl g x
  · rw [h1]
    exact ⟨1, by rw [zpow_one]⟩
  · rw [h1]
    exact ⟨2, by rw [zpow_two, Equiv.Perm.mul_apply]⟩

theorem elemAbelian_cycleOf_mem {n : ℕ} {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card ↥E = 3 ^ (n / 3)) {g : Equiv.Perm (Fin n)} (hg : g ∈ E) {x : Fin n}
    (hx : g x ≠ x) : g.cycleOf x ∈ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ y ∈ E, y ^ 3 = 1 := hE.2
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsame := elemAbelian_sameCycle hE hcard hg hx
  set c := g.cycleOf x with hc
  have hconj : ∀ k : Equiv.Perm (Fin n), k * g = g * k → ∀ a b, g.SameCycle a b →
      g.SameCycle (k a) (k b) := by
    intro k hk a b hab
    have := hab.conj (g := k)
    rwa [show k * g * k⁻¹ = g by rw [hk, mul_inv_cancel_right]] at this
  have hiff : ∀ h ∈ E, ∀ y, g.SameCycle x y ↔ g.SameCycle x (h y) := by
    intro h hh y
    constructor
    · intro hxy
      exact (hsame h hh).trans (hconj h (hcomm h hh g hg) x y hxy)
    · intro hxy
      have hh' : h⁻¹ ∈ E := E.inv_mem hh
      have hk' : h⁻¹ * g = g * h⁻¹ := Commute.inv_left (hcomm h hh g hg : Commute h g)
      have h2 : g.SameCycle (h⁻¹ x) y := by
        have := hconj h⁻¹ hk' x (h y) hxy
        have hhy : h⁻¹ (h y) = y := by simp
        rwa [hhy] at this
      exact (hsame h⁻¹ hh').trans h2
  have hcomm_c : ∀ h ∈ E, h * c = c * h := by
    intro h hh
    refine Equiv.ext (fun y => ?_)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc, Equiv.Perm.cycleOf_apply,
      Equiv.Perm.cycleOf_apply]
    by_cases hy : g.SameCycle x y
    · have hy' := (hiff h hh y).1 hy
      rw [if_pos hy, if_pos hy']
      have := congrArg (fun p : Equiv.Perm (Fin n) => p y) (hcomm h hh g hg)
      simpa [Equiv.Perm.mul_apply] using this
    · have hy' : ¬ g.SameCycle x (h y) := fun h' => hy ((hiff h hh y).2 h')
      rw [if_neg hy, if_neg hy']
  have hc3 : c ^ 3 = 1 := by
    have hcyc : c.IsCycle := Equiv.Perm.isCycle_cycleOf g hx
    have hdvd : orderOf c ∣ 3 :=
      (Equiv.Perm.orderOf_cycleOf_dvd_orderOf g x).trans (orderOf_dvd_of_pow_eq_one (hpow g hg))
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hcyc.ne_one
    · rw [← h1]
      exact pow_orderOf_eq_one c
  set S : Set (Equiv.Perm (Fin n)) := (E : Set (Equiv.Perm (Fin n))) ∪ {c} with hS
  have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    rintro s (hs | hs) t (ht | ht)
    · exact hcomm s hs t ht
    · rw [Set.mem_singleton_iff.1 ht]
      exact hcomm_c s hs
    · rw [Set.mem_singleton_iff.1 hs]
      exact (hcomm_c t ht).symm
    · rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht]
  have hcentS : ∀ s ∈ S, s ∈ Subgroup.centralizer S := fun s hs =>
    Subgroup.mem_centralizer_iff.2 (fun t ht => hSc t ht s hs)
  have hcentS' : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 hcentS
  have hFcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have hcent_a : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n))) := by
      refine (Subgroup.closure_le _).2 (fun s hs => Subgroup.mem_centralizer_iff.2 (fun t ht => ?_))
      rw [Set.mem_singleton_iff.1 ht]
      exact (Subgroup.mem_centralizer_iff.1 (hcentS' ha) s hs).symm
    exact Subgroup.mem_centralizer_iff.1 (hcent_a hb) a rfl
  have hFpow : ∀ a ∈ Subgroup.closure S, a ^ 3 = 1 := by
    intro a ha
    exact Subgroup.closure_induction (p := fun a _ => a ^ 3 = 1)
      (fun x hx => by
        rcases hx with hx | hx
        · exact hpow x hx
        · rw [Set.mem_singleton_iff.1 hx]
          exact hc3)
      (one_pow 3)
      (fun x y hx hy hpx hpy => by
        rw [Commute.mul_pow (show Commute x y from hFcomm x hx y hy) 3, hpx, hpy, one_mul])
      (fun x _ hpx => by rw [inv_pow, hpx, inv_one]) ha
  have hFcard : Nat.card (Subgroup.closure S) ≤ 3 ^ (n / 3) :=
    CFSG.Quasithin.H13.A7.card_le_pow_of_fixes (p := 3) n Finset.univ (by simp)
      (Subgroup.closure S) hFcomm hFpow (fun _ _ y hy => absurd (Finset.mem_univ y) hy)
  have hEF : E ≤ Subgroup.closure S := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hEeq : E = Subgroup.closure S :=
    Subgroup.eq_of_le_of_card_ge hEF (by rw [hcard]; exact hFcard)
  rw [hEeq]
  exact Subgroup.subset_closure (show c ∈ S from Or.inr rfl)

theorem exists_three_cycle_of_maxRank {Q : Type} [Group Q] {n : ℕ}
    (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn : 3 ≤ n) {E : Subgroup Q} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card ↥E = 3 ^ (n / 3)) : ∃ c ∈ E, (permOfQ e c).cycleType = {3} := by
  classical
  let φ : Q →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφ : ∀ q, φ q = permOfQ e q := fun q => rfl
  have hE'el : IsElemAbelian 3 (E.map φ) := IsElemAbelian.map hE φ
  have hE'card : Nat.card ↥(E.map φ) = 3 ^ (n / 3) := by
    rw [← hcard]; exact Subgroup.card_map_of_injective hφinj
  have hne : E.map φ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE'card
    have h1 : 1 ≤ n / 3 := by omega
    have h2 : 3 ^ 1 ≤ 3 ^ (n / 3) := Nat.pow_le_pow_right (by norm_num) h1
    omega
  obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨x, hx⟩ : ∃ x, (g : Equiv.Perm (Fin n)) x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact hg1 (Subtype.ext (Equiv.ext hcon))
  have hc := elemAbelian_cycleOf_mem hE'el hE'card g.2 hx
  obtain ⟨c, hcE, hcc⟩ := id hc
  refine ⟨c, hcE, ?_⟩
  rw [← hφ, hcc]
  have hcyc : ((g : Equiv.Perm (Fin n)).cycleOf x).IsCycle := Equiv.Perm.isCycle_cycleOf _ hx
  have h3 : ((g : Equiv.Perm (Fin n)).cycleOf x) ^ 3 = 1 := hE'el.2 _ hc
  have hord : orderOf ((g : Equiv.Perm (Fin n)).cycleOf x) = 3 :=
    orderOf_eq_prime h3 hcyc.ne_one
  rw [hcyc.cycleType, ← hcyc.orderOf, hord]

theorem imageMod_eq_bot_iff {p : ℕ} {L T : Subgroup G} (hT : T ≤ L) :
    imageMod p L T = ⊥ ↔ T ≤ GLAPPrimeCoreOf p L := by
  unfold imageMod GLAPPrimeCoreOf
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro h
    have := Subgroup.map_mono (f := L.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hT] at this
  · intro h x hx
    have hx' : (x : G) ∈ T := hx
    obtain ⟨y, hy, hyx⟩ := h hx'
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem imageMod_preMod (p : ℕ) (L : Subgroup G) (H : Subgroup (PQuot p L)) :
    imageMod p L (preMod p L H) = H := by
  unfold imageMod preMod
  have h1 : ((Subgroup.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) H).map L.subtype).subgroupOf L =
      Subgroup.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) H :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h1]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H

theorem preMod_le (p : ℕ) (L : Subgroup G) (H : Subgroup (PQuot p L)) : preMod p L H ≤ L := by
  rintro _ ⟨l, -, rfl⟩
  exact l.2

theorem primeCoreOf_le_self (p : ℕ) (L : Subgroup G) : GLAPPrimeCoreOf p L ≤ L := by
  rintro _ ⟨g, hg, rfl⟩
  exact g.2

theorem imageMod_mono {p : ℕ} {L T T' : Subgroup G} (h : T ≤ T') : imageMod p L T ≤ imageMod p L T' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem imageMod_sup {p : ℕ} {L T T' : Subgroup G} (hT : T ≤ L) (hT' : T' ≤ L) :
    imageMod p L (T ⊔ T') = imageMod p L T ⊔ imageMod p L T' := by
  unfold imageMod
  rw [Subgroup.subgroupOf_sup hT hT', Subgroup.map_sup]

theorem glaPLayer_le_layer_of_le {p : ℕ} (hp : p.Prime) {X Y : Subgroup G} (hYX : Y ≤ X)
    (h : GLAPLayer p X ≤ Y) : GLAPLayer p X ≤ GLAPLayer p Y :=
  sSup_le fun M hM => le_sSup (glaPComponent_of_le hp hM ((le_sSup hM).trans h) hYX)

theorem mem_preMod_iff {p : ℕ} {L : Subgroup G} {Tb : Subgroup (PQuot p L)} {z : G} :
    z ∈ preMod p L Tb ↔ ∃ hz : z ∈ L, (QuotientGroup.mk (⟨z, hz⟩ : ↥L) : PQuot p L) ∈ Tb := by
  unfold preMod
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, h, rfl⟩

theorem imageMod_sSup {p : ℕ} {L : Subgroup G} {S : Set (Subgroup G)} (hS : ∀ J ∈ S, J ≤ L) :
    imageMod p L (sSup S) = sSup (imageMod p L '' S) := by
  refine le_antisymm ?_ (sSup_le ?_)
  · have h : sSup S ≤ preMod p L (sSup (imageMod p L '' S)) := by
      refine sSup_le fun J hJ z hz => ?_
      rw [mem_preMod_iff]
      refine ⟨hS J hJ hz, le_sSup (Set.mem_image_of_mem (imageMod p L) hJ) ?_⟩
      exact ⟨⟨z, hS J hJ hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    calc imageMod p L (sSup S) ≤ imageMod p L (preMod p L (sSup (imageMod p L '' S))) :=
          imageMod_mono h
      _ = sSup (imageMod p L '' S) := imageMod_preMod p L _
  · rintro _ ⟨J, hJ, rfl⟩
    exact imageMod_mono (le_sSup hJ)

theorem mem_normalizer_preMod {p : ℕ} {L : Subgroup G} {Tb : Subgroup (PQuot p L)} {g : G}
    (hg : g ∈ L) (h : modOf p L g hg ∈ Subgroup.normalizer (Tb : Set (PQuot p L))) :
    g ∈ Subgroup.normalizer (preMod p L Tb : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro z
  rw [mem_preMod_iff, mem_preMod_iff]
  constructor
  · rintro ⟨hz, hzT⟩
    have hgz : g * z * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg hz) (L.inv_mem hg)
    refine ⟨hgz, ?_⟩
    have := (h (QuotientGroup.mk (⟨z, hz⟩ : ↥L))).1 hzT
    convert this using 1
    rfl
  · rintro ⟨hgz, hT⟩
    have hz : z ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem hg) hgz) hg
      simpa [mul_assoc] using this
    refine ⟨hz, ?_⟩
    apply (h (QuotientGroup.mk (⟨z, hz⟩ : ↥L))).2
    convert hT using 1
    rfl

theorem normalizer_preMod_of_centralizes {p : ℕ} {L : Subgroup G} {x : G}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (Tb : Subgroup (PQuot p L)) :
    x ∈ Subgroup.normalizer (preMod p L Tb : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hc : ∀ w ∈ preMod p L Tb, x * w * x⁻¹ = w := fun w hw => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hxL (preMod_le p L Tb hw))
    rw [← this, mul_inv_cancel_right]
  constructor
  · intro hz; rwa [hc z hz]
  · intro hw
    have hwx := Subgroup.mem_centralizer_singleton_iff.1 (hxL (preMod_le p L Tb hw))
    have h3 : x⁻¹ * (x * z * x⁻¹) * x = x * z * x⁻¹ := by
      calc x⁻¹ * (x * z * x⁻¹) * x = x⁻¹ * ((x * z * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * z * x⁻¹)) := by rw [hwx]
        _ = x * z * x⁻¹ := by group
    have h2 : z = x * z * x⁻¹ := by
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = x * z * x⁻¹ := h3
    rw [h2]; exact hw

theorem altDxy_le_normalizer_preMod {L : Subgroup G} {x y : G} (hxL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hy : y ∈ L) {Tb : Subgroup (PQuot 3 L)}
    (hyT : modOf 3 L y hy ∈ Subgroup.normalizer (Tb : Set (PQuot 3 L))) :
    altDxy x y ≤ Subgroup.normalizer (preMod 3 L Tb : Set G) := by
  unfold altDxy
  exact sup_le ((Subgroup.zpowers_le).2 (normalizer_preMod_of_centralizes hxL Tb))
    ((Subgroup.zpowers_le).2 (mem_normalizer_preMod hy hyT))

theorem le_normalizer_preMod_of_image {L B : Subgroup G} {x : G} (hxL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hdir : IsDirectZpowersInf B x L) {Tb : Subgroup (PQuot 3 L)}
    (h : imageMod 3 L (B ⊓ L) ≤ Subgroup.normalizer (Tb : Set (PQuot 3 L))) :
    B ≤ Subgroup.normalizer (preMod 3 L Tb : Set G) := by
  rw [hdir.1]
  refine sup_le ((Subgroup.zpowers_le).2 (normalizer_preMod_of_centralizes hxL Tb)) ?_
  intro g hg
  refine mem_normalizer_preMod hg.2 (h ?_)
  exact Subgroup.mem_map.2 ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩

theorem imageMod_elemAbelian {p : ℕ} (hp : p.Prime) {L E : Subgroup G} (hEL : E ≤ L)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (imageMod p L E) ∧ Nat.card ↥(imageMod p L E) = Nat.card ↥E := by
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥E →* PQuot p L := (QuotientGroup.mk' (GLAPPrimeCore p ↥L)).comp (Subgroup.inclusion hEL)
  have hrange : imageMod p L E = φ.range := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨Subgroup.inclusion hEL e, e.2, rfl⟩
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    have he' : Subgroup.inclusion hEL e ∈ GLAPPrimeCore p ↥L := by
      have := (MonoidHom.mem_ker).1 he
      exact (QuotientGroup.eq_one_iff _).1 this
    have h1 : (Subgroup.inclusion hEL e) ^ p = 1 := by
      apply Subtype.ext
      have := hE.2 (e : G) e.2
      simpa using this
    have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
    have hord : orderOf (⟨Subgroup.inclusion hEL e, he'⟩ : ↥(GLAPPrimeCore p ↥L)) = 1 := by
      have h2 : orderOf (⟨Subgroup.inclusion hEL e, he'⟩ : ↥(GLAPPrimeCore p ↥L)) ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext h1
      have h3 : orderOf (⟨Subgroup.inclusion hEL e, he'⟩ : ↥(GLAPPrimeCore p ↥L)) ∣
          Nat.card ↥(GLAPPrimeCore p ↥L) := orderOf_dvd_natCard _
      exact (hcop.coprime_dvd_left h2).eq_one_of_dvd h3
    have : (⟨Subgroup.inclusion hEL e, he'⟩ : ↥(GLAPPrimeCore p ↥L)) = 1 := orderOf_eq_one_iff.1 hord
    have h4 : Subgroup.inclusion hEL e = 1 := congrArg Subtype.val this
    apply Subtype.ext
    simpa using congrArg Subtype.val h4
  rw [hrange]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    congr 1
    exact hE.1.is_comm.comm a' b'
  · obtain ⟨e, rfl⟩ := hx
    rw [← map_pow]
    have : (e : ↥E) ^ p = 1 := Subtype.ext (by simpa using hE.2 (e : G) e.2)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

theorem imageMod_glaPLayer {p : ℕ} (hp : p.Prime) {L X : Subgroup G} (hXL : X ≤ L) :
    imageMod p L (GLAPLayer p X) = GLAPLayer p (imageMod p L X) := by
  have hker : Nat.Coprime p (Nat.card ↥((X.subgroupOf L) ⊓ (pQuotHom p L).ker)) :=
    coprime_card_inf_ker_pQuotHom hp L (X.subgroupOf L)
  have h1 : ∀ J, GLAPComponent p X J → GLAPComponent p (imageMod p L X) (imageMod p L J) := by
    intro J hJ
    exact glaPComponent_map hp (pQuotHom p L) hker (glaPComponent_subgroupOf hp hXL hJ)
  have h2 : ∀ I, GLAPComponent p (imageMod p L X) I →
      ∃ J, GLAPComponent p X J ∧ imageMod p L J = I := by
    intro I hI
    obtain ⟨K, hK, hKI⟩ := exists_glaPComponent_map_eq hp (pQuotHom p L) hker hI
    have hsub : Nat.Coprime p (Nat.card ↥((X.subgroupOf L) ⊓ L.subtype.ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    refine ⟨K.map L.subtype, ?_, ?_⟩
    · have := glaPComponent_map hp L.subtype hsub hK
      rwa [Subgroup.map_subgroupOf_eq_of_le hXL] at this
    · have h3 : (K.map L.subtype).subgroupOf L = K :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
      show ((K.map L.subtype).subgroupOf L).map (pQuotHom p L) = I
      rw [h3]
      exact hKI
  have hset : {I | GLAPComponent p (imageMod p L X) I} =
      imageMod p L '' {J | GLAPComponent p X J} := by
    ext I
    constructor
    · intro hI
      obtain ⟨J, hJ, rfl⟩ := h2 I hI
      exact ⟨J, hJ, rfl⟩
    · rintro ⟨J, hJ, rfl⟩
      exact h1 J hJ
  unfold GLAPLayer
  rw [hset]
  exact imageMod_sSup (fun J hJ => (hJ.1).trans hXL)

theorem inf_primeCoreOf_le {p : ℕ} (hp : p.Prime) {L I : Subgroup G} (hIL : I ≤ L) :
    I ⊓ GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p I := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥I := (I ⊓ GLAPPrimeCoreOf p L).subgroupOf I with hN
  have hIO : I ≤ Subgroup.normalizer ((I ⊓ GLAPPrimeCoreOf p L : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hgL : g ∈ L := hIL hg
    have hgO : g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := le_normalizer_glaPPrimeCoreOf p L hgL
    have hgI : g ∈ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer hg
    constructor
    · intro hz
      exact ⟨(Subgroup.mem_normalizer_iff.1 hgI z).1 hz.1, (Subgroup.mem_normalizer_iff.1 hgO z).1 hz.2⟩
    · intro hz
      exact ⟨(Subgroup.mem_normalizer_iff.1 hgI z).2 hz.1, (Subgroup.mem_normalizer_iff.1 hgO z).2 hz.2⟩
  have hNnorm : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hIO
  have hNcop : Nat.Coprime p (Nat.card ↥N) := by
    have h1 : Nat.card ↥N = Nat.card ↥(I ⊓ GLAPPrimeCoreOf p L : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2 : Nat.card ↥(I ⊓ GLAPPrimeCoreOf p L : Subgroup G) ∣ Nat.card ↥(GLAPPrimeCoreOf p L) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(GLAPPrimeCoreOf p L) = Nat.card ↥(GLAPPrimeCore p ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (h2.trans (h3 ▸ dvd_rfl)) hcop
  have hNle : N ≤ GLAPPrimeCore p ↥I := le_sSup ⟨hNnorm, hNcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hNle hx, rfl⟩

open Equiv in
theorem primeCore_le_of_imageMod_simple {p : ℕ} (hp : p.Prime) {L I : Subgroup G} (hIL : I ≤ L)
    (hs : IsSimpleGroup ↥(imageMod p L I)) (hdvd : p ∣ Nat.card ↥(imageMod p L I)) :
    GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOI : GLAPPrimeCoreOf p I ≤ I := primeCoreOf_le_self p I
  have hOL : GLAPPrimeCoreOf p I ≤ L := hOI.trans hIL
  set M := imageMod p L (GLAPPrimeCoreOf p I) with hM
  have hMI : M ≤ imageMod p L I := imageMod_mono hOI
  have hMn : (M.subgroupOf (imageMod p L I)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hMI).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have hiI : (i : G) ∈ I := Subgroup.mem_subgroupOf.1 hi
    have hnI : (i : G) ∈ Subgroup.normalizer (GLAPPrimeCoreOf p I : Set G) :=
      le_normalizer_glaPPrimeCoreOf p I hiI
    constructor
    · rintro ⟨o, ho, rfl⟩
      refine ⟨i * o * i⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 hnI _).1 (Subgroup.mem_subgroupOf.1 ho)
    · intro hm
      obtain ⟨o, ho, hoe⟩ := hm
      refine ⟨i⁻¹ * o * i, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnI) _).1 (Subgroup.mem_subgroupOf.1 ho)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hoe]; group
  have hbot : M.subgroupOf (imageMod p L I) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (imageMod p L I)) with h | h
    · exact h
    · exfalso
      have hc : Nat.card ↥M = Nat.card ↥(imageMod p L I) := by
        rw [← Subgroup.card_top (G := ↥(imageMod p L I)), ← h,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMI).toEquiv]
      have h1 : Nat.card ↥M ∣ Nat.card ↥(GLAPPrimeCoreOf p I) := by
        rw [hM]; unfold imageMod
        refine (Subgroup.card_map_dvd _ _).trans ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOL).toEquiv]
      have h2 : Nat.card ↥(GLAPPrimeCoreOf p I) = Nat.card ↥(GLAPPrimeCore p ↥I) :=
        Subgroup.card_map_of_injective I.subtype_injective
      have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥I)) := CFSG.pPrimeCore_coprime_card
      rw [hc, h2] at h1
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (hdvd.trans h1))
  have hMb : M = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have : (⟨m, hMI hm⟩ : ↥(imageMod p L I)) ∈ M.subgroupOf (imageMod p L I) := hm
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  exact (imageMod_eq_bot_iff hOL).1 hMb

section Perm

variable {Q : Type} [Group Q] {n : ℕ}

open Equiv in
theorem exists_kleinFour_perm {n : ℕ} (Ω : Finset (Fin n)) (hΩ : Ω.card = 4) :
    ∃ V : Subgroup (Equiv.Perm (Fin n)), IsElemAbelian 2 V ∧ Nat.card ↥V = 4 ∧
      (∀ v ∈ V, Equiv.Perm.sign v = 1) ∧ {i | ∃ v ∈ V, v i ≠ i} = (Ω : Set (Fin n)) ∧
      (∀ a ∈ Ω, ∀ b ∈ Ω, ∃ v ∈ V, v a = b) ∧
      ∀ g : Equiv.Perm (Fin n), (∀ i ∈ Ω, g i ∈ Ω) →
        g ∈ Subgroup.normalizer (V : Set (Equiv.Perm (Fin n))) := by
  classical
  have hΩ' : Nat.card ↥Ω = 4 := by simp [hΩ]
  let ψ : ↥(alternatingGroup ↥Ω) →* Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (alternatingGroup.ofSubtype Ω)
  set V : Subgroup (Perm (Fin n)) := (alternatingGroup.kleinFour ↥Ω).map ψ with hV
  have hmem : ∀ v : Perm (Fin n), v ∈ V ↔ v.support ⊆ Ω ∧ (v = 1 ∨ v.cycleType = {2, 2}) := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (alternatingGroup.mem_map_kleinFour_ofSubtype hΩ (alternatingGroup.ofSubtype Ω w)).1
        ⟨w, hw, rfl⟩
    · intro h
      have hv : v ∈ alternatingGroup (Fin n) := by
        rcases h.2 with h1 | h1
        · rw [h1]; exact Subgroup.one_mem _
        · exact Equiv.Perm.cycleType_eq_two_two_subset_alternatingGroup h1
      obtain ⟨w, hw, hwv⟩ := (alternatingGroup.mem_map_kleinFour_ofSubtype hΩ ⟨v, hv⟩).2 h
      exact ⟨w, hw, by simp [ψ, hwv]⟩
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin n)).subtype_injective.comp alternatingGroup.ofSubtype_injective
  haveI hK : IsKleinFour (alternatingGroup.kleinFour ↥Ω) := alternatingGroup.kleinFour_isKleinFour hΩ'
  have hcard : Nat.card ↥V = 4 := by
    rw [hV, Subgroup.card_map_of_injective hψinj]; exact IsKleinFour.card_four
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    rcases ((hmem v).1 hv).2 with h1 | h1
    · rw [h1, one_pow]
    · have : orderOf v = 2 := by rw [← Equiv.Perm.lcm_cycleType, h1]; decide
      rw [← this]; exact pow_orderOf_eq_one v
  have hcomm : IsMulCommutative ↥V := by
    have hc := (IsKleinFour.isMulCommutative (G := ↥(alternatingGroup.kleinFour ↥Ω))).is_comm
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', haa⟩ := a.2
    obtain ⟨b', hb', hbb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← haa, ← hbb, ← map_mul, ← map_mul]
    have := congrArg Subtype.val (hc.comm (⟨a', ha'⟩ : ↥(alternatingGroup.kleinFour ↥Ω)) ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this]
  have htrans : ∀ a ∈ Ω, ∀ b ∈ Ω, ∃ v ∈ V, v a = b := by
    intro a ha b hb
    by_cases hab : a = b
    · exact ⟨1, V.one_mem, by simp [hab]⟩
    have h2 : 2 ≤ ((Ω.erase a).erase b).card := by
      have h1 := Finset.card_erase_of_mem ha
      have h1' := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hab, hb⟩)
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 (by omega : 1 < ((Ω.erase a).erase b).card)
    have hcb := Finset.ne_of_mem_erase hc
    have hca := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    have hcΩ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
    have hdb := Finset.ne_of_mem_erase hd
    have hda := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hd)
    have hdΩ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)
    have hdisj : Equiv.Perm.Disjoint (swap a b) (swap c d) := by
      intro i
      by_cases hi : i = a ∨ i = b
      · right; rcases hi with rfl | rfl
        · exact swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hda)
        · exact swap_apply_of_ne_of_ne (Ne.symm hcb) (Ne.symm hdb)
      · left; push Not at hi; exact swap_apply_of_ne_of_ne hi.1 hi.2
    refine ⟨swap a b * swap c d, (hmem _).2 ⟨?_, Or.inr ?_⟩, ?_⟩
    · intro i hi
      have := Equiv.Perm.support_mul_le (swap a b) (swap c d) hi
      rcases Finset.mem_union.1 this with h | h
      · rcases Equiv.eq_or_eq_of_swap_apply_ne_self (Equiv.Perm.mem_support.1 h) with rfl | rfl
        · exact ha
        · exact hb
      · rcases Equiv.eq_or_eq_of_swap_apply_ne_self (Equiv.Perm.mem_support.1 h) with rfl | rfl
        · exact hcΩ
        · exact hdΩ
    · rw [hdisj.cycleType_mul, (Equiv.Perm.isCycle_swap hab).cycleType,
        (Equiv.Perm.isCycle_swap hcd).cycleType, Equiv.Perm.card_support_swap hab,
        Equiv.Perm.card_support_swap hcd]
      rfl
    · simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hda)]
  refine ⟨V, ⟨hcomm, hsq⟩, hcard, ?_, ?_, htrans, ?_⟩
  · intro v hv
    obtain ⟨w, -, rfl⟩ := hv
    exact (alternatingGroup.ofSubtype Ω w).2
  · ext i
    constructor
    · rintro ⟨v, hv, hvi⟩
      exact ((hmem v).1 hv).1 (Equiv.Perm.mem_support.2 hvi)
    · intro hi
      have hi' : i ∈ Ω := hi
      obtain ⟨j, hj, hji⟩ : ∃ j ∈ Ω, j ≠ i := by
        by_contra hcon
        push Not at hcon
        have : Ω ⊆ {i} := fun j hj => Finset.mem_singleton.2 (hcon j hj)
        have := Finset.card_le_card this
        rw [hΩ, Finset.card_singleton] at this
        omega
      obtain ⟨v, hv, hvi⟩ := htrans i hi' j hj
      exact ⟨v, hv, by rw [hvi]; exact hji⟩
  · intro g hg
    have hgΩ : Ω.map g.toEmbedding = Ω := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
        exact hg j hj
      · rw [Finset.card_map]
    have hginv : ∀ i ∈ Ω, g⁻¹ i ∈ Ω := by
      intro i hi
      rw [← hgΩ] at hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      simpa using hj
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem, Equiv.Perm.cycleType_conj]
    have h1 : g * h * g⁻¹ = 1 ↔ h = 1 := by
      constructor
      · intro e; have := congrArg (fun z => g⁻¹ * z * g) e; simpa [mul_assoc] using this
      · rintro rfl; simp
    rw [h1]
    have h2 : (g * h * g⁻¹).support ⊆ Ω ↔ h.support ⊆ Ω := by
      constructor
      · intro hs i hi
        have : g i ∈ (g * h * g⁻¹).support := by
          rw [Equiv.Perm.mem_support]; simpa [Perm.mul_apply] using (Equiv.Perm.mem_support.1 hi)
        have := hginv _ (hs this)
        simpa using this
      · intro hs i hi
        have : g⁻¹ i ∈ h.support := by
          rw [Equiv.Perm.mem_support]
          intro e
          apply Equiv.Perm.mem_support.1 hi
          have e' : h (g.symm i) = g.symm i := e
          simp [Perm.mul_apply, e']
        have := hg _ (hs this)
        simpa using this
    rw [h2]

private theorem y5x_dbl_disj_comm {α : Type} [DecidableEq α] (p q r s : α) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) :
    Equiv.swap p q * Equiv.swap r s = Equiv.swap r s * Equiv.swap p q := by
  apply Equiv.Perm.Disjoint.commute
  intro i
  by_cases hip : i = p
  · right
    rw [hip]
    exact Equiv.swap_apply_of_ne_of_ne hpr hps
  by_cases hiq : i = q
  · right
    rw [hiq]
    exact Equiv.swap_apply_of_ne_of_ne hqr hqs
  · left
    exact Equiv.swap_apply_of_ne_of_ne hip hiq

private theorem y5x_dbl_snd_comm {α : Type} [DecidableEq α] (p q r s : α) :
    Equiv.swap p q * Equiv.swap r s = Equiv.swap p q * Equiv.swap s r := by
  rw [Equiv.swap_comm r s]

private theorem y5x_dbl_fst_comm {α : Type} [DecidableEq α] (p q r s : α) :
    Equiv.swap p q * Equiv.swap r s = Equiv.swap q p * Equiv.swap r s := by
  rw [Equiv.swap_comm p q]

private theorem y5x_dbl_klein {α : Type} [DecidableEq α] (a b c d : α) (ne_ab : a ≠ b) (ne_ac : a ≠ c) (ne_ad : a ≠ d) (ne_ba : b ≠ a) (ne_bc : b ≠ c) (ne_bd : b ≠ d) (ne_ca : c ≠ a) (ne_cb : c ≠ b) (ne_cd : c ≠ d) (ne_da : d ≠ a) (ne_db : d ≠ b) (ne_dc : d ≠ c)
    (x y z w : α) (hx : x = a ∨ x = b ∨ x = c ∨ x = d) (hy : y = a ∨ y = b ∨ y = c ∨ y = d)
    (hz : z = a ∨ z = b ∨ z = c ∨ z = d) (hw : w = a ∨ w = b ∨ w = c ∨ w = d)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Equiv.swap x y * Equiv.swap z w = Equiv.swap a b * Equiv.swap c d ∨
      Equiv.swap x y * Equiv.swap z w = Equiv.swap a c * Equiv.swap b d ∨
      Equiv.swap x y * Equiv.swap z w = Equiv.swap a d * Equiv.swap b c := by
  rcases hx with h1 | h1 | h1 | h1 <;> rcases hy with h2 | h2 | h2 | h2 <;>
    rcases hz with h3 | h3 | h3 | h3 <;> rcases hw with h4 | h4 | h4 | h4 <;>
    subst x y z w <;>
    first
    | exact absurd rfl hxy
    | exact absurd rfl hxz
    | exact absurd rfl hxw
    | exact absurd rfl hyz
    | exact absurd rfl hyw
    | exact absurd rfl hzw
    | exact Or.inl (rfl)
    | exact Or.inl ((y5x_dbl_snd_comm a b d c))
    | exact Or.inr (Or.inl (rfl))
    | exact Or.inr (Or.inl ((y5x_dbl_snd_comm a c d b)))
    | exact Or.inr (Or.inr (rfl))
    | exact Or.inr (Or.inr ((y5x_dbl_snd_comm a d c b)))
    | exact Or.inl ((y5x_dbl_fst_comm b a c d))
    | exact Or.inl ((y5x_dbl_fst_comm b a d c).trans ((y5x_dbl_snd_comm a b d c)))
    | exact Or.inr (Or.inr ((y5x_dbl_disj_comm b c a d ne_ba ne_bd ne_ca ne_cd)))
    | exact Or.inr (Or.inr ((y5x_dbl_snd_comm b c d a).trans ((y5x_dbl_disj_comm b c a d ne_ba ne_bd ne_ca ne_cd))))
    | exact Or.inr (Or.inl ((y5x_dbl_disj_comm b d a c ne_ba ne_bc ne_da ne_dc)))
    | exact Or.inr (Or.inl ((y5x_dbl_snd_comm b d c a).trans ((y5x_dbl_disj_comm b d a c ne_ba ne_bc ne_da ne_dc))))
    | exact Or.inr (Or.inl ((y5x_dbl_fst_comm c a b d)))
    | exact Or.inr (Or.inl ((y5x_dbl_fst_comm c a d b).trans ((y5x_dbl_snd_comm a c d b))))
    | exact Or.inr (Or.inr ((y5x_dbl_fst_comm c b a d).trans ((y5x_dbl_disj_comm b c a d ne_ba ne_bd ne_ca ne_cd))))
    | exact Or.inr (Or.inr ((y5x_dbl_fst_comm c b d a).trans ((y5x_dbl_snd_comm b c d a).trans ((y5x_dbl_disj_comm b c a d ne_ba ne_bd ne_ca ne_cd)))))
    | exact Or.inl ((y5x_dbl_disj_comm c d a b ne_ca ne_cb ne_da ne_db))
    | exact Or.inl ((y5x_dbl_snd_comm c d b a).trans ((y5x_dbl_disj_comm c d a b ne_ca ne_cb ne_da ne_db)))
    | exact Or.inr (Or.inr ((y5x_dbl_fst_comm d a b c)))
    | exact Or.inr (Or.inr ((y5x_dbl_fst_comm d a c b).trans ((y5x_dbl_snd_comm a d c b))))
    | exact Or.inr (Or.inl ((y5x_dbl_fst_comm d b a c).trans ((y5x_dbl_disj_comm b d a c ne_ba ne_bc ne_da ne_dc))))
    | exact Or.inr (Or.inl ((y5x_dbl_fst_comm d b c a).trans ((y5x_dbl_snd_comm b d c a).trans ((y5x_dbl_disj_comm b d a c ne_ba ne_bc ne_da ne_dc)))))
    | exact Or.inl ((y5x_dbl_fst_comm d c a b).trans ((y5x_dbl_disj_comm c d a b ne_ca ne_cb ne_da ne_db)))
    | exact Or.inl ((y5x_dbl_fst_comm d c b a).trans ((y5x_dbl_snd_comm c d b a).trans ((y5x_dbl_disj_comm c d a b ne_ca ne_cb ne_da ne_db))))

theorem exists_kleinFour (e : Q ≃* ↥(alternatingGroup (Fin n))) (Ω : Finset (Fin n)) (hΩ : Ω.card = 4) :
    ∃ Tb : Subgroup Q, IsElemAbelian 2 Tb ∧ Nat.card ↥Tb = 4 ∧ movedLettersOf e Tb = (Ω : Set (Fin n)) ∧
      (∀ a ∈ Ω, ∀ b ∈ Ω, ∃ t ∈ Tb, permOfQ e t a = b) ∧
      ∀ g : Q, (∀ i ∈ Ω, permOfQ e g i ∈ Ω) → g ∈ Subgroup.normalizer (Tb : Set Q) := by
  classical
  obtain ⟨a, t, ha, hΩeq, ht⟩ := Finset.card_eq_succ.1 (show Ω.card = 3 + 1 from hΩ)
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.1 ht
  subst hΩeq
  have hab : a ≠ b := fun h => ha (by simp [h])
  have hac : a ≠ c := fun h => ha (by simp [h])
  have had : a ≠ d := fun h => ha (by simp [h])
  have hmem : ∀ x : Fin n, x ∈ insert a ({b, c, d} : Finset (Fin n)) ↔ (x = a ∨ x = b ∨ x = c ∨ x = d) := by
    intro x
    simp
  set Ω' : Finset (Fin n) := insert a ({b, c, d} : Finset (Fin n)) with hΩ'
  have hΩa : a ∈ Ω' := (hmem a).2 (Or.inl rfl)
  have hΩb : b ∈ Ω' := (hmem b).2 (Or.inr (Or.inl rfl))
  have hΩc : c ∈ Ω' := (hmem c).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hΩd : d ∈ Ω' := (hmem d).2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨s1, hs1⟩ : ∃ s : Equiv.Perm (Fin n), s = Equiv.swap a b * Equiv.swap c d := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s : Equiv.Perm (Fin n), s = Equiv.swap a c * Equiv.swap b d := ⟨_, rfl⟩
  have hs1a : s1 a = b := by
    rw [hs1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
  have hs1b : s1 b = a := by
    rw [hs1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd, Equiv.swap_apply_right]
  have hs1c : s1 c = d := by
    rw [hs1, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hs1d : s1 d = c := by
    rw [hs1, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hs2a : s2 a = c := by
    rw [hs2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_left]
  have hs2b : s2 b = d := by
    rw [hs2, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne had.symm hcd.symm]
  have hs2c : s2 c = a := by
    rw [hs2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbc.symm hcd, Equiv.swap_apply_right]
  have hs2d : s2 d = b := by
    rw [hs2, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
  have hs12a : (s1 * s2) a = d := by rw [Equiv.Perm.mul_apply, hs2a, hs1c]
  have hs12b : (s1 * s2) b = c := by rw [Equiv.Perm.mul_apply, hs2b, hs1d]
  have hs12c : (s1 * s2) c = b := by rw [Equiv.Perm.mul_apply, hs2c, hs1a]
  have hs12d : (s1 * s2) d = a := by rw [Equiv.Perm.mul_apply, hs2d, hs1b]
  have hfix1 : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → s1 i = i := by
    intro i h1 h2 h3 h4
    rw [hs1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hfix2 : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → s2 i = i := by
    intro i h1 h2 h3 h4
    rw [hs2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2 h4, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hcomm12 : s2 * s1 = s1 * s2 := by
    refine Equiv.ext (fun i => ?_)
    simp only [Equiv.Perm.mul_apply]
    by_cases h1 : i = a
    · rw [h1, hs1a, hs2b, hs2a, hs1c]
    by_cases h2 : i = b
    · rw [h2, hs1b, hs2a, hs2b, hs1d]
    by_cases h3 : i = c
    · rw [h3, hs1c, hs2d, hs2c, hs1a]
    by_cases h4 : i = d
    · rw [h4, hs1d, hs2c, hs2d, hs1b]
    simp only [hfix1 i h1 h2 h3 h4, hfix2 i h1 h2 h3 h4]
  have hs3 : Equiv.swap a d * Equiv.swap b c = s1 * s2 := by
    refine Equiv.ext (fun i => ?_)
    simp only [Equiv.Perm.mul_apply]
    by_cases h1 : i = a
    · rw [h1, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left, hs2a, hs1c]
    by_cases h2 : i = b
    · rw [h2, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hcd, hs2b, hs1d]
    by_cases h3 : i = c
    · rw [h3, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab.symm hbd, hs2c, hs1a]
    by_cases h4 : i = d
    · rw [h4, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm, Equiv.swap_apply_right, hs2d, hs1b]
    rw [Equiv.swap_apply_of_ne_of_ne h2 h3, Equiv.swap_apply_of_ne_of_ne h1 h4, hfix2 i h1 h2 h3 h4,
      hfix1 i h1 h2 h3 h4]
  have hAC1 : Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b :=
    y5x_dbl_disj_comm a b c d hac had hbc hbd
  have hAC2 : Equiv.swap a c * Equiv.swap b d = Equiv.swap b d * Equiv.swap a c :=
    y5x_dbl_disj_comm a c b d hab had hbc.symm hcd
  have sqcomm : ∀ A C : Equiv.Perm (Fin n), A * A = 1 → C * C = 1 → A * C = C * A →
      (A * C) * (A * C) = 1 := by
    intro A C hA hC hAC
    calc (A * C) * (A * C) = A * (C * A) * C := by simp only [mul_assoc]
      _ = A * (A * C) * C := by rw [← hAC]
      _ = (A * A) * (C * C) := by simp only [mul_assoc]
      _ = 1 := by rw [hA, hC, one_mul]
  have hs1sq : s1 * s1 = 1 := by
    rw [hs1]
    exact sqcomm _ _ (Equiv.swap_mul_self a b) (Equiv.swap_mul_self c d) hAC1
  have hs2sq : s2 * s2 = 1 := by
    rw [hs2]
    exact sqcomm _ _ (Equiv.swap_mul_self a c) (Equiv.swap_mul_self b d) hAC2
  have hA : s1 * (s1 * s2) = s2 := by rw [← mul_assoc, hs1sq, one_mul]
  have hB : s2 * (s1 * s2) = s1 := by
    rw [← mul_assoc, hcomm12, mul_assoc, hs2sq, mul_one]
  have hC : s1 * s2 * (s1 * s2) = 1 := by rw [mul_assoc, hB, hs1sq]
  have hs1inv : s1⁻¹ = s1 := inv_eq_of_mul_eq_one_right hs1sq
  have hs2inv : s2⁻¹ = s2 := inv_eq_of_mul_eq_one_right hs2sq
  have hs12inv : (s1 * s2)⁻¹ = s1 * s2 := inv_eq_of_mul_eq_one_right hC
  obtain ⟨V, hV⟩ : ∃ V : Subgroup (Equiv.Perm (Fin n)), V = Subgroup.closure {s1, s2} := ⟨_, rfl⟩
  have hs1V : s1 ∈ V := by rw [hV]; exact Subgroup.subset_closure (Or.inl rfl)
  have hs2V : s2 ∈ V := by rw [hV]; exact Subgroup.subset_closure (Or.inr rfl)
  have hs12V : s1 * s2 ∈ V := V.mul_mem hs1V hs2V
  have hV1 : ∀ v ∈ V, v = 1 ∨ v = s1 ∨ v = s2 ∨ v = s1 * s2 := by
    intro v hv
    rw [hV] at hv
    refine Subgroup.closure_induction (p := fun v _ => v = 1 ∨ v = s1 ∨ v = s2 ∨ v = s1 * s2)
      ?_ ?_ ?_ ?_ hv
    · intro x hx
      rcases hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
        simp only [one_mul, mul_one, mul_assoc, hs1sq, hs2sq, hcomm12, hA, hB, true_or, or_true,
          eq_self_iff_true]
    · intro x _ hx
      rcases hx with h | h | h | h <;> rw [h] <;>
        simp only [inv_one, hs1inv, hs2inv, hs12inv, true_or, or_true, eq_self_iff_true]
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    rcases hV1 v hv with h | h | h | h <;> rcases hV1 w hw with h' | h' | h' | h' <;> rw [h, h'] <;>
      simp only [one_mul, mul_one, mul_assoc, hs1sq, hs2sq, hcomm12, hA, hB]
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    rcases hV1 v hv with h | h | h | h <;> rw [h, pow_two] <;>
      simp only [one_mul, hs1sq, hs2sq, hC]
  have hs1A : s1 ∈ alternatingGroup (Fin n) := by
    rw [hs1, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    norm_num
  have hs2A : s2 ∈ alternatingGroup (Fin n) := by
    rw [hs2, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hac,
      Equiv.Perm.sign_swap hbd]
    norm_num
  have hVA : ∀ v ∈ V, v ∈ alternatingGroup (Fin n) := by
    intro v hv
    rcases hV1 v hv with h | h | h | h <;> rw [h]
    · exact (alternatingGroup (Fin n)).one_mem
    · exact hs1A
    · exact hs2A
    · exact (alternatingGroup (Fin n)).mul_mem hs1A hs2A
  have h1s1 : (1 : Equiv.Perm (Fin n)) ≠ s1 := fun h => hab (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs1a] using this)
  have h1s2 : (1 : Equiv.Perm (Fin n)) ≠ s2 := fun h => hac (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs2a] using this)
  have h1s12 : (1 : Equiv.Perm (Fin n)) ≠ s1 * s2 := fun h => had (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs12a] using this)
  have hs1s2 : s1 ≠ s2 := fun h => hbc (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs1a, hs2a] using this)
  have hs1s12 : s1 ≠ s1 * s2 := fun h => hbd (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs1a, hs12a] using this)
  have hs2s12 : s2 ≠ s1 * s2 := fun h => hcd (by
    have := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
    simpa [hs2a, hs12a] using this)
  have hcard4 : ({1, s1, s2, s1 * s2} : Set (Equiv.Perm (Fin n))).ncard = 4 := by
    have n1 : (1 : Equiv.Perm (Fin n)) ∉ ({s1, s2, s1 * s2} : Set (Equiv.Perm (Fin n))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h1s1, h1s2, h1s12⟩
    have n2 : s1 ∉ ({s2, s1 * s2} : Set (Equiv.Perm (Fin n))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hs1s2, hs1s12⟩
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair hs2s12]
  have hVeq : (V : Set (Equiv.Perm (Fin n))) = {1, s1, s2, s1 * s2} := by
    ext v
    constructor
    · intro hv
      rcases hV1 v hv with h | h | h | h <;> simp [h]
    · intro hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with h | h | h | h <;> rw [h]
      · exact V.one_mem
      · exact hs1V
      · exact hs2V
      · exact hs12V
  have hVcard : Nat.card V = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hVeq, hcard4]
  have hconjswap : ∀ (f : Equiv.Perm (Fin n)) (x y : Fin n),
      f * Equiv.swap x y * f⁻¹ = Equiv.swap (f x) (f y) :=
    fun f x y => (Equiv.swap_apply_apply f x y).symm
  have hsplit : ∀ f s t : Equiv.Perm (Fin n), f * (s * t) * f⁻¹ = (f * s * f⁻¹) * (f * t * f⁻¹) :=
    fun f s t => by group
  have hKV : ∀ x y z w : Fin n, x ∈ Ω' → y ∈ Ω' → z ∈ Ω' → w ∈ Ω' → x ≠ y → x ≠ z → x ≠ w →
      y ≠ z → y ≠ w → z ≠ w → Equiv.swap x y * Equiv.swap z w ∈ V := by
    intro x y z w hx hy hz hw hxy hxz hxw hyz hyw hzw
    rcases y5x_dbl_klein a b c d hab hac had hab.symm hbc hbd hac.symm hbc.symm hcd had.symm hbd.symm
        hcd.symm x y z w ((hmem x).1 hx) ((hmem y).1 hy) ((hmem z).1 hz) ((hmem w).1 hw)
        hxy hxz hxw hyz hyw hzw with h | h | h
    · rw [h, ← hs1]
      exact hs1V
    · rw [h, ← hs2]
      exact hs2V
    · rw [h, hs3]
      exact hs12V
  have hconj : ∀ π : Equiv.Perm (Fin n), (∀ i ∈ Ω', π i ∈ Ω') → ∀ v ∈ V, π * v * π⁻¹ ∈ V := by
    intro π hπ v hv
    have hπ' : ∀ u w : Fin n, u ≠ w → π u ≠ π w := fun u w h h' => h (π.injective h')
    rw [hV] at hv
    refine Subgroup.closure_induction (p := fun v _ => π * v * π⁻¹ ∈ V) ?_ ?_ ?_ ?_ hv
    · intro x hx
      rcases hx with h | h
      · rw [h, hs1, hsplit, hconjswap, hconjswap]
        exact hKV _ _ _ _ (hπ a hΩa) (hπ b hΩb) (hπ c hΩc) (hπ d hΩd) (hπ' a b hab) (hπ' a c hac)
          (hπ' a d had) (hπ' b c hbc) (hπ' b d hbd) (hπ' c d hcd)
      · rw [h, hs2, hsplit, hconjswap, hconjswap]
        exact hKV _ _ _ _ (hπ a hΩa) (hπ c hΩc) (hπ b hΩb) (hπ d hΩd) (hπ' a c hac) (hπ' a b hab)
          (hπ' a d had) (hπ' c b hbc.symm) (hπ' c d hcd) (hπ' b d hbd)
    · rw [mul_one, mul_inv_cancel]
      exact V.one_mem
    · intro x y _ _ ihx ihy
      rw [hsplit]
      exact V.mul_mem ihx ihy
    · intro x _ ihx
      rw [show π * x⁻¹ * π⁻¹ = (π * x * π⁻¹)⁻¹ by group]
      exact V.inv_mem ihx
  have hT : ∀ x ∈ Ω', ∀ y ∈ Ω', ∃ v ∈ V, v x = y := by
    intro x hx y hy
    rw [hmem] at hx hy
    rcases hx with h1 | h1 | h1 | h1 <;> rcases hy with h2 | h2 | h2 | h2 <;> subst x <;> subst y <;>
      first
      | exact ⟨1, V.one_mem, rfl⟩
      | exact ⟨s1, hs1V, hs1a⟩
      | exact ⟨s2, hs2V, hs2a⟩
      | exact ⟨s1 * s2, hs12V, hs12a⟩
      | exact ⟨s1, hs1V, hs1b⟩
      | exact ⟨s2, hs2V, hs2b⟩
      | exact ⟨s1 * s2, hs12V, hs12b⟩
      | exact ⟨s1, hs1V, hs1c⟩
      | exact ⟨s2, hs2V, hs2c⟩
      | exact ⟨s1 * s2, hs12V, hs12c⟩
      | exact ⟨s1, hs1V, hs1d⟩
      | exact ⟨s2, hs2V, hs2d⟩
      | exact ⟨s1 * s2, hs12V, hs12d⟩
  let φ : Q →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφsurj : ∀ v ∈ alternatingGroup (Fin n), ∃ q : Q, φ q = v :=
    fun v hv => ⟨e.symm ⟨v, hv⟩, by simp [φ]⟩
  have hVle : V ≤ φ.range := fun v hv => MonoidHom.mem_range.2 (hφsurj v (hVA v hv))
  have hcardTb : Nat.card ↥(V.comap φ) = 4 := by
    have h := Subgroup.card_map_of_injective (K := V.comap φ) hφinj
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hVle, hVcard] at h
    exact h.symm
  have hTbcomm : IsMulCommutative ↥(V.comap φ) :=
    ⟨⟨fun x y => Subtype.ext (hφinj (by
      simp only [map_mul, Subgroup.coe_mul]
      exact hVcomm (φ x) x.2 (φ y) y.2))⟩⟩
  have hTbsq : ∀ x ∈ V.comap φ, x ^ 2 = 1 := fun x hx =>
    hφinj (by rw [map_pow, map_one]; exact hVsq (φ x) hx)
  have hmoved : movedLettersOf e (V.comap φ) = (Ω' : Set (Fin n)) := by
    ext i
    constructor
    · rintro ⟨h, hh, hne⟩
      have hv : φ h ∈ V := hh
      have hne' : φ h i ≠ i := hne
      rw [Finset.mem_coe, hmem]
      by_contra hi
      push_neg at hi
      obtain ⟨hia, hib, hic, hid⟩ := hi
      apply hne'
      rcases hV1 (φ h) hv with h1 | h1 | h1 | h1
      · rw [h1, Equiv.Perm.one_apply]
      · rw [h1, hfix1 i hia hib hic hid]
      · rw [h1, hfix2 i hia hib hic hid]
      · rw [h1, Equiv.Perm.mul_apply, hfix2 i hia hib hic hid, hfix1 i hia hib hic hid]
    · intro hi
      rw [Finset.mem_coe, hmem] at hi
      obtain ⟨h, hh⟩ : ∃ q : Q, φ q = s1 := hφsurj s1 hs1A
      refine ⟨h, ?_, ?_⟩
      · show φ h ∈ V
        rw [hh]
        exact hs1V
      · show φ h i ≠ i
        rw [hh]
        rcases hi with h1 | h1 | h1 | h1 <;> rw [h1]
        · rw [hs1a]
          exact hab.symm
        · rw [hs1b]
          exact hab
        · rw [hs1c]
          exact hcd.symm
        · rw [hs1d]
          exact hcd
  have htrans : ∀ x ∈ Ω', ∀ y ∈ Ω', ∃ t ∈ V.comap φ, permOfQ e t x = y := by
    intro x hx y hy
    obtain ⟨v, hv, hvxy⟩ := hT x hx y hy
    obtain ⟨q, hq⟩ := hφsurj v (hVA v hv)
    refine ⟨q, ?_, ?_⟩
    · show φ q ∈ V
      rw [hq]
      exact hv
    · show φ q x = y
      rw [hq]
      exact hvxy
  have hnorm : ∀ g : Q, (∀ i ∈ Ω', permOfQ e g i ∈ Ω') →
      g ∈ Subgroup.normalizer ((V.comap φ : Subgroup Q) : Set Q) := by
    intro g hg
    have hσ : ∀ i ∈ Ω', φ g i ∈ Ω' := hg
    have hσinv : ∀ i ∈ Ω', (φ g)⁻¹ i ∈ Ω' := by
      intro i hi
      have himg : Ω'.image (φ g) = Ω' := Finset.eq_of_subset_of_card_le
        (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          exact hσ x hx)
        (by rw [Finset.card_image_of_injective _ (φ g).injective])
      have hi' : i ∈ Ω'.image (φ g) := by
        rw [himg]
        exact hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hi'
      have hij : (φ g)⁻¹ i = j := by
        rw [← hji]
        simp
      rw [hij]
      exact hj
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hv : φ h ∈ V := hh
      show φ (g * h * g⁻¹) ∈ V
      rw [map_mul, map_mul, map_inv]
      exact hconj (φ g) hσ (φ h) hv
    · intro hh
      have hv : φ (g * h * g⁻¹) ∈ V := hh
      rw [map_mul, map_mul, map_inv] at hv
      have h2 := hconj (φ g)⁻¹ hσinv _ hv
      have e2 : (φ g)⁻¹ * (φ g * φ h * (φ g)⁻¹) * ((φ g)⁻¹)⁻¹ = φ h := by group
      rw [e2] at h2
      exact h2
  exact ⟨V.comap φ, ⟨hTbcomm, hTbsq⟩, hcardTb, hmoved, htrans, hnorm⟩

theorem exists_fourGroup (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) (hn12 : n ≤ 12) (yb : Q)
    (hy : (permOfQ e yb).cycleType = {3}) (E : Subgroup Q)
    (hE : (n = 10 ∨ n = 11) → IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 ∧ yb ∈ E) :
    ∃ Tb : Subgroup Q, FourGroupData e yb Tb ∧
      ((n = 10 ∨ n = 11) → E ≤ Subgroup.normalizer (Tb : Set Q)) := by
  classical
  have hS3 : (permOfQ e yb).support.card = 3 := card_support_eq_of_cycleType hy
  obtain ⟨ω, hωS, hωE⟩ : ∃ ω : Fin n, ω ∉ (permOfQ e yb).support ∧
      ((n = 10 ∨ n = 11) → ∀ g ∈ E, permOfQ e g ω = ω) := by
    by_cases hn : n = 10 ∨ n = 11
    · obtain ⟨hEel, -, hybE⟩ := hE hn
      let ψ : ↥E →* Equiv.Perm (Fin n) :=
        ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom).comp E.subtype
      letI : MulAction ↥E (Fin n) := MulAction.compHom (Fin n) ψ
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hmod := (isPGroup_of_isElemAbelian hEel).card_modEq_card_fixedPoints (Fin n)
      have hne : Nat.card (MulAction.fixedPoints ↥E (Fin n)) ≠ 0 := by
        intro h0
        rw [h0] at hmod
        have h3 : n % 3 = 0 := by
          unfold Nat.ModEq at hmod
          simpa [Nat.card_eq_fintype_card] using hmod
        omega
      have hpos : 0 < Nat.card (MulAction.fixedPoints ↥E (Fin n)) := Nat.pos_of_ne_zero hne
      obtain ⟨⟨ω, hω⟩⟩ := (Nat.card_pos_iff.1 hpos).1
      have hfix : ∀ g : ↥E, permOfQ e (g : Q) ω = ω := fun g => MulAction.mem_fixedPoints.1 hω g
      refine ⟨ω, ?_, fun _ g hg => hfix ⟨g, hg⟩⟩
      intro hmem
      exact (Equiv.Perm.mem_support.1 hmem) (hfix ⟨yb, hybE⟩)
    · have : ∃ ω : Fin n, ω ∉ (permOfQ e yb).support := by
        by_contra hcon
        push_neg at hcon
        have h1 : (permOfQ e yb).support = Finset.univ := Finset.eq_univ_of_forall hcon
        rw [h1, Finset.card_univ, Fintype.card_fin] at hS3
        omega
      obtain ⟨ω, hω⟩ := this
      exact ⟨ω, hω, fun h => absurd h hn⟩
  set S := (permOfQ e yb).support with hSdef
  have hΩ4 : (insert ω S).card = 4 := by rw [Finset.card_insert_of_notMem hωS, hS3]
  obtain ⟨Tb, hel, hcard, hmoved, htrans, hnorm⟩ := exists_kleinFour e (insert ω S) hΩ4
  have hybpres : ∀ i ∈ insert ω S, permOfQ e yb i ∈ insert ω S := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hiS
    · have : permOfQ e yb i = i := Equiv.Perm.notMem_support.1 hωS
      rw [this]
      exact hi
    · exact Finset.mem_insert_of_mem (Equiv.Perm.apply_mem_support.2 hiS)
  have hFG : FourGroupData e yb Tb :=
    { elemAb := hel
      card_four := hcard
      yb_cyc := hy
      yb_norm := hnorm yb hybpres
      moves_four := by
        unfold MovesExactly
        rw [hmoved, Set.ncard_coe_finset, hΩ4]
      supp_sub := fun i hi => by
        rw [hmoved]
        exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Equiv.Perm.mem_support.2 hi))
      trans := fun a ha b hb => by
        rw [hmoved] at ha hb
        exact htrans a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) }
  refine ⟨Tb, hFG, fun hn => ?_⟩
  obtain ⟨hEel, -, hybE⟩ := hE hn
  intro g hg
  refine hnorm g (fun i hi => ?_)
  rcases Finset.mem_insert.1 hi with rfl | hiS
  · rw [hωE hn g hg]
    exact hi
  · have hcomm : permOfQ e g * permOfQ e yb = permOfQ e yb * permOfQ e g := by
      have h := congrArg Subtype.val (hEel.1.is_comm.comm ⟨g, hg⟩ ⟨yb, hybE⟩)
      rw [← permOfQ_mul, ← permOfQ_mul]
      exact congrArg (permOfQ e) h
    have hi' : permOfQ e yb i ≠ i := Equiv.Perm.mem_support.1 hiS
    refine Finset.mem_insert_of_mem (Equiv.Perm.mem_support.2 ?_)
    intro heq
    apply hi'
    have h1 : (permOfQ e yb) (permOfQ e g i) = (permOfQ e g) (permOfQ e yb i) := by
      have := congrArg (fun f : Equiv.Perm (Fin n) => f i) hcomm.symm
      simpa [Equiv.Perm.mul_apply] using this
    rw [heq] at h1
    exact (permOfQ e g).injective h1.symm

theorem isRootAlt_altFixSub (e : Q ≃* ↥(alternatingGroup (Fin n))) (Ω : Finset (Fin n))
    (h : 3 ≤ n - Ω.card) : IsRootAlt e (altFixSub e (Ω : Set (Fin n))) (n - Ω.card) := by
  classical
  have hcard : (Ωᶜ).card = n - Ω.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hΩ : 3 ≤ (Ωᶜ).card := by rw [hcard]; exact h
  have hfix : fixingSubgroup (alternatingGroup (Fin n)) (Ω : Set (Fin n)) = altOn Ωᶜ := by
    ext k
    rw [mem_fixingSubgroup_iff, mem_altOn_iff]
    constructor
    · intro hk i hi
      rw [Finset.mem_compl]
      intro hiΩ
      exact (Equiv.Perm.mem_support.1 hi) (hk i (Finset.mem_coe.2 hiΩ))
    · intro hk i hi
      by_contra hne
      exact (Finset.mem_compl.1 (hk (Equiv.Perm.mem_support.2 hne))) (Finset.mem_coe.1 hi)
  have hEq : altFixSub e (Ω : Set (Fin n)) = (altOn Ωᶜ).comap e.toMonoidHom := by
    unfold altFixSub
    rw [hfix]
  refine ⟨?_, ?_⟩
  · obtain ⟨f⟩ := nonempty_altOn_equiv Ωᶜ hcard
    rw [hEq]
    exact ⟨((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm e (altOn Ωᶜ))).trans
      (MulEquiv.subgroupMap e.symm (altOn Ωᶜ)).symm).trans f⟩
  · have hmoved : movedLettersOf e (altFixSub e (Ω : Set (Fin n))) =
        ((Ωᶜ : Finset (Fin n)) : Set (Fin n)) := by
      rw [← movedLettersOf_altOn hΩ]
      ext i
      rw [hEq]
      constructor
      · rintro ⟨q, hq, hi⟩
        exact ⟨e q, hq, hi⟩
      · rintro ⟨k, hk, hi⟩
        exact ⟨e.symm k, by simpa using hk, by simpa using hi⟩
    unfold MovesExactly
    rw [hmoved, Set.ncard_coe_finset, hcard]

theorem fourGroup_root (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) {yb : Q} {Tb : Subgroup Q}
    (h : FourGroupData e yb Tb) : IsRootAlt e (altFixSub e (movedLettersOf e Tb)) (n - 4) := by
  obtain ⟨Ω, hΩ, hΩ4⟩ := exists_finset_movedLetters e h.moves_four
  have := isRootAlt_altFixSub e Ω (by omega)
  rw [hΩ, hΩ4] at this
  exact this

theorem fourGroup_le_J (e : Q ≃* ↥(alternatingGroup (Fin n))) {yb : Q} {Tb : Subgroup Q}
    (h : FourGroupData e yb Tb) :
    altFixSub e (movedLettersOf e Tb) ≤ altFixSub e ((permOfQ e yb).support : Set (Fin n)) := by
  intro q hq
  unfold altFixSub at hq ⊢
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff] at hq ⊢
  intro i hi
  exact hq i (h.supp_sub i (Equiv.Perm.mem_support.1 (Finset.mem_coe.1 hi)))

theorem fourGroup_centralizes (e : Q ≃* ↥(alternatingGroup (Fin n))) {Tb : Subgroup Q} :
    altFixSub e (movedLettersOf e Tb) ≤ Subgroup.centralizer (Tb : Set Q) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  unfold altFixSub at hq
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff] at hq
  have hdisj : Equiv.Perm.Disjoint ((e q : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
      ((e t : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := fun i => by
    by_cases hi : i ∈ movedLettersOf e Tb
    · exact Or.inl (hq i hi)
    · right
      by_contra hne
      exact hi ⟨t, ht, hne⟩
  have hcomm := hdisj.commute.eq
  apply e.injective
  apply Subtype.ext
  simpa using hcomm.symm

private theorem y5x_mem_support_iff_of_comm {σ π : Equiv.Perm (Fin n)} (hc : σ * π = π * σ)
    (i : Fin n) : i ∈ σ.support ↔ π i ∈ σ.support := by
  have h : σ (π i) = π (σ i) := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f i) hc
    simpa only [Equiv.Perm.mul_apply] using this
  rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support, h]
  exact (π.injective.ne_iff).symm

private theorem y5x_permOfQ_pow (e : Q ≃* ↥(alternatingGroup (Fin n))) (q : Q) (k : ℕ) :
    permOfQ e (q ^ k) = permOfQ e q ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, permOfQ_one]
  | succ k ih => rw [pow_succ, permOfQ_mul, ih, pow_succ]

theorem fourGroup_normCent (e : Q ≃* ↥(alternatingGroup (Fin n))) {yb : Q} {Tb : Subgroup Q}
    (h : FourGroupData e yb Tb) :
    Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q) =
      Subgroup.zpowers yb ⊔ altFixSub e (movedLettersOf e Tb) := by
  classical
  obtain ⟨Ω, hΩ, hΩ4⟩ := exists_finset_movedLetters e h.moves_four
  set σ : Equiv.Perm (Fin n) := permOfQ e yb with hσdef
  have hσ3 : σ ^ 3 = 1 := pow_eq_one_of_cycleType_eq h.yb_cyc
  have hS3 : σ.support.card = 3 := card_support_eq_of_cycleType h.yb_cyc
  have hσ3' : σ * (σ * σ) = 1 := by rw [← pow_three]; exact hσ3
  have hSΩ : σ.support ⊆ Ω := by
    intro i hi
    rw [← Finset.mem_coe, hΩ]
    exact h.supp_sub i (Equiv.Perm.mem_support.1 hi)
  have hΩS : (Ω \ σ.support).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSΩ, hΩ4, hS3]
  have hpres : ∀ g ∈ Subgroup.normalizer (Tb : Set Q), ∀ i ∈ Ω, permOfQ e g i ∈ Ω := by
    intro g hg i hi
    have hi' : i ∈ movedLettersOf e Tb := by rw [← hΩ]; exact hi
    obtain ⟨t, ht, hti⟩ := hi'
    have hgt : g * t * g⁻¹ ∈ Tb := (Subgroup.mem_normalizer_iff.1 hg t).1 ht
    have hkey : permOfQ e (g * t * g⁻¹) (permOfQ e g i) = permOfQ e g (permOfQ e t i) := by
      rw [permOfQ_mul, permOfQ_mul, permOfQ_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_eq_iff_eq.2 rfl]
    have hmem : permOfQ e g i ∈ movedLettersOf e Tb := by
      refine ⟨g * t * g⁻¹, hgt, ?_⟩
      show permOfQ e (g * t * g⁻¹) (permOfQ e g i) ≠ permOfQ e g i
      rw [hkey]
      exact fun heq => hti ((permOfQ e g).injective heq)
    rw [← hΩ] at hmem
    exact hmem
  have hsupp : ∀ g : Q, yb * g = g * yb → ∀ i, i ∈ σ.support ↔ permOfQ e g i ∈ σ.support := by
    intro g hg i
    refine y5x_mem_support_iff_of_comm (σ := σ) (π := permOfQ e g) ?_ i
    show permOfQ e yb * permOfQ e g = permOfQ e g * permOfQ e yb
    rw [← permOfQ_mul, ← permOfQ_mul, hg]
  have hT : ∀ a ∈ σ.support, σ.support = {a, σ a, σ (σ a)} := by
    intro a ha
    have hne1 : σ a ≠ a := Equiv.Perm.mem_support.1 ha
    have hne2 : σ (σ a) ≠ a := by
      intro h2
      have h3 : σ (σ (σ a)) = σ a := by rw [h2]
      have h4 : σ (σ (σ a)) = a := by
        have := congrArg (fun f : Equiv.Perm (Fin n) => f a) hσ3'
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this
      exact hne1 (h3.symm.trans h4)
    have hne3 : σ (σ a) ≠ σ a := fun h2 => hne1 (σ.injective h2)
    have hsub : ({a, σ a, σ (σ a)} : Finset (Fin n)) ⊆ σ.support := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact ha
      · exact Equiv.Perm.apply_mem_support.2 ha
      · exact Equiv.Perm.apply_mem_support.2 (Equiv.Perm.apply_mem_support.2 ha)
    have hn1 : a ∉ ({σ a, σ (σ a)} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h1 => hne1 h1.symm, fun h1 => hne2 h1.symm⟩
    have hn2 : σ a ∉ ({σ (σ a)} : Finset (Fin n)) := by
      simp only [Finset.mem_singleton]
      exact fun h1 => hne3 h1.symm
    have hcard : ({a, σ a, σ (σ a)} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2, Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hT' : ∀ a ∈ σ.support, ∀ b ∈ σ.support, b = a ∨ b = σ a ∨ b = σ (σ a) := by
    intro a ha b hb
    rw [hT a ha] at hb
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hb
  apply le_antisymm
  · rintro g ⟨hgN, hgC⟩
    have hgc : yb * g = g * yb := (Subgroup.mem_centralizer_singleton_iff.1 hgC).symm
    have hcomm : σ * permOfQ e g = permOfQ e g * σ := by
      show permOfQ e yb * permOfQ e g = permOfQ e g * permOfQ e yb
      rw [← permOfQ_mul, ← permOfQ_mul, hgc]
    have hfix : ∀ i ∈ Ω, i ∉ σ.support → permOfQ e g i = i := by
      intro i hiΩ hiS
      have hmem : permOfQ e g i ∈ Ω \ σ.support :=
        Finset.mem_sdiff.2 ⟨hpres g hgN i hiΩ, fun hh => hiS ((hsupp g hgc i).2 hh)⟩
      have hi : i ∈ Ω \ σ.support := Finset.mem_sdiff.2 ⟨hiΩ, hiS⟩
      exact Finset.card_le_one.1 (by omega) _ hmem _ hi
    obtain ⟨a, ha⟩ : σ.support.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (σ ^ j) a = permOfQ e g a := by
      rcases hT' a ha (permOfQ e g a) ((hsupp g hgc a).1 ha) with h0 | h1 | h2
      · exact ⟨0, by rw [pow_zero, Equiv.Perm.one_apply, h0]⟩
      · exact ⟨1, by rw [pow_one, h1]⟩
      · exact ⟨2, by rw [pow_two, Equiv.Perm.mul_apply, h2]⟩
    have hcs : σ * (σ ^ j)⁻¹ = (σ ^ j)⁻¹ * σ := ((Commute.refl σ).pow_right j).inv_right.eq
    have hcs' : ∀ y : Fin n, (σ ^ j)⁻¹ (σ y) = σ ((σ ^ j)⁻¹ y) := by
      intro y
      have := congrArg (fun f : Equiv.Perm (Fin n) => f y) hcs
      simp only [Equiv.Perm.mul_apply] at this
      exact this.symm
    have hDσ : ∀ x : Fin n, ((σ ^ j)⁻¹ * permOfQ e g) (σ x) = σ (((σ ^ j)⁻¹ * permOfQ e g) x) := by
      intro x
      have h1 : permOfQ e g (σ x) = σ (permOfQ e g x) := by
        have := congrArg (fun f : Equiv.Perm (Fin n) => f x) hcomm
        simp only [Equiv.Perm.mul_apply] at this
        exact this.symm
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hcs']
    have hDa : ((σ ^ j)⁻¹ * permOfQ e g) a = a := by
      rw [Equiv.Perm.mul_apply, ← hj, Equiv.Perm.inv_eq_iff_eq.2 rfl]
    have hD : ∀ i ∈ Ω, ((σ ^ j)⁻¹ * permOfQ e g) i = i := by
      intro i hiΩ
      by_cases hiS : i ∈ σ.support
      · rcases hT' a ha i hiS with h1 | h1 | h1 <;> rw [h1]
        · exact hDa
        · rw [hDσ a, hDa]
        · rw [hDσ (σ a), hDσ a, hDa]
      · have hσi : σ i = i := Equiv.Perm.notMem_support.1 hiS
        have hpi : permOfQ e g i = i := hfix i hiΩ hiS
        rw [Equiv.Perm.mul_apply, hpi, Equiv.Perm.inv_eq_iff_eq]
        exact (Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσi j).symm
    have hh : (yb ^ j)⁻¹ * g ∈ altFixSub e (movedLettersOf e Tb) := by
      rw [← hΩ]
      refine (mem_altFixSub_iff e _).2 fun i hi => ?_
      rw [permOfQ_mul, permOfQ_inv, y5x_permOfQ_pow]
      exact hD i (Finset.mem_coe.1 hi)
    have hmem := Subgroup.mul_mem_sup (S := Subgroup.zpowers yb) (T := altFixSub e (movedLettersOf e Tb))
      (Subgroup.pow_mem (Subgroup.zpowers yb) (Subgroup.mem_zpowers yb) j) hh
    rwa [mul_inv_cancel_left] at hmem
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨h.yb_norm, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    · intro x hx
      have hxC : x ∈ Subgroup.centralizer (Tb : Set Q) := fourGroup_centralizes e hx
      have hxN : x ∈ Subgroup.normalizer (Tb : Set Q) := Subgroup.centralizer_le_normalizer _ hxC
      have hdisj : Equiv.Perm.Disjoint (permOfQ e x) σ := fun i => by
        by_cases hi : i ∈ σ.support
        · have hiM : i ∈ movedLettersOf e Tb := by rw [← hΩ]; exact Finset.mem_coe.2 (hSΩ hi)
          exact Or.inl ((mem_altFixSub_iff e _).1 hx i hiM)
        · exact Or.inr (Equiv.Perm.notMem_support.1 hi)
      have hcomm' : permOfQ e x * σ = σ * permOfQ e x := hdisj.commute.eq
      have hxy : x * yb = yb * x := by
        apply e.injective
        apply Subtype.ext
        show permOfQ e (x * yb) = permOfQ e (yb * x)
        rw [permOfQ_mul, permOfQ_mul]
        exact hcomm'
      exact Subgroup.mem_inf.2 ⟨hxN, Subgroup.mem_centralizer_singleton_iff.2 hxy⟩

open Equiv in
private theorem y5dr9_comm (e : Q ≃* ↥(alternatingGroup (Fin n))) {yb : Q} {Tb : Subgroup Q}
    (h : FourGroupData e yb Tb) : ∀ i ∈ altFixSub e (movedLettersOf e Tb), i * yb = yb * i := by
  intro i hi
  have hdisj : Equiv.Perm.Disjoint (permOfQ e i) (permOfQ e yb) := fun j => by
    by_cases hj : permOfQ e yb j = j
    · exact Or.inr hj
    · left
      exact (mem_altFixSub_iff e _).1 hi j (h.supp_sub j hj)
  apply permOfQ_injective e
  rw [permOfQ_mul, permOfQ_mul]
  exact hdisj.commute.eq

open Equiv in
theorem fourGroup_isComponent (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) [Finite Q] {yb : Q}
    {Tb : Subgroup Q} (h : FourGroupData e yb Tb) :
    GLAPComponent 3 (Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q))
      (altFixSub e (movedLettersOf e Tb)) := by
  classical
  set I := altFixSub e (movedLettersOf e Tb) with hI
  have hX := fourGroup_normCent e h
  have hle : I ≤ Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q) := by
    rw [hX]; exact le_sup_right
  have hyN : Subgroup.zpowers yb ≤ Subgroup.normalizer (I : Set Q) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 (y5dr9_comm e h))
  have hnorm : (I.subgroupOf (Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
    rw [hX]
    exact sup_le hyN Subgroup.le_normalizer
  obtain ⟨f⟩ := (fourGroup_root e hn9 h).1
  have hm : 5 ≤ Nat.card (Fin (n - 4)) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin (n - 4))) := alternatingGroup.isSimpleGroup hm
  haveI : IsSimpleGroup ↥I := f.isSimpleGroup
  have hnc : ∃ a b : ↥I, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial (alternatingGroup (Fin (n - 4))) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin (n - 4)))
    have hZ := alternatingGroup.center_eq_bot (α := Fin (n - 4)) (by omega)
    have hmem : a ∈ Subgroup.center (alternatingGroup (Fin (n - 4))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply f.symm.injective
      rw [map_mul, map_mul]
      exact hcon _ _
    rw [hZ, Subgroup.mem_bot] at hmem
    exact ha hmem
  have hpL : 3 ∣ Nat.card ↥I := by
    rw [Nat.card_congr f.toEquiv]
    exact p_dvd_card_alternatingGroup Nat.prime_three (by norm_num) (by omega)
  exact GL83.PiGen.glaPComponent_of_normal_simple Nat.prime_three hle hnorm hnc hpL

open Equiv in
theorem fourGroup_component_le (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) [Finite Q] {yb : Q}
    {Tb : Subgroup Q} (h : FourGroupData e yb Tb) {M : Subgroup Q}
    (hM : GLAPComponent 3 (Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q)) M) :
    M ≤ altFixSub e (movedLettersOf e Tb) := by
  classical
  set I := altFixSub e (movedLettersOf e Tb) with hI
  set X := Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q) with hXdef
  have hX : X = Subgroup.zpowers yb ⊔ I := fourGroup_normCent e h
  have hyN : Subgroup.zpowers yb ≤ Subgroup.normalizer (I : Set Q) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 (y5dr9_comm e h))
  have hcent : ∀ k : ℤ, ∀ g ∈ X, yb ^ k * g = g * yb ^ k := by
    intro k g hg
    have : g * yb = yb * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    exact ((Commute.zpow_left (show Commute yb g from this.symm) k)).eq
  have hXX : ⁅X, X⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨c₁, hc₁, i₁, hi₁, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hyN (hX ▸ hg₁)
    obtain ⟨c₂, hc₂, i₂, hi₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hyN (hX ▸ hg₂)
    obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc₁
    obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc₂
    have hiX : ∀ i ∈ I, i ∈ X := fun i hi => by rw [hX]; exact Subgroup.mem_sup_right hi
    have e1 := hcent k₁ i₂ (hiX i₂ hi₂)
    have e2 := hcent k₂ i₁ (hiX i₁ hi₁)
    have e3 := hcent k₁ i₁ (hiX i₁ hi₁)
    have e4 := hcent k₂ i₂ (hiX i₂ hi₂)
    set a := yb ^ k₁
    set b := yb ^ k₂
    set x := b * i₂
    have hab : Commute a b := Commute.zpow_zpow_self yb k₁ k₂
    have ha1 : Commute a i₁ := e3
    have ha2 : Commute a i₂ := e1
    have hb1 : Commute b i₁ := e2
    have hb2 : Commute b i₂ := e4
    have hA : Commute a (i₁ * x * i₁⁻¹) :=
      (ha1.mul_right (hab.mul_right ha2)).mul_right ha1.inv_right
    have hB : Commute b ⁅i₁, i₂⁆ := by
      rw [commutatorElement_def]
      exact ((hb1.mul_right hb2).mul_right hb1.inv_right).mul_right hb2.inv_right
    have h1 : ⁅a * i₁, x⁆ = ⁅i₁, x⁆ := by
      calc ⁅a * i₁, x⁆ = (a * (i₁ * x * i₁⁻¹)) * a⁻¹ * x⁻¹ := by simp only [commutatorElement_def]; group
        _ = ((i₁ * x * i₁⁻¹) * a) * a⁻¹ * x⁻¹ := by rw [hA.eq]
        _ = ⁅i₁, x⁆ := by simp only [commutatorElement_def]; group
    have h2 : ⁅i₁, x⁆ = ⁅i₁, i₂⁆ := by
      calc ⁅i₁, x⁆ = i₁ * b * i₂ * i₁⁻¹ * i₂⁻¹ * b⁻¹ := by simp only [commutatorElement_def, x]; group
        _ = b * i₁ * i₂ * i₁⁻¹ * i₂⁻¹ * b⁻¹ := by rw [hb1.eq]
        _ = b * ⁅i₁, i₂⁆ * b⁻¹ := by simp only [commutatorElement_def]; group
        _ = ⁅i₁, i₂⁆ * b * b⁻¹ := by rw [hB.eq]
        _ = ⁅i₁, i₂⁆ := by group
    rw [h1, h2, commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem hi₁ hi₂) (I.inv_mem hi₁)) (I.inv_mem hi₂)
  calc M = ⁅M, M⁆ := (glaPComponent_perfect hM).symm
    _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hM.1 hM.1
    _ ≤ I := hXX

theorem fourGroup_layer (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) [Finite Q] {yb : Q}
    {Tb : Subgroup Q} (h : FourGroupData e yb Tb) :
    GLAPLayer 3 (Subgroup.normalizer (Tb : Set Q) ⊓ Subgroup.centralizer ({yb} : Set Q)) =
      altFixSub e (movedLettersOf e Tb) :=
  le_antisymm (sSup_le fun _ hM => fourGroup_component_le e hn9 h hM)
    (le_sSup (fourGroup_isComponent e hn9 h))

open Equiv in
private theorem y5dr9_supp_le {n : ℕ} (x y z : Fin n) : (swap x y * swap x z).support ⊆ {x, y, z} := by
  classical
  intro i hi
  by_contra hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  obtain ⟨hx, hy, hz⟩ := hne
  apply Perm.mem_support.1 hi
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne hx hz, swap_apply_of_ne_of_ne hx hy]

open Equiv in
private theorem y5dr9_nf {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsThreeCycle) {a : Fin n} (ha : a ∈ σ.support) :
    σ = swap a (σ (σ a)) * swap a (σ a) ∧ σ a ≠ a ∧ σ (σ a) ≠ a ∧ σ (σ a) ≠ σ a ∧
      σ.support = {a, σ a, σ (σ a)} := by
  classical
  have h3 : σ ^ 3 = 1 := by rw [← hσ.orderOf]; exact pow_orderOf_eq_one σ
  have h1 : σ a ≠ a := Perm.mem_support.1 ha
  have h2 : σ (σ a) ≠ σ a := fun h => h1 (σ.injective h)
  have h4 : σ (σ (σ a)) = a := by
    have := congrArg (fun f : Perm (Fin n) => f a) h3
    simpa [pow_succ, Perm.mul_apply] using this
  have h5 : σ (σ a) ≠ a := by
    intro h; apply h1; rw [h] at h4; exact h4
  have hsupp : σ.support = {a, σ a, σ (σ a)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ha
      · exact Perm.apply_mem_support.2 ha
      · exact Perm.apply_mem_support.2 (Perm.apply_mem_support.2 ha)
    · rw [hσ.card_support, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using h2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1.symm, h5.symm⟩
  refine ⟨?_, h1, h5, h2, hsupp⟩
  ext i
  by_cases hi : i ∈ σ.support
  · rw [hsupp] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2.symm]
    · simp [Perm.mul_apply, swap_apply_left]
    · simp [Perm.mul_apply, swap_apply_of_ne_of_ne h5 h2, h4]
  · have hfix : σ i = i := Perm.notMem_support.1 hi
    rw [hsupp] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨hia, hib, hic⟩ := hi
    simp [Perm.mul_apply, hfix, swap_apply_of_ne_of_ne hia hib, swap_apply_of_ne_of_ne hia hic]

open Equiv in
theorem eq_top_of_threeCycles_mem (e : Q ≃* ↥(alternatingGroup (Fin n))) (Ω : Finset (Fin n)) (hΩ : Ω.card = 4)
    (hn : 7 ≤ n) {H : Subgroup Q}
    (hH : ∀ q : Q, (permOfQ e q).IsThreeCycle → ((permOfQ e q).support ∩ Ω).card ≤ 1 → q ∈ H) : H = ⊤ := by
  classical
  let φ : Q →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  set H' := H.map φ with hH'
  have hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ q, φ q = σ := fun σ hσ =>
    ⟨e.symm ⟨σ, hσ⟩, by simp [φ]⟩
  have hR : 3 ≤ (Ωᶜ).card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  have hC1 : ∀ σ : Perm (Fin n), σ.IsThreeCycle → (σ.support ∩ Ω).card ≤ 1 → σ ∈ H' := by
    intro σ hσ hc
    obtain ⟨q, rfl⟩ := hsurj σ hσ.mem_alternatingGroup
    exact ⟨q, hH q hσ hc, rfl⟩
  have hcj : ∀ (g : Perm (Fin n)) (a b c : Fin n),
      g * (swap a b * swap a c) * g⁻¹ = swap (g a) (g b) * swap (g a) (g c) := by
    intro g a b c
    rw [swap_apply_apply, swap_apply_apply]; group
  have hA : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z → ((({x, y, z} : Finset (Fin n)) ∩ Ω).card ≤ 1) →
      swap x y * swap x z ∈ H' := by
    intro x y z hxy hxz hyz hc
    refine hC1 _ (Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz) ?_
    exact (Finset.card_le_card (Finset.inter_subset_inter_right (y5dr9_supp_le x y z))).trans hc
  have hR2 : ∀ a : Fin n, ∃ r ∈ Ωᶜ, ∃ r' ∈ Ωᶜ, r ≠ a ∧ r' ≠ a ∧ r ≠ r' := by
    intro a
    have h2 : 2 ≤ ((Ωᶜ).erase a).card := by
      have := Finset.pred_card_le_card_erase (s := Ωᶜ) (a := a); omega
    obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1 (by omega : 1 < ((Ωᶜ).erase a).card)
    exact ⟨r, Finset.mem_of_mem_erase hr, r', Finset.mem_of_mem_erase hr', Finset.ne_of_mem_erase hr,
      Finset.ne_of_mem_erase hr', hne⟩
  have hle1 : ∀ (s : Finset (Fin n)) (d : Fin n), (∀ i ∈ s, i ∈ Ω → i = d) → (s ∩ Ω).card ≤ 1 := by
    intro s d h
    refine Finset.card_le_one.2 fun i hi j hj => ?_
    rw [Finset.mem_inter] at hi hj
    rw [h i hi.1 hi.2, h j hj.1 hj.2]
  have hC2 : ∀ a d₁ d₂ : Fin n, a ∉ Ω → d₁ ∈ Ω → d₂ ∈ Ω → d₁ ≠ d₂ → swap a d₂ * swap a d₁ ∈ H' := by
    intro a d₁ d₂ ha hd₁ hd₂ hd
    obtain ⟨r', hr', r'', hr'', hr'a, hr''a, hrr⟩ := hR2 a
    have hr'Ω : r' ∉ Ω := Finset.mem_compl.1 hr'
    have hr''Ω : r'' ∉ Ω := Finset.mem_compl.1 hr''
    have had₁ : a ≠ d₁ := fun h => ha (h ▸ hd₁)
    have had₂ : a ≠ d₂ := fun h => ha (h ▸ hd₂)
    have hr'd₁ : r' ≠ d₁ := fun h => hr'Ω (h ▸ hd₁)
    have hr'd₂ : r' ≠ d₂ := fun h => hr'Ω (h ▸ hd₂)
    have hr''d₁ : r'' ≠ d₁ := fun h => hr''Ω (h ▸ hd₁)
    have hr''d₂ : r'' ≠ d₂ := fun h => hr''Ω (h ▸ hd₂)
    have hτ : swap a r' * swap a d₁ ∈ H' := hA a r' d₁ hr'a.symm had₁ hr'd₁ (hle1 _ d₁ (by
      intro i hi hiΩ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact absurd hiΩ ha
      · exact absurd hiΩ hr'Ω
      · rfl))
    have hg : swap r'' d₂ * swap r'' r' ∈ H' := hA r'' d₂ r' hr''d₂ hrr.symm hr'd₂.symm (hle1 _ d₂ (by
      intro i hi hiΩ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact absurd hiΩ hr''Ω
      · rfl
      · exact absurd hiΩ hr'Ω))
    have hconj := hcj (swap r'' d₂ * swap r'' r') a r' d₁
    have e1 : (swap r'' d₂ * swap r'' r') a = a := by
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hr''a.symm hr'a.symm, swap_apply_of_ne_of_ne hr''a.symm had₂]
    have e2 : (swap r'' d₂ * swap r'' r') r' = d₂ := by simp [Perm.mul_apply]
    have e3 : (swap r'' d₂ * swap r'' r') d₁ = d₁ := by
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hr''d₁.symm hr'd₁.symm, swap_apply_of_ne_of_ne hr''d₁.symm hd]
    rw [e1, e2, e3] at hconj
    rw [← hconj]
    exact H'.mul_mem (H'.mul_mem hg hτ) (H'.inv_mem hg)
  have hC3 : ∀ x y z : Fin n, x ∈ Ω → y ∈ Ω → z ∈ Ω → x ≠ y → x ≠ z → y ≠ z → swap x z * swap x y ∈ H' := by
    intro x y z hx hy hz hxy hxz hyz
    obtain ⟨r, hr, r', hr', -, -, hrr⟩ := hR2 x
    have hrΩ : r ∉ Ω := Finset.mem_compl.1 hr
    have hr'Ω : r' ∉ Ω := Finset.mem_compl.1 hr'
    have hrx : r ≠ x := fun h => hrΩ (h ▸ hx)
    have hry : r ≠ y := fun h => hrΩ (h ▸ hy)
    have hrz : r ≠ z := fun h => hrΩ (h ▸ hz)
    have hr'x : r' ≠ x := fun h => hr'Ω (h ▸ hx)
    have hr'y : r' ≠ y := fun h => hr'Ω (h ▸ hy)
    have hr'z : r' ≠ z := fun h => hr'Ω (h ▸ hz)
    have hτ : swap r z * swap r y ∈ H' := hC2 r y z hrΩ hy hz hyz
    have hg : swap r' x * swap r' r ∈ H' := hA r' x r hr'x hrr.symm hrx.symm (hle1 _ x (by
      intro i hi hiΩ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact absurd hiΩ hr'Ω
      · rfl
      · exact absurd hiΩ hrΩ))
    have hconj := hcj (swap r' x * swap r' r) r z y
    have e1 : (swap r' x * swap r' r) r = x := by simp [Perm.mul_apply]
    have e2 : (swap r' x * swap r' r) z = z := by
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hr'z.symm hrz.symm, swap_apply_of_ne_of_ne hr'z.symm hxz.symm]
    have e3 : (swap r' x * swap r' r) y = y := by
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hr'y.symm hry.symm, swap_apply_of_ne_of_ne hr'y.symm hxy.symm]
    rw [e1, e2, e3] at hconj
    rw [← hconj]
    exact H'.mul_mem (H'.mul_mem hg hτ) (H'.inv_mem hg)
  have hall : ∀ σ : Perm (Fin n), σ.IsThreeCycle → σ ∈ H' := by
    intro σ hσ
    by_cases hout : ∃ a ∈ σ.support, a ∉ Ω
    · obtain ⟨a, ha, haΩ⟩ := hout
      obtain ⟨heq, h1, h2, h3, hsupp⟩ := y5dr9_nf hσ ha
      by_cases hb : σ a ∈ Ω ∧ σ (σ a) ∈ Ω
      · rw [heq]; exact hC2 a (σ a) (σ (σ a)) haΩ hb.1 hb.2 h3.symm
      · refine hC1 σ hσ ?_
        rw [hsupp]
        rcases not_and_or.1 hb with hb | hb
        · refine hle1 _ (σ (σ a)) fun i hi hiΩ => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl
          · exact absurd hiΩ haΩ
          · exact absurd hiΩ hb
          · rfl
        · refine hle1 _ (σ a) fun i hi hiΩ => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl
          · exact absurd hiΩ haΩ
          · rfl
          · exact absurd hiΩ hb
    · push Not at hout
      obtain ⟨a, ha⟩ : σ.support.Nonempty := by
        rw [← Finset.card_pos, hσ.card_support]; norm_num
      obtain ⟨heq, h1, h2, h3, hsupp⟩ := y5dr9_nf hσ ha
      have hsa : σ a ∈ σ.support := Perm.apply_mem_support.2 ha
      have hsa2 : σ (σ a) ∈ σ.support := Perm.apply_mem_support.2 hsa
      rw [heq]
      exact hC3 a (σ a) (σ (σ a)) (hout a ha) (hout _ hsa) (hout _ hsa2) h1.symm h2.symm h3.symm
  have hAn : alternatingGroup (Fin n) ≤ H' := by
    rw [← Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    exact fun σ hσ => hall σ hσ
  rw [eq_top_iff]
  intro q _
  obtain ⟨q', hq', hqq⟩ := hAn (e q).2
  rwa [← hφinj hqq]

theorem altFixSub_join_generate (e : Q ≃* ↥(alternatingGroup (Fin n))) (Ω : Finset (Fin n))
    (hΩ : Ω.card = 4) (hn : 7 ≤ n) :
    (⨆ d ∈ Ω, altFixSub e (↑(Ω.erase d) : Set (Fin n))) = ⊤ := by
  classical
  refine eq_top_of_threeCycles_mem e Ω hΩ hn (fun q _ hq1 => ?_)
  obtain ⟨d, hdΩ, hd⟩ : ∃ d ∈ Ω, ∀ i ∈ Ω.erase d, permOfQ e q i = i := by
    by_cases hempty : (permOfQ e q).support ∩ Ω = ∅
    · obtain ⟨d, hd⟩ : Ω.Nonempty := by
        rw [← Finset.card_pos]
        omega
      refine ⟨d, hd, fun i hi => ?_⟩
      by_contra hne
      have : i ∈ (permOfQ e q).support ∩ Ω :=
        Finset.mem_inter.2 ⟨Equiv.Perm.mem_support.2 hne, Finset.mem_of_mem_erase hi⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty i)
    · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hempty
      refine ⟨d, (Finset.mem_inter.1 hd).2, fun i hi => ?_⟩
      by_contra hne
      have hi' : i ∈ (permOfQ e q).support ∩ Ω :=
        Finset.mem_inter.2 ⟨Equiv.Perm.mem_support.2 hne, Finset.mem_of_mem_erase hi⟩
      exact (Finset.mem_erase.1 hi).1 (Finset.card_le_one.1 hq1 i hi' d hd)
  have hmem : q ∈ altFixSub e (↑(Ω.erase d) : Set (Fin n)) :=
    (mem_altFixSub_iff e _).2 fun i hi => hd i (Finset.mem_coe.1 hi)
  exact (le_iSup₂ (f := fun d (_ : d ∈ Ω) => altFixSub e (↑(Ω.erase d) : Set (Fin n))) d hdΩ) hmem

theorem fourGroup_gen (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn9 : 9 ≤ n) {yb : Q} {Tb : Subgroup Q}
    (h : FourGroupData e yb Tb) :
    Tb ⊔ altFixSub e ((permOfQ e yb).support : Set (Fin n)) = ⊤ := by
  classical
  obtain ⟨Ω, hΩ, hΩ4⟩ := exists_finset_movedLetters e h.moves_four
  set S := (permOfQ e yb).support with hS
  have hSΩ : S ⊆ Ω := fun i hi => by
    rw [← Finset.mem_coe, hΩ]
    exact h.supp_sub i (Equiv.Perm.mem_support.1 hi)
  have hS3 : S.card = 3 := card_support_eq_of_cycleType h.yb_cyc
  obtain ⟨ω, hωΩ, hωS⟩ : ∃ ω ∈ Ω, ω ∉ S := by
    by_contra hcon
    push_neg at hcon
    have := Finset.card_le_card (show Ω ⊆ S from hcon)
    omega
  have hΩerase : S = Ω.erase ω := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      exact Finset.mem_erase.2 ⟨fun hiω => hωS (hiω ▸ hi), hSΩ hi⟩
    · rw [Finset.card_erase_of_mem hωΩ, hΩ4, hS3]
  have hpres : ∀ t ∈ Tb, ∀ i ∈ Ω, permOfQ e t i ∈ Ω := by
    intro t ht i hi
    rw [← Finset.mem_coe, hΩ] at hi ⊢
    obtain ⟨u, hu, hui⟩ := hi
    refine ⟨t * u * t⁻¹, Tb.mul_mem (Tb.mul_mem ht hu) (Tb.inv_mem ht), ?_⟩
    intro heq
    apply hui
    have h1 : permOfQ e (t * u * t⁻¹) (permOfQ e t i) = permOfQ e t (permOfQ e u i) := by
      simp [permOfQ_mul, permOfQ_inv, Equiv.Perm.mul_apply]
    have heq' : permOfQ e (t * u * t⁻¹) (permOfQ e t i) = permOfQ e t i := heq
    rw [heq'] at h1
    exact ((permOfQ e t).injective h1).symm
  have hgen := altFixSub_join_generate e Ω hΩ4 (by omega)
  have hle : ∀ d ∈ Ω, altFixSub e (↑(Ω.erase d) : Set (Fin n)) ≤
      Tb ⊔ altFixSub e (↑S : Set (Fin n)) := by
    intro d hd
    by_cases hdω : d = ω
    · subst hdω
      rw [← hΩerase]
      exact le_sup_right
    · obtain ⟨t, htT, htω⟩ := h.trans ω (by rw [← hΩ]; exact Finset.mem_coe.2 hωΩ) d
        (by rw [← hΩ]; exact Finset.mem_coe.2 hd)
      intro k hk
      have hk' : t⁻¹ * k * t ∈ altFixSub e (↑S : Set (Fin n)) := by
        rw [mem_altFixSub_iff]
        intro i hi
        have hiS : i ∈ S := Finset.mem_coe.1 hi
        have hti : permOfQ e t i ∈ Ω.erase d := by
          refine Finset.mem_erase.2 ⟨fun hdi => ?_, hpres t htT i (hSΩ hiS)⟩
          have : permOfQ e t i = permOfQ e t ω := hdi.trans htω.symm
          exact hωS ((permOfQ e t).injective this ▸ hiS)
        have hkfix := (mem_altFixSub_iff e _).1 hk (permOfQ e t i) (Finset.mem_coe.2 hti)
        simp [permOfQ_mul, permOfQ_inv, Equiv.Perm.mul_apply, hkfix]
      have : k = t * (t⁻¹ * k * t) * t⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left htT) (Subgroup.mem_sup_right hk'))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left htT))
  rw [eq_top_iff, ← hgen]
  exact iSup₂_le hle

theorem fourGroup_E (e : Q ≃* ↥(alternatingGroup (Fin n))) (hn : n = 10 ∨ n = 11) {yb : Q}
    {Tb E : Subgroup Q} (h : FourGroupData e yb Tb) (hE : IsElemAbelian 3 E) (hE27 : Nat.card ↥E = 3 ^ 3)
    (hyE : yb ∈ E) (hEN : E ≤ Subgroup.normalizer (Tb : Set Q)) :
    E ≤ Subgroup.zpowers yb ⊔ (E ⊓ altFixSub e (movedLettersOf e Tb)) ∧
      Subgroup.zpowers yb ⊓ (E ⊓ altFixSub e (movedLettersOf e Tb)) = ⊥ := by
  classical
  haveI : Finite Q := Finite.of_equiv ↥(alternatingGroup (Fin n)) e.symm.toEquiv
  refine ⟨fun g hg => ?_, ?_⟩
  ·
    have hgC : g ∈ Subgroup.centralizer ({yb} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨yb, hyE⟩)
    have hmem : g ∈ Subgroup.zpowers yb ⊔ altFixSub e (movedLettersOf e Tb) := by
      rw [← fourGroup_normCent e h]
      exact ⟨hEN hg, hgC⟩
    have hcomm : ∀ i ∈ altFixSub e (movedLettersOf e Tb), i * yb = yb * i := by
      intro i hi
      have hdisj : Equiv.Perm.Disjoint (permOfQ e i) (permOfQ e yb) := fun j => by
        by_cases hj : permOfQ e yb j = j
        · exact Or.inr hj
        · left
          exact (mem_altFixSub_iff e _).1 hi j (h.supp_sub j hj)
      apply permOfQ_injective e
      rw [permOfQ_mul, permOfQ_mul]
      exact hdisj.commute.eq
    have hyc : yb ∈ Subgroup.centralizer ((altFixSub e (movedLettersOf e Tb) : Subgroup Q) : Set Q) :=
      Subgroup.mem_centralizer_iff.2 hcomm
    have hA : Subgroup.zpowers yb ≤ Subgroup.normalizer ((altFixSub e (movedLettersOf e Tb) : Subgroup Q) : Set Q) :=
      (Subgroup.zpowers_le).2 (Subgroup.centralizer_le_normalizer _ hyc)
    obtain ⟨a, ha, i, hi, hgai⟩ := exists_mul_of_mem_sup_of_le_normalizer hA hmem
    have haE : a ∈ E := ((Subgroup.zpowers_le).2 hyE) ha
    have hiE : i ∈ E := by
      have : i = a⁻¹ * g := by rw [hgai]; group
      rw [this]
      exact E.mul_mem (E.inv_mem haE) hg
    rw [hgai]
    exact Subgroup.mul_mem_sup ha ⟨hiE, hi⟩
  · rw [eq_bot_iff]
    rintro z ⟨hz, -, hzf⟩
    have := (zpowers_inf_altFixSub_support e yb).le ⟨hz, fourGroup_le_J e h hzf⟩
    exact this

end Perm

private theorem y5x_not_three_dvd_preMod {L : Subgroup G} {Tb : Subgroup (PQuot 3 L)} (hT2 : IsPGroup 2 Tb) :
    ¬ 3 ∣ Nat.card ↥(preMod 3 L Tb) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hx3 : (x : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hxne : (x : G) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    norm_num at hx
  obtain ⟨hz, hT⟩ := mem_preMod_iff.1 x.2
  let yL : ↥L := ⟨(x : G), hz⟩
  let t : PQuot 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) yL
  have ht3 : t ^ 3 = 1 := by
    rw [← map_pow]
    have : yL ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  obtain ⟨k, hk⟩ := hT2 ⟨t, hT⟩
  have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have ht1 : t = 1 := by
    have h1 : t ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨ht3, htk⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
    exact h1
  have hyO : yL ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff yL).1 ht1
  have hcopO : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  let o : ↥(GLAPPrimeCore 3 ↥L) := ⟨yL, hyO⟩
  have ho3 : o ^ 3 = 1 := Subtype.ext (Subtype.ext hx3)
  have hone : o ≠ 1 := by
    intro h1
    apply hxne
    exact congrArg (fun q : ↥(GLAPPrimeCore 3 ↥L) => ((q : ↥L) : G)) h1
  have hord : orderOf o = 3 := orderOf_eq_prime ho3 hone
  have h3O : 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
    have := orderOf_dvd_natCard o
    rwa [hord] at this
  have := Nat.Coprime.eq_one_of_dvd hcopO h3O
  norm_num at this

private theorem y5x_sylow_image {L : Subgroup G} {Tb : Subgroup (PQuot 3 L)} (hT2 : IsPGroup 2 Tb)
    (P : Sylow 2 ↥(preMod 3 L Tb)) :
    imageMod 3 L (P.toSubgroup.map (preMod 3 L Tb).subtype) = Tb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : P.toSubgroup.map (preMod 3 L Tb).subtype ≤ preMod 3 L Tb := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let Φ : ↥(preMod 3 L Tb) →* PQuot 3 L :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion (preMod_le 3 L Tb))
  have hΦ : ∀ x : ↥(preMod 3 L Tb), Φ x ∈ Tb := by
    intro x
    exact (mem_preMod_iff.1 x.2).2
  let f : ↥(preMod 3 L Tb) →* ↥Tb := Φ.codRestrict Tb hΦ
  have hf : Function.Surjective f := by
    intro t
    have ht : (t : PQuot 3 L) ∈ imageMod 3 L (preMod 3 L Tb) := by
      rw [imageMod_preMod]
      exact t.2
    obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 ht
    refine ⟨⟨u, Subgroup.mem_subgroupOf.1 hu⟩, Subtype.ext ?_⟩
    exact huv
  haveI : IsPGroup 2 ↥Tb := hT2
  have hTop : IsPGroup 2 ↥(⊤ : Subgroup ↥Tb) := hT2.of_equiv Subgroup.topEquiv.symm
  have hQtop : (⊤ : Subgroup ↥Tb) = (Sylow.mapSurjective hf P).toSubgroup :=
    (Sylow.mapSurjective hf P).is_maximal' hTop le_top
  have hQ : (Sylow.mapSurjective hf P).toSubgroup = P.toSubgroup.map f := Sylow.coe_mapSurjective hf P
  have hS : P.toSubgroup.map f = ⊤ := by
    rw [← hQ]
    exact hQtop.symm
  apply le_antisymm
  · exact (imageMod_mono hSle).trans (imageMod_preMod 3 L Tb).le
  · intro t ht
    have ht' : (⟨t, ht⟩ : ↥Tb) ∈ P.toSubgroup.map f := by
      rw [hS]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.1 ht'
    have hΦx : Φ x = t := congrArg Subtype.val hxt
    have hxS : (x : G) ∈ P.toSubgroup.map (preMod 3 L Tb).subtype :=
      Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ L := preMod_le 3 L Tb x.2
    rw [← hΦx]
    exact Subgroup.mem_map.2 ⟨⟨(x : G), hxL⟩, Subgroup.mem_subgroupOf.2 hxS, rfl⟩

open scoped Pointwise in
theorem exists_lift_twoGroup {L A : Subgroup G} (hA : IsPGroup 3 A) {Tb : Subgroup (PQuot 3 L)}
    (hT2 : IsPGroup 2 Tb) (hAT : A ≤ Subgroup.normalizer (preMod 3 L Tb : Set G)) :
    ∃ T : Subgroup G, T ≤ preMod 3 L Tb ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      imageMod 3 L T = Tb ∧
      ∀ T' : Subgroup G, T' ≤ preMod 3 L Tb → IsPGroup 2 T' → T ≤ T' → T' = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT3 : ¬ 3 ∣ Nat.card ↥(preMod 3 L Tb) := y5x_not_three_dvd_preMod hT2
  have hSyl : ¬ 3 ∣ Nat.card (Sylow 2 ↥(preMod 3 L Tb)) := by
    obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥(preMod 3 L Tb)))
    intro h
    exact hT3 (h.trans ((Sylow.card_dvd_index P0).trans (Subgroup.index_dvd_card _)))
  letI : MulDistribMulAction ↥A ↥(preMod 3 L Tb) :=
    { smul := fun a t => ⟨(a : G) * t * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hAT a.2) t).1 t.2⟩
      one_smul := fun t => Subtype.ext (by
        show (1 : G) * (t : G) * (1 : G)⁻¹ = t
        simp)
      mul_smul := fun a b t => Subtype.ext (by
        show ((a * b : ↥A) : G) * (t : G) * ((a * b : ↥A) : G)⁻¹ =
          (a : G) * ((b : G) * (t : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc])
      smul_one := fun a => Subtype.ext (by
        show (a : G) * (1 : G) * (a : G)⁻¹ = 1
        simp)
      smul_mul := fun a x y => Subtype.ext (by
        show (a : G) * ((x : G) * (y : G)) * (a : G)⁻¹ =
          ((a : G) * (x : G) * (a : G)⁻¹) * ((a : G) * (y : G) * (a : G)⁻¹)
        group) }
  obtain ⟨P, hP⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA (Sylow 2 ↥(preMod 3 L Tb)) hSyl
  rw [MulAction.mem_fixedPoints] at hP
  let S : Subgroup G := P.toSubgroup.map (preMod 3 L Tb).subtype
  have hfix : ∀ a : ↥A, a • P.toSubgroup = P.toSubgroup := by
    intro a
    rw [← Sylow.pointwise_smul_def, hP a]
  have hfwd : ∀ a : ↥A, ∀ h ∈ S, (a : G) * h * (a : G)⁻¹ ∈ S := by
    rintro a h hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    have hmem : a • t ∈ P.toSubgroup := by
      rw [← hfix a]
      exact Subgroup.smul_mem_pointwise_smul t a _ ht
    exact Subgroup.mem_map.2 ⟨a • t, hmem, rfl⟩
  have hnorm : A ≤ Subgroup.normalizer (S : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hfwd ⟨a, ha⟩ h hh
    · intro hh
      have h1 := hfwd ⟨a⁻¹, A.inv_mem ha⟩ _ hh
      have e : (a⁻¹ : G) * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
      rw [e] at h1
      exact h1
  have hmax : ∀ T' : Subgroup G, T' ≤ preMod 3 L Tb → IsPGroup 2 T' → S ≤ T' → T' = S := by
    intro T' hT'T hT'2 hST'
    have hsub : P.toSubgroup ≤ T'.subgroupOf (preMod 3 L Tb) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hST' (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    have hp2 : IsPGroup 2 ↥(T'.subgroupOf (preMod 3 L Tb)) := by
      intro x
      obtain ⟨k, hk⟩ := hT'2 ⟨((x : ↥(preMod 3 L Tb)) : G), Subgroup.mem_subgroupOf.1 x.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have h2 := congrArg (fun q : ↥T' => (q : G)) hk
      simpa using h2
    have heq := P.is_maximal' hp2 hsub
    calc T' = (T'.subgroupOf (preMod 3 L Tb)).map (preMod 3 L Tb).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hT'T).symm
      _ = S := by rw [heq]
  have hSle : S ≤ preMod 3 L Tb := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  exact ⟨S, hSle, P.isPGroup'.map _, hnorm, y5x_sylow_image hT2 P, hmax⟩

open scoped Pointwise in
open Equiv in
theorem imageMod_normalizer_le {L T : Subgroup G} (hT : T ≤ L) (hT2 : IsPGroup 2 T)
    (hSyl : ∀ T' : Subgroup G, T' ≤ preMod 3 L (imageMod 3 L T) → IsPGroup 2 T' → T ≤ T' → T' = T) :
    Subgroup.normalizer ((imageMod 3 L T : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) ≤
      imageMod 3 L (Subgroup.normalizer (T : Set G) ⊓ L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  set Th := preMod 3 L (imageMod 3 L T) with hTh
  have hTTh : T ≤ Th := fun t ht =>
    mem_preMod_iff.2 ⟨hT ht, ⟨⟨t, hT ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩⟩
  have hgN : (g : G) ∈ Subgroup.normalizer (Th : Set G) := mem_normalizer_preMod g.2 hq
  have hP2 : IsPGroup 2 (T.subgroupOf Th) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTTh).symm
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hST : (S : Subgroup ↥Th).map Th.subtype = T := by
    refine hSyl _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) ?_
    intro t ht
    exact ⟨⟨t, hTTh ht⟩, hPS (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  set Tg := T.map (MulAut.conj (g : G)).toMonoidHom with hTg
  have hTgTh : Tg ≤ Th := by
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hgN t).1 (hTTh ht)
  have hcardT : Nat.card ↥(T.subgroupOf Th) = Nat.card ↥(S : Subgroup ↥Th) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTTh).toEquiv, ← hST,
      Subgroup.card_map_of_injective Th.subtype_injective]
  have hcardTg : Nat.card ↥(Tg.subgroupOf Th) = 2 ^ (Nat.card ↥Th).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTgTh).toEquiv, hTg,
      Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTTh).toEquiv, hcardT]
    exact S.card_eq_multiplicity
  let S₁ : Sylow 2 ↥Th := Sylow.ofCard (T.subgroupOf Th) (by rw [hcardT]; exact S.card_eq_multiplicity)
  let S₂ : Sylow 2 ↥Th := Sylow.ofCard (Tg.subgroupOf Th) hcardTg
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq ↥Th S₁ S₂
  have hconj : ∀ z : G, z ∈ T ↔ ((t : G)⁻¹ * g) * z * ((t : G)⁻¹ * g)⁻¹ ∈ T := by
    have key : ∀ w : ↥Th, w ∈ (MulAut.conj t • (T.subgroupOf Th) : Subgroup ↥Th) ↔ w ∈ Tg.subgroupOf Th := by
      intro w
      have := congrArg (fun P : Sylow 2 ↥Th => w ∈ (P : Subgroup ↥Th)) ht
      simp only [Sylow.coe_subgroup_smul, S₁, S₂, Sylow.coe_ofCard] at this
      exact Iff.of_eq this
    intro z
    constructor
    · intro hz
      have hgz : ⟨(g : G) * z * (g : G)⁻¹, hTgTh ⟨z, hz, rfl⟩⟩ ∈ Tg.subgroupOf Th :=
        Subgroup.mem_subgroupOf.2 ⟨z, hz, rfl⟩
      rw [← key] at hgz
      obtain ⟨w, hw, hwe⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hgz
      have hwe' : (t : G) * (w : G) * (t : G)⁻¹ = (g : G) * z * (g : G)⁻¹ := congrArg Subtype.val hwe
      have : ((t : G)⁻¹ * g) * z * ((t : G)⁻¹ * g)⁻¹ = (w : G) := by
        calc ((t : G)⁻¹ * g) * z * ((t : G)⁻¹ * g)⁻¹ = (t : G)⁻¹ * ((g : G) * z * (g : G)⁻¹) * (t : G) := by group
          _ = (t : G)⁻¹ * ((t : G) * (w : G) * (t : G)⁻¹) * (t : G) := by rw [hwe']
          _ = (w : G) := by group
      rw [this]; exact Subgroup.mem_subgroupOf.1 hw
    · intro hz
      set z' := ((t : G)⁻¹ * g) * z * ((t : G)⁻¹ * g)⁻¹ with hz'
      have hz'Th : z' ∈ Th := hTTh hz
      have hw : (⟨z', hz'Th⟩ : ↥Th) ∈ T.subgroupOf Th := Subgroup.mem_subgroupOf.2 hz
      have h1 : t * ⟨z', hz'Th⟩ * t⁻¹ ∈ (MulAut.conj t • (T.subgroupOf Th) : Subgroup ↥Th) :=
        (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨_, hw, rfl⟩
      rw [key] at h1
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_subgroupOf.1 h1
      have hue' : (g : G) * u * (g : G)⁻¹ = (t : G) * z' * (t : G)⁻¹ := hue
      have : z = u := by
        have : (t : G) * z' * (t : G)⁻¹ = (g : G) * z * (g : G)⁻¹ := by rw [hz']; group
        rw [this] at hue'
        exact (mul_left_cancel (mul_right_cancel hue')).symm
      rw [this]; exact hu
  have hn : (t : G)⁻¹ * g ∈ Subgroup.normalizer (T : Set G) := Subgroup.mem_normalizer_iff.2 hconj
  have htL : (t : G) ∈ L := preMod_le 3 L _ t.2
  have hnL : (t : G)⁻¹ * g ∈ L := L.mul_mem (L.inv_mem htL) g.2
  have htimg : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : PQuot 3 L) ∈
      imageMod 3 L (Subgroup.normalizer (T : Set G) ⊓ L) := by
    obtain ⟨_, h⟩ := mem_preMod_iff.1 t.2
    exact imageMod_mono (le_inf (fun x hx => Subgroup.le_normalizer hx) hT) h
  have hnimg : (QuotientGroup.mk (⟨(t : G)⁻¹ * g, hnL⟩ : ↥L) : PQuot 3 L) ∈
      imageMod 3 L (Subgroup.normalizer (T : Set G) ⊓ L) :=
    ⟨⟨(t : G)⁻¹ * g, hnL⟩, Subgroup.mem_subgroupOf.2 ⟨hn, hnL⟩, rfl⟩
  have : (QuotientGroup.mk g : PQuot 3 L) =
      QuotientGroup.mk (⟨t, htL⟩ : ↥L) * QuotientGroup.mk (⟨(t : G)⁻¹ * g, hnL⟩ : ↥L) := by
    rw [← QuotientGroup.mk_mul]; congr 1; apply Subtype.ext; simp
  rw [this]
  exact Subgroup.mul_mem _ htimg hnimg

open Equiv in
theorem imageMod_fixed_lift {K N Dd : Subgroup G} (hDp : IsPGroup 3 Dd) (hDK : Dd ≤ Subgroup.normalizer (K : Set G))
    (hDN : Dd ≤ Subgroup.normalizer (N : Set G)) (hNK : N ≤ K) {q : PQuot 3 K} (hq : q ∈ imageMod 3 K N)
    (hfix : ∀ (d : G) (hd : d ∈ Dd), barAut 3 K ⟨d, hDK hd⟩ q = q) :
    q ∈ imageMod 3 K (N ⊓ Subgroup.centralizer (Dd : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Type := {g : G // ∃ h : g ∈ N, (QuotientGroup.mk (⟨g, hNK h⟩ : ↥K) : PQuot 3 K) = q}
  have hconjN : ∀ d ∈ Dd, ∀ g ∈ N, d * g * d⁻¹ ∈ N := fun d hd g hg =>
    (Subgroup.mem_normalizer_iff.1 (hDN hd) g).1 hg
  have hfib : ∀ (d : G) (hd : d ∈ Dd) (g : X), ∃ h : d * g.1 * d⁻¹ ∈ N,
      (QuotientGroup.mk (⟨d * g.1 * d⁻¹, hNK h⟩ : ↥K) : PQuot 3 K) = q := by
    intro d hd g
    obtain ⟨hg, hgq⟩ := g.2
    refine ⟨hconjN d hd g.1 hg, ?_⟩
    have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 K ⟨d, hDK hd⟩ ⟨g.1, hNK hg⟩
    rw [hgq, hfix d hd] at h1
    have e : (⟨d * g.1 * d⁻¹, hNK (hconjN d hd g.1 hg)⟩ : ↥K) =
        K.normalizerMonoidHom ⟨d, hDK hd⟩ ⟨g.1, hNK hg⟩ := Subtype.ext rfl
    rw [e]; exact h1.symm
  let act : MulAction ↥Dd X :=
    { smul := fun d g => ⟨d.1 * g.1 * d.1⁻¹, hfib d.1 d.2 g⟩
      one_smul := fun g => Subtype.ext (by
        show ((1 : ↥Dd) : G) * g.1 * ((1 : ↥Dd) : G)⁻¹ = g.1; simp)
      mul_smul := fun a b g => Subtype.ext (by
        show ((a * b : ↥Dd) : G) * g.1 * ((a * b : ↥Dd) : G)⁻¹ =
          (a : G) * ((b : G) * g.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]; group) }
  haveI : Finite X := Subtype.finite
  have hmod := hDp.card_modEq_card_fixedPoints X
  obtain ⟨⟨z, hzK⟩, hzN, hzq⟩ := hq
  have hzN' : z ∈ N := Subgroup.mem_subgroupOf.1 hzN
  let W := GLAPPrimeCoreOf 3 K
  have hmemW : ∀ g : X, z⁻¹ * g.1 ∈ N ⊓ W := by
    intro g
    obtain ⟨hg, hgq⟩ := g.2
    refine ⟨N.mul_mem (N.inv_mem hzN') hg, ?_⟩
    have h1 : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : PQuot 3 K) = QuotientGroup.mk ⟨g.1, hNK hg⟩ := by
      rw [hgq]; exact hzq
    rw [QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  have hmemX : ∀ w : ↥(N ⊓ W : Subgroup G), ∃ h : z * w.1 ∈ N,
      (QuotientGroup.mk (⟨z * w.1, hNK h⟩ : ↥K) : PQuot 3 K) = q := by
    intro w
    obtain ⟨w', hw', hww⟩ := w.2.2
    refine ⟨N.mul_mem hzN' w.2.1, ?_⟩
    have : (⟨z * w.1, hNK (N.mul_mem hzN' w.2.1)⟩ : ↥K) = ⟨z, hzK⟩ * w' := by
      apply Subtype.ext; simp only [Subgroup.coe_mul]; rw [← hww]; rfl
    rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hw', mul_one]
    exact hzq
  have hX : Nat.card X = Nat.card ↥(N ⊓ W : Subgroup G) :=
    Nat.card_congr
      { toFun := fun g => ⟨z⁻¹ * g.1, hmemW g⟩
        invFun := fun w => ⟨z * w.1, hmemX w⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
  have hcop : ¬ 3 ∣ Nat.card X := by
    rw [hX]
    intro h3
    have h1 : Nat.card ↥(N ⊓ W : Subgroup G) ∣ Nat.card ↥W := Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥W = Nat.card ↥(GLAPPrimeCore 3 ↥K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have hc : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
    have := Nat.Coprime.coprime_dvd_right (h2 ▸ h1) hc
    exact absurd (Nat.Coprime.eq_one_of_dvd this h3) (by norm_num)
  have hne : Nat.card (MulAction.fixedPoints ↥Dd X) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hcop (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨⟨g, hg⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  obtain ⟨hgN, hgq⟩ := g.2
  have hgC : g.1 ∈ Subgroup.centralizer (Dd : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hg ⟨d, hd⟩)
    change d * g.1 * d⁻¹ = g.1 at this
    calc d * g.1 = d * g.1 * d⁻¹ * d := by group
      _ = g.1 * d := by rw [this]
  exact ⟨⟨g.1, hNK hgN⟩, Subgroup.mem_subgroupOf.2 ⟨hgN, hgC⟩, hgq⟩

theorem imageMod_centralizer_inf_le {K N Dd : Subgroup G} (hDp : IsPGroup 3 Dd) (hDK : Dd ≤ Subgroup.normalizer (K : Set G))
    (hDN : Dd ≤ Subgroup.normalizer (N : Set G)) (hNK : N ≤ K) :
    imageMod 3 K (K ⊓ Subgroup.centralizer (Dd : Set G)) ⊓ imageMod 3 K N ≤
      imageMod 3 K (N ⊓ Subgroup.centralizer (Dd : Set G)) := by
  rintro q ⟨⟨g, hg, rfl⟩, hqN⟩
  refine imageMod_fixed_lift hDp hDK hDN hNK hqN ?_
  intro d hd
  have hgC : (g : G) ∈ Subgroup.centralizer (Dd : Set G) := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).2
  have hcomm : d * (g : G) = (g : G) * d := Subgroup.mem_centralizer_iff.1 hgC d hd
  show barAut 3 K ⟨d, hDK hd⟩ (pQuotHom 3 K g) = pQuotHom 3 K g
  rw [barAut_pQuotHom]
  congr 1
  apply Subtype.ext
  show d * (g : G) * d⁻¹ = g
  rw [hcomm]
  group

theorem imageMod_inf_centralizer_le {L N : Subgroup G} {y : G} (hy : y ∈ L) (hy3 : y ^ 3 = 1) (hNL : N ≤ L)
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) :
    imageMod 3 L N ⊓ Subgroup.centralizer ({modOf 3 L y hy} : Set (PQuot 3 L)) ≤
      imageMod 3 L (N ⊓ Subgroup.centralizer ({y} : Set G)) := by
  rintro q ⟨hqN, hqc⟩
  have hDK : Subgroup.zpowers y ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).2 (Subgroup.le_normalizer hy)
  have hDN : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set G) := (Subgroup.zpowers_le).2 hyN
  have hfix : ∀ (d : G) (hd : d ∈ Subgroup.zpowers y), barAut 3 L ⟨d, hDK hd⟩ q = q := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    have hyk : y ^ k ∈ L := L.zpow_mem hy k
    have h1 : barAut 3 L ⟨y ^ k, hDK hd⟩ = MulAut.conj (QuotientGroup.mk (⟨y ^ k, hyk⟩ : ↥L) : PQuot 3 L) :=
      barAut_eq_conj_of_mem hyk
    rw [h1, MulAut.conj_apply]
    have hqy : q * modOf 3 L y hy = modOf 3 L y hy * q := Subgroup.mem_centralizer_singleton_iff.1 hqc
    have hmk : (QuotientGroup.mk (⟨y ^ k, hyk⟩ : ↥L) : PQuot 3 L) = (modOf 3 L y hy) ^ k := by
      unfold modOf
      rw [← QuotientGroup.mk_zpow]
      rfl
    rw [hmk]
    have hc : Commute q (modOf 3 L y hy) := hqy
    have := (hc.zpow_right k).eq
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have := imageMod_fixed_lift (isPGroup_zpowers_of_pow_eq_one hy3) hDK hDN hNL hqN hfix
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at this

theorem imageMod_normCent_le {L T : Subgroup G} {x y : G} (hy : y ∈ L) :
    imageMod 3 L (Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L) ≤
      Subgroup.normalizer ((imageMod 3 L T : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) ⊓
        Subgroup.centralizer ({modOf 3 L y hy} : Set (PQuot 3 L)) := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' := Subgroup.mem_subgroupOf.1 hg
  have hgN : (g : G) ∈ Subgroup.normalizer (T : Set G) := hg'.1.1
  have hgD : (g : G) ∈ Subgroup.centralizer (altDxy x y : Set G) := hg'.1.2
  refine ⟨?_, ?_⟩
  · have hg'N : g ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.1 hgN z
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) ⟨g, hg'N, rfl⟩
  · have hyD : y ∈ altDxy x y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hcomm : y * (g : G) = (g : G) * y := Subgroup.mem_centralizer_iff.1 hgD y hyD
    change QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g ∈ Subgroup.centralizer ({modOf 3 L y hy} : Set (PQuot 3 L))
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g * QuotientGroup.mk (⟨y, hy⟩ : ↥L) =
      QuotientGroup.mk (⟨y, hy⟩ : ↥L) * QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g
    have h2 : g * (⟨y, hy⟩ : ↥L) = (⟨y, hy⟩ : ↥L) * g := Subtype.ext hcomm.symm
    calc QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g * QuotientGroup.mk (⟨y, hy⟩ : ↥L)
        = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (g * ⟨y, hy⟩) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨y, hy⟩ * g) := by rw [h2]
      _ = QuotientGroup.mk (⟨y, hy⟩ : ↥L) * QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g := map_mul _ _ _

theorem imageMod_normCent {L T : Subgroup G} {x y : G} (hxL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hy : y ∈ L) (hyo : orderOf y = 3) (hxo : x ^ 3 = 1) (hxy : x * y = y * x) (hT : T ≤ L) (hT2 : IsPGroup 2 T)
    (hDN : altDxy x y ≤ Subgroup.normalizer (T : Set G))
    (hSyl : ∀ T' : Subgroup G, T' ≤ preMod 3 L (imageMod 3 L T) → IsPGroup 2 T' → T ≤ T' → T' = T) :
    imageMod 3 L (Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L) =
      Subgroup.normalizer ((imageMod 3 L T : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) ⊓
        Subgroup.centralizer ({modOf 3 L y hy} : Set (PQuot 3 L)) := by
  have hyD : y ∈ altDxy x y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  refine le_antisymm (imageMod_normCent_le hy) ?_
  intro q hq
  have hyN' : y ∈ Subgroup.normalizer ((Subgroup.normalizer (T : Set G) ⊓ L : Subgroup G) : Set G) :=
    Subgroup.le_normalizer ⟨hDN hyD, hy⟩
  have h1 := imageMod_normalizer_le hT hT2 hSyl hq.1
  have h2 := imageMod_inf_centralizer_le hy (by rw [← hyo]; exact pow_orderOf_eq_one y) inf_le_right hyN'
    ⟨h1, hq.2⟩
  refine imageMod_mono ?_ h2
  intro g hg
  have hgD : g ∈ L ⊓ Subgroup.centralizer (altDxy x y : Set G) := by
    rw [inf_centralizer_altDxy_eq hxL]
    exact ⟨hg.1.2, hg.2⟩
  exact ⟨⟨hg.1.1, hgD.2⟩, hg.1.2⟩

theorem genByPElts_of_isElemAbelian {p : ℕ} {I : Subgroup G} (hI : IsElemAbelian p I) : GenByPElts p I :=
  fun g hg => Subgroup.subset_closure ⟨hg, isPGroup_zpowers_of_pow_eq_one (hI.2 g hg)⟩

theorem genByPElts_layer {p : ℕ} (hp : p.Prime) (X : Subgroup G) : GenByPElts p (GLAPLayer p X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Λ : Subgroup G := GLAPLayer p X
  let S : Set G := {g : G | g ∈ Λ ∧ IsPGroup p (Subgroup.zpowers g)}
  let N : Subgroup G := Subgroup.closure S
  have hNΛ : N ≤ Λ := (Subgroup.closure_le _).2 fun g hg => hg.1
  have hconj : ∀ a ∈ Λ, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
    rintro a ha s ⟨hs, hsp⟩
    refine ⟨Λ.mul_mem (Λ.mul_mem ha hs) (Λ.inv_mem ha), ?_⟩
    obtain ⟨m, hm⟩ := isPGroup_zpowers_iff_exists_pow.1 hsp
    refine isPGroup_zpowers_iff_exists_pow.2 ⟨m, ?_⟩
    rw [conj_pow, hm, mul_one, mul_inv_cancel]
  have hstab : ∀ g ∈ Λ, N ≤ N.comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    exact Subgroup.subset_closure (hconj g hg s hs)
  have hNn : (N.subgroupOf Λ).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hstab (g : G) g.2 hn
    simpa [Subgroup.mem_comap, MulAut.conj_apply, mul_assoc] using h1
  have hidx : Nat.Coprime p (N.subgroupOf Λ).index := by
    obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥Λ))
    have hQN : Q.toSubgroup ≤ N.subgroupOf Λ := by
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      apply Subgroup.subset_closure
      refine ⟨q.2, ?_⟩
      obtain ⟨k, hk⟩ := Q.isPGroup' (⟨q, hq⟩ : ↥Q.toSubgroup)
      refine isPGroup_zpowers_iff_exists_pow.2 ⟨k, ?_⟩
      have h2 : q ^ p ^ k = 1 := congrArg Subtype.val hk
      exact congrArg Subtype.val h2
    have hdvd1 : (N.subgroupOf Λ).index ∣ Q.toSubgroup.index := Subgroup.index_dvd_of_le hQN
    have hnd : ¬ p ∣ Q.toSubgroup.index := Sylow.not_dvd_index Q
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hnd (h.trans hdvd1)
  have hNeq : N = Λ := layer_isOPrimeResidual hp X N hNΛ hNn hidx
  exact hNeq.ge

private theorem y5x_three_dvd_card_alt (m : ℕ) (hm : 5 ≤ m) :
    3 ∣ Nat.card (alternatingGroup (Fin m)) := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin m)
  have hfin : Nat.card (Fin m) = m := by simp
  rw [Nat.card_perm, hfin] at h1
  have h2 : 3 ∣ 2 * Nat.card (alternatingGroup (Fin m)) := by
    rw [h1]
    exact Nat.dvd_factorial (by norm_num) (by omega)
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2)

theorem isAltPType_of_imageMod {L I : Subgroup G} (hIL : I ≤ L) {m : ℕ} (hm : 5 ≤ m)
    (h : Nonempty (↥(imageMod 3 L I) ≃* ↥(alternatingGroup (Fin m)))) : IsAltPType 3 I m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup (by simp [hm])
  have h3A : 3 ∣ Nat.card (alternatingGroup (Fin m)) := y5x_three_dvd_card_alt m hm
  let Φ : ↥I →* PQuot 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hIL)
  have hΦ : ∀ i : ↥I, Φ i ∈ imageMod 3 L I := fun i =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hIL i, Subgroup.mem_subgroupOf.2 i.2, rfl⟩
  let Φ' : ↥I →* ↥(imageMod 3 L I) := Φ.codRestrict (imageMod 3 L I) hΦ
  let f : ↥I →* ↥(alternatingGroup (Fin m)) := ψ.toMonoidHom.comp Φ'
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨s, hs⟩ := ψ.surjective a
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.1 s.2
    refine ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, ?_⟩
    have h1 : Φ' ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩ = s := Subtype.ext hxs
    show ψ (Φ' ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩) = a
    rw [h1]
    exact hs
  have hOL : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  have hOI : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥I)) := CFSG.pPrimeCore_coprime_card
  have hker : f.ker = GLAPPrimeCore 3 ↥I := by
    apply le_antisymm
    · have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
        have hsub : f.ker.map (Subgroup.inclusion hIL) ≤ GLAPPrimeCore 3 ↥L := by
          rintro _ ⟨x, hx, rfl⟩
          have hx1 : f x = 1 := hx
          have hΦ1 : Φ x = 1 := by
            have h2 : Φ' x = 1 := by
              apply ψ.injective
              rw [map_one]
              exact hx1
            exact congrArg Subtype.val h2
          exact (QuotientGroup.eq_one_iff _).1 hΦ1
        have hdvd : Nat.card (f.ker.map (Subgroup.inclusion hIL)) ∣ Nat.card (GLAPPrimeCore 3 ↥L) :=
          Subgroup.card_dvd_of_le hsub
        rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIL)] at hdvd
        exact Nat.Coprime.coprime_dvd_right hdvd hOL
      exact le_sSup ⟨inferInstance, hcop⟩
    · intro x hx
      have hH : (GLAPPrimeCore 3 ↥I).map f = ⊥ := by
        haveI : ((GLAPPrimeCore 3 ↥I).map f).Normal := Subgroup.Normal.map inferInstance f hf
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore 3 ↥I).map f) with hb | ht
        · exact hb
        · exfalso
          have hcard := Subgroup.card_map_dvd (GLAPPrimeCore 3 ↥I) f
          rw [ht, Subgroup.card_top] at hcard
          have h3O : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥I) := dvd_trans h3A hcard
          have := Nat.Coprime.eq_one_of_dvd hOI h3O
          norm_num at this
      have hmem : f x ∈ (GLAPPrimeCore 3 ↥I).map f := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rw [hH, Subgroup.mem_bot] at hmem
      exact hmem
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

private theorem y5x_mem_layer_of_imageMod {p : ℕ} (hp : p.Prime) {L Z : Subgroup G} (hZL : Z ≤ L) {g : G}
    (hgZ : g ∈ Z) (hgp : IsPGroup p (Subgroup.zpowers g))
    (h : (QuotientGroup.mk (⟨g, hZL hgZ⟩ : ↥L) : PQuot p L) ∈ imageMod p L (GLAPLayer p Z)) :
    g ∈ GLAPLayer p Z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hJZ : GLAPLayer p Z ≤ Z := sSup_le fun _ hL => hL.1
  have hJn : ((GLAPLayer p Z).subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJZ).2 fun g hg =>
      mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hgL : g ∈ L := hZL hgZ
  obtain ⟨m, hm⟩ := (isPGroup_zpowers_iff_exists_pow).1 hgp
  obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.1 h
  have huJ : (u : G) ∈ GLAPLayer p Z := Subgroup.mem_subgroupOf.1 hu
  have huZ : (u : G) ∈ Z := hJZ huJ
  have hk : (u : ↥L)⁻¹ * ⟨g, hgL⟩ ∈ GLAPPrimeCore p ↥L := QuotientGroup.eq.1 huv
  let Kz : Subgroup ↥Z := (GLAPPrimeCore p ↥L).comap (Subgroup.inclusion hZL)
  have hKz : Nat.Coprime p (Nat.card ↥Kz) := by
    have hsub : Kz.map (Subgroup.inclusion hZL) ≤ GLAPPrimeCore p ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hZL)] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
  set kZ : ↥Z := (⟨u, huZ⟩ : ↥Z)⁻¹ * ⟨g, hgZ⟩ with hkZdef
  have hkZK : kZ ∈ Kz := by
    show Subgroup.inclusion hZL kZ ∈ GLAPPrimeCore p ↥L
    rw [hkZdef, map_mul, map_inv]
    exact hk
  let q : ↥Z →* ↥Z ⧸ (GLAPLayer p Z).subgroupOf Z := QuotientGroup.mk' _
  have hqu : q ⟨u, huZ⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 huJ)
  have hqg : q ⟨g, hgZ⟩ = q kZ := by
    have : (⟨g, hgZ⟩ : ↥Z) = ⟨u, huZ⟩ * kZ := by rw [hkZdef]; group
    rw [this, map_mul, hqu, one_mul]
  have hpm : q kZ ^ p ^ m = 1 := by
    rw [← hqg, ← map_pow]
    have : (⟨g, hgZ⟩ : ↥Z) ^ p ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [this, map_one]
  have hkz : q kZ ^ Nat.card ↥Kz = 1 := by
    have h1 : (⟨kZ, hkZK⟩ : ↥Kz) ^ Nat.card ↥Kz = 1 := pow_card_eq_one'
    have h2 : kZ ^ Nat.card ↥Kz = 1 := congrArg Subtype.val h1
    rw [← map_pow, h2, map_one]
  have hcop : Nat.Coprime (p ^ m) (Nat.card ↥Kz) := Nat.Coprime.pow_left m hKz
  have h1 : q kZ ^ Nat.gcd (p ^ m) (Nat.card ↥Kz) = 1 := pow_gcd_eq_one.2 ⟨hpm, hkz⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  have hkJ : kZ ∈ (GLAPLayer p Z).subgroupOf Z := (QuotientGroup.eq_one_iff _).1 h1
  have hkJ' : (kZ : G) ∈ GLAPLayer p Z := Subgroup.mem_subgroupOf.1 hkJ
  have hg_eq : g = (u : G) * (kZ : G) := by
    rw [hkZdef]
    simp
  rw [hg_eq]
  exact (GLAPLayer p Z).mul_mem huJ hkJ'

theorem le_layer_of_imageMod_le {p : ℕ} (hp : p.Prime) {L Z I : Subgroup G} (hZL : Z ≤ L) (hIZ : I ≤ Z)
    (hgen : GenByPElts p I) (h : imageMod p L I ≤ imageMod p L (GLAPLayer p Z)) : I ≤ GLAPLayer p Z := by
  have key : ∀ g : G, g ∈ I → IsPGroup p (Subgroup.zpowers g) → g ∈ GLAPLayer p Z := by
    intro g hgI hgp
    have hgL : g ∈ L := hZL (hIZ hgI)
    have hmem : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : PQuot p L) ∈ imageMod p L I :=
      Subgroup.mem_map.2 ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.2 hgI, rfl⟩
    exact y5x_mem_layer_of_imageMod hp hZL (hIZ hgI) hgp (h hmem)
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro g ⟨hgI, hgp⟩
  exact key g hgI hgp

theorem coversMod_of_image_sup {p : ℕ} {L T J : Subgroup G} (hT : T ≤ L) (hJ : J ≤ L)
    (h : imageMod p L T ⊔ imageMod p L J = ⊤) : CoversMod p (T ⊔ J) L := by
  unfold CoversMod
  refine le_antisymm (sup_le inf_le_right ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact g.2
  · intro l hl
    have hmem : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : PQuot p L) ∈ imageMod p L (T ⊔ J) := by
      rw [imageMod_sup hT hJ, h]; exact Subgroup.mem_top _
    obtain ⟨u, hu, hul⟩ := hmem
    have hu' : (u : G) ∈ T ⊔ J := hu
    have hk : (u : G)⁻¹ * l ∈ GLAPPrimeCoreOf p L := by
      have := QuotientGroup.eq.1 hul
      exact ⟨u⁻¹ * ⟨l, hl⟩, this, rfl⟩
    have : l = (u : G) * ((u : G)⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hu', u.2⟩) hk

private theorem y5x_mem_sup_of_comm {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let S : Subgroup G :=
    { carrier := {u | ∃ h ∈ H, ∃ k ∈ K, h * k = u}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        calc h1 * h2 * (k1 * k2) = h1 * (h2 * k1) * k2 := by group
          _ = h1 * (k1 * h2) * k2 := by rw [hHK h2 hh2 k1 hk1]
          _ = h1 * k1 * (h2 * k2) := by group
      inv_mem' := by
        rintro _ ⟨h1, hh1, k1, hk1, rfl⟩
        refine ⟨h1⁻¹, H.inv_mem hh1, k1⁻¹, K.inv_mem hk1, ?_⟩
        calc h1⁻¹ * k1⁻¹ = (k1 * h1)⁻¹ := by group
          _ = (h1 * k1)⁻¹ := by rw [hHK h1 hh1 k1 hk1] }
  have hsup : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  exact hsup hx

private theorem y5x_eq_one_of_pow3_mem_O {L : Subgroup G} {u : G} (hL : u ∈ L) (hu3 : u ^ 3 = 1)
    (hmk : (QuotientGroup.mk (⟨u, hL⟩ : ↥L) : PQuot 3 L) = 1) : u = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyO : (⟨u, hL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 hmk
  let o : ↥(GLAPPrimeCore 3 ↥L) := ⟨⟨u, hL⟩, hyO⟩
  have ho3 : o ^ 3 = 1 := Subtype.ext (Subtype.ext hu3)
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ho3) with h1 | h1
  · exact congrArg (fun q : ↥(GLAPPrimeCore 3 ↥L) => ((q : ↥L) : G)) (orderOf_eq_one_iff.1 h1)
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
    have h3O : 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
      have := orderOf_dvd_natCard o
      rwa [h1] at this
    have := Nat.Coprime.eq_one_of_dvd hcop h3O
    norm_num at this

theorem B_eq_of_image {B L T I : Subgroup G} {x y : G} {n : ℕ} {Ω : Set (Fin n)}
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hdir : IsDirectZpowersInf B x L)
    (hBel : IsElemAbelian 3 B) (hyB : y ∈ B) (hxB : x ∈ B) (hyL : y ∈ L) (hyo : orderOf y = 3)
    (hBN : B ≤ Subgroup.normalizer (T : Set G))
    (hIeq : I = GLAPLayer 3 (Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L))
    (e : PQuot 3 L ≃* ↥(alternatingGroup (Fin n)))
    (hcyc : (permOfMod 3 L n e y).cycleType = {3})
    (himg : imageMod 3 L I = altFixSub e Ω)
    (hIJ : altFixSub e Ω ≤ altFixSub e ((permOfMod 3 L n e y).support : Set (Fin n)))
    (hE : imageMod 3 L (B ⊓ L) ≤ Subgroup.zpowers (modOf 3 L y hyL) ⊔ (imageMod 3 L (B ⊓ L) ⊓ altFixSub e Ω) ∧
      Subgroup.zpowers (modOf 3 L y hyL) ⊓ (imageMod 3 L (B ⊓ L) ⊓ altFixSub e Ω) = ⊥) :
    B = altDxy x y ⊔ (B ⊓ I) ∧ altDxy x y ⊓ (B ⊓ I) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBel.1.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩)
  have hB3 : ∀ g ∈ B, g ^ 3 = 1 := fun g hg => hBel.2 g hg
  have hIX : I ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L := by
    rw [hIeq]
    exact sSup_le fun _ hM => hM.1
  have hIL : I ≤ L := hIX.trans inf_le_right
  have key : ∀ g : G, g ∈ B → ∀ hgL : g ∈ L,
      (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : PQuot 3 L) ∈ altFixSub e Ω → g ∈ I := by
    intro g hg hgL hmem
    have hgX : g ∈ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L := by
      exact ⟨⟨hBN hg, mem_centralizer_altDxy_iff.2 ⟨hcomm g hg x hxB, hcomm g hg y hyB⟩⟩, hgL⟩
    have hgp : IsPGroup 3 (Subgroup.zpowers g) :=
      isPGroup_zpowers_iff_exists_pow.2 ⟨1, by simpa using hB3 g hg⟩
    have hmem' : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : PQuot 3 L) ∈ imageMod 3 L
        (GLAPLayer 3 (Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L)) := by
      rw [← hIeq, himg]
      exact hmem
    rw [hIeq]
    exact y5x_mem_layer_of_imageMod Nat.prime_three inf_le_right hgX hgp hmem'
  have hcommB : ∀ k ∈ imageMod 3 L (B ⊓ L), modOf 3 L y hyL * k = k * modOf 3 L y hyL := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hk
    have hcB : (c : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)).1
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨y, hyL⟩ : ↥L) * QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) c =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) c * QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨y, hyL⟩ : ↥L)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm y hyB c hcB)
  have hBsplit : ∀ b ∈ B ⊓ L, b ∈ Subgroup.zpowers y ⊔ (B ⊓ I) := by
    intro b hb
    have hbL : b ∈ L := hb.2
    have hmemB : (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : PQuot 3 L) ∈ imageMod 3 L (B ⊓ L) :=
      Subgroup.mem_map.2 ⟨⟨b, hbL⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
    obtain ⟨h, hh, k, hk, hhk⟩ := y5x_mem_sup_of_comm
      (H := Subgroup.zpowers (modOf 3 L y hyL)) (K := imageMod 3 L (B ⊓ L) ⊓ altFixSub e Ω)
      (fun h hh k hk => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact ((show Commute (modOf 3 L y hyL) k from hcommB k hk.1).zpow_left j).eq)
      (hE.1 hmemB)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    let d : ↥L := ((⟨y, hyL⟩ : ↥L) ^ j)⁻¹ * ⟨b, hbL⟩
    have hdk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) d = k := by
      have hhk' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨y, hyL⟩ : ↥L) ^ j * k =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨b, hbL⟩ : ↥L) := hhk
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (((⟨y, hyL⟩ : ↥L) ^ j)⁻¹ * ⟨b, hbL⟩) = k
      rw [map_mul, map_inv, map_zpow, ← hhk']
      exact inv_mul_cancel_left _ _
    have hdG : (d : G) = (y ^ j)⁻¹ * b := by
      simp [d]
    have hdB : (d : G) ∈ B := by
      rw [hdG]
      exact B.mul_mem (B.inv_mem (B.zpow_mem hyB j)) hb.1
    have hdI : (d : G) ∈ I := by
      apply key (d : G) hdB d.2
      have hd' : (QuotientGroup.mk (⟨(d : G), d.2⟩ : ↥L) : PQuot 3 L) = k := hdk
      rw [hd']
      exact hk.2
    have hfin : y ^ j * (d : G) ∈ Subgroup.zpowers y ⊔ (B ⊓ I) :=
      Subgroup.mul_mem_sup ((Subgroup.zpowers y).zpow_mem (Subgroup.mem_zpowers y) j) ⟨hdB, hdI⟩
    have hb_eq : y ^ j * (d : G) = b := by
      rw [hdG]
      group
    rwa [hb_eq] at hfin
  have hBeq : B = altDxy x y ⊔ (B ⊓ I) := by
    have hxD : Subgroup.zpowers x ≤ altDxy x y := le_sup_left
    have hyD : Subgroup.zpowers y ≤ altDxy x y := le_sup_right
    have hDle : altDxy x y ≤ altDxy x y ⊔ (B ⊓ I) := le_sup_left
    refine le_antisymm ?_ (sup_le (sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hyB)) inf_le_left)
    intro b hb
    rw [hdir.1] at hb
    obtain ⟨h, hh, k, hk, hhk⟩ := y5x_mem_sup_of_comm (H := Subgroup.zpowers x) (K := B ⊓ L)
      (fun h hh k hk => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact ((show Commute x k from hcomm x hxB k hk.1).zpow_left j).eq)
      hb
    rw [← hhk]
    apply Subgroup.mul_mem
    · exact hDle (hxD hh)
    · exact sup_le_sup_right hyD _ (hBsplit k hk)
  have hDI : altDxy x y ⊓ (B ⊓ I) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu1, hu2⟩
    have huB : u ∈ B := hu2.1
    have huI : u ∈ I := hu2.2
    have huL : u ∈ L := hIL huI
    obtain ⟨h, hh, k, hk, hhk⟩ := y5x_mem_sup_of_comm (H := Subgroup.zpowers x) (K := Subgroup.zpowers y)
      (fun h hh k hk => by
        obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((show Commute x y from hcomm x hxB y hyB).zpow_zpow a b).eq)
      hu1
    have hkL : k ∈ L := Subgroup.zpowers_le.2 hyL hk
    have hhL : h ∈ L := by
      have hh_eq : h = u * k⁻¹ := by
        rw [← hhk]
        group
      rw [hh_eq]
      exact L.mul_mem huL (L.inv_mem hkL)
    have hh1 : h ∈ Subgroup.zpowers x ⊓ (B ⊓ L) :=
      Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_inf.2 ⟨(Subgroup.zpowers_le.2 hxB) hh, hhL⟩⟩
    have hh_one : h = 1 := by
      have h2 : h ∈ (⊥ : Subgroup G) := by
        rw [← hdir.2]
        exact hh1
      exact Subgroup.mem_bot.1 h2
    have hu_k : u = k := by
      rw [← hhk, hh_one, one_mul]
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hk
    have huy : u = y ^ b := hu_k.trans hb.symm
    have hyu : (⟨u, huL⟩ : ↥L) = (⟨y, hyL⟩ : ↥L) ^ b := Subtype.ext (by simpa using huy)
    have hmk : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : PQuot 3 L) = 1 := by
      have hmem : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : PQuot 3 L) ∈
          Subgroup.zpowers (modOf 3 L y hyL) ⊓ (imageMod 3 L (B ⊓ L) ⊓ altFixSub e Ω) := by
        refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
        · have hpow : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : PQuot 3 L) = modOf 3 L y hyL ^ b := by
            rw [hyu]
            exact map_zpow (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) (⟨y, hyL⟩ : ↥L) b
          rw [hpow]
          exact (Subgroup.zpowers (modOf 3 L y hyL)).zpow_mem (Subgroup.mem_zpowers _) b
        · exact Subgroup.mem_map.2 ⟨⟨u, huL⟩, Subgroup.mem_subgroupOf.2 ⟨huB, huL⟩, rfl⟩
        · have hmemI : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : PQuot 3 L) ∈ imageMod 3 L I :=
            Subgroup.mem_map.2 ⟨⟨u, huL⟩, Subgroup.mem_subgroupOf.2 huI, rfl⟩
          rw [himg] at hmemI
          exact hmemI
      rw [hE.2] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hu_one : u = 1 := y5x_eq_one_of_pow3_mem_O huL (hB3 u huB) hmk
    exact Subgroup.mem_bot.2 hu_one
  exact ⟨hBeq, hDI⟩

theorem l73_exists_y_in_B (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n ≤ 11) :
    ∃ y' ∈ B, y' ∈ L ∧ orderOf y' = 3 ∧ ∃ e : PQuot 3 L ≃* ↥(alternatingGroup (Fin n)),
      IsPCycleMod 3 L n e y' := by
  obtain ⟨e⟩ := S.alt
  have hn9 : 9 ≤ n := by have := S.three_mul_le; omega
  have hBLel : IsElemAbelian 3 (B ⊓ L : Subgroup G) :=
    isElemAbelian_mono (IsSStarMax.bmax hB).1 inf_le_left
  obtain ⟨h1, h2⟩ := imageMod_elemAbelian hc.prime (inf_le_right : B ⊓ L ≤ L) hBLel
  have hcard : Nat.card ↥(imageMod 3 L (B ⊓ L)) = 3 ^ (n / 3) := by
    rw [h2, l73_card_BL hc hB S hn]
    have : n / 3 = 3 := by omega
    rw [this]
  obtain ⟨q, hq, hqc⟩ := exists_three_cycle_of_maxRank e (by omega) h1 hcard
  obtain ⟨g, hg, rfl⟩ := hq
  have hgBL : (g : G) ∈ B ⊓ L := hg
  have hperm : permOfMod 3 L n e (g : G) = permOfQ e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g) := by
    unfold permOfQ permOfMod
    rw [dif_pos g.2]
    rfl
  refine ⟨(g : G), hgBL.1, hgBL.2, ?_, e, hgBL.2, ?_⟩
  · have hne : (g : G) ≠ 1 := by
      intro h1'
      have : permOfQ e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) g) = 1 := by
        have : g = 1 := Subtype.ext h1'
        subst this
        simp [permOfQ]
      rw [this] at hqc
      simp at hqc
    exact orderOf_eq_prime ((IsSStarMax.bmax hB).1.2 _ hgBL.1) hne
  · rw [hperm]
    exact hqc

theorem l73_rechoose (hc : S6Ctx G 3) {B : Subgroup G} {x : G}
    {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L)
    (S : AltSetup 3 B x L n y J) (hn : n ≤ 11) :
    ∃ (y' : G) (J' : Subgroup G), y' ∈ B ∧ AltSetup 3 B x L n y' J' := by
  obtain ⟨y', hyB, -, hyo, e, hy⟩ := l73_exists_y_in_B hc hB S hn
  obtain ⟨J', hJ'⟩ := AltSetup.rechoose hc hB S e hy hyo
  exact ⟨y', J', hyB, hJ'⟩

structure L73TI (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G) (J : Subgroup G)
    (T I : Subgroup G) : Prop where
  T_le : T ≤ L
  T_two : IsPGroup 2 T
  T_not_le : ¬ T ≤ GLAPPrimeCoreOf 3 L
  D_le_N : altDxy x y ≤ Subgroup.normalizer (T : Set G)
  B_le_N : (n = 10 ∨ n = 11) → B ≤ Subgroup.normalizer (T : Set G)
  covers : CoversMod 3 (T ⊔ J) L
  I_eq : I = GLAPLayer 3 (Subgroup.normalizer (T : Set G) ⊓
    Subgroup.centralizer (altDxy x y : Set G) ⊓ L)
  I_le_J : I ≤ J
  I_alt : IsAltPType 3 I (n - 4)
  comm_T : (⁅I, T⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 L
  gen : GenByPElts 3 I
  B_eq_I : (n = 10 ∨ n = 11) → B = altDxy x y ⊔ (B ⊓ I) ∧ altDxy x y ⊓ (B ⊓ I) = ⊥
  root : ∃ e : PQuot 3 L ≃* ↥(alternatingGroup (Fin n)), IsPCycleMod 3 L n e y ∧
    (∃ Ω₄ : Finset (Fin n), Ω₄.card = 4 ∧ (permOfMod 3 L n e y).support ⊆ Ω₄ ∧
      imageMod 3 L I = altFixSub e (Ω₄ : Set (Fin n))) ∧
    imageMod 3 L J = altFixSub e ((permOfMod 3 L n e y).support : Set (Fin n))

theorem l73_exists_TI (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn12 : n ≤ 12)
    (hy : n < 12 → y ∈ B) : ∃ T I : Subgroup G, L73TI B x L n y J T I := by
  obtain ⟨e, hcyc, hfix⟩ := S.cycle
  have hn9 : 9 ≤ n := by have := S.three_mul_le; omega
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hB).1
  have hyL : y ∈ L := S.y_mem
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hperm : permOfQ e (modOf 3 L y hyL) = permOfMod 3 L n e y := by
    unfold permOfQ permOfMod modOf
    rw [dif_pos hyL]
  have hcycQ : (permOfQ e (modOf 3 L y hyL)).cycleType = {3} := by
    rw [hperm]; exact hcyc.2
  have hDB : (n = 10 ∨ n = 11) → altDxy x y ≤ B := by
    intro hn
    have hyB : y ∈ B := hy (by omega)
    exact sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have hE : (n = 10 ∨ n = 11) → IsElemAbelian 3 (imageMod 3 L (B ⊓ L)) ∧
      Nat.card ↥(imageMod 3 L (B ⊓ L)) = 3 ^ 3 ∧ modOf 3 L y hyL ∈ imageMod 3 L (B ⊓ L) := by
    intro hn
    have hyB : y ∈ B := hy (by omega)
    have hel : IsElemAbelian 3 (B ⊓ L : Subgroup G) := isElemAbelian_mono (IsSStarMax.bmax hB).1 inf_le_left
    obtain ⟨h1, h2⟩ := imageMod_elemAbelian hc.prime (inf_le_right : B ⊓ L ≤ L) hel
    refine ⟨h1, h2.trans (l73_card_BL hc hB S (by omega)), ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 ⟨hyB, hyL⟩, rfl⟩
  obtain ⟨Tb, hTb, hTbE⟩ := exists_fourGroup e hn9 hn12 (modOf 3 L y hyL) hcycQ (imageMod 3 L (B ⊓ L)) hE
  have hTb2 : IsPGroup 2 Tb := isPGroup_of_isElemAbelian hTb.elemAb
  have hDpg : IsPGroup 3 (altDxy x y) := isPGroup_of_isElemAbelian S.isElemAbelian_D
  have hTex : ∃ T : Subgroup G, T ≤ preMod 3 L Tb ∧ IsPGroup 2 T ∧ altDxy x y ≤ Subgroup.normalizer (T : Set G) ∧
      ((n = 10 ∨ n = 11) → B ≤ Subgroup.normalizer (T : Set G)) ∧ imageMod 3 L T = Tb ∧
      ∀ T' : Subgroup G, T' ≤ preMod 3 L Tb → IsPGroup 2 T' → T ≤ T' → T' = T := by
    by_cases hn10 : n = 10 ∨ n = 11
    · have hBN : B ≤ Subgroup.normalizer (preMod 3 L Tb : Set G) :=
        le_normalizer_preMod_of_image hxL S.B_eq (hTbE hn10)
      obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := exists_lift_twoGroup (GLAIsBmax.isPGroup (IsSStarMax.bmax hB)) hTb2 hBN
      exact ⟨T, hT1, hT2, (hDB hn10).trans hT3, fun _ => hT3, hT4, hT5⟩
    · have hDN : altDxy x y ≤ Subgroup.normalizer (preMod 3 L Tb : Set G) :=
        altDxy_le_normalizer_preMod hxL hyL hTb.yb_norm
      obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := exists_lift_twoGroup hDpg hTb2 hDN
      exact ⟨T, hT1, hT2, hT3, fun h => absurd h hn10, hT4, hT5⟩
  obtain ⟨T, hTpre, hT2, hDT, hBT, hTimg, hSyl⟩ := hTex
  have hTL : T ≤ L := hTpre.trans (preMod_le 3 L Tb)
  set X := Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L with hX
  have hXL : X ≤ L := inf_le_right
  have hSyl' : ∀ T' : Subgroup G, T' ≤ preMod 3 L (imageMod 3 L T) → IsPGroup 2 T' → T ≤ T' → T' = T := by
    rw [hTimg]; exact hSyl
  have himgX := imageMod_normCent hxL hyL S.y_order (by
    have := S.isElemAbelian_D.2 x (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    exact this) (by
    exact (isElemAbelian_commute S.isElemAbelian_D (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))) hTL hT2 hDT hSyl'
  rw [hTimg] at himgX
  set I := GLAPLayer 3 X with hI
  have himgI : imageMod 3 L I = altFixSub e (movedLettersOf e Tb) := by
    rw [hI, imageMod_glaPLayer hc.prime hXL, himgX]
    exact fourGroup_layer e hn9 hTb
  have hIX : I ≤ X := sSup_le fun K hK => hK.1
  have hIL : I ≤ L := hIX.trans hXL
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  have hJimg : imageMod 3 L J = altFixSub e ((permOfMod 3 L n e y).support : Set (Fin n)) := by
    unfold altFixSub
    rw [← hfix]
    exact (Subgroup.comap_map_eq_self_of_injective e.injective _).symm
  have hIJim : altFixSub e (movedLettersOf e Tb) ≤ altFixSub e ((permOfMod 3 L n e y).support : Set (Fin n)) := by
    have := fourGroup_le_J e hTb
    rwa [hperm] at this
  refine ⟨T, I, hTL, hT2, ?_, hDT, hBT, ?_, rfl, ?_, ?_, ?_, genByPElts_layer hc.prime X, ?_, ⟨e, hcyc, ?_, hJimg⟩⟩
  · intro hle
    have h0 : imageMod 3 L T = ⊥ := (imageMod_eq_bot_iff hTL).2 hle
    rw [hTimg] at h0
    have h4 := hTb.card_four
    rw [h0, Subgroup.card_bot] at h4
    omega
  · refine coversMod_of_image_sup hTL hJL ?_
    rw [hTimg, hJimg]
    have := fourGroup_gen e hn9 hTb
    rwa [hperm] at this
  · have hIZ : I ≤ L ⊓ Subgroup.centralizer (altDxy x y : Set G) :=
      le_inf hIL (hIX.trans (inf_le_left.trans inf_le_right))
    have := le_layer_of_imageMod_le hc.prime (inf_le_left : L ⊓ Subgroup.centralizer (altDxy x y : Set G) ≤ L)
      hIZ (genByPElts_layer hc.prime X) (by
        rw [S.J_layer, himgI, hJimg]; exact hIJim)
    rwa [S.J_layer] at this
  · obtain ⟨f⟩ := (fourGroup_root e hn9 hTb).1
    exact isAltPType_of_imageMod hIL (by omega) ⟨(MulEquiv.subgroupCongr himgI).trans f⟩
  · have hcen : imageMod 3 L I ≤ Subgroup.centralizer ((imageMod 3 L T : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) := by
      rw [himgI, hTimg]; exact fourGroup_centralizes e
    rw [Subgroup.commutator_comm]
    exact l72_comm_le_core hIL hTL hcen
  · intro hn
    have hyB : y ∈ B := hy (by omega)
    exact B_eq_of_image hxL S.B_eq (IsSStarMax.bmax hB).1 hyB hxB hyL S.y_order (hBT hn) rfl e (by
      rw [← hperm]; exact hcycQ) himgI hIJim
      (fourGroup_E e hn hTb (hE hn).1 (hE hn).2.1 (hE hn).2.2 (hTbE hn))
  · obtain ⟨Ω₄, hΩ₄, hΩ₄4⟩ := exists_finset_movedLetters e hTb.moves_four
    refine ⟨Ω₄, hΩ₄4, fun i hi => ?_, by rw [himgI, hΩ₄]⟩
    have hi' : permOfQ e (modOf 3 L y hyL) i ≠ i := by
      rw [hperm]; exact Equiv.Perm.mem_support.1 hi
    have := hTb.supp_sub i hi'
    rw [← hΩ₄] at this
    exact Finset.mem_coe.1 this

end CFSG.LocalAnalysis.GLTheoremA
