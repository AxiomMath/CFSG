module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofCyclic
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

@[expose] def IsU62Index : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => r = 5 ∧ IsTwoPow q 1
  | _ => False

@[expose] def Bal207RankSyl : Prop :=
  ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), Bal207Index p d.1 → ¬ (p = 5 ∧ IsSuzuki2Index d.1) →
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E ∧ Nat.card E = p ^ 2

@[expose] def Bal207RankCenter : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], p.Prime → CFSG.Open.IsQuasisimple K →
    IsLieQuot K (Bal207Index p) → ¬ (p = 3 ∧ IsLieQuot K IsU62Index) →
      Nat.Coprime p (Nat.card (Subgroup.center K))

@[expose] def Bal207RankU62 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsLieQuot K IsU62Index →
    3 ∣ Nat.card (Subgroup.center K) → ∀ α : MulAut K, α ^ 3 = 1 →
      ∃ y : K, y ^ 3 = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α

@[expose] def Bal207RankAut : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsLieQuot K (Bal207Index p) → ¬ (p = 5 ∧ IsLieQuot K IsSuzuki2Index) →
      ∀ α : MulAut K, α ^ p = 1 →
        ∃ y : K, y ^ p = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α

section GroupTheory

variable {K : Type*} [Group K]

theorem rankAux_mem_center_of_conj_eq_one {y : K} (h : MulAut.conj y = 1) :
    y ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : y * g * y⁻¹ = g := by
    have := congrArg (fun f : MulAut K => f g) h
    simpa only [MulAut.conj_apply, MulAut.one_apply] using this
  calc g * y = y * g * y⁻¹ * y := by rw [h1]
    _ = y * g := by group

variable [Finite K]

theorem rankAux_eq_one_of_mem_center {p : ℕ} (hZ : Nat.Coprime p (Nat.card (Subgroup.center K)))
    {z : K} (hz : z ∈ Subgroup.center K) (hzp : z ^ p = 1) : z = 1 := by
  have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h2 : orderOf z ∣ Nat.card (Subgroup.center K) := Subgroup.orderOf_dvd_natCard _ hz
  have h3 : Nat.Coprime (orderOf z) (Nat.card (Subgroup.center K)) :=
    Nat.Coprime.coprime_dvd_left h1 hZ
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2)

theorem rankAux_mem_zpowers_of_conj {p : ℕ} (hZ : Nat.Coprime p (Nat.card (Subgroup.center K)))
    {y k : K} (hyp : y ^ p = 1) (hkp : k ^ p = 1) (hyk : Commute y k)
    (h : MulAut.conj y ∈ Subgroup.zpowers (MulAut.conj k)) : y ∈ Subgroup.zpowers k := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow] at hi
  have hc : MulAut.conj (y * (k ^ i)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hi, mul_inv_cancel]
  have hcomm : Commute y (k ^ i)⁻¹ := (hyk.zpow_right i).inv_right
  have hki : (k ^ i) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkp, one_zpow]
  have hpow : (y * (k ^ i)⁻¹) ^ p = 1 := by
    rw [hcomm.mul_pow, hyp, one_mul, inv_pow, hki, inv_one]
  have h1 := rankAux_eq_one_of_mem_center hZ (rankAux_mem_center_of_conj_eq_one hc) hpow
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact Subgroup.zpow_mem_zpowers k i

theorem rankAux_zpow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {α : G} (hα : α ^ p = 1) (i : ℤ) :
    (α ^ i) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]

theorem rankAux_conj_ne_one {p : ℕ} (hp : p.Prime)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {y : K} (hy : orderOf y = p) :
    MulAut.conj y ≠ 1 := by
  intro h
  have h1 := rankAux_eq_one_of_mem_center hZ (rankAux_mem_center_of_conj_eq_one h)
    (hy ▸ pow_orderOf_eq_one y)
  rw [h1, orderOf_one] at hy
  exact hp.one_lt.ne hy

theorem rankAux_fix_outer {p : ℕ} (hp : p.Prime)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) (hpK : p ∣ Nat.card K)
    (α : MulAut K) (hα : α ^ p = 1) (hin : α ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ y : K, y ^ p = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α := by
  classical
  haveI := Fact.mk hp
  have hnc : ∀ y : K, orderOf y = p → MulAut.conj y ≠ 1 := fun y hy => rankAux_conj_ne_one hp hZ hy
  have hα1 : α ≠ 1 := fun h => hin ⟨1, by rw [map_one, h]⟩
  have hαo : orderOf α = p := orderOf_eq_prime hα hα1
  let F : Subgroup K :=
    { carrier := {y | α y = y}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := map_one α
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
        rw [ha] }
  have hPG : IsPGroup p (Subgroup.zpowers α) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, ← hi, rankAux_zpow_pow_eq_one hα i]
    rfl
  have hcong := hPG.card_modEq_card_fixedPoints K
  have hfix : ∀ y : K, α y = y ↔ y ∈ MulAction.fixedPoints (Subgroup.zpowers α) K := by
    intro y
    constructor
    · intro h g
      have hst : α ∈ MulAction.stabilizer (MulAut K) y := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact h
      have hle : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut K) y :=
        Subgroup.zpowers_le.mpr hst
      exact hle g.2
    · intro h
      exact h ⟨α, Subgroup.mem_zpowers α⟩
  have hFcard : Nat.card F = Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) K) :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  have hpF : p ∣ Nat.card F := by
    rw [hFcard]
    exact Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpK))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpF
  have hyo : orderOf (y : K) = p := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨(y : K), hyo ▸ pow_orderOf_eq_one _, y.2, ?_⟩
  intro h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  by_cases hi1 : α ^ i = 1
  · exact hnc _ hyo (hi ▸ hi1)
  · apply hin
    have hoi : orderOf (α ^ i) = p := orderOf_eq_prime (rankAux_zpow_pow_eq_one hα i) hi1
    have heq : Subgroup.zpowers (α ^ i) = Subgroup.zpowers α :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers α i))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hoi, hαo])
    have h1 : α ∈ Subgroup.zpowers (α ^ i) := heq ▸ Subgroup.mem_zpowers α
    rw [hi] at h1
    exact (Subgroup.zpowers_le (H := (MulAut.conj : K →* MulAut K).range)).mpr
      (MonoidHom.mem_range.mpr ⟨(y : K), rfl⟩) h1

theorem rankAux_fix {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) (hS : ∀ P : Sylow p K, ¬ IsCyclic P)
    (α : MulAut K) (hα : α ^ p = 1) :
    ∃ y : K, y ^ p = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α := by
  classical
  haveI := Fact.mk hp
  have hnc : ∀ y : K, orderOf y = p → MulAut.conj y ≠ 1 := fun y hy => rankAux_conj_ne_one hp hZ hy
  have hpK : p ∣ Nat.card K := by
    by_contra h
    obtain ⟨P⟩ : Nonempty (Sylow p K) := inferInstance
    apply hS P
    have h1 : Nat.card P = 1 := by
      rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd h, pow_zero]
    exact @isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.mp h1).1
  by_cases hin : α ∈ (MulAut.conj : K →* MulAut K).range
  ·
    obtain ⟨k₀, hk₀⟩ := hin
    have hk₀p : k₀ ^ p ∈ Subgroup.center K := by
      apply rankAux_mem_center_of_conj_eq_one
      rw [map_pow, hk₀, hα]
    obtain ⟨k, hkp, hk⟩ : ∃ k : K, k ^ p = 1 ∧ MulAut.conj k = α := by
      have hm : Nat.Coprime (orderOf (k₀ ^ p)) p :=
        (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hk₀p) hZ).symm
      obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hp.one_lt
      refine ⟨k₀ ^ (orderOf (k₀ ^ p) * s), ?_, ?_⟩
      · rw [← pow_mul, mul_comm (orderOf (k₀ ^ p) * s) p, pow_mul, pow_mul, pow_orderOf_eq_one,
          one_pow]
      · rw [map_pow, hk₀]
        conv_lhs => rw [← Nat.div_add_mod (orderOf (k₀ ^ p) * s) p, hs, pow_add, pow_mul, hα,
          one_pow, one_mul, pow_one]
    subst hk
    by_cases hk1 : k = 1
    ·
      subst hk1
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpK
      refine ⟨y, hy ▸ pow_orderOf_eq_one y, by rw [map_one, MulAut.one_apply], ?_⟩
      rw [map_one, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
      exact hnc y hy
    have hko : orderOf k = p := orderOf_eq_prime hkp hk1
    obtain ⟨P, hP⟩ := (isElemAbelian_zpowers hkp).isPGroup.exists_le_sylow
    have hkP : k ∈ P := hP (Subgroup.mem_zpowers k)
    haveI : Nontrivial P := ⟨⟨⟨k, hkP⟩, 1, fun h => hk1 (congrArg Subtype.val h)⟩⟩
    haveI := P.isPGroup'.center_nontrivial
    obtain ⟨n, hn, hcard⟩ :=
      (IsPGroup.nontrivial_iff_card (P.isPGroup'.to_subgroup (Subgroup.center P))).mp
        inferInstance
    have hpZ : p ∣ Nat.card (Subgroup.center P) := by
      rw [hcard]
      exact dvd_pow_self p hn.ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
    set z' : K := ((z : P) : K) with hz'
    have hz'o : orderOf z' = p := by rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hz'p : z' ^ p = 1 := hz'o ▸ pow_orderOf_eq_one z'
    have hzP : ∀ x ∈ P, Commute x z' := by
      intro x hx
      have h1 := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
      exact congrArg Subtype.val h1
    have hzk : Commute z' k := (hzP k hkP).symm
    by_cases hz : MulAut.conj z' ∈ Subgroup.zpowers (MulAut.conj k)
    ·
      have hzk' : z' ∈ Subgroup.zpowers k := rankAux_mem_zpowers_of_conj hZ hz'p hkp hzk hz
      have hkz : k ∈ Subgroup.zpowers z' := by
        have hle : Subgroup.zpowers z' ≤ Subgroup.zpowers k := Subgroup.zpowers_le.mpr hzk'
        have heq : Subgroup.zpowers z' = Subgroup.zpowers k :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hko, hz'o])
        rw [heq]
        exact Subgroup.mem_zpowers k
      have hPk : ∀ x ∈ P, Commute x k := by
        intro x hx
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkz
        rw [← hj]
        exact (hzP x hx).zpow_right j
      obtain ⟨y, hyP, hyp, hyk⟩ : ∃ y ∈ P, y ^ p = 1 ∧ y ∉ Subgroup.zpowers k := by
        by_contra hcon
        push Not at hcon
        apply hS P
        refine CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.isCyclic_of_card_pow_eq_one_le hp2
          P.isPGroup' ?_
        calc Nat.card {x : P // x ^ p = 1}
            ≤ Nat.card (Subgroup.zpowers k) := by
              refine Nat.card_le_card_of_injective
                (fun x => ⟨((x.1 : P) : K), hcon _ x.1.2 (by
                  have := congrArg Subtype.val x.2
                  simpa using this)⟩) ?_
              intro a b hab
              have h1 := congrArg Subtype.val hab
              exact Subtype.ext (Subtype.ext h1)
          _ = p := by rw [Nat.card_zpowers, hko]
      refine ⟨y, hyp, ?_, fun h => hyk (rankAux_mem_zpowers_of_conj hZ hyp hkp (hPk y hyP) h)⟩
      rw [MulAut.conj_apply, (hPk y hyP).symm.eq, mul_inv_cancel_right]
    · refine ⟨z', hz'p, ?_, hz⟩
      rw [MulAut.conj_apply, hzk.symm.eq, mul_inv_cancel_right]
  · exact rankAux_fix_outer hp hZ hpK α hα hin

end GroupTheory

theorem rankAux_not_isCyclic_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) (P : Sylow p G) :
    ¬ IsCyclic P := by
  haveI := Fact.mk hp
  intro hcyc
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  haveI : IsCyclic Q := isCyclic_of_surjective (P.equiv Q) (P.equiv Q).surjective
  haveI : IsCyclic E := Subgroup.isCyclic_of_le hQ
  have h1 := IsCyclic.exponent_eq_card (α := E)
  have h2 : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  rw [h1, hEc] at h2
  have h3 := Nat.le_of_dvd hp.pos h2
  have h4 := hp.two_le
  nlinarith

theorem rankAux_not_isCyclic_sylow_of_surjective {K G : Type*} [Group K] [Group G] [Finite K]
    {p : ℕ} (hp : p.Prime) {f : K →* G} (hf : Function.Surjective f)
    (hG : ∀ Q : Sylow p G, ¬ IsCyclic Q) (P : Sylow p K) : ¬ IsCyclic P := by
  haveI := Fact.mk hp
  intro hc
  apply hG (P.mapSurjective hf)
  exact isCyclic_of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)

theorem bal207RankAut_of_parts (hSyl : Bal207RankSyl) (hZ : Bal207RankCenter)
    (hU : Bal207RankU62) : Bal207RankAut := by
  intro p hp hp2 K _ _ hq hK hsz α hα
  by_cases hU62 : p = 3 ∧ IsLieQuot K IsU62Index ∧ 3 ∣ Nat.card (Subgroup.center K)
  · obtain ⟨rfl, hu, h3⟩ := hU62
    exact hU K hq hu h3 α hα
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center K)) := by
    by_cases hu : p = 3 ∧ IsLieQuot K IsU62Index
    · obtain ⟨rfl, hu⟩ := hu
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hU62 ⟨rfl, hu, h⟩
    · exact hZ p K hp hq hK hu
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hEc⟩ := hSyl p d hd fun h => hsz ⟨h.1, d, h.2, ⟨e⟩⟩
  have hS : ∀ P : Sylow p K, ¬ IsCyclic P := by
    refine rankAux_not_isCyclic_sylow_of_surjective hp
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) ?_
      (rankAux_not_isCyclic_sylow hp hE hEc)
    exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  exact rankAux_fix hp hp2 hcop hS α hα

theorem rankAux_exists_complement {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} (hBel : IsElemAbelian p B) :
    ∃ A : Subgroup X, A ≤ B ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
      A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B := by
  obtain ⟨A, hAB, -, hdisj, hsup⟩ :=
    CFSG.SignalizerFunctorTheorem.exists_complement_containing hp hBel
      (inf_le_left : B ⊓ Subgroup.centralizer (K : Set X) ≤ B) (bot_le : (⊥ : Subgroup X) ≤ B)
      (inf_bot_eq _)
  refine ⟨A, hAB, ?_, by rw [sup_comm]; exact hsup⟩
  rw [eq_bot_iff]
  intro a ha
  have h1 : a ∈ (B ⊓ Subgroup.centralizer (K : Set X)) ⊓ A := ⟨⟨hAB ha.1, ha.2⟩, ha.1⟩
  rw [hdisj] at h1
  exact h1

theorem rankAux_normalizerMonoidHom_apply {X : Type} [Group X] (K : Subgroup X)
    (g : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K) :
    ((K.normalizerMonoidHom g k : ↥K) : X) = g * k * (g : X)⁻¹ := by
  simp

theorem rankAux_conj_mem_zpowers {X : Type} [Group X] {p : ℕ} {K B : Subgroup X}
    (hSC : IsSCp p ⊤ B) {x : X} (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hsup : Subgroup.zpowers x ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B)
    {y : ↥K} (hyp : y ^ p = 1) (hyα : K.normalizerMonoidHom ⟨x, hxN⟩ y = y) :
    MulAut.conj y ∈ Subgroup.zpowers (K.normalizerMonoidHom ⟨x, hxN⟩) := by
  have hBel : IsElemAbelian p B := hSC.2.1
  set ψ := K.normalizerMonoidHom with hψdef
  have hψ := rankAux_normalizerMonoidHom_apply K
  set α : MulAut ↥K := ψ ⟨x, hxN⟩ with hα
  have hyp' : (y : X) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
  have hyx : x * (y : X) = (y : X) * x := by
    have h1 := congrArg (fun z : ↥K => (z : X)) hyα
    simp only [hα, hψdef, hψ] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hBy : B ≤ Subgroup.centralizer ({(y : X)} : Set X) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hyx
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc.2 (y : X) y.2).symm
  have hyB : (y : X) ∈ B := by
    have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers (y : X)) :=
      IsElemAbelian.sup_of_commute hBel (isElemAbelian_zpowers hyp') fun b hb z hz => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have h1 : Commute b (y : X) := Subgroup.mem_centralizer_singleton_iff.mp (hBy hb)
        exact (h1.zpow_right j).eq
    have h1 := hSC.2.2 _ le_top hE le_sup_left
    rw [← h1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  let T : Subgroup X :=
    ((Subgroup.zpowers α).comap ψ).map (Subgroup.normalizer (K : Set X)).subtype
  have hxT : x ∈ T := ⟨⟨x, hxN⟩, Subgroup.mem_zpowers α, rfl⟩
  have hCT : Subgroup.centralizer (K : Set X) ≤ T := by
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (K : Set X) :=
      Subgroup.centralizer_le_normalizer (K : Set X) hc
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    have h1 : ψ ⟨c, hcN⟩ = 1 := by
      ext k
      rw [hψdef, hψ, MulAut.one_apply]
      show c * (k : X) * c⁻¹ = k
      rw [← Subgroup.mem_centralizer_iff.mp hc (k : X) k.2, mul_inv_cancel_right]
    show ψ ⟨c, hcN⟩ ∈ Subgroup.zpowers α
    rw [h1]
    exact one_mem _
  have hBT : B ≤ T := by
    rw [← hsup]
    exact sup_le (by rw [Subgroup.zpowers_le]; exact hxT) (inf_le_right.trans hCT)
  obtain ⟨g, hg, hgy⟩ := hBT hyB
  have h1 : ψ g = MulAut.conj y := by
    ext k
    rw [hψdef, hψ, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hgy]
    rfl
  rw [← h1]
  exact hg

theorem bal207Rank_of_aut (h : Bal207RankAut) : Bal207Rank := by
  intro X _ _ _ p K B hp hp2 hcomp hSC hBN hK
  classical
  by_cases hex : ∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧
      A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧ A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B
  · exact Or.inl hex
  have hcyc : ∀ A : Subgroup X, A ≤ B → A ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
      A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B → IsCyclic ↥A := by
    intro A hAB hd hs
    by_contra hnc
    exact hex ⟨A, hAB, hnc, hd, hs⟩
  by_cases hsz : p = 5 ∧ IsLieQuot ↥K IsSuzuki2Index
  · exact Or.inr ⟨hsz.1, hsz.2, hcyc⟩
  exfalso
  have hBel : IsElemAbelian p B := hSC.2.1
  obtain ⟨A, hAB, hAC, hAsup⟩ := rankAux_exists_complement (K := K) hp hBel
  haveI := hcyc A hAB hAC hAsup
  obtain ⟨x, hxA⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp inferInstance
  have hxB : x ∈ B := hAB (hxA ▸ Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hBN hxB
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hαp : K.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [h1, map_one]
  obtain ⟨y, hyp, hyα, hyz⟩ := h p hp hp2 ↥K hcomp.2.2 hK hsz _ hαp
  rw [← hxA] at hAsup
  exact hyz (rankAux_conj_mem_zpowers hSC hxN hAsup hyp hyα)

theorem bal207Rank_of_parts (hSyl : Bal207RankSyl) (hZ : Bal207RankCenter)
    (hU : Bal207RankU62) : Bal207Rank :=
  bal207Rank_of_aut (bal207RankAut_of_parts hSyl hZ hU)

end CFSG.HardMathSupport.Dickson.Bal207
