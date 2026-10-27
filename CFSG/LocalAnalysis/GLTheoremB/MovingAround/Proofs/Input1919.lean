module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims11x
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input1919

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf innerAut)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open scoped commutatorElement

section Lift

theorem card_ker_dvd_hopf {S E : Type} [Group S] [Finite S] [Group.IsPerfect S] [Group E] [Finite E]
    [Group.IsPerfect E] (q : E →* S) (hq : Function.Surjective q) (hC : q.ker ≤ Subgroup.center E) :
    Nat.card q.ker ∣ Nat.card (hopfMultiplier S) := by
  obtain ⟨-, h, -, -, -, -, eK, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier q hq hC
  rw [← Nat.card_congr eK.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

variable {K S : Type} [Group K] [Group S]

@[expose] def fibre (π : K →* S) (τ : MulAut S) : Subgroup (K × K) where
  carrier := {x | τ (π x.1) = π x.2}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

theorem mem_fibre {π : K →* S} {τ : MulAut S} {x : K × K} :
    x ∈ fibre π τ ↔ τ (π x.1) = π x.2 :=
  Iff.rfl

theorem commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b c d : G}
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.1 hc
  have hd' := Subgroup.mem_center_iff.1 hd
  have e1 : c * (a * d * b * a⁻¹) * c⁻¹ = a * d * b * a⁻¹ := by
    rw [← hc' (a * d * b * a⁻¹)]; group
  have e2 : d * (b * a⁻¹ * b⁻¹) * d⁻¹ = b * a⁻¹ * b⁻¹ := by
    rw [← hd' (b * a⁻¹ * b⁻¹)]; group
  calc ⁅a * c, b * d⁆ = c * (a * d * b * a⁻¹) * c⁻¹ * (b⁻¹ * d⁻¹) := by
        rw [commutatorElement_def, hc' a, hd' b]; group
    _ = a * (d * (b * a⁻¹ * b⁻¹) * d⁻¹) := by rw [e1]; group
    _ = ⁅a, b⁆ := by rw [e2, commutatorElement_def]; group

variable [Finite K] [Finite S] [Group.IsPerfect S]

theorem exists_lift (hK : commutator K = ⊤) (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K)
    (hgcd : Nat.gcd (Nat.card (hopfMultiplier S)) (Nat.card (Subgroup.center K) ^ 2) ∣
      Nat.card (Subgroup.center K)) (τ : MulAut S) :
    ∃ α : MulAut K, ∀ k, π (α k) = τ (π k) := by
  classical
  set Z : Subgroup K := Subgroup.center K with hZ
  set P : Subgroup (K × K) := fibre π τ with hP
  set P' : Subgroup (K × K) := ⁅P, P⁆ with hP'
  set C : Subgroup (K × K) := Z.prod Z with hC
  have hCcen : C ≤ Subgroup.center (K × K) := by
    intro x hx
    obtain ⟨hz, hz'⟩ := Subgroup.mem_prod.1 hx
    rw [Subgroup.mem_center_iff] at hz hz' ⊢
    intro g
    exact Prod.ext (hz g.1) (hz' g.2)
  haveI : C.Normal := Subgroup.normal_of_le_center hCcen
  have hP1 : P.map (MonoidHom.fst K K) = ⊤ := by
    refine eq_top_iff.2 fun k _ => ?_
    obtain ⟨k', hk'⟩ := hπ (τ (π k))
    exact ⟨(k, k'), hk'.symm, rfl⟩
  have hP2 : P.map (MonoidHom.snd K K) = ⊤ := by
    refine eq_top_iff.2 fun k' _ => ?_
    obtain ⟨k, hk⟩ := hπ (τ.symm (π k'))
    refine ⟨(k, k'), ?_, rfl⟩
    show τ (π k) = π k'
    rw [hk, MulEquiv.apply_symm_apply]
  have hP'1 : P'.map (MonoidHom.fst K K) = ⊤ := by
    rw [hP', Subgroup.map_commutator, hP1, ← _root_.commutator_def, hK]
  have hP'2 : P'.map (MonoidHom.snd K K) = ⊤ := by
    rw [hP', Subgroup.map_commutator, hP2, ← _root_.commutator_def, hK]
  have hP'P : P' ≤ P := commutator_self_le P
  have hPC : P ≤ P' ⊔ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ : x.1 ∈ P'.map (MonoidHom.fst K K) := hP'1 ▸ Subgroup.mem_top x.1
    have hyx' : y.1 = x.1 := hyx
    have hxy : x * y⁻¹ ∈ C := by
      have hyP := hP'P hy
      refine ⟨?_, ?_⟩
      · show x.1 * y.1⁻¹ ∈ Z
        rw [hyx', mul_inv_cancel]
        exact Z.one_mem
      · show x.2 * y.2⁻¹ ∈ Z
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← mem_fibre.1 hx, ← mem_fibre.1 hyP,
          hyx', mul_inv_cancel]
    have : x = (x * y⁻¹) * y := by group
    rw [this]
    exact (P' ⊔ C).mul_mem (Subgroup.mem_sup_right hxy) (Subgroup.mem_sup_left hy)
  have hperf : ⁅P', P'⁆ = P' := by
    refine le_antisymm (commutator_self_le P') ?_
    calc P' = ⁅P, P⁆ := rfl
      _ ≤ ⁅P' ⊔ C, P' ⊔ C⁆ := Subgroup.commutator_mono hPC hPC
      _ ≤ ⁅P', P'⁆ := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [← SetLike.mem_coe, Subgroup.mul_normal] at ha hb
        obtain ⟨a₀, ha₀, c, hc, rfl⟩ := ha
        obtain ⟨b₀, hb₀, d, hd, rfl⟩ := hb
        rw [commutatorElement_mul_central (hCcen hc) (hCcen hd)]
        exact Subgroup.commutator_mem_commutator ha₀ hb₀
  haveI : Group.IsPerfect ↥P' := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_injective P'.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set q : ↥P' →* S := π.comp ((MonoidHom.snd K K).comp P'.subtype) with hq
  have hqs : Function.Surjective q := by
    intro s
    obtain ⟨k', rfl⟩ := hπ s
    obtain ⟨y, hy, hyk⟩ : k' ∈ P'.map (MonoidHom.snd K K) := hP'2 ▸ Subgroup.mem_top k'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hq, MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg π hyk
  have hqker : ∀ y : ↥P', y ∈ q.ker → (y : K × K) ∈ C := by
    intro y hy
    have h2 : π (y : K × K).2 = 1 := hy
    have h1 := mem_fibre.1 (hP'P y.2)
    rw [h2, MulEquiv.map_eq_one_iff] at h1
    exact ⟨show (y : K × K).1 ∈ Z from hker ▸ h1, show (y : K × K).2 ∈ Z from hker ▸ h2⟩
  have hqC : q.ker ≤ Subgroup.center ↥P' := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hCcen (hqker y hy)) g
  have hdvd1 := card_ker_dvd_hopf q hqs hqC
  have hdvd2 : Nat.card q.ker ∣ Nat.card Z ^ 2 := by
    have hle : (q.ker).map P'.subtype ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      exact hqker y hy
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective P'.subtype_injective, hC,
      Nat.card_congr (Subgroup.prodEquiv Z Z).toEquiv, Nat.card_prod] at h1
    rwa [sq]
  set p₁ : ↥P' →* K := (MonoidHom.fst K K).comp P'.subtype with hp₁
  have hp₁s : Function.Surjective p₁ := by
    intro k
    obtain ⟨y, hy, hyk⟩ : k ∈ P'.map (MonoidHom.fst K K) := hP'1 ▸ Subgroup.mem_top k
    exact ⟨⟨y, hy⟩, hyk⟩
  have hc1 : Nat.card ↥P' = Nat.card K * Nat.card p₁.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p₁.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p₁ hp₁s).toEquiv]
  have hc2 : Nat.card ↥P' = Nat.card S * Nat.card q.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hqs).toEquiv]
  have hc3 : Nat.card K = Nat.card S * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker]
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  have hkq : Nat.card q.ker = Nat.card Z * Nat.card p₁.ker := by
    have h := hc1.symm.trans hc2
    rw [hc3, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left hS0 h).symm
  have hk1 : Nat.card p₁.ker = 1 := by
    have h1 : Nat.card Z * Nat.card p₁.ker ∣ Nat.card Z * 1 := by
      rw [mul_one, ← hkq]
      exact (Nat.dvd_gcd hdvd1 hdvd2).trans hgcd
    exact Nat.eq_one_of_dvd_one (Nat.dvd_of_mul_dvd_mul_left hZ0 h1)
  have hp₁i : Function.Injective p₁ :=
    (MonoidHom.ker_eq_bot_iff p₁).1 (Subgroup.eq_bot_of_card_eq _ hk1)
  set e₁ : ↥P' ≃* K := MulEquiv.ofBijective p₁ ⟨hp₁i, hp₁s⟩ with he₁
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : K →* K,
      α₀ = ((MonoidHom.snd K K).comp P'.subtype).comp e₁.symm.toMonoidHom := ⟨_, rfl⟩
  have hα₀s : Function.Surjective α₀ := by
    intro k'
    obtain ⟨y, hy, hyk⟩ : k' ∈ P'.map (MonoidHom.snd K K) := hP'2 ▸ Subgroup.mem_top k'
    refine ⟨e₁ ⟨y, hy⟩, ?_⟩
    rw [hα₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hyk
  have hbij : Function.Bijective α₀ := ⟨Finite.injective_iff_surjective.2 hα₀s, hα₀s⟩
  refine ⟨MulEquiv.ofBijective α₀ hbij, fun k => ?_⟩
  have hy1 : ((e₁.symm k : ↥P') : K × K).1 = k := e₁.apply_symm_apply k
  have h := mem_fibre.1 (hP'P (e₁.symm k).2)
  rw [hy1] at h
  rw [h]
  show π (α₀ k) = _
  rw [hα₀]
  rfl

theorem autQ_surjective (hK : commutator K = ⊤)
    (hgcd : Nat.gcd (Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)))
      (Nat.card (Subgroup.center K) ^ 2) ∣ Nat.card (Subgroup.center K)) :
    Function.Surjective (Lemma123.autQ K) := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hK
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  intro τ
  obtain ⟨α, hα⟩ := exists_lift hK (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hgcd τ
  refine ⟨α, ?_⟩
  ext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  exact hα k

theorem not_balanced_of_autQ_surjective {p : ℕ} (hK : commutator K = ⊤)
    (hs : Function.Surjective (Lemma123.autQ K))
    (h : ¬ IsLocallyOTwoBalancedWrtP p 1 (K ⧸ Subgroup.center K)) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  intro hbal
  apply h
  set Φ : MulAut K ≃* MulAut (K ⧸ Subgroup.center K) :=
    MulEquiv.ofBijective (Lemma123.autQ K) ⟨Lemma123.autQ_injective hK, hs⟩ with hΦ
  refine Inputs123a.isLocallyOTwoBalancedWrtP_of_map Φ.symm.toMonoidHom Φ.symm.injective ?_ hbal
  rintro _ ⟨k, rfl⟩
  refine ⟨MulAut.conj (k : K ⧸ Subgroup.center K), ⟨_, rfl⟩, ?_⟩
  apply Φ.injective
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  exact (Lemma123.autQ_conj k).symm

end Lift

section Alt

theorem gcd_dvd_of_two_or_six {m z : ℕ} (hm : m = 2 ∨ m = 6) (hz : z ∣ m) :
    Nat.gcd m (z ^ 2) ∣ z := by
  rcases hm with rfl | rfl
  · have : z ≤ 2 := Nat.le_of_dvd (by norm_num) hz
    interval_cases z <;> revert hz <;> decide
  · have : z ≤ 6 := Nat.le_of_dvd (by norm_num) hz
    interval_cases z <;> revert hz <;> decide

theorem mod_cases {p n : ℕ} (hp : p.Prime) (h : n % p = 2 ∨ n % p = 4 ∨ (p = 3 ∧ n % 3 ≠ 0)) :
    n % p = 2 ∨ n % p = 4 % p := by
  rcases h with h | h | ⟨rfl, h⟩
  · exact Or.inl h
  · right
    have : 4 < p := by have := Nat.mod_lt n hp.pos; omega
    rw [Nat.mod_eq_of_lt this]
    exact h
  · omega

variable {K : Type} [Group K] [Finite K]

theorem card_center_dvd_hopf (hK : commutator K = ⊤) :
    Nat.card (Subgroup.center K) ∣ Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hK
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  have h := card_ker_dvd_hopf (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk'] at h

theorem not_balanced_alt_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n)
    (hA : IsAltType n (K ⧸ Subgroup.center K)) (h4 : n % p = 4 % p) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  obtain ⟨θ⟩ := hA
  have hsub : (n - 4) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h4
  have hdm := Nat.div_add_mod (n - 4) p
  rw [hsub, add_zero] at hdm
  obtain ⟨σ, hσA, hσp, hσ1, hfix⟩ :=
    Inputs123a.exists_perm_fix (n := n) (r := 4) (m := (n - 4) / p) hp hp2 (by
      rcases Nat.eq_zero_or_pos ((n - 4) / p) with h0 | h0
      · rw [h0, mul_zero] at hdm; omega
      · exact h0) (by rw [mul_comm] at hdm; omega)
  exact Inputs123a.not_balanced_of_four hp θ hσA hσp hσ1 hfix

theorem center_eq_bot_alt_two {p n : ℕ} (hq : CFSG.Open.IsQuasisimple K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p K = ⊥) (hn5 : 5 ≤ n) (hA : IsAltType n (K ⧸ Subgroup.center K))
    (h2 : n % p = 2) : Subgroup.center K = ⊥ := by
  obtain ⟨θ⟩ := hA
  have hK : commutator K = ⊤ := hq.1
  rcases Nat.lt_or_ge n 8 with h8 | h8
  · refine SchurFacts.center_eq_bot_of_not_sq_dvd hp hK hO ?_
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    have hpn : p ≤ n := by
      by_contra h
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega
    interval_cases n <;> interval_cases p <;> simp_all (config := { decide := true })
  · have hz := card_center_dvd_hopf hK
    rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr θ,
      CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup h8] at hz
    by_contra hne
    have := SchurFacts.prime_dvd_card_of_isPGroup hp
      (SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hO) hne
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (this.trans hz))

noncomputable def equivQuotCenter (hZ : Subgroup.center K = ⊥) : K ≃* K ⧸ Subgroup.center K :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem not_balanced_alt_two_core {p n : ℕ} (hq : CFSG.Open.IsQuasisimple K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p K = ⊥) (hn5 : 5 ≤ n) (hA : IsAltType n (K ⧸ Subgroup.center K))
    (h2 : n % p = 2) : ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  have hZ := center_eq_bot_alt_two hq hp hp2 hO hn5 hA h2
  obtain ⟨θ⟩ := hA
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr ((equivQuotCenter hZ).trans θ)]
  exact Inputs123a.not_balanced_alt_of_mod hp hp2 hn5 (Or.inl h2)

theorem not_balanced_alt_core {p : ℕ} (hq : CFSG.Open.IsQuasisimple K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p K = ⊥)
    (h : ∃ n : ℕ, 5 ≤ n ∧ IsAltType n (K ⧸ Subgroup.center K) ∧
      (n % p = 2 ∨ n % p = 4 ∨ (p = 3 ∧ n % 3 ≠ 0))) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  obtain ⟨n, hn5, hA, hmod⟩ := h
  rcases mod_cases hp hmod with h2 | h4
  · exact not_balanced_alt_two_core hq hp hp2 hO hn5 hA h2
  · exact not_balanced_alt_four hp hp2 hn5 hA h4

end Alt

section Witness

variable {X : Type} [Group X]

theorem innerAut_normal : (innerAut X).Normal :=
  ⟨fun _ ⟨y, hy⟩ g => ⟨g y, by rw [← hy]; exact
    (CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv g y).symm⟩⟩

theorem conj_injective_of_center (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  refine (injective_iff_map_eq_one _).2 fun z hz => ?_
  have := Lemma123.mem_center_of_conj_eq_one hz
  rwa [hZ, Subgroup.mem_bot] at this

variable [Finite X]

theorem not_balanced_of_inv {p : ℕ} (hp : p.Prime) (hZ : Subgroup.center X = ⊥) {x : X}
    (hx : orderOf x = p) {t : MulAut X} (ht2 : t * t = 1) (ht1 : t ≠ 1) (htx : t x = x)
    (hC : ∀ z : X, z * x = x * z → t z = z) : ¬ IsLocallyOTwoBalancedWrtP p 1 X := by
  classical
  have hinj := conj_injective_of_center hZ
  haveI := innerAut_normal (X := X)
  set d : MulAut X := MulAut.conj x with hd
  have hdo : orderOf d = p := by rw [hd, orderOf_injective _ hinj x]; exact hx
  set T : Subgroup (MulAut X) := Subgroup.zpowers t with hT
  set H : Subgroup (MulAut X) := innerAut X ⊔ T with hH
  have hstab : T ≤ MulAction.stabilizer (MulAut X) x :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 htx)
  have htd : t * d = d * t := by
    have hb := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv t x
    rw [htx] at hb
    calc t * d = t * d * t⁻¹ * t := by group
      _ = d * t := by rw [hb]
  refine Inputs123a.not_balanced_of_core hp hdo le_sup_left (le_sup_left (b := T) ⟨x, rfl⟩) ?_
  have hTle : T ≤ H ⊓ Subgroup.centralizer ({d} : Set (MulAut X)) := by
    rw [hT, Subgroup.zpowers_le]
    exact ⟨le_sup_right (a := innerAut X) (Subgroup.mem_zpowers t),
      Subgroup.mem_centralizer_singleton_iff.2 htd⟩
  have hT2 : IsPGroup 2 T := l119_isPGroup_zpowers (by rw [sq]; exact ht2)
  have hnorm : H ⊓ Subgroup.centralizer ({d} : Set (MulAut X)) ≤
      Subgroup.normalizer (T : Set (MulAut X)) := by
    rintro h ⟨hhH, hhC⟩
    have hhd : h * d = d * h := Subgroup.mem_centralizer_singleton_iff.1 hhC
    have hhH' : h ∈ ((innerAut X ⊔ T : Subgroup (MulAut X)) : Set (MulAut X)) := hhH
    rw [Subgroup.normal_mul] at hhH'
    obtain ⟨a, ⟨z, rfl⟩, b, hb, rfl⟩ := hhH'
    have hbx : b x = x := MulAction.mem_stabilizer_iff.1 (hstab hb)
    have hhx : (MulAut.conj z * b) x = x := by
      apply hinj
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, ← hd, hhd]
      group
    rw [MulAut.mul_apply, hbx, MulAut.conj_apply] at hhx
    have hz : z * x = x * z := by
      calc z * x = z * x * z⁻¹ * z := by group
        _ = x * z := by rw [hhx]
    have htz : t z = z := hC z hz
    have hc1 : Commute (MulAut.conj z) t := by
      have hb2 := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv t z
      rw [htz] at hb2
      show MulAut.conj z * t = t * MulAut.conj z
      calc MulAut.conj z * t = t * MulAut.conj z * t⁻¹ * t := by rw [hb2]
        _ = t * MulAut.conj z := by group
    have hc2 : Commute b t := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.refl t).zpow_left j
    have hc : Commute (MulAut.conj z * b) t := hc1.mul_left hc2
    refine Inputs123a.le_normalizer_of_conj (S := Subgroup.zpowers (MulAut.conj z * b))
      (fun g hg q hq => ?_) (Subgroup.mem_zpowers _)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [((hc.zpow_left i).zpow_right j).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers t j
  intro hbot
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTle hnorm hT2
  rw [hbot, le_bot_iff] at hle
  exact ht1 (by
    have : t ∈ T := Subgroup.mem_zpowers t
    rw [hle] at this
    exact this)

end Witness

section L34

open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem not_balanced_projectiveSL_three_four {k : Type} [Field k] (hk : Nat.card k = 4) :
    ¬ IsLocallyOTwoBalancedWrtP 3 1 (projectiveSL 3 k) := by
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hxE : aP u ∈ eZero k := aP_mem_eZero
  have hx1 : aP u ≠ 1 := aP_ne_one hk hu
  have hZ : Subgroup.center (projectiveSL 3 k) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have : MulAut.conj z = 1 := Lemma123.conj_eq_one_of_mem_center hz
    exact Subgroup.mem_bot.2 (conj_injective hk (this.trans (map_one _).symm))
  refine not_balanced_of_inv Nat.prime_three hZ
    (orderOf_eq_prime (pow_three_of_mem_eZero hk hxE) hx1) (betaAut_mul_self hk hσ)
    (betaAut_ne_one hk) (betaAut_fixed hk hσ hxE) fun z hz => ?_
  have hzC : z ∈ Subgroup.centralizer ({aP u} : Set (projectiveSL 3 k)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hz
  rw [centralizer_eq_eZero hk hxE hx1] at hzC
  exact betaAut_fixed hk hσ hzC

theorem not_balanced_L34_core
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 3 K = ⊥)
    (hL : IsLThreeFour (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP 3 1 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : commutator K = ⊤ := hq.1
  obtain ⟨F, hF, hFfin, hF4, ⟨e⟩⟩ := hL
  have hM : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = 48 := by
    rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr e]
    exact CFSG.HardMathSupport.Solomon.Proving.card_hopfMultiplier_statedProj_three_four hF4
  have hz := card_center_dvd_hopf hK
  rw [hM] at hz
  obtain ⟨j, hj⟩ := (SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hO).exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 (by omega)).trans (hj ▸ hz)
    norm_num at this
  have hgcd : Nat.gcd (Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)))
      (Nat.card (Subgroup.center K) ^ 2) ∣ Nat.card (Subgroup.center K) := by
    rw [hM, hj]
    interval_cases j <;> decide
  refine not_balanced_of_autQ_surjective hK (autQ_surjective hK hgcd) ?_
  obtain ⟨k, _, hk, ⟨φ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL ⟨F, hF, hFfin, hF4, ⟨e⟩⟩
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr φ]
  exact not_balanced_projectiveSL_three_four hk

end L34

section L27

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {F : Type} [Field F]

theorem eq_smul_of_proj_eq {A B : SpecialLinearGroup (Fin 2) F} (h : proj 2 F A = proj 2 F B) :
    ∃ c : F, c ^ 2 = 1 ∧ (B : Matrix (Fin 2) (Fin 2) F) = c • (A : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc, hAB⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  refine ⟨c, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one], ?_⟩
  have hAB' : ((A⁻¹ * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      scalar (Fin 2) (c : F) := hAB
  have h1 : (B : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ * B : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    calc (B : Matrix (Fin 2) (Fin 2) F) =
          ((A * (A⁻¹ * B) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
            rw [mul_inv_cancel_left]
      _ = _ := rfl
  rw [h1, hAB', scalar_apply]
  ext i j
  rw [mul_diagonal]
  simp [mul_comm]

theorem diag_conj_fin_two (a b c d : F) :
    !![(1 : F), 0; 0, -1] * !![a, b; c, d] * !![(1 : F), 0; 0, -1] = !![a, -b; -c, d] := by
  simp [Matrix.mul_fin_two]

theorem not_balanced_projectiveSL_two_seven (hF : Nat.card F = 7) :
    ¬ IsLocallyOTwoBalancedWrtP 3 1 (projectiveSL 2 F) := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have h7 : (7 : F) = 0 := by
    haveI := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [Fintype.card_eq_nat_card, hF] at h
    exact_mod_cast h
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h2 : (2 : F) ≠ 0 := fun h => h1 (by linear_combination h7 - 3 * h)
  have h4 : (4 : F) ≠ 0 := fun h => h1 (by linear_combination 2 * h - h7)
  have h6 : (6 : F) ≠ 0 := fun h => h1 (by linear_combination h7 - h)
  have h8 : (8 : F) ≠ 0 := fun h => h1 (by linear_combination h - h7)
  let g₀ : SpecialLinearGroup (Fin 2) F :=
    ⟨!![2, 0; 0, 4], by rw [det_fin_two_of]; linear_combination h7⟩
  have hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) F) = !![2, 0; 0, 4] := rfl
  have hx3 : proj 2 F g₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : g₀ ^ 3 = 1 := by
      apply Subtype.ext
      change (g₀ : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
      rw [hg₀, pow_three, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j
      · simp; linear_combination h7
      · simp
      · simp
      · simp; linear_combination 9 * h7
    rw [this, map_one]
  have hx1 : proj 2 F g₀ ≠ 1 := by
    intro h
    obtain ⟨c, -, hg⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
    have hg' : (g₀ : Matrix (Fin 2) (Fin 2) F) = scalar (Fin 2) (c : F) := hg
    rw [hg₀] at hg'
    have e00 := congrFun (congrFun hg' 0) 0
    have e11 := congrFun (congrFun hg' 1) 1
    simp [scalar_apply] at e00 e11
    exact h2 (by linear_combination e11 - e00)
  let D : GL (Fin 2) F := ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp, by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩
  have hD : (D : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := rfl
  have hDi : ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := rfl
  have hDD : D * D = 1 := Units.ext (by
    rw [Units.val_mul, hD, Matrix.mul_fin_two, Units.val_one, Matrix.one_fin_two]; simp)
  have ht2 : conjAut 2 F D * conjAut 2 F D = 1 := by rw [← map_mul, hDD, map_one]
  have hconj : ∀ g : SpecialLinearGroup (Fin 2) F,
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 F D g :
        SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![(g : Matrix (Fin 2) (Fin 2) F) 0 0, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
          -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    intro g
    rw [coe_slConjugation, hD, hDi, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) F),
      diag_conj_fin_two]
    simp
  have ht_diag : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 →
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → conjAut 2 F D (proj 2 F g) = proj 2 F g := by
    intro g h01 h10
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 F D g :
        SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F)
    rw [hconj, h01, h10, neg_zero, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) F), h01, h10]
    simp
  have htx : conjAut 2 F D (proj 2 F g₀) = proj 2 F g₀ :=
    ht_diag g₀ (by rw [hg₀]; simp) (by rw [hg₀]; simp)
  have ht1 : conjAut 2 F D ≠ 1 := by
    intro h
    let u₀ : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩
    have hu₀ : (u₀ : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
    have hu := congrArg (fun φ : MulAut (projectiveSL 2 F) => φ (proj 2 F u₀)) h
    simp only [MulAut.one_apply] at hu
    rw [conjAut_proj] at hu
    obtain ⟨c, -, hcu⟩ := eq_smul_of_proj_eq hu
    rw [hconj, hu₀] at hcu
    have e00 := congrFun (congrFun hcu 0) 0
    have e01 := congrFun (congrFun hcu 0) 1
    simp at e00 e01
    exact h2 (by linear_combination e00 + e01)
  have hC : ∀ z : projectiveSL 2 F, z * proj 2 F g₀ = proj 2 F g₀ * z →
      conjAut 2 F D z = z := by
    intro z hz
    obtain ⟨g, rfl⟩ := proj_surjective 2 F z
    rw [← map_mul, ← map_mul] at hz
    obtain ⟨c, hc, hcg⟩ := eq_smul_of_proj_eq hz
    have hdet := g.2
    rw [det_fin_two] at hdet
    replace hcg : (g₀ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        c • ((g : Matrix (Fin 2) (Fin 2) F) * (g₀ : Matrix (Fin 2) (Fin 2) F)) := hcg
    rw [hg₀, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) F), Matrix.mul_fin_two,
      Matrix.mul_fin_two] at hcg
    have e00 := congrFun (congrFun hcg 0) 0
    have e01 := congrFun (congrFun hcg 0) 1
    have e10 := congrFun (congrFun hcg 1) 0
    have e11 := congrFun (congrFun hcg 1) 1
    simp at e00 e01 e10 e11
    have hc1 : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases hc1 with rfl | rfl
    · refine ht_diag g ?_ ?_
      · have : (2 : F) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination -e01
        exact (mul_eq_zero.1 this).resolve_left h2
      · have : (2 : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
        exact (mul_eq_zero.1 this).resolve_left h2
    · exfalso
      have hp : (4 : F) * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by linear_combination e00
      have hs : (8 : F) * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by linear_combination e11
      have hq : (6 : F) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination e01
      rw [(mul_eq_zero.1 hp).resolve_left h4, (mul_eq_zero.1 hs).resolve_left h8,
        (mul_eq_zero.1 hq).resolve_left h6] at hdet
      simp at hdet
  exact not_balanced_of_inv Nat.prime_three
    (CFSG.ComponentClassification.OddSelector.center_projectiveSL_two_eq_bot (by rw [hF]; norm_num))
    (orderOf_eq_prime hx3 hx1) ht2 ht1 htx hC

theorem exists_equiv_projectiveSL_two {Y : Type} [Group Y] (h : IsLpType 2 7 Y) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 7 ∧ Nonempty (Y ≃* projectiveSL 2 F) := by
  obtain ⟨F, hF, _, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hcard, ⟨(e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F)⟩⟩

variable {K : Type} [Group K] [Finite K]

theorem not_balanced_L27_core (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 3 K = ⊥)
    (hL : IsLpType 2 7 (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP 3 1 K := by
  have hZ : Subgroup.center K = ⊥ := SchurFacts.center_eq_bot_of_not_sq_dvd Nat.prime_three hq.1 hO
    (by rw [Prop1116Design.card_statedProj_two_seven hL]; norm_num)
  obtain ⟨F, _, hF, ⟨φ⟩⟩ := exists_equiv_projectiveSL_two hL
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr ((equivQuotCenter hZ).trans φ)]
  exact not_balanced_projectiveSL_two_seven hF

theorem not_balanced_L27
    (hq : CFSG.Open.IsQuasisimple K)
    (hL : IsLpType 2 7 (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP 3 1 K := by
  have hK : commutator K = ⊤ := hq.1
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hL
  haveI := Fintype.ofFinite F
  have hM : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = 2 := by
    obtain ⟨-, ⟨g⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      (k := F) (by rw [Fintype.card_eq_nat_card, hF]; norm_num)
      (by rw [Fintype.card_eq_nat_card, hF]; norm_num)
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm)
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr g.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Fintype.card_eq_nat_card, hF]
    norm_num
  refine not_balanced_of_autQ_surjective hK
    (autQ_surjective hK (gcd_dvd_of_two_or_six (Or.inl hM) (card_center_dvd_hopf hK))) ?_
  obtain ⟨F', _, hF', ⟨φ⟩⟩ := exists_equiv_projectiveSL_two ⟨F, hFf, hFfin, hF, ⟨e⟩⟩
  haveI : Finite F' := Nat.finite_of_card_ne_zero (by rw [hF']; norm_num)
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr φ]
  exact not_balanced_projectiveSL_two_seven hF'

end L27

section OmegaGen

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.CatalogInputs Matrix

variable {J : Type} [Fintype J] [DecidableEq J]

theorem isometry_of_mem_isometryCore {Q : (J → ZMod 2) → ZMod 2} {g : GL J (ZMod 2)}
    (hg : g ∈ CFSG.MatrixModel.isometryCore Q) (v : J → ZMod 2) :
    Q ((g : Matrix J J (ZMod 2)) *ᵥ v) = Q v := by
  let S : Subgroup (GL J (ZMod 2)) :=
    { carrier := {g | ∀ v, Q ((g : Matrix J J (ZMod 2)) *ᵥ v) = Q v}
      mul_mem' := fun {a b} ha hb v => by
        simp only [Set.mem_setOf_eq] at *
        rw [Units.val_mul, ← mulVec_mulVec, ha, hb]
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        simp only [Set.mem_setOf_eq] at *
        have := ha (((a⁻¹ : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v)
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at this
        exact this.symm }
  have hle : CFSG.MatrixModel.isometryCore Q ≤ S := (Subgroup.closure_le S).2 fun g hg => hg
  exact hle hg v

theorem gl_ext_mulVec {g g' : GL J (ZMod 2)}
    (h : ∀ v, (g : Matrix J J (ZMod 2)) *ᵥ v = (g' : Matrix J J (ZMod 2)) *ᵥ v) : g = g' :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact h v))

@[expose] noncomputable def swapLin (ja jb : J) : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.swap ja jb)

theorem swapLin_apply (ja jb : J) (v : J → ZMod 2) (j : J) :
    swapLin ja jb v j = v (Equiv.swap ja jb j) := rfl

theorem swapLin_swapLin (ja jb : J) (v : J → ZMod 2) : swapLin ja jb (swapLin ja jb v) = v := by
  ext j
  simp [swapLin_apply, Equiv.swap_apply_self]

theorem swapLin_single_left (ja jb : J) (c : ZMod 2) :
    swapLin ja jb (Pi.single ja c) = Pi.single jb c := by
  ext j
  simp only [swapLin_apply, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

theorem swapLin_single_right (ja jb : J) (c : ZMod 2) :
    swapLin ja jb (Pi.single jb c) = Pi.single ja c := by
  ext j
  simp only [swapLin_apply, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

theorem swapLin_of_vanish {ja jb : J} {y : J → ZMod 2} (ha : y ja = 0) (hb : y jb = 0) :
    swapLin ja jb y = y := by
  ext j
  rw [swapLin_apply]
  by_cases hja : j = ja
  · subst hja; rw [Equiv.swap_apply_left, ha, hb]
  · by_cases hjb : j = jb
    · subst hjb; rw [Equiv.swap_apply_right, ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

@[expose] noncomputable def swapGL (ja jb : J) : GL J (ZMod 2) where
  val := LinearMap.toMatrix' (swapLin ja jb)
  inv := LinearMap.toMatrix' (swapLin ja jb)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => swapLin_swapLin ja jb v
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v => swapLin_swapLin ja jb v

theorem swapGL_mulVec (ja jb : J) (v : J → ZMod 2) :
    ((swapGL ja jb : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v = swapLin ja jb v :=
  LinearMap.toMatrix'_mulVec _ _

theorem swapGL_inv_mulVec (ja jb : J) (v : J → ZMod 2) :
    (((swapGL ja jb)⁻¹ : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v = swapLin ja jb v :=
  LinearMap.toMatrix'_mulVec _ _

theorem swapGL_mul_self (ja jb : J) : swapGL ja jb * swapGL ja jb = 1 :=
  gl_ext_mulVec fun v => by
    rw [Units.val_mul, ← mulVec_mulVec, swapGL_mulVec, swapGL_mulVec, swapLin_swapLin,
      Units.val_one, one_mulVec]

theorem conj_mem_commutator {G : Type*} [Group G] {I : Subgroup G} {g ω : G} (hg : g ∈ I)
    (hω : ω ∈ ⁅I, I⁆) : g * ω * g⁻¹ ∈ ⁅I, I⁆ := by
  rw [← Subgroup.map_subtype_commutator] at hω ⊢
  obtain ⟨ω', hω', rfl⟩ := hω
  haveI : (_root_.commutator ↥I).Normal := inferInstance
  exact ⟨⟨g, hg⟩ * ω' * ⟨g, hg⟩⁻¹, this.conj_mem ω' hω' ⟨g, hg⟩, by simp⟩

@[expose] noncomputable def conjOmega {G : Type*} [Group G] {I : Subgroup G} {g : G} (hg : g ∈ I) :
    MulAut ↥⁅I, I⁆ where
  toFun ω := ⟨g * ω * g⁻¹, conj_mem_commutator hg ω.2⟩
  invFun ω := ⟨g⁻¹ * ω * g, by simpa using conj_mem_commutator (I.inv_mem hg) ω.2⟩
  left_inv ω := Subtype.ext (by simp [mul_assoc])
  right_inv ω := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

variable {I : Type} [Fintype I] [DecidableEq I]
  {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)} {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)}
  {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}

theorem commute_swap_of_commute (h : HypExt E R P) {Q' : (J → ZMod 2) → ZMod 2} {ja jb : J}
    (hab : ja ≠ jb) (hP : ∀ z, P z = Pi.single ja (z ja) + Pi.single jb (z jb))
    (hQP : ∀ z, Q' (P z) = z ja * z jb) {A : GL I (ZMod 2)}
    (hfpf : ∀ v, (A : Matrix I I (ZMod 2)) *ᵥ v = v → v = 0) {z : GL J (ZMod 2)}
    (hz : ∀ v, Q' ((z : Matrix J J (ZMod 2)) *ᵥ v) = Q' v)
    (hzx : z * Units.map (extMat h) A = Units.map (extMat h) A * z) :
    z * swapGL ja jb = swapGL ja jb * z := by
  classical
  set M : Matrix J J (ZMod 2) := (z : Matrix J J (ZMod 2)) with hM
  set X : Matrix J J (ZMod 2) := extMat h (A : Matrix I I (ZMod 2)) with hXdef
  have hX : ∀ v, X *ᵥ v = E ((A : Matrix I I (ZMod 2)) *ᵥ R v) + P v := extMat_mulVec h _
  have hMX : ∀ v, M *ᵥ (X *ᵥ v) = X *ᵥ (M *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec]
    congr 1
    exact congrArg Units.val hzx
  have hfix : ∀ v, X *ᵥ v = v → P v = v := by
    intro v hv
    rw [hX] at hv
    have h1 : E ((A : Matrix I I (ZMod 2)) *ᵥ R v) = E (R v) := by
      have h2 := h.sum v
      exact add_right_cancel (hv.trans h2.symm)
    have h2 : (A : Matrix I I (ZMod 2)) *ᵥ R v = R v := by
      have := congrArg R h1
      rwa [h.RE, h.RE] at this
    have h3 := h.sum v
    rw [hfpf _ h2, map_zero, zero_add] at h3
    exact h3
  have hfixP : ∀ v, X *ᵥ (P v) = P v := by
    intro v
    rw [hX, h.RP, mulVec_zero, map_zero, zero_add, h.PP]
  have hMP : ∀ v, P (M *ᵥ P v) = M *ᵥ P v := fun v => hfix _ (by rw [← hMX, hfixP])
  have hME : ∀ w, P (M *ᵥ E w) = 0 := by
    intro w
    have hinj : Function.Injective
        (Matrix.toLin' (A : Matrix I I (ZMod 2)) -
          (LinearMap.id : (I → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2))) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      apply hfpf
      have : (A : Matrix I I (ZMod 2)) *ᵥ u - u = 0 := by
        simpa [Matrix.toLin'_apply] using hu
      exact sub_eq_zero.1 this
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.1 hinj) w
    have hu' : (A : Matrix I I (ZMod 2)) *ᵥ u - u = w := by
      simpa [Matrix.toLin'_apply] using hu
    have hEw : E w = X *ᵥ E u - E u := by
      rw [hX, h.RE, h.PE, add_zero, ← hu', map_sub]
    rw [hEw, mulVec_sub, hMX, map_sub, hX, map_add, h.PE, zero_add, h.PP, sub_self]
  have hvan : ∀ y : J → ZMod 2, P y = 0 → y ja = 0 ∧ y jb = 0 := by
    intro y hy
    rw [hP] at hy
    have ha := congrFun hy ja
    have hb := congrFun hy jb
    simp [Pi.single_apply, hab, hab.symm] at ha hb
    exact ⟨ha, hb⟩
  set a : J → ZMod 2 := Pi.single ja 1 with ha
  set b : J → ZMod 2 := Pi.single jb 1 with hb
  have hPa : P a = a := by rw [hP]; ext j; simp [a, Pi.single_apply, hab.symm]
  have hPb : P b = b := by rw [hP]; ext j; simp [b, Pi.single_apply, hab]
  have hMa : M *ᵥ a = Pi.single ja ((M *ᵥ a) ja) + Pi.single jb ((M *ᵥ a) jb) := by
    have := hMP a
    rw [hPa] at this
    rw [← hP]
    exact this.symm
  have hMb : M *ᵥ b = Pi.single ja ((M *ᵥ b) ja) + Pi.single jb ((M *ᵥ b) jb) := by
    have := hMP b
    rw [hPb] at this
    rw [← hP]
    exact this.symm
  have hQa : (M *ᵥ a) ja * (M *ᵥ a) jb = 0 := by
    rw [← hQP, ← hPa, hMP, hPa, hz, ← hPa, hQP]
    simp [a, Pi.single_apply, hab.symm]
  have hQb : (M *ᵥ b) ja * (M *ᵥ b) jb = 0 := by
    rw [← hQP, ← hPb, hMP, hPb, hz, ← hPb, hQP]
    simp [b, Pi.single_apply, hab]
  have hMinj : Function.Injective (fun v => M *ᵥ v) := by
    intro v v' hvv'
    have h1 := congrArg (fun y => ((z⁻¹ : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ y) hvv'
    simp only [hM, mulVec_mulVec, Units.inv_mul, one_mulVec] at h1
    exact h1
  have hMa0 : ¬ ((M *ᵥ a) ja = 0 ∧ (M *ᵥ a) jb = 0) := by
    rintro ⟨h1, h2⟩
    have : M *ᵥ a = M *ᵥ 0 := by rw [hMa, h1, h2, mulVec_zero]; simp
    have := congrFun (hMinj this) ja
    simp [a] at this
  have hMb0 : ¬ ((M *ᵥ b) ja = 0 ∧ (M *ᵥ b) jb = 0) := by
    rintro ⟨h1, h2⟩
    have : M *ᵥ b = M *ᵥ 0 := by rw [hMb, h1, h2, mulVec_zero]; simp
    have := congrFun (hMinj this) jb
    simp [b] at this
  have hMab : ¬ ((M *ᵥ a) ja = (M *ᵥ b) ja ∧ (M *ᵥ a) jb = (M *ᵥ b) jb) := by
    rintro ⟨h1, h2⟩
    have : M *ᵥ a = M *ᵥ b := by rw [hMa, hMb, h1, h2]
    have := congrFun (hMinj this) ja
    simp [a, b, Pi.single_apply, hab] at this
  have hcases : ∀ c₁ d₁ c₂ d₂ : ZMod 2, c₁ * d₁ = 0 → c₂ * d₂ = 0 → ¬ (c₁ = 0 ∧ d₁ = 0) →
      ¬ (c₂ = 0 ∧ d₂ = 0) → ¬ (c₁ = c₂ ∧ d₁ = d₂) → c₁ = d₂ ∧ d₁ = c₂ := by decide
  obtain ⟨hc, hd⟩ := hcases _ _ _ _ hQa hQb hMa0 hMb0 hMab
  have hsMa : swapLin ja jb (M *ᵥ a) = M *ᵥ b := by
    rw [hMa, map_add, swapLin_single_left, swapLin_single_right, hMb, hc, hd, add_comm]
  have hsMb : swapLin ja jb (M *ᵥ b) = M *ᵥ a := by
    rw [hMb, map_add, swapLin_single_left, swapLin_single_right, hMa, ← hc, ← hd, add_comm]
  have hsME : ∀ w, swapLin ja jb (M *ᵥ E w) = M *ᵥ E w := fun w =>
    swapLin_of_vanish (hvan _ (hME w)).1 (hvan _ (hME w)).2
  have hEva : ∀ w, E w ja = 0 ∧ E w jb = 0 := fun w => hvan _ (h.PE w)
  have hdecomp : ∀ v : J → ZMod 2, v = E (R v) + v ja • a + v jb • b := by
    intro v
    conv_lhs => rw [← h.sum v]
    rw [hP, add_assoc]
    congr 1
    congr 1 <;> ext j <;> simp [a, b, Pi.single_apply]
  have hsv : ∀ v : J → ZMod 2, swapLin ja jb v = E (R v) + v ja • b + v jb • a := by
    intro v
    conv_lhs => rw [hdecomp v]
    rw [map_add, map_add, map_smul, map_smul, swapLin_of_vanish (hEva _).1 (hEva _).2]
    simp only [a, b, swapLin_single_left, swapLin_single_right]
  refine gl_ext_mulVec fun v => ?_
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, swapGL_mulVec,
    swapGL_mulVec, hsv v]
  conv_rhs => rw [hdecomp v]
  rw [← hM, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, mulVec_smul,
    mulVec_smul, map_add, map_add, map_smul, map_smul, hsME, hsMa, hsMb]

theorem not_balanced_omega_ext (h : HypExt E R P) {Q : (I → ZMod 2) → ZMod 2}
    {Q' : (J → ZMod 2) → ZMod 2} (hQ : ∀ w z, Q' (E w + P z) = Q w + Q' (P z)) {ja jb : J}
    (hab : ja ≠ jb) (hP : ∀ z, P z = Pi.single ja (z ja) + Pi.single jb (z jb))
    (hQP : ∀ z, Q' (P z) = z ja * z jb) {s : GL J (ZMod 2)}
    (hs : s ∈ CFSG.MatrixModel.isometryCore Q')
    (hst : ¬ Commute (swapGL ja jb * s * (swapGL ja jb)⁻¹ * s⁻¹) (swapGL ja jb))
    {p : ℕ} (hp : p.Prime) {A : GL I (ZMod 2)}
    (hA : A ∈ ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆)
    (hAp : orderOf A = p) (hfpf : ∀ v, (A : Matrix I I (ZMod 2)) *ᵥ v = v → v = 0)
    (hZ : Subgroup.center
      ↥⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ = ⊥) :
    ¬ IsLocallyOTwoBalancedWrtP p 1
      ↥⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ := by
  classical
  set Iso := CFSG.MatrixModel.isometryCore Q' with hIso
  set t := swapGL ja jb with ht
  have hvan : ∀ y : J → ZMod 2, P y = 0 → y ja = 0 ∧ y jb = 0 := by
    intro y hy
    rw [hP] at hy
    have ha := congrFun hy ja
    have hb := congrFun hy jb
    simp [Pi.single_apply, hab, hab.symm] at ha hb
    exact ⟨ha, hb⟩
  have hEva : ∀ w, E w ja = 0 ∧ E w jb = 0 := fun w => hvan _ (h.PE w)
  have hPt : ∀ v, P (swapLin ja jb v) = swapLin ja jb (P v) := by
    intro v
    rw [hP, hP, map_add, swapLin_single_left, swapLin_single_right, swapLin_apply, swapLin_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]
  have hRt : ∀ v, R (swapLin ja jb v) = R v := by
    intro v
    have e : swapLin ja jb v = E (R v) + P (swapLin ja jb v) := by
      conv_lhs => rw [← h.sum v]
      rw [map_add, swapLin_of_vanish (hEva _).1 (hEva _).2, hPt]
    rw [e, map_add, h.RE, h.RP, add_zero]
  have htIso : t ∈ Iso := by
    apply Subgroup.subset_closure
    intro v
    rw [ht, swapGL_mulVec]
    have e1 := hQ (R (swapLin ja jb v)) (swapLin ja jb v)
    rw [h.sum] at e1
    have e2 := hQ (R v) v
    rw [h.sum] at e2
    rw [e1, e2, hRt, hQP, hQP, swapLin_apply, swapLin_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, mul_comm]
  set x : GL J (ZMod 2) := Units.map (extMat h) A with hx
  have hxΩ : x ∈ ⁅Iso, Iso⁆ := map_commutator_le h hQ (Subgroup.mem_map_of_mem _ hA)
  have hxmv : ∀ v, (x : Matrix J J (ZMod 2)) *ᵥ v =
      E ((A : Matrix I I (ZMod 2)) *ᵥ R v) + P v := fun v => extMat_mulVec h _ v
  have htx : t * x = x * t := gl_ext_mulVec fun v => by
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ht, swapGL_mulVec,
      swapGL_mulVec, hxmv, hxmv, map_add, swapLin_of_vanish (hEva _).1 (hEva _).2, hRt, hPt]
  have htt : t * t = 1 := swapGL_mul_self ja jb
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set t' : MulAut ↥⁅Iso, Iso⁆ := conjOmega htIso with ht'
  have ht'apply : ∀ ω : ↥⁅Iso, Iso⁆, ((t' ω : ↥⁅Iso, Iso⁆) : GL J (ZMod 2)) = t * ω * t⁻¹ :=
    fun ω => rfl
  have ht'2 : t' * t' = 1 := by
    refine MulEquiv.ext fun ω => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, ht'apply, ht'apply, htinv]
    calc t * (t * (ω : GL J (ZMod 2)) * t) * t = (t * t) * ω * (t * t) := by group
      _ = ω := by rw [htt]; group
  have ht'1 : t' ≠ 1 := by
    intro h1
    have hω : t * s * t⁻¹ * s⁻¹ ∈ ⁅Iso, Iso⁆ := by
      have := Subgroup.commutator_mem_commutator htIso hs
      rwa [commutatorElement_def] at this
    have h2 := congrArg (fun φ : MulAut ↥⁅Iso, Iso⁆ =>
      ((φ ⟨_, hω⟩ : ↥⁅Iso, Iso⁆) : GL J (ZMod 2))) h1
    simp only [MulAut.one_apply, ht'apply] at h2
    apply hst
    show (t * s * t⁻¹ * s⁻¹) * t = t * (t * s * t⁻¹ * s⁻¹)
    calc (t * s * t⁻¹ * s⁻¹) * t = (t * (t * s * t⁻¹ * s⁻¹) * t⁻¹) * t := by rw [h2]
      _ = t * (t * s * t⁻¹ * s⁻¹) := by group
  have ht'x : t' ⟨x, hxΩ⟩ = ⟨x, hxΩ⟩ := Subtype.ext (by
    rw [ht'apply]
    show t * x * t⁻¹ = x
    rw [htx]
    group)
  have hC : ∀ z : ↥⁅Iso, Iso⁆, z * ⟨x, hxΩ⟩ = ⟨x, hxΩ⟩ * z → t' z = z := by
    intro z hz
    apply Subtype.ext
    rw [ht'apply]
    have hzIso : (z : GL J (ZMod 2)) ∈ Iso := commutator_self_le Iso z.2
    have hzx : (z : GL J (ZMod 2)) * x = x * z := congrArg Subtype.val hz
    have hc : (z : GL J (ZMod 2)) * t = t * z :=
      commute_swap_of_commute h hab hP hQP hfpf (isometry_of_mem_isometryCore hzIso) hzx
    rw [← hc]
    group
  have hxo : orderOf (⟨x, hxΩ⟩ : ↥⁅Iso, Iso⁆) = p := by
    rw [Subgroup.orderOf_mk, hx, orderOf_injective _ (units_map_injective h) A, hAp]
  exact not_balanced_of_inv hp hZ hxo ht'2 ht'1 ht'x hC

end OmegaGen

section OmegaInst

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.CatalogInputs Matrix

variable {J : Type} [Fintype J] [DecidableEq J]

@[expose] noncomputable def transvLin (c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (w : J → ZMod 2) :
    (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) :=
  LinearMap.id + c.smulRight w

theorem transvLin_apply (c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (w v : J → ZMod 2) :
    transvLin c w v = v + c v • w := rfl

theorem transvLin_transvLin {c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2} {w : J → ZMod 2} (hcw : c w = 0)
    (v : J → ZMod 2) : transvLin c w (transvLin c w v) = v := by
  rw [transvLin_apply, transvLin_apply, map_add, map_smul, hcw, smul_zero, add_zero, add_assoc,
    ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def transvGL (c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2) (w : J → ZMod 2)
    (hcw : c w = 0) : GL J (ZMod 2) where
  val := LinearMap.toMatrix' (transvLin c w)
  inv := LinearMap.toMatrix' (transvLin c w)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext (transvLin_transvLin hcw)
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext (transvLin_transvLin hcw)

theorem transvGL_mulVec {c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2} {w : J → ZMod 2} (hcw : c w = 0)
    (v : J → ZMod 2) :
    ((transvGL c w hcw : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v = v + c v • w :=
  LinearMap.toMatrix'_mulVec _ _

theorem transvGL_inv_mulVec {c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2} {w : J → ZMod 2} (hcw : c w = 0)
    (v : J → ZMod 2) :
    (((transvGL c w hcw)⁻¹ : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v = v + c v • w :=
  LinearMap.toMatrix'_mulVec _ _

theorem comm_mulVec {ja jb : J} {c : (J → ZMod 2) →ₗ[ZMod 2] ZMod 2} {w : J → ZMod 2}
    (hcw : c w = 0) (v : J → ZMod 2) :
    (((swapGL ja jb * transvGL c w hcw * (swapGL ja jb)⁻¹ * (transvGL c w hcw)⁻¹) * swapGL ja jb :
        GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v =
      swapLin ja jb (transvLin c w (swapLin ja jb (transvLin c w (swapLin ja jb v)))) ∧
    ((swapGL ja jb * (swapGL ja jb * transvGL c w hcw * (swapGL ja jb)⁻¹ *
        (transvGL c w hcw)⁻¹) : GL J (ZMod 2)) : Matrix J J (ZMod 2)) *ᵥ v =
      swapLin ja jb (swapLin ja jb (transvLin c w (swapLin ja jb (transvLin c w v)))) := by
  refine ⟨?_, ?_⟩ <;>
    simp only [Units.val_mul, ← mulVec_mulVec, swapGL_mulVec, swapGL_inv_mulVec, transvGL_mulVec,
      transvGL_inv_mulVec, transvLin_apply]

@[expose] noncomputable def plusC (m : ℕ) :
    (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v (Sum.inr 0) + v (Sum.inl 1) + v (Sum.inr 1)
  map_add' v v' := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[expose] noncomputable def plusW (m : ℕ) : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2 :=
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1

theorem plusC_apply (m : ℕ) (v : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) :
    plusC m v = v (Sum.inr 0) + v (Sum.inl 1) + v (Sum.inr 1) := rfl

theorem plusC_plusW (m : ℕ) : plusC m (plusW m) = 0 := by
  simp [plusC_apply, plusW, Pi.single_apply]
  decide

theorem plus_split (m : ℕ) (v : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) :
    StatedQuadPlus (m + 1 + 1) (ZMod 2) v = v (Sum.inl 0) * v (Sum.inr 0) +
      (v (Sum.inl 1) * v (Sum.inr 1) +
        ∑ i : Fin m, v (Sum.inl i.succ.succ) * v (Sum.inr i.succ.succ)) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_succ]

theorem plusW_succ_succ (m : ℕ) (i : Fin m) :
    plusW m (Sum.inl i.succ.succ) = 0 ∧ plusW m (Sum.inr i.succ.succ) = 0 := by
  have h0 : (i.succ.succ : Fin (m + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
  have h1 : (i.succ.succ : Fin (m + 1 + 1)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
    exact Fin.succ_ne_zero _
  simp [plusW, Pi.single_apply, h0, h1]

theorem plus_transv_isometry (m : ℕ) (v : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) :
    StatedQuadPlus (m + 1 + 1) (ZMod 2) (v + plusC m v • plusW m) =
      StatedQuadPlus (m + 1 + 1) (ZMod 2) v := by
  rw [plus_split, plus_split]
  have htail : ∑ i : Fin m, (v + plusC m v • plusW m) (Sum.inl i.succ.succ) *
        (v + plusC m v • plusW m) (Sum.inr i.succ.succ) =
      ∑ i : Fin m, v (Sum.inl i.succ.succ) * v (Sum.inr i.succ.succ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [(plusW_succ_succ m i).1, (plusW_succ_succ m i).2]
  rw [htail]
  have h10 : (1 : Fin (m + 1 + 1)) ≠ 0 := Fin.one_pos.ne'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, plusW, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, if_true, if_false, h10, h10.symm, plusC_apply]
  have key : ∀ a b d e : ZMod 2, (a + (b + d + e) * (1 + 0 + 0)) * (b + (b + d + e) * (0 + 0 + 0)) +
      (d + (b + d + e) * (0 + 1 + 0)) * (e + (b + d + e) * (0 + 0 + 1)) = a * b + d * e := by
    decide
  rw [← add_assoc, ← add_assoc, key]

theorem plus_witness (m : ℕ) :
    ∃ s ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1 + 1) (ZMod 2)),
      ¬ Commute (swapGL (Sum.inl 0) (Sum.inr 0) * s * (swapGL (Sum.inl 0) (Sum.inr 0))⁻¹ * s⁻¹)
        (swapGL (Sum.inl 0) (Sum.inr 0)) := by
  refine ⟨transvGL (plusC m) (plusW m) (plusC_plusW m), Subgroup.subset_closure fun v => ?_, ?_⟩
  · rw [transvGL_mulVec]
    exact plus_transv_isometry m v
  · intro hc
    have h1 := (comm_mulVec (ja := Sum.inl 0) (jb := Sum.inr 0) (plusC_plusW m)
      (Pi.single (Sum.inl 1) 1)).1
    have h2 := (comm_mulVec (ja := Sum.inl 0) (jb := Sum.inr 0) (plusC_plusW m)
      (Pi.single (Sum.inl 1) 1)).2
    rw [hc.eq] at h1
    have h3 := congrFun (h1.symm.trans h2) (Sum.inl 0)
    have h10 : (1 : Fin (m + 1 + 1)) ≠ 0 := Fin.one_pos.ne'
    simp [swapLin_apply, transvLin_apply, plusC_apply, plusW, Pi.single_apply, Equiv.swap_apply_def,
      h10, h10.symm] at h3
    exact absurd h3 (by decide)

@[expose] noncomputable def minusC (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 1))
  map_add' v v' := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[expose] noncomputable def minusW (m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2 :=
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr (Sum.inr 0)) 1

theorem minusC_apply (m : ℕ) (v : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    minusC m v = v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 1)) := rfl

theorem minusC_minusW (m : ℕ) : minusC m (minusW m) = 0 := by
  simp [minusC_apply, minusW, Pi.single_apply]

theorem minus_split (m : ℕ) (v : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 v = v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) +
      ∑ i : Fin m, v (Sum.inl i.succ) * v (Sum.inr (Sum.inl i.succ)) +
      v (Sum.inr (Sum.inr 0)) ^ 2 + 1 * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      1 * v (Sum.inr (Sum.inr 1)) ^ 2 := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Fin.sum_univ_succ]

theorem minus_transv_isometry (m : ℕ) (v : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (v + minusC m v • minusW m) =
      StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 v := by
  rw [minus_split, minus_split]
  have htail : ∑ i : Fin m, (v + minusC m v • minusW m) (Sum.inl i.succ) *
        (v + minusC m v • minusW m) (Sum.inr (Sum.inl i.succ)) =
      ∑ i : Fin m, v (Sum.inl i.succ) * v (Sum.inr (Sum.inl i.succ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [minusW, Pi.single_apply, Fin.succ_ne_zero]
  rw [htail]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, minusW, Pi.single_apply, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, if_true, if_false, minusC_apply, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff]
  generalize ∑ i : Fin m, v (Sum.inl i.succ) * v (Sum.inr (Sum.inl i.succ)) = T
  have key : ∀ a b u w T : ZMod 2,
      (a + (b + w) * (1 + 0)) * (b + (b + w) * (0 + 0)) + T + (u + (b + w) * (0 + 1)) ^ 2 +
        1 * (u + (b + w) * (0 + 1)) * (w + (b + w) * (0 + 0)) + 1 * (w + (b + w) * (0 + 0)) ^ 2 =
      a * b + T + u ^ 2 + 1 * u * w + 1 * w ^ 2 := by
    decide
  simpa using key _ _ _ _ T

theorem minus_witness (m : ℕ) :
    ∃ s ∈ CFSG.MatrixModel.isometryCore (ι := Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2)
        (StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1),
      ¬ Commute (swapGL (J := Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2) (Sum.inl 0) (Sum.inr (Sum.inl 0)) * s *
          (swapGL (J := Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2) (Sum.inl 0) (Sum.inr (Sum.inl 0)))⁻¹ * s⁻¹)
        (swapGL (J := Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2) (Sum.inl 0) (Sum.inr (Sum.inl 0))) := by
  refine ⟨transvGL (minusC m) (minusW m) (minusC_minusW m), Subgroup.subset_closure fun v => ?_, ?_⟩
  · rw [transvGL_mulVec]
    exact minus_transv_isometry m v
  · intro hc
    have h1 := (comm_mulVec (ja := Sum.inl 0) (jb := Sum.inr (Sum.inl 0)) (minusC_minusW m)
      (Pi.single (Sum.inr (Sum.inr 1)) 1)).1
    have h2 := (comm_mulVec (ja := Sum.inl 0) (jb := Sum.inr (Sum.inl 0)) (minusC_minusW m)
      (Pi.single (Sum.inr (Sum.inr 1)) 1)).2
    rw [hc.eq] at h1
    have h3 := congrFun (h1.symm.trans h2) (Sum.inl 0)
    simp [swapLin_apply, transvLin_apply, minusC_apply, minusW, Pi.single_apply,
      Equiv.swap_apply_def] at h3

@[expose] def extPlusE (n : ℕ) : (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) where
  toFun y := Sum.elim (Fin.cons 0 (fun i : Fin n => y (Sum.inl i)))
    (Fin.cons 0 (fun i : Fin n => y (Sum.inr i)))
  map_add' y z := by
    ext (j | j) <;> induction j using Fin.cases <;> simp
  map_smul' c y := by
    ext (j | j) <;> induction j using Fin.cases <;> simp

@[expose] def extPlusR (n : ℕ) : (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2) where
  toFun z := Sum.elim (fun i : Fin n => z (Sum.inl i.succ)) (fun i : Fin n => z (Sum.inr i.succ))
  map_add' y z := by
    ext (i | i) <;> simp
  map_smul' c y := by
    ext (i | i) <;> simp

@[expose] def extPlusP (n : ℕ) :
    (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) where
  toFun z := Sum.elim (fun j => if j = 0 then z (Sum.inl 0) else 0)
    (fun j => if j = 0 then z (Sum.inr 0) else 0)
  map_add' y z := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [hj]
  map_smul' c y := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [hj]

theorem extPlus_hyp (n : ℕ) : CatalogInputs.HypExt (extPlusE n) (extPlusR n) (extPlusP n) where
  RE w := by
    ext (i | i) <;> simp [extPlusR, extPlusE]
  PE w := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [extPlusP, extPlusE, hj]
  RP z := by
    ext (i | i) <;> simp [extPlusR, extPlusP]
  PP z := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [extPlusP, hj]
  sum z := by
    ext (j | j) <;> induction j using Fin.cases <;> simp [extPlusE, extPlusR, extPlusP]

theorem extPlus_hQ (n : ℕ) (w : Fin n ⊕ Fin n → ZMod 2) (z : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) :
    CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2) (extPlusE n w + extPlusP n z) =
      CFSG.Open.StatedQuadPlus n (ZMod 2) w +
        CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2) (extPlusP n z) := by
  simp [CFSG.Open.StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, extPlusE, extPlusP,
    Fin.sum_univ_succ, Pi.single_apply]
  ring

@[expose] def extMinusE (m : ℕ) :
    (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) where
  toFun y := Sum.elim (Fin.cons 0 (fun i : Fin m => y (Sum.inl i)))
    (Sum.elim (Fin.cons 0 (fun i : Fin m => y (Sum.inr (Sum.inl i))))
      (fun j : Fin 2 => y (Sum.inr (Sum.inr j))))
  map_add' y z := by
    ext (j | j | j)
    · induction j using Fin.cases <;> simp
    · induction j using Fin.cases <;> simp
    · simp
  map_smul' c y := by
    ext (j | j | j)
    · induction j using Fin.cases <;> simp
    · induction j using Fin.cases <;> simp
    · simp

@[expose] def extMinusR (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) where
  toFun z := Sum.elim (fun i : Fin m => z (Sum.inl i.succ))
    (Sum.elim (fun i : Fin m => z (Sum.inr (Sum.inl i.succ))) (fun j : Fin 2 => z (Sum.inr (Sum.inr j))))
  map_add' y z := by
    ext (i | i | i) <;> simp
  map_smul' c y := by
    ext (i | i | i) <;> simp

@[expose] def extMinusP (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2]
      (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) where
  toFun z := Sum.elim (fun j => if j = 0 then z (Sum.inl 0) else 0)
    (Sum.elim (fun j => if j = 0 then z (Sum.inr (Sum.inl 0)) else 0) 0)
  map_add' y z := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [hj]
  map_smul' c y := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [hj]

theorem extMinus_hyp (m : ℕ) : CatalogInputs.HypExt (extMinusE m) (extMinusR m) (extMinusP m) where
  RE w := by
    ext (i | i | i) <;> simp [extMinusR, extMinusE]
  PE w := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [extMinusP, extMinusE, hj]
  RP z := by
    ext (i | i | i) <;> simp [extMinusR, extMinusP]
  PP z := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [extMinusP, hj]
  sum z := by
    ext (j | j | j) <;> induction j using Fin.cases <;> simp [extMinusE, extMinusR, extMinusP]

theorem extMinus_hQ (m : ℕ) (w : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)
    (z : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (extMinusE m w + extMinusP m z) =
      CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1 w +
        CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (extMinusP m z) := by
  simp [CFSG.Open.StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, extMinusE, extMinusP,
    Fin.sum_univ_succ, Pi.single_apply]
  ring

theorem plusP_eq (m : ℕ) (z : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) :
    extPlusP (m + 1) z = Pi.single (Sum.inl 0) (z (Sum.inl 0)) + Pi.single (Sum.inr 0) (z (Sum.inr 0)) := by
  ext (j | j) <;> by_cases hj : j = 0 <;> simp [extPlusP, Pi.single_apply, hj]

theorem plusQP (m : ℕ) (z : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → ZMod 2) :
    StatedQuadPlus (m + 1 + 1) (ZMod 2) (extPlusP (m + 1) z) = z (Sum.inl 0) * z (Sum.inr 0) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, extPlusP, Fin.sum_univ_succ, Fin.succ_ne_zero]

theorem minusP_eq (m : ℕ) (z : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    extMinusP m z = Pi.single (Sum.inl 0) (z (Sum.inl 0)) +
      Pi.single (Sum.inr (Sum.inl 0)) (z (Sum.inr (Sum.inl 0))) := by
  ext (j | j | j)
  · by_cases hj : j = 0 <;> simp [extMinusP, Pi.single_apply, hj]
  · by_cases hj : j = 0 <;> simp [extMinusP, Pi.single_apply, hj]
  · simp [extMinusP, Pi.single_apply]

theorem minusQP (m : ℕ) (z : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (extMinusP m z) = z (Sum.inl 0) * z (Sum.inr (Sum.inl 0)) := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, extMinusP, Fin.sum_univ_succ, Fin.succ_ne_zero]

theorem not_balanced_omega_plus {m p : ℕ} (hp : p.Prime) {A : GL (Fin (m + 1) ⊕ Fin (m + 1)) (ZMod 2)}
    (hA : A ∈ StatedOmega (StatedQuadPlus (m + 1) (ZMod 2))) (hAp : orderOf A = p)
    (hfpf : ∀ v, (A : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) (ZMod 2)) *ᵥ v = v →
      v = 0)
    (hZ : Subgroup.center ↥(StatedOmega (StatedQuadPlus (m + 1 + 1) (ZMod 2))) = ⊥) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 ↥(StatedOmega (StatedQuadPlus (m + 1 + 1) (ZMod 2))) := by
  obtain ⟨s, hs, hst⟩ := plus_witness m
  exact not_balanced_omega_ext (extPlus_hyp (m + 1)) (extPlus_hQ (m + 1)) Sum.inl_ne_inr (plusP_eq m)
    (plusQP m) hs hst hp hA hAp hfpf hZ

theorem not_balanced_omega_minus {m p : ℕ} (hp : p.Prime)
    {A : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hA : A ∈ StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1)) (hAp : orderOf A = p)
    (hfpf : ∀ v, (A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ v = v →
      v = 0)
    (hZ : Subgroup.center ↥(StatedOmega (StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1)) = ⊥) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 ↥(StatedOmega (StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1)) := by
  obtain ⟨s, hs, hst⟩ := minus_witness m
  exact not_balanced_omega_ext (extMinus_hyp m) (extMinus_hQ m) Sum.inl_ne_inr (minusP_eq m)
    (minusQP m) hs hst hp hA hAp hfpf hZ

end OmegaInst

section OmegaK

theorem center_eq_bot_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hZ : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]

variable {K : Type} [Group K] [Finite K]

theorem not_balanced_omega_core (hPi : InputPiCenter) (hq : CFSG.Open.IsQuasisimple K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p K = ⊥)
    (h : ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (K ⧸ Subgroup.center K) ∧
      HasFixedPointFreeOrder ε n p) : ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  obtain ⟨ε, n, hn, hOm, hfp⟩ := h
  by_cases h7 : IsHatSeven K
  · obtain ⟨-, hZ3, ⟨θ⟩⟩ := h7
    have hp3 : p = 3 := by
      have hne : Subgroup.center K ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hZ3
        norm_num at hZ3
      have h3 := SchurFacts.prime_dvd_card_of_isPGroup hp
        (SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hO) hne
      rw [hZ3] at h3
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    exact not_balanced_alt_four Nat.prime_three (by norm_num) (by norm_num) ⟨θ⟩ (by norm_num)
  · have hZ : Subgroup.center K = ⊥ :=
      hPi K p hp hp2 ⟨hq, hO, Or.inr (Or.inl ⟨n, ε, hn, hOm, hfp⟩)⟩ h7
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    cases ε with
    | true =>
      obtain ⟨e⟩ := hOm
      obtain ⟨A, hA, hAp, hfpf⟩ := hfp
      have e' := (equivQuotCenter hZ).trans e
      rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr e']
      exact not_balanced_omega_plus hp hA hAp hfpf (center_eq_bot_of_equiv e' hZ)
    | false =>
      obtain ⟨e⟩ := hOm
      obtain ⟨A, hA, hAp, hfpf⟩ := hfp
      have e' := (equivQuotCenter hZ).trans e
      rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr e']
      exact not_balanced_omega_minus hp hA hAp hfpf (center_eq_bot_of_equiv e' hZ)

end OmegaK

section Assembly

@[expose] def Input19_19Spor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    (IsSporType .Fi22 (K ⧸ Subgroup.center K) → ¬ IsLocallyOTwoBalancedWrtP 5 1 K) ∧
      (IsSporType .He (K ⧸ Subgroup.center K) → ¬ IsLocallyOTwoBalancedWrtP 3 1 K)

end Assembly

section Consumers

open Claims11x in
theorem lemma118Sub_of_inputs' (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hI233 : Claims11x.Input23_3_1)
    (hI234 : Lemma123.Input23_4) : Lemma118T.Lemma118Sub := by
  intro G _ _ m B M E A a K h n Q₁ Q₂ hn hpn hrn hT hr2 hq4
  by_contra hA
  apply h.notM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  obtain ⟨ha, ha1⟩ := h.ha
  have hK : GLAPComponent 3 (Cg a) K := h.hK
  have hnotD := h.notD
  obtain ⟨hAel, -⟩ := l119_sec11_facts hSec
  have hn10 : 10 ≤ n := by
    rw [hr2] at hrn
    norm_num at hrn
    omega
  obtain ⟨hn3, hrk⟩ := rank_bound hn hn10 hT ha1 hq4
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hAc a ha x hx
  have hKa : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hK.1 hk)) a (Set.mem_singleton a)
  have hQ1card : 3 < Nat.card Q₁ := by
    obtain ⟨k₁, hk₁⟩ := exists_card_eq_pow (Lemma118T.isPGroup_of_isElemAbelian hT.Q₁ab)
    have hr₁ : CFSG.Open.pRank 3 Q₁ = k₁ := Lemma118T.pRank_eq_of_isElemAbelian_card hT.Q₁ab hk₁
    have : k₁ = 3 := by rw [← hr₁, hT.Q₁rk, hn3]
    rw [hk₁, this]
    norm_num
  have hCN : Cg a ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_rank hK hT.Q₁K hT.Q₁ab hQ1card hrk
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hACg.trans hCN
  have hAC : Nat.card ↥(A ⊓ centBar 3 ⊤ K) ≤ 3 :=
    hrk _ (inf_centBar_top_le hACg) (isElemAbelian_mono hAel inf_le_left)
  have hAcard : 81 ≤ Nat.card A := by
    rw [l1110_card_eq_pow_pRank hAel]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 A := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcond : 3 ^ (n / 3) * Nat.card ↥(A ⊓ centBar 3 ⊤ K) ≤ Nat.card A := by
    rw [hn3]
    omega
  have hcov := hI233 G 3 Nat.prime_three (by norm_num) (Cg a) K A (E ⊓ A) hK hACg hAN hAel n
    (by omega) hpn hn hcond inf_le_right hr2
  have haE : a ∉ E ⊓ A := fun haEA => hnotD ⟨E, h.pair.1.1, (Subgroup.mem_inf.1 haEA).1⟩
  have hfaith := faithful_A0 ha ha1 haE hAel hKa hAC
  have hA0ne : E ⊓ A ≠ ⊥ := by
    intro hbot
    rw [hbot] at hr2
    have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup G) = 0 := by
      have := Lemma118T.pRank_eq_of_isElemAbelian_card (p := 3) (R := (⊥ : Subgroup G))
        (isElemAbelian_mono hAel bot_le) (k := 0) (by simp)
      exact this
    omega
  have htypes := (hI234 G 3 Nat.prime_three (by norm_num) (Cg a) K (E ⊓ A) hK
    (inf_le_right.trans hACg) (inf_le_right.trans hAN) (isElemAbelian_mono hAel inf_le_right) hA0ne
    hfaith n (by omega) (isAltType_quot_center hn (by omega)) hpn).2
  have hpieces : (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Lemma123.Ke' 3 K e) ≤ M := by
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    have hsub : IsSubnormal (K ⊓ Cg e) (Cg a ⊓ Cg e) := isSubnormal_inf hK.2.1 _
    have hcg2 : Subgroup.centralizer ({e, a} : Set G) = Cg a ⊓ Cg e := l119_cg2_eq a e
    refine sup_le ?_ ?_
    · have hcore : GLAPPrimeCoreOf 3 (K ⊓ Cg e) ≤ GLAPPrimeCoreOf 3 (Cg a ⊓ Cg e) :=
        glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hsub
      have hM2 : GLAPPrimeCoreOf 3 (Cg2 e a) ≤ M := (h112 hSec ha ha1 he he1).resolve_right hnotD
      rw [Cg2, hcg2] at hM2
      exact hcore.trans hM2
    · unfold GLAPLayer
      refine sSup_le fun Q hQ => ?_
      have hQ0 : GLAPComponent 3 (K ⊓ Cg e) Q := hQ
      have hQ' : GLAPComponent 3 (Cg a ⊓ Cg e) Q :=
        l119_glaPComponent_of_isSubnormal (by norm_num) hsub hQ0
      have hJ : GLAPComponent 3 (Cg2 e a) Q := by
        rw [Cg2, hcg2]
        exact hQ'
      obtain ⟨n', hn'5, -, hn'mod, hn'alt⟩ := htypes e he he1 Q hQ0
      have hmod : n' % 3 ≠ 0 := by
        rw [hn'mod]
        intro h0
        exact hpn (Nat.dvd_of_mod_eq_zero h0)
      have hquasi := l119_isQuasisimple_barOf (p := 3) (by norm_num) hQ0
      have h1 : ¬ IsLocallyOTwoBalancedWrtP 3 1 (barOf 3 Q) :=
        not_balanced_alt_core hquasi Nat.prime_three (by norm_num)
          (glaPPrimeCore_quotient_eq_bot Nat.prime_three)
          ⟨n', hn'5, hn'alt, Or.inr (Or.inr ⟨rfl, hmod⟩)⟩
      have h2 : 3 = 3 → IsLTwoTwentySeven (barOf 3 Q) → ¬ IsCompLocallyOTwoBalanced 3 1 A Q :=
        fun _ hL27 _ => Prop1116.InputNotL27Pi_holds (barOf 3 Q) hL27
          (Or.inl ⟨n', hn'5, hn'alt, Or.inr (Or.inr ⟨rfl, hmod⟩)⟩)
      rcases h115 hSec ha ha1 he he1 hJ h1 h2 with hQM | ⟨A1, hA1, haA1⟩
      · exact hQM
      · exact absurd ⟨A1, hA1, haA1⟩ hnotD
  intro k hk
  obtain ⟨y, hy, hyk⟩ := exists_of_barX_le hcov hk (hK.1 hk)
  have := M.mul_mem (hpieces hy) (h111 hSec ha ha1 hyk)
  simpa using this

open Prop1116Design in
theorem prop1116_chev2_of_inputs' (hI33 : InputChevTwoOdd) (hschur : InputSchurFiveSeven)
    (h115 : Prop115Statement) : Prop1116Chev2Statement := by
  intro G _ _ m p B M E A a K q e J0 J1 P hch2
  by_contra hq3
  have hp : p.Prime := P.hp
  have hp2 : p ≠ 2 := P.standing.ne_two
  have hq1 : CFSG.Open.IsQuasisimple (barOf p J0) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hJ0
  have hcases := hI33 _ q P.hq.1 P.hq.2.1 hq3 P.hJ0chev hch2
  have hZ : Subgroup.center (barOf p J0) = ⊥ := by
    rcases hcases with ⟨hA5, _⟩ | ⟨hL7, _⟩
    · exact hschur hp hp2 P.hJ0 (Or.inl hA5)
    · exact hschur hp hp2 P.hJ0 (Or.inr hL7)
  have hcard : (Nat.card (barOf p J0) = 60 ∧ q = 5) ∨ (Nat.card (barOf p J0) = 168 ∧ q = 7) := by
    rcases hcases with ⟨hA5, hq5⟩ | ⟨hL7, hq7⟩
    · refine Or.inl ⟨?_, hq5⟩
      obtain ⟨f⟩ := hA5
      rw [card_eq_card_quot_center hZ, Nat.card_congr f.toEquiv]
      exact card_alt_five
    · refine Or.inr ⟨?_, hq7⟩
      rw [card_eq_card_quot_center hZ]
      exact card_statedProj_two_seven hL7
  have hp3 : p = 3 := by
    have hdvd := P.hJ0p
    rcases hcard with ⟨hc, hq5⟩ | ⟨hc, hq7⟩
    · rw [hc] at hdvd
      rcases prime_dvd_sixty hp hdvd with h | h | h
      · exact absurd h hp2
      · exact h
      · exact absurd (h.trans hq5.symm) P.hq.2.2.symm
    · rw [hc] at hdvd
      have h1 : p ∣ 2 * 2 * 2 * 3 * 7 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
          · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5) hp2
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5) hp2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4) hp2
        · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h2 |>.trans hq7.symm)
          P.hq.2.2.symm
  have hO1 : GLAPPrimeCore p (barOf p J0) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J0) := by
    rcases hcases with ⟨hA5, _⟩ | ⟨hL7, _⟩
    · exact not_balanced_alt_core hq1 hp hp2 hO1 ⟨5, le_rfl, hA5, Or.inl (by rw [hp3])⟩
    · subst hp3
      exact not_balanced_L27_core hq1 hO1 hL7
  have h2 : p = 3 → IsLTwoTwentySeven (barOf p J0) → ¬ IsCompLocallyOTwoBalanced p 1 A J0 := by
    intro _ hL27
    exfalso
    have h9828 := card_psl2_27_of_isL27 hL27
    rcases hcard with ⟨hc, _⟩ | ⟨hc, _⟩ <;> omega
  rcases h115 P.toSec11 P.ha.1 P.ha.2 P.he.1 P.he.2 P.hJ0 h1 h2 with h | ⟨A1, hA1, haA1⟩
  · exact P.hJ0M h
  · exact P.notD ⟨A1, hA1, haA1⟩

end Consumers

theorem not_balanced_pi19 (hPiC : InputPiCenter) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p K = ⊥)
    (h : Prop1116.Pi19Ty p (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP p 1 K := by
  rcases h with hA | hΩ
  · exact not_balanced_alt_core hq hp hp2 hO hA
  · exact not_balanced_omega_core hPiC hq hp hp2 hO hΩ

section Prop1117

variable {G : Type} [Group G] [Finite G]

open Prop1116 in
theorem layer_le' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {B M E A : Subgroup G} {a : G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hPiC : InputPiCenter) (hNot27 : InputNotL27Pi) (h115 : Prop115Statement)
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q)
    {X : Type} [Group X] [Finite X]
    (hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
      X ⧸ Subgroup.center X))
    (hTK : Pi19Ty p (X ⧸ Subgroup.center X)) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, ⟨e⟩⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  obtain ⟨eK⟩ := hQK
  have eP : ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) ≃*
      X ⧸ Subgroup.center X := e.symm.trans eK
  have hTP : Pi19Ty p ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) :=
    pi19Ty_congr p eP.symm hTK
  have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p P) :=
    not_balanced_pi19 hPiC hPq hp hp2 (glaPPrimeCore_quotient_eq_bot hp) hTP
  have h2 : p = 3 → IsLTwoTwentySeven (barOf p P) → ¬ IsCompLocallyOTwoBalanced p 1 A P := by
    intro hp3 hL27 _
    exact (hNot27 (barOf p P) hL27 (hp3 ▸ hTP)).elim
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ h1 h2 with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact CFSG.LocalAnalysis.GLTheoremB.barX_mono p hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD

open Prop1116 in
theorem no_bad' {p m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hKPi : Pi19Ty p (barOf p K ⧸ Subgroup.center (barOf p K)))
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hI18 : Input18_3_diag) (hPiC : InputPiCenter)
    (hNot27 : InputNotL27Pi) (hOmDvd : InputOmegaDvd) (h115 : Prop115Statement) :
    ¬ ∃ z : ↥(Cg a), (z : G) ∈ E ⊓ A ∧ (z : G) ≠ 1 ∧
      ((z : G) ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨z₀, hz₀A, hz₀1, hbad⟩
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hAel.2 x hx
  have hACg : A ≤ Cg a := le_cg_of_mem_elemAbelian hAel ha
  set A0 : Subgroup G := E ⊓ A with hA0
  have hA0A : A0 ≤ A := inf_le_right
  have hA0C : A0 ≤ Cg a := hA0A.trans hACg
  have hA0el : IsElemAbelian p A0 := l119_isElemAbelian_of_le hA0A hAel
  have hrA0' : 2 ≤ CFSG.Open.pRank p A0 := hrA0
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := fam p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbc : IsComponentOf Kb ⊤ := l119_isComponent_barX hK
  have hKbmem : Kb ∈ 𝓛 := fam_base p (Cg a) K A0C
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := fam_comp hK A0C
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYsub : IsSubnormal Yb ⊤ := l119_isSubnormal_sSup_components h𝓛c
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ (hA0A ((Subgroup.mem_subgroupOf).1 hz)) _ (hA0A ((Subgroup.mem_subgroupOf).1 hw))
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    exact fam_bar_normalizes A0C hz
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar :=
    CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hrA0' (l119_pRank_image_ge hp hA0C hA0el)
  have hKbe : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have hKbPi : Pi19Ty p (↥Kb ⧸ Subgroup.center ↥Kb) := pi19Ty_congr p (l119_centerQuot_equiv hKbe) hKPi
  have hKbdvd : p ∣ Nat.card ↥Kb := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Kb)]
    exact dvd_mul_of_dvd_left (pi19Ty_dvd hp hp2 hOmDvd hKbPi) _
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans hKbdvd (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hz₀C : z₀ ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Bbar :=
    Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀ ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A.2
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    simpa using congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hbad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀ hb)
    · left
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀ hz₀C w hw) hC x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hLayer : ∀ b ∈ Bbar, b ≠ 1 → (b ∈ Subgroup.centralizer (Yb : Set _) ∨
      b ∉ Subgroup.normalizer (Kb : Set _)) →
      GLAPLayer p (Yb ⊓ Subgroup.centralizer ({b} : Set _)) ≤ barX p (Cg a) M := by
    intro b hb hb1 hJ
    have hbB := hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    have hz1 : (z : G) ≠ 1 := by
      intro h
      apply hb1
      have hzeq : z = 1 := Subtype.ext h
      rw [hzeq, map_one]
    have hzpow : (z : G) ^ p = 1 := hApow _ hzA.2
    have hzC : (z : G) ∈ Cg a := z.2
    have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
    have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have hzpow' : z ^ p = 1 := by
          apply Subtype.ext
          simpa using hzpow
        rw [hzpow', map_one]
      · exact hb1
    have hdich : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∈ Subgroup.centralizer (Yb : Set _) ∨
        ∀ X ∈ 𝓛, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∉ Subgroup.normalizer (X : Set _) := by
      rcases hJ with hC | hN
      · left
        exact hC
      · right
        rintro X ⟨w, hw, rfl⟩ hmem
        apply hN
        exact (l119_normalizer_gLBConj_iff (hBcomm z hz w hw) Kb).1 hmem
    unfold GLAPLayer
    refine sSup_le fun Q hQ => ?_
    obtain ⟨X₀, hX₀, ⟨e0⟩⟩ := hI18 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Yb 𝓛
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) hbord (hBnorm hbB) rfl hYcomp hcomm𝓛 hdich Q hQ
    obtain ⟨w, hw, rfl⟩ := hX₀
    have eK : ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w) Kb) ≃* ↥Kb :=
      (l119_gLBConj_equiv _ Kb).symm
    have hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
        ↥Kb ⧸ Subgroup.center ↥Kb) := ⟨e0.trans (l119_centerQuot_equiv eK)⟩
    exact layer_le' hp hp2 hSec ha ha1 hnotD hPiC hNot27 h115 hzA hz1 hzC hzp hYsub hQ hQK hKbPi
  have hYM : Yb ≤ barX p (Cg a) M := by
    have hI22' := hI22 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
      hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
      ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀, hb₀B, hb₀1, hJb₀⟩
    rw [hI22']
    refine sSup_le ?_
    rintro Z ⟨b, hb, hb1, hJ, rfl⟩
    exact hLayer b hb hb1 hJ
  have hKM' : barX p (Cg a) K ≤ barX p (Cg a) M := le_trans (le_sSup hKbmem) hYM
  apply hKM
  intro k hk
  obtain ⟨m', hm, hmk⟩ := exists_of_barX_le hKM' hk (hK.1 hk)
  have hmM : m'⁻¹ * k ∈ M := h111 hSec ha ha1 hmk
  have := M.mul_mem hm hmM
  simpa using this

end Prop1117

open AltFacts3 in
theorem prop1117_of_inputs_fixed' (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (hPiC : InputPiCenter) (hI22 : Input22_3_2)
    (hI18 : Input18_3_diag) (hNot27 : Prop1116.InputNotL27Pi) (hOmDvd : Prop1116.InputOmegaDvd)
    (hOm : Prop1116.InputOmegaGen)
    (hSchur : Prop1116.InputSchurAlt) :
    Prop1117Statement := by
  have hAlt := AltFacts3.inputAltGenFixed_holds
  intro G _ _ m p B M E A h a ha ha1
  obtain ⟨hp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    have hb := h.standing.beta
    unfold GLABeta at hb
    exact ⟨hb.1, hb.2.1⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have h111 : Prop111Statement := prop111_of_prop112 h112
  by_cases hA1 : ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
  · obtain ⟨A1, hA1, haA1⟩ := hA1
    exact le_sup_right.trans (hA1.2.clause_a a haA1 ha1)
  · have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := hA1
    have h11 : GLAPPrimeCoreOf p (Cg a) ≤ M := h111 h ha ha1
    unfold piOf piLayer
    refine iSup₂_le fun K hK => ?_
    obtain ⟨hKc, hKpi⟩ := hK
    by_contra hKM
    obtain ⟨hDDp, -⟩ := h.pair
    obtain ⟨-, hDp, hrA0⟩ := hDDp
    obtain ⟨hSCs, -⟩ := hDp
    obtain ⟨hSCp, -⟩ := hSCs
    obtain ⟨-, hAel, -⟩ := hSCp
    have hACg : A ≤ Subgroup.centralizer ({a} : Set G) := Prop1116.le_cg_of_mem_elemAbelian hAel ha
    have hBle : E ⊓ A ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right.trans hACg
    have hBel : IsElemAbelian p (E ⊓ A) := l119_isElemAbelian_of_le inf_le_right hAel
    have hBrk : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hrA0
    have hKpi' : IsPiGroup p (barOf p K) := hKpi
    have hquasi : CFSG.Open.IsQuasisimple (barOf p K) := hKpi'.1
    have hO : GLAPPrimeCore p (barOf p K) = ⊥ := hKpi'.2.1
    have hPi : Prop1116.Pi19Ty p (barOf p K ⧸ Subgroup.center (barOf p K)) :=
      Prop1116.pi19Ty_of_isPiGroup hp hp2 hKpi'
    have hJ0 := no_bad' hp hp2 h ha ha1 hKc hKM hnotD hPi h111 hI22 hI18 hPiC hNot27
      hOmDvd h115
    have hNorm : ∀ e ∈ E ⊓ A, e ≠ 1 → e ∈ Subgroup.normalizer (K : Set G) := by
      intro e he he1
      by_contra hn
      exact hJ0 ⟨⟨e, hBle he⟩, he, he1, Or.inl hn⟩
    have hBnorm : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]; exact (Subgroup.normalizer (K : Set G)).one_mem
      · exact hNorm e he he1
    have hKe : ∀ e ∈ E ⊓ A, e ≠ 1 → Prop1116.Ke p K e ≤ M := by
      intro e he he1
      have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G)) (Cg2 e a) := by
        have h1 : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G))
            (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) :=
          isSubnormal_inf hKc.2.1 (Subgroup.centralizer ({e} : Set G))
        rw [← l119_cg2_eq a e] at h1
        exact h1
      have hO2 : GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({e} : Set G)) ≤ M := by
        refine (glaPPrimeCoreOf_le_of_isSubnormal hp hsub).trans ?_
        rcases h112 h ha ha1 he he1 with hM | ⟨A1, hA1, haA1⟩
        · exact hM
        · exact absurd ⟨A1, hA1, haA1⟩ hnotD
      refine sup_le hO2 (iSup_le fun J => iSup_le fun hJ => ?_)
      obtain ⟨hJc, hJpi⟩ := hJ
      have hJ2 : GLAPComponent p (Cg2 e a) J := l119_glaPComponent_of_isSubnormal hp hsub hJc
      have hJq : CFSG.Open.IsQuasisimple (barOf p J) := hJpi.1
      have hJPi : Prop1116.Pi19Ty p (barOf p J ⧸ Subgroup.center (barOf p J)) :=
        Prop1116.pi19Ty_of_isPiGroup hp hp2 hJpi
      have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J) :=
        not_balanced_pi19 hPiC hJq hp hp2 hJpi.2.1 hJPi
      have h2 : p = 3 → IsLTwoTwentySeven (barOf p J) → ¬ IsCompLocallyOTwoBalanced p 1 A J := by
        intro hp3 hL27 _
        exact (hNot27 (barOf p J) hL27 (hp3 ▸ hJPi)).elim
      rcases h115 h ha ha1 he he1 hJ2 h1 h2 with hJM | ⟨A1, hA1, haA1⟩
      · exact hJM
      · exact absurd ⟨A1, hA1, haA1⟩ hnotD
    have hMsup : (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Prop1116.Ke p K e) ≤ M :=
      iSup_le fun e => iSup_le fun he => iSup_le fun he1 => hKe e he he1
    have hcover : barX p (Cg a) K ≤ barX p (Cg a)
        (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Prop1116.Ke p K e) → False := by
      intro hle
      apply hKM
      intro k hk
      obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (hle.trans (CFSG.LocalAnalysis.GLTheoremB.barX_mono p hMsup)) hk (hKc.1 hk)
      have hm := h11 hjk
      simpa using M.mul_mem hj hm
    rcases hKpi'.2.2 with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hO', hfp⟩ | ⟨hp3, ⟨f⟩⟩
    ·
      have hn2 : (k * p + 2) % p = 2 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hsch : Subgroup.center (barOf p K) = ⊥ :=
        hSchur (barOf p K) p hp hp2 hquasi hO (k * p + 2) hn2 ⟨f⟩
      have hAltTy : IsAltType (k * p + 2) (barOf p K) :=
        ⟨(l119_center_bot_quot hsch).symm.trans f⟩
      have hnd : ¬ p ∣ k * p + 2 := by
        intro hd
        have h2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_left p k)).1 hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      rcases hAlt G p hp hp2 (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk (k * p + 2) hn2 hAltTy with
        hcov | hlt
      · exact hcover hcov
      · exact Prop1116.cex117_false h117
          { toSec11 := h, ha := ⟨ha, ha1⟩, hK := hKc,
            ht := Or.inl ⟨k * p + 2, hAltTy, hlt, hnd⟩, notM := hKM, notD := hnotD }
    ·
      exact hcover (hOm G p hp hp2 (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk ⟨ε, n, hn, hO', hfp⟩)
    ·
      subst hp3
      exact hcover (AltFacts2.inputA7Gen_holds G (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk ⟨f⟩)

open AltFacts3 in
theorem prop1117_of_inputs_noAlt' (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (hPiC : InputPiCenter) (hI22 : Input22_3_2)
    (hI18 : Input18_3_diag) (hNot27 : Prop1116.InputNotL27Pi) (hOmDvd : Prop1116.InputOmegaDvd)
    (hOm : Prop1116.InputOmegaGen) (hSchur : Prop1116.InputSchurAlt) :
    Prop1117Statement :=
  prop1117_of_inputs_fixed' h112 h115 h117 hPiC hI22 hI18 hNot27 hOmDvd
    hOm hSchur

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input1919
