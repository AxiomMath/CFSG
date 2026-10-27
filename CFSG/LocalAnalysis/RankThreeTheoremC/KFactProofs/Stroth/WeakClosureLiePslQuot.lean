module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieNumerics
import CFSG.GroupTheory.WeirSylow.GL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

section Generic

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem mem_normalizer_of_conj_mem (H : Subgroup K) {g : K} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set K) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hinj : Function.Injective (MulAut.conj g : K →* K) := (MulAut.conj g).injective
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective hinj).ge
  rintro _ ⟨h, hh, rfl⟩
  simpa [MulAut.conj_apply] using hg h hh

theorem normalizerMovesLines_range_twisted [Fact p.Prime] {a r : ℕ} (hr : 2 ≤ r)
    (Ψ : (Fin r → Multiplicative (ZMod (p ^ a))) →* K) (hΨ : Function.Injective Ψ)
    (hswap : ∀ i j : Fin r, ∃ g : K, ∀ c, g * Ψ c * g⁻¹ = Ψ (c ∘ Equiv.swap i j))
    (i₀ : Fin r)
    (htwist : ∃ g : K, ∃ μ : ℤ, ¬ (p : ℤ) ∣ μ - 1 ∧
      ∀ c, g * Ψ c * g⁻¹ = Ψ (Function.update c i₀ (c i₀ ^ μ))) :
    NormalizerMovesLines p Ψ.range := by
  have hnorm : ∀ g : K, (∀ c, ∃ d, g * Ψ c * g⁻¹ = Ψ d) →
      g ∈ Subgroup.normalizer (Ψ.range : Set K) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hg c
    rw [hd]
    exact ⟨d, rfl⟩
  refine normalizerMovesLines_of_twistedFrame hr Ψ.range (MonoidHom.ofInjective hΨ) ?_ i₀ ?_
  · intro i j
    obtain ⟨g, hg⟩ := hswap i j
    refine ⟨g, hnorm g fun c => ⟨_, hg c⟩, fun c => ?_⟩
    rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hg]
  · obtain ⟨g, μ, hμ, hg⟩ := htwist
    refine ⟨g, hnorm g fun c => ⟨_, hg c⟩, μ, hμ, fun c => ?_⟩
    rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hg]

theorem normalizerMovesLines_range_sumZero [Fact p.Prime] {a r : ℕ} (hr : 3 ≤ r) (hpr : ¬ p ∣ r)
    (Ψ : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r →* K) (hΨ : Function.Injective Ψ)
    (hswap : ∀ i j : Fin r, ∃ g : K, ∀ c : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r,
      ∃ c' : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r,
        (c' : Fin r → Multiplicative (ZMod (p ^ a))) =
          (c : Fin r → Multiplicative (ZMod (p ^ a))) ∘ Equiv.swap i j ∧
        g * Ψ c * g⁻¹ = Ψ c') :
    NormalizerMovesLines p Ψ.range := by
  refine normalizerMovesLines_of_sumZeroFrame hr hpr Ψ.range (MonoidHom.ofInjective hΨ) ?_
  intro i j
  obtain ⟨g, hg⟩ := hswap i j
  refine ⟨g, mem_normalizer_of_conj_mem _ ?_, fun c => ?_⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨c', -, hc'⟩ := hg c
    rw [hc']
    exact ⟨c', rfl⟩
  · obtain ⟨c', hc'1, hc'2⟩ := hg c
    exact ⟨c', hc'1, by rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hc'2]⟩

theorem wcOn_of_range [Fact p.Prime] {A : Type} [Group A] (Ψ : A →* K)
    (hΨ : Function.Injective Ψ) (hcard : Nat.card A = p ^ (Nat.card K).factorization p)
    (h : IsMulCommutative Ψ.range → 2 ≤ CFSG.Open.pRank p Ψ.range →
      NormalizerMovesLines p Ψ.range) : WCOn p K := by
  have hcard' : Nat.card Ψ.range = p ^ (Nat.card K).factorization p := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv).symm
  let P₀ : Sylow p K := Sylow.ofCard Ψ.range hcard'
  have hP₀ : (P₀ : Subgroup K) = Ψ.range := Sylow.coe_ofCard _ _
  refine WCOn.of_normalizerMovesLines P₀ fun hab hrank => ?_
  rw [hP₀] at hab hrank ⊢
  exact h hab hrank

theorem wcOn_of_range_nml [Fact p.Prime] {A : Type} [Group A] (Ψ : A →* K)
    (hΨ : Function.Injective Ψ) (hcard : Nat.card A = p ^ (Nat.card K).factorization p)
    (h : NormalizerMovesLines p Ψ.range) : WCOn p K :=
  wcOn_of_range Ψ hΨ hcard fun _ _ => h

theorem wcOn_of_range_cyclic [Fact p.Prime] {A : Type} [Group A] [IsCyclic A] (Ψ : A →* K)
    (hΨ : Function.Injective Ψ) (hcard : Nat.card A = p ^ (Nat.card K).factorization p) :
    WCOn p K := by
  refine wcOn_of_range Ψ hΨ hcard fun _ hrank => ?_
  haveI : IsCyclic Ψ.range := isCyclic_of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  have := pRank_le_one_of_isCyclic (p := p) (H := Ψ.range) Fact.out inferInstance
  omega

theorem eq_one_of_mem_of_pow_eq_one [Fact p.Prime] {H : Type} [Group H] (N : Subgroup H)
    (hN : ¬ p ∣ Nat.card N) {x : H} (hx : x ∈ N) {k : ℕ} (hk : x ^ p ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN)
  have h3 : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card N) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

end Generic

section SL

variable {F : Type} [Field F] {n : ℕ} {p : ℕ}

@[expose] def slProj (n : ℕ) (F : Type) [Field F] :
    StatedSL n F →* StatedProj (StatedSL n F) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))

theorem slProj_eq_one_iff (g : StatedSL n F) :
    slProj n F g = 1 ↔ g ∈ (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) :=
  QuotientGroup.eq_one_iff g

section Lift

variable {A : Type} [Group A]

@[expose] noncomputable def liftSL (T : A →* GL (Fin n) F)
    (hdet : ∀ a, ((T a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1) :
    A →* StatedProj (StatedSL n F) :=
  (slProj n F).comp (T.codRestrict (StatedSL n F)
    fun a => CFSG.Open.StatedAPI.mem_statedSL_of_det (hdet a))

theorem liftSL_apply (T : A →* GL (Fin n) F)
    (hdet : ∀ a, ((T a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1) (a : A) :
    liftSL T hdet a =
      slProj n F ⟨T a, CFSG.Open.StatedAPI.mem_statedSL_of_det (hdet a)⟩ := rfl

theorem liftSL_conj {T : A →* GL (Fin n) F}
    {hdet : ∀ a, ((T a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1}
    {g : GL (Fin n) F} (hg : (g : Matrix (Fin n) (Fin n) F).det = 1) {a a' : A}
    (h : g * T a * g⁻¹ = T a') :
    slProj n F ⟨g, CFSG.Open.StatedAPI.mem_statedSL_of_det hg⟩ * liftSL T hdet a *
        (slProj n F ⟨g, CFSG.Open.StatedAPI.mem_statedSL_of_det hg⟩)⁻¹ = liftSL T hdet a' := by
  rw [liftSL_apply, liftSL_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (slProj n F) (Subtype.ext ?_)
  simpa using h

theorem liftSL_injective [Fact p.Prime] {T : A →* GL (Fin n) F}
    {hdet : ∀ a, ((T a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1}
    (hT : Function.Injective T) (hA : ∀ a : A, ∃ k : ℕ, a ^ p ^ k = 1)
    (hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))) :
    Function.Injective (liftSL T hdet) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [liftSL_apply, slProj_eq_one_iff] at ha
  obtain ⟨k, hk⟩ := hA a
  have hpow : (⟨T a, CFSG.Open.StatedAPI.mem_statedSL_of_det (hdet a)⟩ : StatedSL n F) ^ p ^ k =
      1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hk, map_one]
  have h1 := eq_one_of_mem_of_pow_eq_one _ hN ha hpow
  have h2 : T a = 1 := congrArg Subtype.val h1
  exact hT (by rw [h2, map_one])

end Lift

theorem exists_det_one_conj {A : Type} [Group A] {T : A →* GL (Fin n) F}
    (hU : ∀ z : Fˣ, ∃ u : GL (Fin n) F, (∀ a, u * T a * u⁻¹ = T a) ∧
      ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = z)
    (g : GL (Fin n) F) :
    ∃ g' : GL (Fin n) F, ((g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 ∧
      ∀ a, g' * T a * g'⁻¹ = g * T a * g⁻¹ := by
  obtain ⟨u, hu, hudet⟩ := hU (Matrix.GeneralLinearGroup.det g)⁻¹
  refine ⟨g * u, ?_, fun a => ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, hudet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.mul_inv _
  · calc g * u * T a * (g * u)⁻¹ = g * (u * T a * u⁻¹) * g⁻¹ := by group
      _ = g * T a * g⁻¹ := by rw [hu]

theorem det_eq_one_of_pow_eq_one [Fact p.Prime] [Finite F] (hpq : ¬ p ∣ Nat.card F - 1)
    {g : GL (Fin n) F} {k : ℕ} (hg : g ^ p ^ k = 1) :
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h1 : (Matrix.GeneralLinearGroup.det g) ^ p ^ k = 1 := by rw [← map_pow, hg, map_one]
  have h2 : (Matrix.GeneralLinearGroup.det g) ^ (Nat.card F - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (p ^ k) (Nat.card F - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpq)
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [hcop.gcd_eq_one, pow_one] at h3
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h3]
  rfl

theorem not_dvd_card_scalars_of_not_dvd_sub_one [Fact p.Prime] [Finite F]
    (hpq : ¬ p ∣ Nat.card F - 1) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
  CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSL n F) Fact.out hpq
    (fun c _ => by
      rw [← Nat.card_units]
      exact pow_card_eq_one')

theorem not_dvd_card_scalars_of_not_dvd [Fact p.Prime] [Finite F] (hpn : ¬ p ∣ n) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
  CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSL n F) Fact.out hpn
    (fun c hc => by
      have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL hc
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext (by simpa using hdet))

theorem card_projSL_mul [Finite F] [NeZero n] :
    Nat.card (StatedProj (StatedSL n F)) *
        Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) * (Nat.card F - 1) =
      Nat.card (GL (Fin n) F) := by
  have h1 := Matrix.card_SL_mul_card_units (n := Fin n) (R := F)
  rw [Nat.card_units] at h1
  rw [← h1, ← CFSG.Open.StatedAPI.card_statedSL,
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))]

theorem factorization_card_projSL [Fact p.Prime] (hp2 : p ≠ 2) [Finite F] [NeZero n]
    (hpq : ¬ p ∣ Nat.card F)
    (hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))) :
    (Nat.card (StatedProj (StatedSL n F))).factorization p +
        (Nat.card F - 1).factorization p =
      CrossNum.crossA p (Nat.card F) * (n / CrossNum.crossE p (Nat.card F)) +
        padicValNat p ((n / CrossNum.crossE p (Nat.card F)).factorial) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpq' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL := CFSG.GroupTheory.WeirSylow.factorization_card_GL hodd F hpq' n
  rw [← card_projSL_mul (F := F) (n := n),
    Nat.factorization_mul (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') (by omega),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hN] at hGL
  have hcard : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  rw [hcard] at hGL
  unfold CrossNum.crossA CrossNum.crossE
  omega

end SL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
