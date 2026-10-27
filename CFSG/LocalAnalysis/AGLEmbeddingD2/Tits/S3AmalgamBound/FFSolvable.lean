module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSideInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.GorensteinWalter CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem no_coprime_prime_order_centralizing {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (Q Cb : Subgroup Y) [Q.Normal] [Cb.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set Y) ≤ Q) {u : Y} (hu : u ∈ Cb)
    (hcent : ∀ z ∈ Cb ⊓ Q, u * z * u⁻¹ = z) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hord : orderOf u = q) : False := by
  set Z := Cb ⊓ Q with hZ
  set R := Subgroup.zpowers u with hR
  have hRCb : R ≤ Cb := (Subgroup.zpowers_le).2 hu
  have hRcard : Nat.card R = q := by rw [hR, Nat.card_zpowers, hord]
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    rw [hRcard, hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq (Fact.out)).2 hqp)
  have hnorm : R ≤ Subgroup.normalizer (Q : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact le_top
  have hQR : ⁅Q, R⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : x * r * x⁻¹ ∈ Cb := ‹Cb.Normal›.conj_mem r (hRCb hr) x
      exact Cb.mul_mem h1 (Cb.inv_mem (hRCb hr))
    · rw [commutatorElement_def]
      have h1 : r * x⁻¹ * r⁻¹ ∈ Q := ‹Q.Normal›.conj_mem x⁻¹ (Q.inv_mem hx) r
      have := Q.mul_mem hx h1
      simpa [mul_assoc] using this
  have hZR : ⁅Z, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hc : Commute u z := by
      have := hcent z hz
      exact (commute_iff_eq _ _).2 (by rw [mul_inv_eq_iff_eq_mul] at this; exact this)
    exact (hc.zpow_left k).eq
  have hdouble : ⁅⁅Q, R⁆, R⁆ = ⊥ := by
    apply le_bot_iff.1
    calc ⁅⁅Q, R⁆, R⁆ ≤ ⁅Z, R⁆ := Subgroup.commutator_mono hQR le_rfl
      _ = ⊥ := hZR
  have h0 := commutator_eq_bot_of_coprime_double_commutator_eq_bot Q R hnorm hcop hdouble
  have hu' : u ∈ Subgroup.centralizer (Q : Set Y) := by
    have : ⁅R, Q⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h0
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at this
    exact this (Subgroup.mem_zpowers u)
  have huQ : u ∈ Q := hQc hu'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨u, huQ⟩
  have h2 : orderOf u = p ^ k := by
    have : orderOf (⟨u, huQ⟩ : Q) = orderOf u := Subgroup.orderOf_mk _ _
    rw [← this]; exact hk
  rw [hord] at h2
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).1 (hq.dvd_of_dvd_pow (show q ∣ p ^ k from h2 ▸ dvd_refl q)))

theorem isSolvable_of_normal_cyclic_inter {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (Q Cb : Subgroup Y) [Q.Normal] [Cb.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set Y) ≤ Q)
    (hZ : IsCyclic ↥(Cb ⊓ Q)) : Group.IsSolvable ↥Cb := by
  classical
  set Z := Cb ⊓ Q with hZdef
  let ρ : ↥Cb →* MulAut ↥Z := (MulAut.conjNormal : Y →* MulAut ↥Z).comp Cb.subtype
  have hρ : ∀ (a : Cb) (z : Z), ((ρ a z : Z) : Y) = a * z * (a : Y)⁻¹ := fun a z => rfl
  obtain ⟨g, hg⟩ := hZ.exists_generator
  have hpow : ∀ (φ : MulAut ↥Z) (k : ℤ), φ (g ^ k) = (φ g) ^ k := fun φ k => map_zpow φ g k
  have key : ∀ φ ψ : MulAut ↥Z, φ (ψ g) = ψ (φ g) := by
    intro φ ψ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg (φ g))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg (ψ g))
    have e1 : φ (ψ g) = g ^ (i * j) := by
      rw [← hj, hpow, ← hi, ← zpow_mul]
    have e2 : ψ (φ g) = g ^ (j * i) := by
      rw [← hi, hpow, ← hj, ← zpow_mul]
    rw [e1, e2, mul_comm]
  have hcomm : ∀ φ ψ : MulAut ↥Z, φ * ψ = ψ * φ := by
    intro φ ψ
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    show φ (ψ (g ^ k)) = ψ (φ (g ^ k))
    rw [hpow ψ k, hpow φ k, map_zpow, map_zpow, key]
  have hsolR : Group.IsSolvable ↥ρ.range := by
    refine Group.isSolvable_of_comm (fun a b => Subtype.ext ?_)
    exact hcomm a b
  have hker : IsPGroup p ↥ρ.ker := by
    rw [IsPGroup.iff_orderOf]
    intro w
    have hw : ρ w.1 = 1 := w.2
    have hcentw : ∀ z ∈ Cb ⊓ Q, ((w.1 : Cb) : Y) * z * ((w.1 : Cb) : Y)⁻¹ = z := by
      intro z hz
      have := congrArg (fun φ : MulAut ↥Z => ((φ ⟨z, hz⟩ : Z) : Y)) hw
      simpa [hρ] using this
    set y : Y := ((w.1 : Cb) : Y) with hy
    have hord : orderOf w = orderOf y := by
      rw [← Subgroup.orderOf_coe w, ← Subgroup.orderOf_coe (w.1 : Cb)]
    have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
    have hpw : orderOf y = p ^ (orderOf y).primeFactorsList.length := by
      refine Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdn => ?_)
      by_contra hdp
      refine no_coprime_prime_order_centralizing Q Cb hQ hQc
        (u := y ^ (orderOf y / d)) (Cb.pow_mem (w.1 : Cb).2 _) ?_ hd hdp
        (orderOf_pow_orderOf_div hn0 hdn)
      intro z hz
      have hc : Commute y z := (commute_iff_eq _ _).2 (by
        have := hcentw z hz
        rw [mul_inv_eq_iff_eq_mul] at this; exact this)
      have := (hc.pow_left (orderOf y / d)).eq
      rw [mul_inv_eq_iff_eq_mul]; exact this
    exact ⟨_, hord.trans hpw⟩
  have hnil : Group.IsNilpotent ↥ρ.ker := hker.isNilpotent
  have hsolK : Group.IsSolvable ↥ρ.ker := inferInstance
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem isPSolvable_of_normal_cyclic_sylow {X C : Type*} [Group X] [Finite X] [Group C] [Finite C]
    {p : ℕ} [Fact p.Prime] (hcon : CFSG.ABGLocalTools.IsPConstrained p X) (ι : C →* X)
    (hι : Function.Injective ι) (hnorm : ι.range.Normal)
    (S₀ : Sylow p C) (hS₀ : IsCyclic ↥(S₀ : Subgroup C)) : CFSG.HallHigman.IsPSolvable p C := by
  have hcyc : ∀ S : Sylow p C, IsCyclic ↥(S : Subgroup C) := fun S => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq C S₀ S
    exact isCyclic_of_surjective _ (Sylow.equivSMul S₀ g).surjective
  obtain ⟨Q, hQn, hQp, hQc⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.hasPrimeConstraint_of_isPConstrained hcon
  set N := primeComplementCore (G := X) p with hN
  have hNn : N.Normal := primeComplementCore_normal p
  set f : C →* X ⧸ N := (QuotientGroup.mk' N).comp ι with hf
  have hfn : f.range.Normal := by
    have : f.range = ι.range.map (QuotientGroup.mk' N) := by
      rw [hf, MonoidHom.range_comp]
    rw [this]
    exact Subgroup.Normal.map hnorm _ (QuotientGroup.mk'_surjective N)
  have hker : p.Coprime (Nat.card f.ker) := by
    have h1 : f.ker.map ι ≤ N := by
      rintro _ ⟨c, hc, rfl⟩
      have := MonoidHom.mem_ker.1 hc
      rw [hf, MonoidHom.comp_apply] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : Nat.card f.ker ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective hι]
      exact Subgroup.card_dvd_of_le h1
    exact (primeComplementCore_coprime p).of_dvd_right h2
  set f' : C →* f.range := f.rangeRestrict with hf'
  have hf's : Function.Surjective f' := f.rangeRestrict_surjective
  have hZ : IsCyclic ↥(f.range ⊓ Q) := by
    have hZpY : IsPGroup p ↥(f.range ⊓ Q) := hQp.to_le inf_le_right
    have hZp : IsPGroup p ↥((f.range ⊓ Q).subgroupOf f.range) :=
      hZpY.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left)).symm
    obtain ⟨P', hP'⟩ := hZp.exists_le_sylow
    obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf's p P'
    have hP'eq : (P' : Subgroup f.range) = (S : Subgroup C).map f' := by
      rw [← hS]; rfl
    have := hcyc S
    have : IsCyclic ↥((S : Subgroup C).map f') :=
      isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective f' S)
    have hle : (f.range ⊓ Q).subgroupOf f.range ≤ (S : Subgroup C).map f' := hP'eq ▸ hP'
    have := Subgroup.isCyclic_of_le hle
    exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe (inf_le_left)).surjective
  have hsol : Group.IsSolvable ↥f.range :=
    isSolvable_of_normal_cyclic_inter Q f.range hQp hQc hZ
  have hq : Group.IsSolvable (C ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange f).injective
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
    f.ker hker hq

theorem ffSolvableInput : FFSolvableInput := by
  intro G _ _ M T hF hT hcon S hS
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hMN : M ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) :=
    (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
  have hCM : ffC M T ≤ M := inf_le_right
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
  refine isPSolvable_of_normal_cyclic_sylow (X := ↥M) hcon (Subgroup.inclusion hCM)
    (Subgroup.inclusion_injective hCM) ?_ S ?_
  · rw [Subgroup.inclusion_range]; exact hCn
  · have := hS
    exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective (S : Subgroup ↥(ffC M T))
      (ffC M T).subtype (ffC M T).subtype_injective).symm.surjective

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
