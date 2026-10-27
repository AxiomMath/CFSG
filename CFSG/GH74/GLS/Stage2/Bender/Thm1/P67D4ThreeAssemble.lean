module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeZ0
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeS
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeTheta
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67InnerTools
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.PartOne.KGD CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem conj_map_congr {Y : Type*} [Group Y] (e : Y ≃* Y) (c : Y) :
    MulAut.conj (e c) = MulAut.congr e (MulAut.conj c) :=
  MulEquiv.ext fun y => by simp [MulAut.conj_apply, MulAut.congr_apply]

section Consumer

theorem d4_false_of_good_plane {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEV : E.map (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = V)
    (hgood : D4PlaneGood σ (p ^ f) E) : False := by
  classical
  obtain ⟨⟨x, hxE, hx1, hdata⟩, hZ0⟩ := hgood
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_bot hcen
  obtain ⟨-, -, -, -, hZab, -, hZcop, hZbot, hcomm⟩ := id h2
  have hEv : ∀ e ∈ E, MulAut.conj e ∈ V := fun e he => by
    rw [← hEV]
    exact Subgroup.mem_map_of_mem _ he
  have hZinn := inner_of_singular_line hp hf K hK σ hσ h2 h3 hx1 (hEv x hxE) hdata
  set Z₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Z.comap (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hZ₀
  have hZ₀mem : ∀ t, t ∈ Z₀ ↔ MulAut.conj t ∈ Z := fun t => Iff.rfl
  have hZc : ∀ t ∈ Z₀, ∀ e ∈ E, t * e = e * t := by
    intro t ht e he
    apply hinj
    rw [map_mul, map_mul]
    exact (hcomm _ (hEv e he) _ ((hZ₀mem t).1 ht)).symm
  have hZab₀ : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ ((hZ₀mem a).1 ha) _ ((hZ₀mem b).1 hb)
  have hZn : ∀ x ∈ E, x ≠ 1 → ∀ s ∈ Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), ∀ t ∈ Z₀,
      s * t * s⁻¹ ∈ Z₀ := by
    intro x hx hx1 s hs t ht
    have hv1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (by rw [h, map_one]))
    have hnorm : MulAut.conj s ∈ Subgroup.normalizer
        (Z : Set (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
      refine h3 _ (hEv x hx) hv1 s ?_
      rw [mem_fixSub, MulAut.conj_apply]
      have hxs : x * s = s * x := (Subgroup.mem_centralizer_singleton_iff.1 hs).symm
      calc x * s * x⁻¹ = s * x * x⁻¹ := by rw [hxs]
        _ = s := by group
    have h := (Subgroup.mem_normalizer_iff.1 hnorm (MulAut.conj t)).1 ((hZ₀mem t).1 ht)
    have e : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (s * t * s⁻¹) =
        MulAut.conj s * MulAut.conj t * (MulAut.conj s)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hZ₀mem, e]
    exact h
  have hcop : ∀ t ∈ Z₀, Nat.Coprime 3 (orderOf t) := by
    intro t ht
    have hdvd : orderOf (MulAut.conj t : MulAut _) ∣ Nat.card Z := by
      have := orderOf_dvd_natCard (⟨MulAut.conj t, (hZ₀mem t).1 ht⟩ : Z)
      rwa [← Subgroup.orderOf_coe] at this
    have heq : orderOf (MulAut.conj t : MulAut _) = orderOf t :=
      orderOf_injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hinj t
    rw [← heq]
    exact Nat.Coprime.coprime_dvd_right hdvd hZcop.symm
  have hZ0' := hZ0 Z₀ hZc hZab₀ hZn hcop
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZbot (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  obtain ⟨t, rfl⟩ := hZinn z hzZ
  exact hz1 (by rw [hZ0' t ((hZ₀mem t).2 hzZ), map_one])

theorem d4_false_of_good_conj {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEV : E.map (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = V)
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hgood : D4PlaneGood σ (p ^ f) (E.map (β⁻¹).toMonoidHom)) : False := by
  classical
  let e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (β⁻¹ :
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  have h2' := h2.map_mulEquiv (MulAut.congr e)
  have h3' := N3Full.map_mulEquiv e h3
  have hconj : ∀ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj (e c) = MulAut.congr e (MulAut.conj c) := fun c => conj_map_congr e c
  refine d4_false_of_good_plane hp hf K hK σ hσ h2' h3' (E.map (β⁻¹).toMonoidHom) ?_ hgood
  rw [← hEV, Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun c => hconj c

end Consumer

section Toral

theorem d4_good_of_frames {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hq2 : 2 < ℓ ^ f) (hℓ3 : ℓ ≠ 3) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (F : D4PhiFrame K σ (ℓ ^ f) ε) (hF : F.Contains E)
    (F' : D4SteinbergFrame K σ (ℓ ^ f) ε) (hF' : F'.Contains E) : D4PlaneGood σ (ℓ ^ f) E := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hq1 : (1 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_pow _ _ hℓ.pos
  have hd0 : 0 ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  obtain ⟨c', hc'⟩ := hF'
  refine ⟨exists_singularData_of_threeSix_plane hℓ hf K hK σ hσ hq2 hℓ3 hε hd
    (AlgebraicClosure K) F'.Fr F'.hFr F'.hgG F'.hFg E hEcard c' hc', ?_⟩
  intro Z₀ hZc hZab hZn _
  obtain ⟨c, hc⟩ := hF
  have hFrE : F.Fr = iterateFrobenius (AlgebraicClosure K) ℓ f :=
    RingHom.ext fun x => by rw [F.hFr, iterateFrobenius_def]
  have hg0 := F.hg0
  rw [hFrE] at hg0 hc
  have hperf := F.hperf
  rw [hFrE] at hperf
  exact d4_three_Z0_trivial hf K hK σ hσ hε hq2 hℓ3 F.hn F.w F.hnw F.hw F.hg0C hg0 hperf E hE
    hEcard c hc Z₀ hZc hZab hZn

theorem d4_false_of_aniso (hleaf : D4PlaneToral) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hEV : E.map (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = V)
    (hanis : ∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R →
      R ≠ ⊥ → ¬ E ≤ Subgroup.normalizer
        (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) : False := by
  classical
  have hq5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    omega
  have hq2 : 2 < p ^ f := lt_of_lt_of_le (by omega) (le_trans hq5 (Nat.le_self_pow (by omega) p))
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = p ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hE' : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElementaryAbelian 3 (E.map (β⁻¹).toMonoidHom) := fun β =>
    IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcardE' : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card (E.map (β⁻¹).toMonoidHom) = 3 ^ 2 := fun β => by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hmod : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by
    have h3p : ¬ 3 ∣ p ^ f := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm
    omega
  rcases hmod with hq1 | hq1
  · obtain ⟨β, ⟨F, hF⟩, ⟨F', hF'⟩⟩ := d4_toral_q1 hp2 hf hq1 K hK σ hσ E hE hEcard hanis
    exact d4_false_of_good_conj hp hf K hK σ hσ h2 h3 E hEV β
      (d4_good_of_frames hp hf K hK σ hσ hq2 hp3 (Or.inl rfl) _ (hE' β) (hcardE' β) F hF F' hF')
  · obtain ⟨β, ⟨⟨F, hF⟩, ⟨F', hF'⟩⟩ | hgood⟩ :=
      hleaf p f hp hp2 hp3 hf K hK σ hσ hq1 E hE hEcard hanis
    · exact d4_false_of_good_conj hp hf K hK σ hσ h2 h3 E hEV β
        (d4_good_of_frames hp hf K hK σ hσ hq2 hp3 (Or.inr rfl) _ (hE' β) (hcardE' β) F hF F'
          hF')
    · exact d4_false_of_good_conj hp hf K hK σ hσ h2 h3 E hEV β hgood

end Toral

end CFSG.GH74.GLS.Stage2.Bender.Thm1
