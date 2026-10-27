module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointStructure
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  Subgroup

section Lambda

variable {G : Type*} [Group G]

theorem commute_of_coprime_aux {p : ℕ} (hp : p.Prime) {g d : G} {k : ℕ} (hk : 1 ≤ k)
    (hg : orderOf g = p ^ k) (hd : d * g * d⁻¹ ∈ zpowers g) (hdp : p.Coprime (orderOf d))
    (hdw : d * g ^ (p ^ (k - 1)) = g ^ (p ^ (k - 1)) * d) : d * g = g * d := by
  obtain ⟨a, ha⟩ := mem_zpowers_iff.mp hd
  have hconj : ∀ j : ℕ, d ^ j * g * (d ^ j)⁻¹ = g ^ (a ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : d ^ (j + 1) * g * (d ^ (j + 1))⁻¹ = d * (d ^ j * g * (d ^ j)⁻¹) * d⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [h1, ih, ← conj_zpow, ← ha, ← zpow_mul, pow_succ', mul_comm]
  have hint : ∀ n : ℤ, g ^ n = 1 ↔ ((p : ℤ) ^ k ∣ n) := by
    intro n
    rw [← orderOf_dvd_iff_zpow_eq_one, hg]
    push_cast
    rfl
  have h1 : (p : ℤ) ^ k ∣ a ^ orderOf d - 1 := by
    rw [← hint, zpow_sub, zpow_one, ← hconj, pow_orderOf_eq_one]
    simp
  have h2 : (p : ℤ) ∣ a - 1 := by
    have hw : d * g ^ (p ^ (k - 1)) * d⁻¹ = g ^ (p ^ (k - 1)) := by
      rw [hdw]; group
    have h3 : g ^ (a * ((p ^ (k - 1) : ℕ) : ℤ)) = g ^ ((p ^ (k - 1) : ℕ) : ℤ) := by
      rw [zpow_mul, ha, zpow_natCast, zpow_natCast, conj_pow, hw]
    have h4 : g ^ ((a - 1) * ((p ^ (k - 1) : ℕ) : ℤ)) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, h3, mul_inv_cancel]
    rw [hint] at h4
    have h5 : (p : ℤ) ^ k = (p : ℤ) ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [h5] at h4
    have h6 : (p : ℤ) ^ (k - 1) * p ∣ (p : ℤ) ^ (k - 1) * (a - 1) := by
      rw [mul_comm ((p : ℤ) ^ (k - 1)) (a - 1)]
      push_cast at h4
      exact h4
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).mp h6
  have h7 : (p : ℤ) ^ k ∣ a - 1 := by
    set S : ℤ := ∑ i ∈ Finset.range (orderOf d), a ^ i with hS
    have hSm : S * (a - 1) = a ^ orderOf d - 1 := geom_sum_mul a (orderOf d)
    have hpS : ¬ (p : ℤ) ∣ S := by
      intro hpS
      have h8 : (p : ℤ) ∣ S - (orderOf d : ℤ) := by
        have : S - (orderOf d : ℤ) = ∑ i ∈ Finset.range (orderOf d), (a ^ i - 1) := by
          rw [Finset.sum_sub_distrib, hS]; simp
        rw [this]
        exact Finset.dvd_sum fun i _ => h2.trans (by simpa using sub_dvd_pow_sub_pow a 1 i)
      have h9 : (p : ℤ) ∣ (orderOf d : ℤ) := by
        have := dvd_sub hpS h8
        simpa using this
      have h10 : p ∣ orderOf d := by exact_mod_cast h9
      have := Nat.Coprime.eq_one_of_dvd hdp h10
      have hp1 := hp.one_lt
      omega
    have hcop : IsCoprime ((p : ℤ) ^ k) S :=
      IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd
        (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hpS)
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [mul_comm, hSm]
    exact h1
  have h8 : g ^ (a - 1) = 1 := (hint _).mpr h7
  have h9 : d * g * d⁻¹ = g := by
    rw [← ha]
    have : g ^ a = g * g ^ (a - 1) := by rw [← zpow_one_add]; congr 1; ring
    rw [this, h8, mul_one]
  calc d * g = (d * g * d⁻¹) * d := by group
    _ = g * d := by rw [h9]

variable [Finite G]

theorem commute_of_coprime_cyclic {p : ℕ} (hp : p.Prime) {N : Subgroup G} (hN : IsPGroup p N)
    (hc : IsCyclic N) {z d : G} (hzN : z ∈ N) (hzp : orderOf z = p)
    (hd : d ∈ normalizer (N : Set G)) (hdp : p.Coprime (orderOf d)) (hdz : d * z = z * d) :
    ∀ n ∈ N, d * n = n * d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hgo : orderOf (g : G) = p ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hmem : ∀ x ∈ N, x ∈ zpowers (g : G) := fun x hx => by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hdvd : p ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
      rwa [Subgroup.orderOf_mk, hzp] at this
    rw [hk, hk0, pow_zero] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  have hw : (g : G) ^ (p ^ (k - 1)) ∈ zpowers z := by
    let zN : N := ⟨z, hzN⟩
    let wN : N := g ^ (p ^ (k - 1))
    have hzcard : Nat.card (zpowers zN) = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk z hzN, hzp]
    have hgN : orderOf g = p ^ k := by rwa [← Subgroup.orderOf_coe]
    have hwcard : Nat.card (zpowers wN) = p := by
      rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by
        rw [hgN]; exact pow_dvd_pow p (Nat.sub_le k 1)), hgN]
      rw [show p ^ k = p ^ (k - 1) * p by rw [← pow_succ]; congr 1; omega,
        Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
    have heq : zpowers wN = zpowers zN :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (hwcard.trans hzcard.symm)
    have hmemw : wN ∈ zpowers zN := heq ▸ mem_zpowers wN
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmemw
    exact mem_zpowers_iff.mpr ⟨n, by simpa [wN] using congrArg Subtype.val hn⟩
  have hdw : d * (g : G) ^ (p ^ (k - 1)) = (g : G) ^ (p ^ (k - 1)) * d := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hw
    rw [← hn]
    exact (Commute.zpow_right (show Commute d z from hdz) n).eq
  have hdg : d * (g : G) = (g : G) * d := by
    refine commute_of_coprime_aux hp hk1 hgo ?_ hdp hdw
    exact hmem _ (((mem_normalizer_iff.mp hd) (g : G)).1 g.2)
  intro n hn
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hmem n hn)
  rw [← hm]
  exact (Commute.zpow_right (show Commute d (g : G) from hdg) m).eq

end Lambda

section Centralizer

variable {X : Type*} [Group X] [Finite X]

theorem inf_centralizer_le_pCore {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hKn : K.Normal) :
    K ⊓ centralizer (K : Set X) ≤ CFSG.pCore p X := by
  set C : Subgroup X := K ⊓ centralizer (K : Set X) with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ⟨hKn.conj_mem c hc.1 g, ?_⟩⟩
    refine mem_centralizer_iff.mpr fun k hk => ?_
    have := mem_centralizer_iff.mp hc.2 (g⁻¹ * k * g) (hKn.conj_mem' k hk g)
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * k := by group
  have hCc : ∀ a b : C, a * b = b * a := by
    intro a b
    exact Subtype.ext (mem_centralizer_iff.mp a.2.2 b b.2.1).symm
  have hCnil : Group.IsNilpotent C := by
    let _ : CommGroup C := { (inferInstance : Group C) with mul_comm := hCc }
    infer_instance
  rw [← CFSG.Fitting_eq_pcore X p hcore]
  exact le_sSup ⟨hCn, hCnil⟩

theorem isPGroup_centralizer_of_unique_component {p : ℕ} [Fact p.Prime] (R : Sylow p X)
    {K : Subgroup X} (hcore : primeComplementCore (G := X) p = ⊥) (hK : IsComponentOf K ⊤)
    (hKn : K.Normal) (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ centralizer (K : Set X) : Subgroup X))
    {z : X} (hz : z ∈ center X) (hzp : orderOf z = p) :
    IsPGroup p (centralizer (K : Set X)) := by
  have hp : p.Prime := Fact.out
  set D : Subgroup X := centralizer (K : Set X) with hD
  set N : Subgroup X := CFSG.pCore p X with hN
  have hF : CFSG.fittingSubgroup X = N := CFSG.Fitting_eq_pcore X p hcore
  have hNn : N.Normal := CFSG.pCore_normal
  have hNp : IsPGroup p N := CFSG.pCore_isPGroup
  have hlayer : CFSG.layer X = K := le_antisymm
    (sSup_le fun L hL => (huniq L ((CFSG.isComponent_iff_open L).mp hL)).le)
    (le_layer_of_isComponentOf hK)
  have hND : N ≤ D := by
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := X))
    rw [hF, hlayer] at h
    exact h
  have hNR : N ≤ (R : Subgroup X) :=
    sSup_le fun K ⟨hKn, hKp⟩ => @IsPGroup.le_sylow_of_normal _ _ _ K hKn hKp R
  have hNc : IsCyclic N := by
    have hle : N ≤ (R : Subgroup X) ⊓ D := le_inf hNR hND
    have : IsCyclic (N.subgroupOf ((R : Subgroup X) ⊓ D)) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  have hzN : z ∈ N := mem_pCore_of_mem_center hz hzp
  have hKD : K ⊓ D ≤ N := inf_centralizer_le_pCore hcore hKn
  have hcop : ∀ d ∈ D, p.Coprime (orderOf d) → d = 1 := by
    intro d hd hdp
    have hdN : d ∈ normalizer (N : Set X) := by
      have := hNn
      rw [Subgroup.normalizer_eq_top]
      trivial
    have hdc : ∀ n ∈ N, d * n = n * d :=
      commute_of_coprime_cyclic hp hNp hNc hzN hzp hdN hdp (mem_center_iff.mp hz d)
    have hdF : d ∈ N ⊔ K := by
      have hFs : CFSG.generalizedFitting X = N ⊔ K := by
        rw [CFSG.generalizedFitting, hF, hlayer]
      rw [← hFs]
      refine CFSG.centralizer_generalizedFitting_le X ?_
      rw [mem_centralizer_iff]
      intro w hw
      rw [hFs] at hw
      have hle : N ⊔ K ≤ centralizer ({d} : Set X) := by
        refine sup_le (fun n hn => ?_) (fun k hk => ?_)
        · exact mem_centralizer_singleton_iff.mpr (hdc n hn).symm
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hd k hk)
      exact mem_centralizer_singleton_iff.mp (hle hw)
    obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hdF
    have hkD : k ∈ D := by
      have := D.mul_mem (D.inv_mem (hND hn)) hd
      simpa using this
    have hdN' : n * k ∈ N := N.mul_mem hn (hKD ⟨hk, hkD⟩)
    obtain ⟨j, hj⟩ := hNp ⟨n * k, hdN'⟩
    have hdvd : orderOf (n * k) ∣ p ^ j := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hj)
    have h1 : orderOf (n * k) = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right j hdp.symm) hdvd
    exact orderOf_eq_one_iff.mp h1
  intro y
  have hy0 : orderOf (y : X) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨e, m', hm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy0 p hp.ne_one
  have hd1 : orderOf ((y : X) ^ (p ^ e)) = m' := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hm ▸ dvd_mul_right _ _), hm,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hcop' : p.Coprime m' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm'
  have h1 : (y : X) ^ (p ^ e) = 1 := hcop _ (D.pow_mem y.2 _) (hd1 ▸ hcop')
  refine ⟨e, Subtype.ext ?_⟩
  simpa using h1

end Centralizer

namespace PPointReduced

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {x : G}
  {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}

theorem isPGroup_centralizer [Fact p.Prime] (h : PPointReduced p M x R K) {z : RedCent p x}
    (hz : z ∈ center (RedCent p x)) (hzp : orderOf z = p) :
    IsPGroup p (centralizer (K : Set (RedCent p x))) :=
  isPGroup_centralizer_of_unique_component R h.red.core_eq_bot h.component h.normal h.unique
    h.cyclic hz hzp

theorem centralizer_le_sylow [Fact p.Prime] (h : PPointReduced p M x R K) {z : RedCent p x}
    (hz : z ∈ center (RedCent p x)) (hzp : orderOf z = p) :
    centralizer (K : Set (RedCent p x)) ≤ (R : Subgroup (RedCent p x)) :=
  have := h.normal
  (h.isPGroup_centralizer hz hzp).le_sylow_of_normal R

theorem isCyclic_centralizer [Fact p.Prime] (h : PPointReduced p M x R K) {z : RedCent p x}
    (hz : z ∈ center (RedCent p x)) (hzp : orderOf z = p) :
    IsCyclic (centralizer (K : Set (RedCent p x))) := by
  have := h.cyclic
  rwa [inf_eq_right.mpr (h.centralizer_le_sylow hz hzp)] at this

end PPointReduced

end CFSG.LocalAnalysis.RankFourTheoremC
