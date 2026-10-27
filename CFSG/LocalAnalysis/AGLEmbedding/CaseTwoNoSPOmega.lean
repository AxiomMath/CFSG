module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
  {K : Subgroup (D1CzQuot p z)}

omit [Finite G] in
theorem mem_zpowers_of_pow_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {A : Subgroup X} [IsCyclic A] {t a : X} (htA : t ∈ A) (htp : orderOf t = p) (haA : a ∈ A)
    (hap : a ^ p = 1) : a ∈ Subgroup.zpowers t := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  · exact mem_zpowers_of_orderOf_eq_of_isCyclic haA htA (by rw [orderOf_eq_prime hap ha1, htp])

theorem D1CzReduced.exists_omega (hc : D1CzReduced p M z T Pbar K) (hL2 : KFactCaseTwoLocal)
    (hzK : d1CzElt p z ∉ K)
    (hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)))
    (hK : IsCaseTwoGroup p K) :
    ∃ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K, orderOf t = p ∧
      (∀ g ∈ (Pbar : Subgroup (D1CzQuot p z)), Commute t g) ∧
      ∀ g ∈ (Pbar : Subgroup (D1CzQuot p z)),
        (∀ h ∈ (Pbar : Subgroup (D1CzQuot p z)), Commute g h) → g ^ p = 1 →
          g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers (d1CzElt p z) := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn := hc.normal
  obtain ⟨hZ, -⟩ := hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK
  have hYcyc := hc.red.isCyclic_inf_centralizer_of_not_mem_of_center hc.center hc.order hc.comp
    hKn hzK hZ
  obtain ⟨t, htA, htp, -⟩ := exists_mem_sylow_inf_component hp hc.red.ne_two hc.red.core_eq_bot
    Pbar hc.comp
  refine ⟨t, htA, htp, fun g hg => ?_, fun g hg hgc hgp => ?_⟩
  ·
    have hgP : g * t * g⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg htA.1) (Subgroup.inv_mem _ hg)
    have hgA : g * t * g⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hgP, hKn.conj_mem t htA.2 g⟩
    have hgt : g * t * g⁻¹ ∈ Subgroup.zpowers t := conj_mem_zpowers_of_isCyclic rfl htA hgA
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨g, hg⟩
    have hgn : g ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact (commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp htp
      (mem_normalizer_zpowers_of_mem_zpowers hgt) hgn).symm
  ·
    obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKn.isSubnormal
    have hfix : ∀ x ∈ (TK : Subgroup K), MulAut.conjNormal (H := K) g x = x := by
      intro x hx
      have hxA : (x : D1CzQuot p z) ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K := by
        rw [← hTK]
        exact ⟨x, hx, rfl⟩
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, (hgc _ hxA.1).eq, mul_inv_cancel_right]
    obtain ⟨a, haT, ha⟩ := ((hL2 p K hK).2.2 TK).2.1 _ hfix
    set a' : D1CzQuot p z := (a : D1CzQuot p z) with ha'
    have ha'A : a' ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K := by
      rw [← hTK]
      exact ⟨a, haT, rfl⟩
    set d := a'⁻¹ * g with hd
    have hdC : d ∈ Subgroup.centralizer (K : Set (D1CzQuot p z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : D1CzQuot p z)) ha
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc k * d = a'⁻¹ * (a' * k * a'⁻¹) * g := by rw [hd]; group
        _ = a'⁻¹ * (g * k * g⁻¹) * g := by rw [← h1]
        _ = d * k := by rw [hd]; group
    have hdP : d ∈ (Pbar : Subgroup (D1CzQuot p z)) := by
      rw [hd]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha'A.1) hg
    have hgad : g = a' * d := by rw [hd, mul_inv_cancel_left]
    have had : Commute a' d := Subgroup.mem_centralizer_iff.mp hdC a' ha'A.2
    have hpow : a' ^ p * d ^ p = 1 := by rw [← had.mul_pow, ← hgad, hgp]
    have hap : a' ^ p = 1 := by
      have hmem : a' ^ p ∈ K ⊓ Subgroup.centralizer (K : Set (D1CzQuot p z)) := by
        refine ⟨K.pow_mem ha'A.2 p, ?_⟩
        have : a' ^ p = (d ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hpow
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hdC p)
      have hZ' : (⟨a' ^ p, hmem.1⟩ : K) ∈ Subgroup.center K :=
        Subgroup.mem_center_iff.mpr fun k =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp hmem.2 k k.2)
      rw [hZ, Subgroup.mem_bot] at hZ'
      exact congrArg Subtype.val hZ'
    have hdp : d ^ p = 1 := by rw [hap, one_mul] at hpow; exact hpow
    have haz : a' ∈ Subgroup.zpowers t := mem_zpowers_of_pow_eq_one hp htA htp ha'A hap
    have hzY : d1CzElt p z ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓
        Subgroup.centralizer (K : Set (D1CzQuot p z)) :=
      ⟨mem_sylow_of_mem_center hc.center hc.order Pbar,
        Subgroup.center_le_centralizer _ hc.center⟩
    have hdz : d ∈ Subgroup.zpowers (d1CzElt p z) :=
      mem_zpowers_of_pow_eq_one hp hzY hc.order ⟨hdP, hdC⟩ hdp
    rw [hgad]
    exact Subgroup.mul_mem_sup haz hdz

theorem D1CzReduced.shape_omega (hc : D1CzReduced p M z T Pbar K) (hL2 : KFactCaseTwoLocal)
    (hzK : d1CzElt p z ∉ K)
    (hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)))
    (hK : IsCaseTwoGroup p K) (hzp : orderOf z = p) :
    ∃ t ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
      (∀ g ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype, Commute t g) ∧
      orderOf t = p ∧ t ∉ Subgroup.zpowers z ∧
      ∀ g ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
        (∀ h ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
          Commute g h) → g ^ p = 1 → g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t', htA, htp, htc, hΩ⟩ := hc.exists_omega hL2 hzK hcyc hK
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
    with hπ
  have hinj : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), π x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p :=
      (QuotientGroup.eq_one_iff x).mp h1
    have hbot := inf_eq_bot_of_isPGroup hp T.isPGroup' (primeComplementCore_coprime p)
    have hmem : x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))) ⊓
        primeComplementCore p := ⟨hx, hxO⟩
    rw [hbot] at hmem
    exact hmem
  have hmemP : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      π x ∈ (Pbar : Subgroup (D1CzQuot p z)) := fun x hx => by
    rw [hc.sylow_eq]
    exact ⟨x, hx, rfl⟩
  have hcommT : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      ∀ y ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), Commute (π x) (π y) →
        Commute x y := by
    intro x hx y hy hxy
    have h1 : π (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hxy.eq, mul_inv_cancel]
    have h2 := hinj _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hy hx))) h1
    exact mul_inv_eq_one.mp h2
  have htP : t' ∈ (Pbar : Subgroup (D1CzQuot p z)) := htA.1
  rw [hc.sylow_eq] at htP
  obtain ⟨τ, hτT, hτt⟩ := htP
  subst hτt
  set ζ : Subgroup.centralizer ({z} : Set G) := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    with hζ
  have hζZ : ζ ∈ Subgroup.center (Subgroup.centralizer ({z} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hζp : orderOf ζ = p := by rw [hζ, Subgroup.orderOf_mk, hzp]
  have hζT : ζ ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))) :=
    mem_sylow_of_mem_center hζZ hζp T
  have hπζ : π ζ = d1CzElt p z := rfl
  have hτp : orderOf τ = p := by
    have h1 : π (τ ^ p) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq htp)
    have h2 := hinj _ (Subgroup.pow_mem _ hτT p) h1
    have h3 : τ ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at htp
      exact hp.one_lt.ne htp
    exact orderOf_eq_prime h2 h3
  refine ⟨(τ : G), ⟨τ, hτT, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨σ, hσT, rfl⟩
    have h1 := hcommT τ hτT σ hσT (htc _ (hmemP σ hσT))
    exact congrArg Subtype.val h1
  · rw [Subgroup.orderOf_coe, hτp]
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hτk : τ = ζ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hζ]; exact hk.symm)
    have hmem : π τ ∈ Subgroup.zpowers (d1CzElt p z) := by
      rw [hτk, map_zpow, hπζ]
      exact Subgroup.zpow_mem_zpowers _ k
    have heq : Subgroup.zpowers (π τ) = Subgroup.zpowers (d1CzElt p z) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, htp, hc.order])
    exact hzK ((Subgroup.zpowers_le.mpr htA.2) (heq ▸ Subgroup.mem_zpowers _))
  · rintro _ ⟨σ, hσT, rfl⟩ hgc hgp
    have hσc : ∀ h ∈ (Pbar : Subgroup (D1CzQuot p z)), Commute (π σ) h := by
      intro h hh
      rw [hc.sylow_eq] at hh
      obtain ⟨σ', hσ'T, rfl⟩ := hh
      have h1 : Commute σ σ' := Subtype.ext (hgc _ ⟨σ', hσ'T, rfl⟩)
      exact h1.map π
    have hσp : π σ ^ p = 1 := by
      have h1 : σ ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)
      rw [← map_pow, h1, map_one]
    have hcz : Commute (π τ) (d1CzElt p z) := Subgroup.mem_center_iff.mp hc.center (π τ)
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (mem_zpowers_sup_zpowers_iff hcz).mp (hΩ _ (hmemP σ hσT) hσc hσp)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hw : (τ ^ i * ζ ^ j)⁻¹ * σ = 1 := by
      refine hinj _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.zpow_mem _ hτT i) (Subgroup.zpow_mem _ hζT j))) hσT) ?_
      rw [map_mul, map_inv, map_mul, map_zpow, map_zpow, hπζ, hab, inv_mul_cancel]
    have hσeq : σ = τ ^ i * ζ ^ j := (inv_mul_eq_one.mp hw).symm
    rw [hσeq]
    show ((τ ^ i * ζ ^ j : Subgroup.centralizer ({z} : Set G)) : G) ∈ _
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ i) (Subgroup.zpow_mem_zpowers _ j)

end Cz

end CFSG.AGLEmbedding
