module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift

public section

namespace CFSG.AGLEmbedding

open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Line

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_conj {p : ℕ} [Fact p.Prime] {s τ z w : G} (hτz : Commute τ z)
    (hτp : orderOf τ = p) (hwp : orderOf w = p)
    (hw : w ∈ Subgroup.zpowers τ ⊔ Subgroup.zpowers z) (hsz : s * z * s⁻¹ = z)
    (hsτ : s * τ * s⁻¹ ∈ Subgroup.zpowers τ) (hsτ1 : s * τ * s⁻¹ ≠ τ)
    (hsw : s * w * s⁻¹ ∈ Subgroup.zpowers w) (hwz : w ∉ Subgroup.zpowers z) :
    τ ∈ Subgroup.zpowers w := by
  have hp : p.Prime := Fact.out
  by_contra hτw
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_zpowers_sup_zpowers_iff hτz).mp hw
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hsτ
  have hsw' : s * (τ ^ a * z ^ b) * s⁻¹ = τ ^ (i * a) * z ^ b := by
    have h1 : s * τ ^ a * s⁻¹ = (s * τ * s⁻¹) ^ a := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    have h2 : s * z ^ b * s⁻¹ = (s * z * s⁻¹) ^ b := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    calc s * (τ ^ a * z ^ b) * s⁻¹ = (s * τ ^ a * s⁻¹) * (s * z ^ b * s⁻¹) := by group
      _ = τ ^ (i * a) * z ^ b := by rw [h1, h2, ← hi, hsz, ← zpow_mul]
  set c := s * (τ ^ a * z ^ b) * s⁻¹ * (τ ^ a * z ^ b)⁻¹ with hc
  have hcw : c ∈ Subgroup.zpowers (τ ^ a * z ^ b) :=
    Subgroup.mul_mem _ hsw (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  have hcτ : c = τ ^ (i * a - a) := by
    rw [hc, hsw', mul_inv_rev]
    calc τ ^ (i * a) * z ^ b * ((z ^ b)⁻¹ * (τ ^ a)⁻¹) = τ ^ (i * a) * (τ ^ a)⁻¹ := by group
      _ = τ ^ (i * a - a) := by rw [← zpow_neg, ← zpow_add]; ring_nf
  have hbot := zpowers_inf_zpowers_eq_bot_of_not_mem hτp hτw
  have hc1 : c = 1 := by
    have hmem : c ∈ Subgroup.zpowers τ ⊓ Subgroup.zpowers (τ ^ a * z ^ b) :=
      ⟨hcτ ▸ Subgroup.zpow_mem_zpowers τ _, hcw⟩
    rw [hbot] at hmem
    exact hmem
  rw [hcτ] at hc1
  have hdvd : (p : ℤ) ∣ (i - 1) * a := by
    rw [← hτp, orderOf_dvd_iff_zpow_eq_one]
    rw [show (i - 1) * a = i * a - a by ring]
    exact hc1
  have hi1 : ¬ (p : ℤ) ∣ (i - 1) := by
    intro hd
    apply hsτ1
    rw [← hi]
    have h1 : τ ^ (i - 1) = 1 := by rw [← hτp] at hd; exact orderOf_dvd_iff_zpow_eq_one.mp hd
    calc τ ^ i = τ ^ (i - 1) * τ := by rw [← zpow_add_one]; ring_nf
      _ = τ := by rw [h1, one_mul]
  have hpa : (p : ℤ) ∣ a := by
    rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_or_dvd hdvd with h | h
    · exact absurd h hi1
    · exact h
  have hτa : τ ^ a = 1 := by rw [← hτp] at hpa; exact orderOf_dvd_iff_zpow_eq_one.mp hpa
  apply hwz
  rw [hτa, one_mul]
  exact Subgroup.zpow_mem_zpowers z b

end Line

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
  {K : Subgroup (D1CzQuot p z)}

theorem D1CzReduced.exists_inv_line (hc : D1CzReduced p M z T Pbar K) (hL2 : KFactCaseTwoLocal)
    (hK : IsCaseTwoGroup p K)
    (hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)))
    {t : D1CzQuot p z} (htA : t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K) (htp : orderOf t = p)
    (htc : ∀ g ∈ (Pbar : Subgroup (D1CzQuot p z)), Commute t g) :
    ∃ s ∈ Subgroup.normalizer ((Pbar : Subgroup (D1CzQuot p z)) : Set (D1CzQuot p z)),
      s * t * s⁻¹ ∈ Subgroup.zpowers t ∧ s * t * s⁻¹ ≠ t := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn := hc.normal
  obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKn.isSubnormal
  have htK : t ∈ (TK : Subgroup K).map K.subtype := hTK ▸ htA
  obtain ⟨τ, hτT, hτt⟩ := htK
  obtain ⟨s₀, hs₀N, hs₀fp⟩ := ((hL2 p K hK).2.2 TK).1
  set s₁ : D1CzQuot p z := (s₀ : D1CzQuot p z) with hs₁
  have hτ' : s₀ * τ * s₀⁻¹ ∈ (TK : Subgroup K) :=
    (Subgroup.mem_normalizer_iff.mp hs₀N τ).mp hτT
  have hst : s₁ * t * s₁⁻¹ = ((s₀ * τ * s₀⁻¹ : K) : D1CzQuot p z) := by
    rw [← hτt, hs₁]
    simp
  have hstA : s₁ * t * s₁⁻¹ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ K := by
    rw [hst, ← hTK]
    exact ⟨_, hτ', rfl⟩
  have hstt : s₁ * t * s₁⁻¹ ∈ Subgroup.zpowers t := by
    have : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)) := hcyc
    exact conj_mem_zpowers_of_isCyclic rfl htA hstA
  have ht1 : t ≠ 1 := fun h => hp.one_lt.ne' (by rw [← htp, h, orderOf_one])
  have hst1 : s₁ * t * s₁⁻¹ ≠ t := by
    intro h
    have hfix : s₀ * τ * s₀⁻¹ = τ := by
      apply Subtype.ext
      rw [← hst, h, ← hτt]
      rfl
    have hτ1 := hs₀fp τ hτT hfix
    apply ht1
    rw [← hτt, hτ1]
    rfl
  have hord : orderOf (s₁ * t * s₁⁻¹) = p := by
    have h1 : s₁ * t * s₁⁻¹ = MulAut.conj s₁ t := rfl
    rw [h1, MulEquiv.orderOf_eq, htp]
  have heq : Subgroup.zpowers (s₁ * t * s₁⁻¹) = Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hstt)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, htp])
  have htmem : t ∈ Subgroup.zpowers (s₁ * t * s₁⁻¹) := heq ▸ Subgroup.mem_zpowers t
  set C₀ := Subgroup.centralizer ({t} : Set (D1CzQuot p z)) with hC₀
  have hPC : (Pbar : Subgroup (D1CzQuot p z)) ≤ C₀ := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htc g hg).eq.symm
  set Q₁ := (Pbar : Subgroup (D1CzQuot p z)).map (MulAut.conj s₁).toMonoidHom with hQ₁
  have hQC : Q₁ ≤ C₀ := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : Commute (s₁ * t * s₁⁻¹) (s₁ * g * s₁⁻¹) := by
      have := (htc g hg).map (MulAut.conj s₁).toMonoidHom
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htmem
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hk]
    exact ((h1.zpow_left k).eq).symm
  have hQp : IsPGroup p Q₁ := Pbar.isPGroup'.map _
  obtain ⟨c, hcQ⟩ := exists_conjugate_le_sylow_of_le p Pbar hPC hQC hQp
  have hct : (c : D1CzQuot p z) * (s₁ * t * s₁⁻¹) * (c : D1CzQuot p z)⁻¹ = s₁ * t * s₁⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hstt
    have hcc : Commute (c : D1CzQuot p z) t :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [← hk, (hcc.zpow_right k).eq, mul_inv_cancel_right]
  have hconj : ((c : D1CzQuot p z) * s₁) * t * ((c : D1CzQuot p z) * s₁)⁻¹ = s₁ * t * s₁⁻¹ := by
    rw [← hct]
    group
  refine ⟨(c : D1CzQuot p z) * s₁, ?_, by rw [hconj]; exact hstt, by rw [hconj]; exact hst1⟩
  apply mem_normalizer_of_conj_map_le
  have hmap : (Pbar : Subgroup (D1CzQuot p z)).map
      (MulAut.conj ((c : D1CzQuot p z) * s₁)).toMonoidHom =
      Q₁.map (MulAut.conj (c : D1CzQuot p z)).toMonoidHom := by
    rw [hQ₁, Subgroup.map_map]
    congr 1
    ext g
    simp [mul_assoc]
  rw [hmap]
  exact hcQ

theorem D1CzReduced.exists_kline_inv (hc : D1CzReduced p M z T Pbar K)
    (hL2 : KFactCaseTwoLocal) (hzK : d1CzElt p z ∉ K)
    (hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot p z)) ⊓ K : Subgroup (D1CzQuot p z)))
    (hK : IsCaseTwoGroup p K) (hzp : orderOf z = p) :
    ∃ τ ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      QuotientGroup.mk' (primeComplementCore p) τ ∈ K ∧
      (∀ g ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), Commute τ g) ∧
      orderOf τ = p ∧ (τ : G) ∉ Subgroup.zpowers z ∧
      (∀ g ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
        (∀ h ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), Commute g h) → g ^ p = 1 →
          g ∈ Subgroup.zpowers τ ⊔ Subgroup.zpowers
            (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
              Subgroup.centralizer ({z} : Set G))) ∧
      ∃ s ∈ Subgroup.normalizer
          ((T : Subgroup (Subgroup.centralizer ({z} : Set G))) : Set _),
        s * τ * s⁻¹ ∈ Subgroup.zpowers τ ∧ s * τ * s⁻¹ ≠ τ := by
  have hp := hc.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t', htA, htp, htc, hΩ⟩ := hc.exists_omega hL2 hzK hcyc hK
  obtain ⟨s', hs'N, hs't, hs't1⟩ := D1CzReduced.exists_inv_line hc hL2 hK hcyc htA htp htc
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
    with hπ
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hinj : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      ∀ y ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), π x = π y → x = y :=
    fun x hx y hy hxy => eq_of_mk_eq_of_isPGroup hp _ hO T.isPGroup' hx hy hxy
  have hmemP : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      π x ∈ (Pbar : Subgroup (D1CzQuot p z)) := fun x hx => by
    rw [hc.sylow_eq]
    exact ⟨x, hx, rfl⟩
  have hcommT : ∀ x ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      ∀ y ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), Commute (π x) (π y) →
        Commute x y := by
    intro x hx y hy hxy
    exact hinj _ (Subgroup.mul_mem _ hx hy) _ (Subgroup.mul_mem _ hy hx)
      (by rw [map_mul, map_mul, hxy.eq])
  have htP : t' ∈ (Pbar : Subgroup (D1CzQuot p z)) := htA.1
  rw [hc.sylow_eq] at htP
  obtain ⟨τ, hτT, hτt⟩ := htP
  subst hτt
  set ζ : Subgroup.centralizer ({z} : Set G) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hζ
  have hζZ : ζ ∈ Subgroup.center (Subgroup.centralizer ({z} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hζp : orderOf ζ = p := by rw [hζ, Subgroup.orderOf_mk, hzp]
  have hζT : ζ ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))) :=
    mem_sylow_of_mem_center hζZ hζp T
  have hπζ : π ζ = d1CzElt p z := rfl
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at htp
    exact hp.one_lt.ne htp
  have hτp : orderOf τ = p := by
    have h1 : π (τ ^ p) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq htp)
    have h2 := hinj _ (Subgroup.pow_mem _ hτT p) 1 (Subgroup.one_mem _) (by rw [h1, map_one])
    exact orderOf_eq_prime h2 hτ1
  have hτz : (τ : G) ∉ Subgroup.zpowers z := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hτk : τ = ζ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hζ]; exact hk.symm)
    have hmem : π τ ∈ Subgroup.zpowers (d1CzElt p z) := by
      rw [hτk, map_zpow, hπζ]
      exact Subgroup.zpow_mem_zpowers _ k
    have heq : Subgroup.zpowers (π τ) = Subgroup.zpowers (d1CzElt p z) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, htp, hc.order])
    exact hzK ((Subgroup.zpowers_le.mpr htA.2) (heq ▸ Subgroup.mem_zpowers _))
  have hΩT : ∀ g ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))),
      (∀ h ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))), Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers τ ⊔ Subgroup.zpowers ζ := by
    intro σ hσT hgc hgp
    have hσc : ∀ h ∈ (Pbar : Subgroup (D1CzQuot p z)), Commute (π σ) h := by
      intro h hh
      rw [hc.sylow_eq] at hh
      obtain ⟨σ', hσ'T, rfl⟩ := hh
      exact (hgc σ' hσ'T).map π
    have hσp : π σ ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hcz : Commute (π τ) (d1CzElt p z) := Subgroup.mem_center_iff.mp hc.center (π τ)
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (mem_zpowers_sup_zpowers_iff hcz).mp (hΩ _ (hmemP σ hσT) hσc hσp)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hσeq : σ = τ ^ i * ζ ^ j := by
      refine hinj _ hσT _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hτT i)
        (Subgroup.zpow_mem _ hζT j)) ?_
      rw [map_mul, map_zpow, map_zpow, hπζ, hab]
    rw [hσeq]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ i) (Subgroup.zpow_mem_zpowers _ j)
  have hs'N' : s' ∈ Subgroup.normalizer
      (((T : Subgroup (Subgroup.centralizer ({z} : Set G))).map π :
        Subgroup (D1CzQuot p z)) : Set (D1CzQuot p z)) := by
    rw [← hc.sylow_eq]
    exact hs'N
  obtain ⟨s, hsN, hss'⟩ := exists_mk_eq_of_mem_normalizer_map
    (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) hO T.isPGroup' hs'N'
  have hsτT : s * τ * s⁻¹ ∈ (T : Subgroup (Subgroup.centralizer ({z} : Set G))) :=
    (Subgroup.mem_normalizer_iff.mp hsN τ).mp hτT
  have hπs : π (s * τ * s⁻¹) = s' * π τ * s'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hss']
  refine ⟨τ, hτT, htA.2, fun g hg => hcommT τ hτT g hg (htc _ (hmemP g hg)), hτp, hτz, hΩT,
    s, hsN, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs't
    have h1 : s * τ * s⁻¹ = τ ^ k :=
      hinj _ hsτT _ (Subgroup.zpow_mem _ hτT k) (by rw [hπs, map_zpow, hk])
    rw [h1]
    exact Subgroup.zpow_mem_zpowers τ k
  · intro h
    apply hs't1
    rw [← hπs, h]

end Cz

end CFSG.AGLEmbedding
