module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideLift
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]
variable {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem L34MSide.coprime_card_of_perfect_le_centralizer (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hB0 : D1CzB0 3 R z) (hL : IsLinThreeFour K) (hOR : ¬ D1SmallOuterR 3 H Rbar K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {V : Subgroup G} (hVM : V ≤ M) (hVC : V ≤ Subgroup.centralizer ({z} : Set G))
    (hVp : ⁅V, V⁆ = V) : Nat.Coprime 3 (Nat.card V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVH : V ≤ H := hVC.trans hCz
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hsolv := hΓ3 K hs hn hc T₁ hTnc hΓT hd.small (Or.inr (Or.inr hL))
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set W := (V.subgroupOf H).map π with hW
  have hWp : ⁅W, W⁆ = W := by
    have h1 : ⁅V.subgroupOf H, V.subgroupOf H⁆ = V.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVH, hVp]
    rw [hW, ← Subgroup.map_commutator, h1]
  have hWX : W ≤ d1X0 3 M H := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    ⟨hVH (Subgroup.mem_subgroupOf.mp hu), hVM (Subgroup.mem_subgroupOf.mp hu)⟩
  have hWC := hd.le_centralizer_of_perfect_of_eq hY (hSch K hs hn hc) hsolv hWX hWp
  obtain ⟨hzH, hzC⟩ := hz.2.2
  set zb := π ⟨z, hzH⟩ with hzb
  have hz3 : orderOf z = 3 := hz.2.1
  have hbound : ∀ Q : Subgroup (H ⧸ primeComplementCore (G := H) 3),
      Q ≤ Subgroup.centralizer (K : Set _) → IsPGroup 3 Q → Nat.card Q ≤ 3 :=
    fun Q hQC hQp => hd.card_le_of_le_centralizer hR hQC hQp
  have hzp : IsPGroup 3 (Subgroup.zpowers (⟨z, hzH⟩ : H)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← hz3]
    exact (orderOf_injective H.subtype H.subtype_injective ⟨z, hzH⟩).symm
  have hzb3 : orderOf zb = 3 := by
    have hcard := L34MSide.card_map_mk_of_pGroup hzp
    rw [MonoidHom.map_zpowers, Nat.card_zpowers, Nat.card_zpowers] at hcard
    rw [hcard, ← hz3]
    exact (orderOf_injective H.subtype H.subtype_injective ⟨z, hzH⟩).symm
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hvH : (v : G) ∈ H := hVH v.2
  set vb := π ⟨v, hvH⟩ with hvb
  have hvo : orderOf (⟨v, hvH⟩ : H) = 3 := by
    have e1 := orderOf_injective H.subtype H.subtype_injective ⟨v, hvH⟩
    have e2 := orderOf_injective V.subtype V.subtype_injective v
    simp only [Subgroup.coe_subtype] at e1 e2
    rw [← e1, e2, hv]
  have hvp : IsPGroup 3 (Subgroup.zpowers (⟨v, hvH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one, hvo])
  have hvb3 : orderOf vb = 3 := by
    have hcard := L34MSide.card_map_mk_of_pGroup hvp
    rw [MonoidHom.map_zpowers, Nat.card_zpowers, Nat.card_zpowers] at hcard
    rw [hcard, hvo]
  have hvbW : vb ∈ W := ⟨⟨v, hvH⟩, Subgroup.mem_subgroupOf.mpr v.2, rfl⟩
  have hvbz : vb * zb = zb * vb := by
    rw [hvb, hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hVC v.2)
    simpa using this
  have hzbp : IsPGroup 3 (Subgroup.zpowers zb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one, hzb3])
  have hvbp : IsPGroup 3 (Subgroup.zpowers vb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one, hvb3])
  have hzbN : Subgroup.zpowers zb ≤ Subgroup.normalizer ((Subgroup.zpowers vb : Subgroup _) :
      Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left hvbz k)).eq
  have hQp : IsPGroup 3 ↥(Subgroup.zpowers zb ⊔ Subgroup.zpowers vb) :=
    hzbp.to_sup_of_normal_right' hvbp hzbN
  have hQC : Subgroup.zpowers zb ⊔ Subgroup.zpowers vb ≤ Subgroup.centralizer (K : Set _) :=
    sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr (hWC hvbW))
  have hQ3 := hbound _ hQC hQp
  have heq1 : Subgroup.zpowers vb = Subgroup.zpowers zb ⊔ Subgroup.zpowers vb :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, hvb3]; exact hQ3)
  have hzbv : zb ∈ Subgroup.zpowers vb := heq1 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers zb)
  have hzbW : zb ∈ W := (Subgroup.zpowers_le.mpr hvbW) hzbv
  have hzcen : (⟨zb, hzbW⟩ : W) ∈ Subgroup.center W := by
    refine Subgroup.mem_center_iff.mpr fun w => Subtype.ext ?_
    obtain ⟨u, hu, hue⟩ := w.2
    simp only [Subgroup.coe_mul]
    rw [← hue, hzb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hVC (Subgroup.mem_subgroupOf.mp hu))
    simpa using this
  have hpow : ∀ g : W, g ^ (Subgroup.center W).index = 1 := by
    intro g
    have hWperf : commutator W = ⊤ := (Subgroup.isPerfect_iff.mpr hWp).1
    have hker : g ∈ (MonoidHom.transferCenterPow W).ker :=
      Abelianization.commutator_subset_ker _ (hWperf ▸ Subgroup.mem_top g)
    rw [MonoidHom.mem_ker] at hker
    rw [← MonoidHom.transferCenterPow_apply, hker, Subgroup.coe_one]
  have hzo : orderOf (⟨zb, hzbW⟩ : W) = 3 := by
    have := orderOf_injective W.subtype W.subtype_injective ⟨zb, hzbW⟩
    simp only [Subgroup.coe_subtype] at this
    rw [← this, hzb3]
  have hdvd3 : 3 ∣ (Subgroup.center W).index := by
    have := orderOf_dvd_of_pow_eq_one (hpow ⟨zb, hzbW⟩)
    rwa [hzo] at this
  have h3c : 3 ∣ Nat.card (Subgroup.center W) := by
    have := Subgroup.orderOf_dvd_natCard _ hzcen
    rwa [hzo] at this
  have h9 : 3 ^ 2 ∣ Nat.card W := by
    rw [← (Subgroup.center W).card_mul_index, pow_two]
    exact Nat.mul_dvd_mul h3c hdvd3
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 W))
  have hS9 := Sylow.pow_dvd_card_of_pow_dvd_card S h9
  have hSb := hbound ((S : Subgroup W).map W.subtype)
    (fun x hx => by obtain ⟨w, -, rfl⟩ := hx; exact hWC w.2) (S.isPGroup'.map _)
  rw [Subgroup.card_map_of_injective W.subtype_injective] at hSb
  have := Nat.le_of_dvd Nat.card_pos hS9
  omega

theorem L34MSide.perfect_mtilde (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hExp : KFactSmallSylowExp)
    (hOut : KFactSmallOutPPrime)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hB0 : D1CzB0 3 R z) (hL : IsLinThreeFour K) (hOR : ¬ D1SmallOuterR 3 H Rbar K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ D : Subgroup (M ⧸ primeComplementCore (G := M) 3), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨z, hd.cfg.ext.le_M hz.1⟩} :
          Set _) →
      ¬ 3 ∣ Nat.card D := by
  have hzM : z ∈ M := hd.cfg.ext.le_M hz.1
  have hz3 : orderOf z = 3 := hz.2.1
  have hperfM : ∀ D : Subgroup M, D ≤ Subgroup.centralizer ({(⟨z, hzM⟩ : M)} : Set M) →
      ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D := by
    intro D hDC hDp h3
    have hVC : D.map M.subtype ≤ Subgroup.centralizer ({z} : Set G) := by
      rintro _ ⟨d, hd', rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hDC hd')
      exact congrArg Subtype.val this
    have hVp : ⁅D.map M.subtype, D.map M.subtype⁆ = D.map M.subtype := by
      rw [← Subgroup.map_commutator, hDp]
    have hcop := L34MSide.coprime_card_of_perfect_le_centralizer hUE hSch hΓ3 hExp hOut hd hz
      hB0 hL hOR hCz (Subgroup.map_subtype_le _) hVC hVp
    rw [Subgroup.card_map_of_injective M.subtype_injective] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3
  intro D hDp hDC
  exact L34MSide.not_dvd_card_of_perfect_le_centralizer_mk 3
    (L34MSide.isPGroup_zpowers_of_orderOf hzM hz3) hperfM D hDp hDC

theorem L34MSide.mtilde_component (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hExp : KFactSmallSylowExp)
    (hOut : KFactSmallOutPPrime)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hB0 : D1CzB0 3 R z) (hL : IsLinThreeFour K) (hOR : ¬ D1SmallOuterR 3 H Rbar K)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {Lt : Subgroup (M ⧸ primeComplementCore (G := M) 3)} (hLt : IsComponentOf Lt ⊤) :
    QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨z, hd.cfg.ext.le_M hz.1⟩ ∈
        Subgroup.normalizer (Lt : Set (M ⧸ primeComplementCore (G := M) 3)) ∧
      QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨z, hd.cfg.ext.le_M hz.1⟩ ∉
        Subgroup.centralizer (Lt : Set (M ⧸ primeComplementCore (G := M) 3)) := by
  have hzM : z ∈ M := hd.cfg.ext.le_M hz.1
  have hz3 : orderOf z = 3 := hz.2.1
  have hZ := L34MSide.perfect_mtilde hUE hSch hΓ3 hExp hOut hd hz hB0 hL hOR hCz
  have hcore := primeComplementCore_quotient_eq_bot (G := M) 3
  have hn3 := prime_dvd_card_center_quotient_of_isComponentOf Nat.prime_three hcore hLt
  have hu : (QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨z, hzM⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hz3]; exact pow_orderOf_eq_one z
    rw [this, map_one]
  exact ⟨L34MSide.mem_normalizer_of_perfect_centralizer_not_dvd 3 hLt hu hn3
      (fun D hDp hDC => hZ D hDp hDC),
    L34MSide.not_mem_centralizer_of_perfect_centralizer_not_dvd 3 hLt hn3
      (fun D hDp hDC => hZ D hDp hDC)⟩

end CFSG.AGLEmbedding
