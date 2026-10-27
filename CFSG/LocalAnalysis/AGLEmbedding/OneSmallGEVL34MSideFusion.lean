module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreCount
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem L34MSide.fusion_data (hUE : KFactUPrimeExc)
    (hOrb : KFactSmallOrbits) (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K) :
    (∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) ∧ (∀ r ∈ R, r ^ 3 = 1) ∧
    Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) = 3 ^ 2 ∧
    (∀ r ∈ R, r ∉ d1LiftX p H R K → r ∈ fusionSet R z) := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hE : (3 = 3 ∧ IsLinThreeFour K) ∨ (3 = 5 ∧ IsFi22 K) := Or.inl ⟨rfl, hL⟩
  obtain ⟨T₁, hT₁, -, -⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  obtain ⟨T, hT, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hU3 : ¬ IsSmallUnitary 3 K := fun h => (not_l34_and_not_a6_of_u33 hO h).1 hL
  have hA6 : ¬ IsAltTwoP 3 K := fun h => not_l34_of_a6 hO h hL
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3]
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut (fun _ _ => hOR))
  have hexpR := hd.pow_eq_one_of_d1LiftX_decomp hExp hz hdec
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hdvd, hinv₁, hinv₂⟩ := D1OneSmallData.fusion_count hd hz hB0 hdec hexpR
  have hT1 : (((d1LiftX 3 H R K : Subgroup G) : Set G) \ {1}).ncard = 3 ^ 2 - 1 := by
    obtain ⟨-, hTc⟩ := hd.d1LiftX_facts hz
    rw [Set.ncard_sdiff_singleton_of_mem (d1LiftX 3 H R K).one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hTc.trans hcard)
  refine ⟨hdec, hexpR, hcard, ?_⟩
  rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨hA, -⟩
  · have h8 := eq_eight_of_dvd (h _ hinv₁) (h _ hinv₂) hdvd
    have heq := Set.eq_of_subset_of_ncard_le hinv₂.1 (by rw [h8, hT1])
    have hz1 : z ≠ 1 := fun h1 => by
      have := hz.2.1
      rw [h1, orderOf_one] at this
      omega
    have hzt : ∀ t ∈ d1LiftX 3 H R K, z * t ∈ fusionSet R z := by
      intro t ht
      by_cases ht1 : t = 1
      · rw [ht1, mul_one]; exact self_mem_fusionSet hz1
      · have : t ∈ {t | t ∈ d1LiftX 3 H R K ∧ z * t ∈ fusionSet R z} \ {1} :=
          heq ▸ ⟨ht, ht1⟩
        exact this.1.2
    exact mem_fusionSet_of_not_mem_of_mul (d1LiftX_le 3 H R K) hz.1 hRz hexpR hdec hzt
  · omega
  · exact absurd hA hA6

theorem L34MSide.card_le_of_mem_fusionSet (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) {w g : G}
    (hw : w ∈ fusionSet R z)
    (hc : ∀ y ∈ (P : Subgroup G), g * y * g⁻¹ * w = w * (g * y * g⁻¹)) :
    Nat.card (P : Subgroup G) ≤ Nat.card R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hw1, n, -, hwn⟩ := hw
  have hzo : orderOf z = p := hz.2.1
  have hcardz : Nat.card (Subgroup.zpowers (n * z * n⁻¹)) = p := by
    rw [Nat.card_zpowers]
    have : n * z * n⁻¹ = MulAut.conj n z := by simp [MulAut.conj_apply]
    rw [this, MulEquiv.orderOf_eq, hzo]
  have hmem : n * z * n⁻¹ ∈ Subgroup.zpowers w := by
    have h := mem_zpowers_of_prime_card hcardz (g := ⟨w, hwn⟩)
      (g' := ⟨n * z * n⁻¹, Subgroup.mem_zpowers _⟩)
      (fun h => hw1 (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  set c := n⁻¹ * g with hcdef
  set P' := (P : Subgroup G).map (MulAut.conj c).toMonoidHom with hP'
  have hP'C : P' ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * y * g⁻¹ * (n * z * n⁻¹) = n * z * n⁻¹ * (g * y * g⁻¹) := by
      rw [← hk]
      exact ((Commute.zpow_right (hc y hy) k))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcdef]
    have h2 : n⁻¹ * (g * y * g⁻¹ * (n * z * n⁻¹)) * n =
        n⁻¹ * (n * z * n⁻¹ * (g * y * g⁻¹)) * n := by rw [h1]
    calc n⁻¹ * g * y * (n⁻¹ * g)⁻¹ * z = n⁻¹ * (g * y * g⁻¹ * (n * z * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * z * n⁻¹ * (g * y * g⁻¹)) * n := h2
      _ = z * (n⁻¹ * g * y * (n⁻¹ * g)⁻¹) := by group
  have hP'p : IsPGroup p P' := P.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hB0
  have hle := card_le_card_map_sylow Q hP'p hP'C
  rw [hQ] at hle
  rwa [hP', Subgroup.card_map_of_injective (MulAut.conj c).injective] at hle

theorem L34MSide.mem_d1LiftX_of_mem_center (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z)
    (hfus : ∀ r ∈ R, r ∉ d1LiftX p H R K → r ∈ fusionSet R z)
    (hPR : Nat.card R < Nat.card (P : Subgroup G)) {x : G} (hxP : x ∈ (P : Subgroup G))
    (hxc : ∀ y ∈ (P : Subgroup G), x * y = y * x) : x ∈ d1LiftX p H R K := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.le_P
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (R : Set G))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hxc r (hRP hr)).symm
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxP)
  have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
  have hsup : IsPGroup p ↥((Subgroup.zpowers x) ⊔ R) := hxp.to_sup_of_normal_right' hRp hxN
  have hsupC : (Subgroup.zpowers x) ⊔ R ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le ?_ hRC
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hxc z (hRP hz.1)
  obtain ⟨Q, hQ⟩ := hB0
  have hle := card_le_card_map_sylow Q hsup hsupC
  rw [hQ] at hle
  have heq : (Subgroup.zpowers x) ⊔ R = R :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right hle).symm
  have hxR : x ∈ R := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  by_contra hxT
  have hw := hfus x hxR hxT
  have := L34MSide.card_le_of_mem_fusionSet hd hz ⟨Q, hQ⟩ (g := 1) hw (fun y hy => by
    simp only [one_mul, inv_one, mul_one]; exact (hxc y hy).symm)
  omega

theorem L34MSide.card_lt_card_sylow (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) :
    Nat.card R < Nat.card (P : Subgroup G) := by
  obtain ⟨x, hxP, -, hxR, -⟩ := hd.exists_moving_elt hz hB0
  exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hd.cfg.ext.le_P (fun h => hxR (h ▸ hxP)))

theorem L34MSide.exists_center_ne_one (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) :
    ∃ x ∈ (P : Subgroup G), x ≠ 1 ∧ ∀ y ∈ (P : Subgroup G), x * y = y * x := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hlt := L34MSide.card_lt_card_sylow hd hz hB0
  have hnt : Nontrivial (P : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : 0 < Nat.card R := Nat.card_pos
    omega
  have hc := P.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
  refine ⟨((c : (P : Subgroup G)) : G), (c : (P : Subgroup G)).2, ?_, fun y hy => ?_⟩
  · intro h
    apply hc1
    exact Subtype.ext (Subtype.ext h)
  · have := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm

end CFSG.AGLEmbedding
