module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqAbs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqComm
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34Esc

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
def L34Squeeze.commSub (M C₀ : Subgroup G) (z : G) (hMC : M ≤ Subgroup.normalizer (C₀ : Set G)) :
    Subgroup G where
  carrier := {y | y ∈ M ∧ y * z * y⁻¹ * z⁻¹ ∈ C₀}
  one_mem' := ⟨M.one_mem, by simp [C₀.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨M.mul_mem ha hb, ?_⟩
    have h1 : a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ ∈ C₀ :=
      (Subgroup.mem_normalizer_iff.mp (hMC ha) _).mp hbc
    have := C₀.mul_mem h1 hac
    have e : a * b * z * (a * b)⁻¹ * z⁻¹ =
        a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) := by group
    rw [e]
    exact this
  inv_mem' := by
    rintro a ⟨ha, hac⟩
    refine ⟨M.inv_mem ha, ?_⟩
    have h1 : a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ ∈ C₀ :=
      (Subgroup.mem_normalizer_iff.mp (hMC (M.inv_mem ha)) _).mp (C₀.inv_mem hac)
    have e : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem D1OneSmallData.d1LiftX_le_of_squeeze (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) (hp3 : p = 3) (hA6 : ¬ IsAltTwoP 3 K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2)
    {C₀ U : Subgroup G} (hC₀M : C₀ ≤ M) (hMC : M ≤ Subgroup.normalizer (C₀ : Set G))
    (hsyl : IsSylowTwoOf U C₀) (hNU : M ⊓ Subgroup.normalizer (U : Set G) ≤ H) :
    d1LiftX p H R K ≤ C₀ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxP, hxN, -, hxz⟩ := hd.exists_moving_elt hz hB0
  have hxM : x ∈ M := hd.cfg.ext.sylow_le hxP
  obtain ⟨c, hcC, hcN⟩ := L34Squeeze.exists_inv_mul_mem_normalizer hsyl (hMC hxM)
  have hcxM : c⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hC₀M hcC)) hxM
  have hcxB : c⁻¹ * x ∈ H ⊓ M := ⟨hNU ⟨hcxM, hcN⟩, hcxM⟩
  have hR3 : IsPGroup p R := hd.cfg.ext.isPGroup
  have hxp : IsPGroup p ↥(Subgroup.zpowers x) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxP)
  have hX3 : IsPGroup p ↥(Subgroup.zpowers x ⊔ R) :=
    hxp.to_sup_of_normal_right' hR3 (Subgroup.zpowers_le.mpr hxN)
  have hBC : H ⊓ M ≤ Subgroup.normalizer (C₀ : Set G) := inf_le_right.trans hMC
  have hXC : Subgroup.zpowers x ⊔ R ≤ Subgroup.normalizer (C₀ : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (hMC hxM)) (hd.cfg.ext.le_M.trans hMC)
  have hXN : Subgroup.zpowers x ⊔ R ≤ (H ⊓ M) ⊔ C₀ := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (hd.cfg.ext.le_inf.trans le_sup_left)
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hcxB)
  have hsylR : ¬ p ∣ R.relIndex (H ⊓ M) := by
    obtain ⟨T, hT⟩ := hd.cfg.ext.isSylow
    have hRT : R.subgroupOf H = T := by
      rw [← hT]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hidx : ¬ p ∣ R.relIndex H := by
      unfold Subgroup.relIndex
      rw [hRT]
      exact T.not_dvd_index
    intro hdvd
    apply hidx
    rw [← Subgroup.relIndex_mul_relIndex R (H ⊓ M) H hd.cfg.ext.le_inf inf_le_left]
    exact hdvd.mul_right _
  have hxRC : x ∈ R ⊔ C₀ := L34Squeeze.le_sup_of_sylow hBC hXC hXN hR3 hX3 le_sup_right
    hd.cfg.ext.le_inf hsylR (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hzR : z ∈ R := hz.1
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hsub : R ⊔ C₀ ≤ L34Squeeze.commSub M C₀ z hMC := by
    refine sup_le (fun r hr => ⟨hd.cfg.ext.le_M hr, ?_⟩) (fun c' hc' => ⟨hC₀M hc', ?_⟩)
    · have h1 : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
      have : r * z * r⁻¹ * z⁻¹ = 1 := by rw [h1]; group
      rw [this]; exact C₀.one_mem
    · have h1 : z * c'⁻¹ * z⁻¹ ∈ C₀ :=
        (Subgroup.mem_normalizer_iff.mp (hMC hzM) _).mp (C₀.inv_mem hc')
      have := C₀.mul_mem hc' h1
      simpa [mul_assoc] using this
  have hxc : x * z * x⁻¹ * z⁻¹ ∈ C₀ := (hsub hxRC).2
  have hxzR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzR
  obtain ⟨t₀, ht₀, i, hti⟩ := hdec _ hxzR
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    apply hxz
    rw [hti, one_mul]
    exact Subgroup.npow_mem_zpowers z i
  have hr₀ : t₀ * z ^ i * z⁻¹ ∈ C₀ := by rw [← hti]; exact hxc
  have hsT : ∀ s ∈ d1LiftX p H R K, s ≠ 1 → s * z ^ i * z⁻¹ ∈ C₀ := by
    intro s hs hs1
    obtain ⟨n, hnN, hnz, -, hnt⟩ :=
      hd.exists_conj_eq_of_l34 hOrb hz hdec hp3 hA6 hcard t₀ ht₀ ht₀1 s hs hs1
    have hnM : n ∈ M := hd.cfg.ext.normalizer_le hnN
    have h1 := (Subgroup.mem_normalizer_iff.mp (hMC hnM) _).mp hr₀
    have hzi : n * z ^ i * n⁻¹ = z ^ i := by rw [← conj_pow, hnz]
    have hzinv : n * z⁻¹ * n⁻¹ = z⁻¹ := by rw [← conj_inv, hnz]
    have e : n * (t₀ * z ^ i * z⁻¹) * n⁻¹ = s * z ^ i * z⁻¹ := by
      calc n * (t₀ * z ^ i * z⁻¹) * n⁻¹
          = (n * t₀ * n⁻¹) * (n * z ^ i * n⁻¹) * (n * z⁻¹ * n⁻¹) := by group
        _ = s * z ^ i * z⁻¹ := by rw [hnt, hzi, hzinv]
    rw [← e]
    exact h1
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]; exact C₀.one_mem
  have hsinv : s⁻¹ ∈ d1LiftX p H R K := Subgroup.inv_mem _ hs
  have hsinv1 : s⁻¹ ≠ 1 := inv_ne_one.mpr hs1
  have h1 := hsT s hs hs1
  have h2 := hsT s⁻¹ hsinv hsinv1
  have hsq : s * s ∈ C₀ := by
    have := C₀.mul_mem h1 (C₀.inv_mem h2)
    have e : s * z ^ i * z⁻¹ * (s⁻¹ * z ^ i * z⁻¹)⁻¹ = s * s := by group
    rw [e] at this
    exact this
  have hs3 : s ^ 3 = 1 := by
    have := hexpR s (d1LiftX_le p H R K hs)
    rwa [hp3] at this
  have e : s = (s * s) * (s * s) := by
    calc s = s * s ^ 3 := by rw [hs3, mul_one]
      _ = (s * s) * (s * s) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  exact C₀.mul_mem hsq hsq

theorem D1OneSmallData.d1LiftX_le_of_czElt_mem (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hp3 : p = 3) (hA6 : ¬ IsAltTwoP 3 K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2)
    {C₀ : Subgroup G} (hMC : M ≤ Subgroup.normalizer (C₀ : Set G)) (hzC : z ∈ C₀) :
    d1LiftX p H R K ≤ C₀ := by
  obtain ⟨x, hxP, hxN, -, hxz⟩ := hd.exists_moving_elt hz hB0
  have hxM : x ∈ M := hd.cfg.ext.sylow_le hxP
  have hxzC : x * z * x⁻¹ ∈ C₀ := (Subgroup.mem_normalizer_iff.mp (hMC hxM) z).mp hzC
  have hxzR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz.1
  obtain ⟨t₀, ht₀, i, hti⟩ := hdec _ hxzR
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    apply hxz
    rw [hti, one_mul]
    exact Subgroup.npow_mem_zpowers z i
  have ht₀C : t₀ ∈ C₀ := by
    have h1 : t₀ * z ^ i * (z ^ i)⁻¹ ∈ C₀ :=
      C₀.mul_mem (hti ▸ hxzC) (C₀.inv_mem (C₀.pow_mem hzC i))
    simpa using h1
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]; exact C₀.one_mem
  obtain ⟨n, hnN, -, -, hnt⟩ :=
    hd.exists_conj_eq_of_l34 hOrb hz hdec hp3 hA6 hcard t₀ ht₀ ht₀1 s hs hs1
  have hnM : n ∈ M := hd.cfg.ext.normalizer_le hnN
  rw [← hnt]
  exact (Subgroup.mem_normalizer_iff.mp (hMC hnM) t₀).mp ht₀C

omit [Finite G] in
theorem L34Squeeze.mem_normalizer_inf_centralizer {A Y : Subgroup G} {m : G}
    (hmA : m ∈ Subgroup.normalizer (A : Set G)) (hmY : m ∈ Subgroup.normalizer (Y : Set G)) :
    m ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  have hY := Subgroup.mem_normalizer_iff.mp hmY
  have hA := Subgroup.mem_normalizer_iff.mp hmA
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨hhA, hhC⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨(hA h).mp hhA, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hhC ⊢
    intro y hy
    have hy' : m⁻¹ * y * m ∈ Y := by
      have := (hY (m⁻¹ * y * m)).mpr (by simpa [mul_assoc] using hy)
      exact this
    have := hhC _ hy'
    calc y * (m * h * m⁻¹) = m * ((m⁻¹ * y * m) * h) * m⁻¹ := by group
      _ = m * (h * (m⁻¹ * y * m)) * m⁻¹ := by rw [this]
      _ = m * h * m⁻¹ * y := by group
  · intro hh
    obtain ⟨hhA, hhC⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨(hA h).mpr hhA, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hhC ⊢
    intro y hy
    have hy' : m * y * m⁻¹ ∈ Y := (hY y).mp hy
    have := hhC _ hy'
    have e : m * (y * h) * m⁻¹ = m * (h * y) * m⁻¹ := by
      calc m * (y * h) * m⁻¹ = m * y * m⁻¹ * (m * h * m⁻¹) := by group
        _ = m * h * m⁻¹ * (m * y * m⁻¹) := this
        _ = m * (h * y) * m⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)

theorem D1OneSmallData.false_of_fixed_normal_core (hUE : KFactUPrimeExc)
    (hOrb : KFactSmallOrbits) (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K)
    (hNM : M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M)
    {A : Subgroup G} (hAS : A ≤ centerOf (pCoreOf 2 H)) (hA1 : A ≠ ⊥)
    (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hYM : M ≤ Subgroup.normalizer
      ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G))
    (hsyl : IsSylowTwoOf (pCoreOf 2 (H ⊓ M)) (M ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) ∨
      z ∈ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) : Subgroup G) : Set G)) :
    False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  set U := pCoreOf 2 (H ⊓ M) with hUdef
  set S := pCoreOf 2 H with hSdef
  set Y := A ⊓ Subgroup.centralizer (U : Set G) with hYdef
  set C₀ := M ⊓ Subgroup.centralizer (Y : Set G) with hC₀def
  have hU2 : IsPGroup 2 U := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have hS2 : IsPGroup 2 S := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hA2 : IsPGroup 2 A := hS2.to_le (hAS.trans inf_le_left)
  have hUHM : U ≤ H ⊓ M := RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)
  have hHMU : H ⊓ M ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hMC : M ≤ Subgroup.normalizer (C₀ : Set G) := fun m hm =>
    L34Squeeze.mem_normalizer_inf_centralizer (Subgroup.le_normalizer hm) (hYM hm)
  have hNU : M ⊓ Subgroup.normalizer (U : Set G) ≤ H := by rw [hNM]; exact inf_le_left
  have hTC : d1LiftX 3 H R K ≤ C₀ := by
    rcases hsyl with hsyl | hzC
    · exact hd.d1LiftX_le_of_squeeze hOrb hz hB0 hdec hexpR rfl hA6 hcard inf_le_left hMC hsyl
        hNU
    · exact hd.d1LiftX_le_of_czElt_mem hOrb hz hB0 hdec rfl hA6 hcard hMC
        (Subgroup.mem_inf.mpr ⟨hd.cfg.ext.le_M hz.1, hzC⟩)
  have hTA : ∀ t ∈ d1LiftX 3 H R K, ∀ a ∈ A, t * a = a * t := by
    intro t ht
    have htH : t ∈ H := d1LiftX_le_H 3 H R K ht
    have ht3 : t ^ 3 = 1 := hexpR t (d1LiftX_le 3 H R K ht)
    refine L34Squeeze.commute_of_commute_fixed (A := A) (U := U) ?_ hA2 hU2 ?_ ?_ ?_ ?_ ?_
    · intro a ha b hb
      obtain ⟨-, haC⟩ := Subgroup.mem_inf.mp (hAS ha)
      obtain ⟨hbS, -⟩ := Subgroup.mem_inf.mp (hAS hb)
      exact (Subgroup.mem_centralizer_iff.mp haC b hbS).symm
    · intro a ha
      exact (Subgroup.mem_normalizer_iff.mp (hHA htH) a).mp ha
    · intro u hu a ha
      exact (Subgroup.mem_normalizer_iff.mp (hHA (hUHM hu).1) a).mp ha
    · exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ht3)
    · intro u hu a ha
      have hcS := hd.commutator_mem_twoCore_of_d1LiftX hUE rfl hL hu ht
      obtain ⟨-, haC⟩ := Subgroup.mem_inf.mp (hAS ha)
      exact (Subgroup.mem_centralizer_iff.mp haC _ hcS)
    · intro a ha haU
      have haY : a ∈ Y := Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_iff.mpr haU⟩
      obtain ⟨-, htC⟩ := Subgroup.mem_inf.mp (hTC ht)
      exact (Subgroup.mem_centralizer_iff.mp htC a haY).symm
  set X := H ⊓ Subgroup.centralizer (A : Set G) with hXdef
  have hXn : H ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    L34Squeeze.mem_normalizer_inf_centralizer (Subgroup.le_normalizer hh) (hHA hh)
  have hTX : d1LiftX 3 H R K ≤ X := fun t ht =>
    Subgroup.mem_inf.mpr ⟨d1LiftX_le_H 3 H R K ht,
      Subgroup.mem_centralizer_iff.mpr fun a ha => (hTA t ht a ha).symm⟩
  have hXM := hd.not_le_of_normal_of_d1LiftX_le hUE rfl hL hXn hTX
  have hHY : H ≤ X ⊔ (H ⊓ M) := by
    rcases hd.le_or_le_of_l34 hUE rfl hL (le_sup_right : H ⊓ M ≤ X ⊔ (H ⊓ M))
      (sup_le inf_le_left inf_le_left) with hYM' | hHY
    · exact absurd (le_sup_left.trans hYM') hXM
    · exact hHY
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := by
    intro x hx
    obtain ⟨-, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hcomm : ∀ b ∈ Y, x * b * x⁻¹ = b := fun b hb => by
      rw [← Subgroup.mem_centralizer_iff.mp hxC b (Subgroup.mem_inf.mp hb).1]; group
    constructor
    · intro ha; rw [hcomm a ha]; exact ha
    · intro ha
      have h1 := hcomm _ ha
      have h2 : x⁻¹ * (x * a * x⁻¹) * x = x * a * x⁻¹ := by
        calc x⁻¹ * (x * a * x⁻¹) * x = x⁻¹ * (x * (x * a * x⁻¹) * x⁻¹) * x := by rw [h1]
          _ = x * a * x⁻¹ := by group
      have : x⁻¹ * (x * a * x⁻¹) * x = a := by group
      rw [← this, h2]
      exact ha
  have hHMY : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    L34Squeeze.mem_normalizer_inf_centralizer (hHA hx.1) (hHMU hx)
  have hHYn : H ≤ Subgroup.normalizer (Y : Set G) := hHY.trans (sup_le hXY hHMY)
  obtain ⟨a, haA, ha1, hac⟩ := L34Squeeze.exists_ne_one_commute hU2 hA2
    (fun u hu => hHA (hUHM hu).1) hA1
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have : a ∈ Y := Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_centralizer_iff.mpr hac⟩
    rw [hbot] at this
    exact ha1 ((Subgroup.mem_bot).mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Y : Set G)) :=
    ⟨Y, hY1, hA2.to_le inf_le_left, rfl⟩
  have hNH := hd.cfg.ext.maxTwoLocal_H.2 _ hloc hHYn
  have hMH : M ≤ H := hNH ▸ hYM
  exact (hd.cfg.ext.inf_lt_right).ne (inf_eq_right.mpr hMH)

end CFSG.AGLEmbedding
