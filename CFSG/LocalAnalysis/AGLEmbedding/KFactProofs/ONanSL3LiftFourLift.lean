module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCentre
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftGrp
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour

open CFSG
open scoped commutatorElement

section FixedPoint

variable {X : Type*} [Group X]

theorem exists_fixed_mul {Z : Subgroup X} [Finite Z] (hZ : IsPGroup 2 Z) {f : X}
    (hf3 : f * f * f = 1) (hfZ : ∀ z ∈ Z, f * z * f⁻¹ ∈ Z) {k : X}
    (hu : k⁻¹ * (f * k * f⁻¹) ∈ Z) : ∃ ζ ∈ Z, f * (k * ζ) * f⁻¹ = k * ζ := by
  classical
  set u : X := k⁻¹ * (f * k * f⁻¹) with hu_def
  have hfk : f * k * f⁻¹ = k * u := by rw [hu_def]; group
  have hnorm : u * (f * u * f⁻¹) * (f * f * u * (f * f)⁻¹) = 1 := by
    have h1 : k = (f * f * f) * k * (f * f * f)⁻¹ := by rw [hf3]; group
    have h2 : (f * f * f) * k * (f * f * f)⁻¹ =
        k * (u * (f * u * f⁻¹) * (f * f * u * (f * f)⁻¹)) := by
      rw [hu_def]; group
    rw [h2] at h1
    exact (mul_eq_left.1 h1.symm)
  let T : Function.End Z := fun z => ⟨u * (f * (z : X) * f⁻¹), Z.mul_mem hu (hfZ z z.2)⟩
  have hT3 : ∀ z : Z, T (T (T z)) = z := by
    intro z
    apply Subtype.ext
    change u * (f * (u * (f * (u * (f * (z : X) * f⁻¹)) * f⁻¹)) * f⁻¹) = z
    have e1 : u * (f * (u * (f * (u * (f * (z : X) * f⁻¹)) * f⁻¹)) * f⁻¹) =
        (u * (f * u * f⁻¹) * (f * f * u * (f * f)⁻¹)) *
          ((f * f * f) * (z : X) * (f * f * f)⁻¹) := by
      group
    rw [e1, hnorm, hf3]
    group
  have hTpow : T ^ 3 ^ 1 = 1 := by
    funext z
    change T (T (T z)) = z
    exact hT3 z
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype Z := Fintype.ofFinite Z
  have hcard := Equiv.Perm.card_fixedPoints_modEq hTpow
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hne : Fintype.card (Function.fixedPoints T) ≠ 0 := by
    intro h0
    rw [h0] at hcard
    have h3 : 3 ∣ Fintype.card Z := (Nat.modEq_zero_iff_dvd).1 (by simpa using hcard)
    rw [Fintype.card_eq_nat_card, hn] at h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  obtain ⟨⟨z₀, hz₀⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  have hz₀' : u * (f * (z₀ : X) * f⁻¹) = z₀ := congrArg Subtype.val hz₀
  refine ⟨z₀, z₀.2, ?_⟩
  calc f * (k * (z₀ : X)) * f⁻¹ = (f * k * f⁻¹) * (f * (z₀ : X) * f⁻¹) := by group
    _ = k * (u * (f * (z₀ : X) * f⁻¹)) := by rw [hfk, mul_assoc]
    _ = k * (z₀ : X) := by rw [hz₀']

end FixedPoint

section Quotient

variable {X X' : Type} [Group X] [Finite X] [Group X']

omit [Finite X] in
theorem eq_one_of_mem_sylow_of_mem_twoPart (R : Sylow 3 X) {K : Subgroup X} {r : X}
    (hr : r ∈ (R : Subgroup X)) (h : r ∈ twoPart K) : r = 1 := by
  obtain ⟨m, hm⟩ := R.2 ⟨r, hr⟩
  obtain ⟨-, -, n, hn⟩ := h
  have hm' : r ^ 3 ^ m = 1 := congrArg Subtype.val hm
  have h1 : orderOf r ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have h2 : orderOf r ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (3 ^ m) (2 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

variable {π : X →* X'} {K : Subgroup X} [K.Normal]

omit [Finite X] in
theorem map_mem_centralizer_iff (hK : commutator K = ⊤) (hker : π.ker = twoPart K) (x : X) :
    π x ∈ Subgroup.centralizer ((K.map π : Subgroup X') : Set X') ↔
      x ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h κ hκ
    have hall : ∀ κ ∈ K, x * κ * x⁻¹ * κ⁻¹ ∈ twoPart K := by
      intro κ hκ
      have h1 := h (π κ) (Subgroup.mem_map_of_mem π hκ)
      rw [← hker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, ← h1, mul_inv_cancel_right]
    have h4 := conj_eq_of_comm_mem hK (centralIn_twoPart K) hall κ hκ
    calc κ * x = (x * κ * x⁻¹) * x := by rw [h4]
      _ = x * κ := by group
  · intro h k' hk'
    obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hk'
    rw [← map_mul, ← map_mul, h κ hκ]

@[expose] def fixedSet (A K : Subgroup X) : Set K :=
  {k : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧ f * (k : X) * f⁻¹ = k}

omit [K.Normal] [Finite X] in
theorem injOn_sylow (R : Sylow 3 X) (hker : π.ker = twoPart K) {a b : X}
    (ha : a ∈ (R : Subgroup X)) (hb : b ∈ (R : Subgroup X)) (h : π a = π b) : a = b := by
  have h1 : a * b⁻¹ ∈ twoPart K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have h2 := eq_one_of_mem_sylow_of_mem_twoPart R ((R : Subgroup X).mul_mem ha
    ((R : Subgroup X).inv_mem hb)) h1
  exact mul_inv_eq_one.1 h2

omit [K.Normal] [Finite X] in
theorem exists_preimage_elemAbelian (R : Sylow 3 X) (hker : π.ker = twoPart K)
    {A' : Subgroup X'} (hA'R : A' ≤ (R : Subgroup X).map π) (hA'e : Open.IsElemAbelian 3 A')
    (hA'card : Nat.card A' = 27) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ A.map π = A' ∧ Open.IsElemAbelian 3 A ∧
      Nat.card A = 27 := by
  classical
  set A : Subgroup X := A'.comap π ⊓ (R : Subgroup X) with hA
  have hAR : A ≤ (R : Subgroup X) := inf_le_right
  have hAmap : A.map π = A' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro a' ha'
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 (hA'R ha')
      exact ⟨r, ⟨ha', hr⟩, rfl⟩
  have hinj : ∀ a ∈ A, ∀ b ∈ A, π a = π b → a = b := fun a ha b hb h =>
    injOn_sylow R hker (hAR ha) (hAR hb) h
  refine ⟨A, hAR, hAmap, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hinj _ (A.mul_mem a.2 b.2) _ (A.mul_mem b.2 a.2)
    have h := hA'e.1.is_comm.comm (⟨π a, a.2.1⟩ : A') ⟨π b, b.2.1⟩
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  · have hxR : x ^ 3 ∈ (R : Subgroup X) := (R : Subgroup X).pow_mem (hAR hx) 3
    refine injOn_sylow R hker hxR (R : Subgroup X).one_mem ?_
    rw [map_pow, map_one]
    exact hA'e.2 (π x) hx.1
  · have hbij : Function.Bijective (fun a : A => (⟨π a, a.2.1⟩ : A')) := by
      constructor
      · intro a b h
        exact Subtype.ext (hinj _ a.2 _ b.2 (congrArg Subtype.val h))
      · intro a'
        have : (a' : X') ∈ A.map π := by rw [hAmap]; exact a'.2
        obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 this
        exact ⟨⟨y, hy⟩, Subtype.ext hya⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), hA'card]

omit [K.Normal] in
theorem pRank_map_sylow [Finite X'] (R : Sylow 3 X) (hker : π.ker = twoPart K) :
    Open.pRank 3 ((R : Subgroup X).map π) = Open.pRank 3 (R : Subgroup X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hinj : Function.Injective (π.comp (R : Subgroup X).subtype) := fun a b h =>
    Subtype.ext (injOn_sylow R hker a.2 b.2 h)
  have e : (R : Subgroup X) ≃* (π.comp (R : Subgroup X).subtype).range :=
    MonoidHom.ofInjective hinj
  have e' : (R : Subgroup X) ≃* ((R : Subgroup X).map π) :=
    e.trans (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  rw [← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp,
    ← CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp,
    CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e').symm

theorem closure_fixedSet_eq_top_of_map (hK : commutator K = ⊤)
    (hker : π.ker = twoPart K) {A : Subgroup X} (hA3 : ∀ a ∈ A, a * a * a = 1)
    (hgen : Subgroup.closure (fixedSet (A.map π) (K.map π)) = ⊤) :
    Subgroup.closure (fixedSet A K) = ⊤ := by
  classical
  let θ : K →* K.map π := π.subgroupMap K
  have hθ : Function.Surjective θ := π.subgroupMap_surjective K
  have hθval : ∀ κ : K, ((θ κ : K.map π) : X') = π (κ : X) := fun κ => rfl
  have hlift : ∀ k' ∈ fixedSet (A.map π) (K.map π), ∃ k ∈ fixedSet A K, θ k = k' := by
    rintro k' ⟨f', hf'A, hf'C, hfix⟩
    obtain ⟨f, hfA, rfl⟩ := Subgroup.mem_map.1 hf'A
    obtain ⟨κ₀, rfl⟩ := hθ k'
    have hfC : f ∉ Subgroup.centralizer (K : Set X) := fun h =>
      hf'C ((map_mem_centralizer_iff hK hker f).2 h)
    have hfix' : π (f * (κ₀ : X) * f⁻¹) = π κ₀ := by
      rw [map_mul, map_mul, map_inv]
      exact hfix
    have hu : (κ₀ : X)⁻¹ * (f * κ₀ * f⁻¹) ∈ twoPart K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hfix', inv_mul_cancel]
    obtain ⟨ζ, hζ, hfix''⟩ := exists_fixed_mul (isPGroup_twoPart K) (hA3 f hfA)
      (fun z hz => (inferInstance : (twoPart K).Normal).conj_mem z hz f) hu
    refine ⟨⟨(κ₀ : X) * ζ, K.mul_mem κ₀.2 ((centralIn_twoPart K).1 hζ)⟩, ⟨f, hfA, hfC, hfix''⟩, ?_⟩
    apply Subtype.ext
    have hπζ : π ζ = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hζ
    change π ((κ₀ : X) * ζ) = π κ₀
    rw [map_mul, hπζ, mul_one]
  have hmap : (Subgroup.closure (fixedSet A K)).map θ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine (Subgroup.closure_le _).2 fun k' hk' => ?_
    obtain ⟨k, hk, rfl⟩ := hlift k' hk'
    exact Subgroup.mem_map_of_mem θ (Subgroup.subset_closure hk)
  set L : Subgroup X := (Subgroup.closure (fixedSet A K)).map K.subtype with hL
  have hLK : L ≤ K := by
    rintro _ ⟨l, -, rfl⟩
    exact l.2
  have hdec : ∀ κ ∈ K, ∃ z ∈ twoPart K, ∃ l ∈ L, κ = z * l := by
    intro κ hκ
    have h1 : θ ⟨κ, hκ⟩ ∈ (Subgroup.closure (fixedSet A K)).map θ := by rw [hmap]; trivial
    obtain ⟨l, hl, hlθ⟩ := Subgroup.mem_map.1 h1
    refine ⟨κ * (l : X)⁻¹, ?_, (l : X), ⟨l, hl, rfl⟩, by group⟩
    have h2 : π (l : X) = π κ := congrArg Subtype.val hlθ
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  have hKL := le_of_perfect_of_dec hK hLK (centralIn_twoPart K) hdec
  rw [eq_top_iff]
  intro κ _
  obtain ⟨l, hl, hlκ⟩ := Subgroup.mem_map.1 (hKL κ.2)
  have hlκ' : l = κ := Subtype.ext hlκ
  rw [← hlκ']
  exact hl

theorem exists_generating_of_quotient [Finite X'] (hπ : Function.Surjective π)
    (R : Sylow 3 X) (hK : commutator K = ⊤) (hker : π.ker = twoPart K) {z : X}
    (hzc : z ∈ Subgroup.center X) (hzK : z ∈ K) (hz3 : orderOf z = 3)
    (hΩ : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z)
    (hrank : Open.pRank 3 (R : Subgroup X) = 3)
    (H : ∀ (R' : Sylow 3 X') (z' : X') [(K.map π).Normal], z' ∈ Subgroup.center X' →
      z' ∈ K.map π → orderOf z' = 3 →
      (∀ c ∈ (R' : Subgroup X') ⊓ Subgroup.centralizer ((K.map π : Subgroup X') : Set X'),
        orderOf c = 3 → c ∈ Subgroup.zpowers z') →
      Open.pRank 3 (R' : Subgroup X') = 3 →
      ∃ A' : Subgroup X', A' ≤ (R' : Subgroup X') ∧ Open.IsElemAbelian 3 A' ∧ Nat.card A' = 27 ∧
        Subgroup.closure (fixedSet A' (K.map π)) = ⊤) :
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure (fixedSet A K) = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (K.map π).Normal := Subgroup.Normal.map ‹K.Normal› π hπ
  set R' : Sylow 3 X' := Sylow.mapSurjective hπ R with hR'
  have hR'coe : (R' : Subgroup X') = (R : Subgroup X).map π := rfl
  have hz'c : π z ∈ Subgroup.center X' := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hπ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc y]
  have hz'K : π z ∈ K.map π := Subgroup.mem_map_of_mem π hzK
  have hπz1 : π z ≠ 1 := by
    intro h
    have hz2 : z ∈ twoPart K := by rw [← hker]; exact h
    obtain ⟨-, -, n, hn⟩ := hz2
    have h3 : 3 ∣ 2 ^ n := hz3 ▸ orderOf_dvd_of_pow_eq_one hn
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hz'3 : orderOf (π z) = 3 := by
    refine orderOf_eq_prime ?_ hπz1
    rw [← map_pow, ← hz3, pow_orderOf_eq_one, map_one]
  have hΩ' : ∀ c ∈ (R' : Subgroup X') ⊓ Subgroup.centralizer ((K.map π : Subgroup X') : Set X'),
      orderOf c = 3 → c ∈ Subgroup.zpowers (π z) := by
    rintro c ⟨hcR, hcC⟩ hc3
    rw [hR'coe] at hcR
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hcR
    have hrC : r ∈ Subgroup.centralizer (K : Set X) := (map_mem_centralizer_iff hK hker r).1 hcC
    have hr3 : r ^ 3 = 1 := by
      refine injOn_sylow R hker ((R : Subgroup X).pow_mem hr 3) (R : Subgroup X).one_mem ?_
      rw [map_pow, map_one, ← hc3]
      exact pow_orderOf_eq_one _
    have hr1 : r ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hc3
      omega
    have hrord : orderOf r = 3 := orderOf_eq_prime hr3 hr1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hΩ r ⟨hr, hrC⟩ hrord)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn, map_zpow]⟩
  have hrank' : Open.pRank 3 (R' : Subgroup X') = 3 := by
    rw [hR'coe, pRank_map_sylow R hker, hrank]
  obtain ⟨A', hA'R, hA'e, hA'card, hA'gen⟩ := H R' (π z) hz'c hz'K hz'3 hΩ' hrank'
  obtain ⟨A, hAR, hAmap, hAe, hAcard⟩ :=
    exists_preimage_elemAbelian R hker (hR'coe ▸ hA'R) hA'e hA'card
  refine ⟨A, hAR, hAe, SL3Lift.three_le_pRank_of_card hAe hAcard, ?_⟩
  refine closure_fixedSet_eq_top_of_map hK hker (fun a ha => ?_) (hAmap ▸ hA'gen)
  have := hAe.2 a ha
  rw [pow_three'] at this
  exact this

end Quotient

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour
