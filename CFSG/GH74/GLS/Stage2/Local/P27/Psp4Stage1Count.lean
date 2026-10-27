module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Num

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local.P27

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem cnt_bar_injective {X : Subgroup G} (hX : X ≤ Cen z) (hX2 : IsPGroup 2 ↥X) :
    Function.Injective ((toBar z).comp (Subgroup.inclusion hX)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro s hs
  have h1 : Subgroup.inclusion hX s ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar]; exact hs
  have hd : orderOf (⟨Subgroup.inclusion hX s, h1⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
      Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hd
  have hodd : Odd (orderOf (Subgroup.inclusion hX s)) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))) hd
  rw [orderOf_injective _ (Subgroup.inclusion_injective hX)] at hodd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hX2) s
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    exact orderOf_eq_one_iff.1 (by simpa using hk)
  · exact absurd hodd (by
      rw [Nat.not_odd_iff_even]
      exact (Nat.even_pow.2 ⟨by norm_num, by omega⟩))

theorem cnt_card_barOf {X : Subgroup G} (hX : X ≤ Cen z) (hX2 : IsPGroup 2 ↥X) :
    Nat.card ↥(barOf z X) = Nat.card ↥X := by
  have hinj := cnt_bar_injective hX hX2
  have hr : ((toBar z).comp (Subgroup.inclusion hX)).range = barOf z X := by
    ext x
    simp only [MonoidHom.mem_range, barOf, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hX y, y.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite G] in
theorem cnt_two_pow (hS : IsSylowOf 2 S (Cen z)) (c : ↥(Cen z)) (hc : (c : G) ∈ S) :
    ∃ k : ℕ, c ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (S_isPGroup hS)) ⟨(c : G), hc⟩
  refine ⟨k, ?_⟩
  have : (⟨(c : G), hc⟩ : ↥S) ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem cnt_barOf_RC (hS : IsSylowOf 2 S (Cen z)) : barOf z (RC S z) = barOf z S ⊓ LBar z := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, hc.1, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, hc.2, rfl⟩
  · rintro x ⟨⟨c, hcS, rfl⟩, hxL⟩
    refine ⟨c, ⟨hcS, ?_⟩, rfl⟩
    obtain ⟨k, hk⟩ := cnt_two_pow hS c hcS
    exact (Stage1.Thm6.Prod.mem_LC_iff_of_pElt (z := z) c hk).2 hxL

theorem cnt_card_barOf_RC (hS : IsSylowOf 2 S (Cen z)) :
    Nat.card ↥(barOf z S ⊓ LBar z) = Nat.card ↥(RC S z) := by
  rw [← cnt_barOf_RC hS]
  exact cnt_card_barOf (inf_le_left.trans (S_le_Cen hS)) ((S_isPGroup hS).to_le inf_le_left)

theorem cnt_two_pow_index (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂) :
    2 ^ ((LBar z).index).factorization 2 = (RC S z).relIndex S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := LBar_normal z
  obtain ⟨hR, -, -⟩ := bar_sylow_structure hS hP
  have hSB := sylow_barS hS
  have hS2 := S_isPGroup hS
  have hSC := S_le_Cen hS
  have hc1 : Nat.card ↥(barOf z S) = 2 ^ (Nat.card (CentralizerBar z)).factorization 2 := by
    have := hSB.card_eq
    rwa [Subgroup.card_top] at this
  have hc2 : Nat.card ↥(barOf z S ⊓ LBar z) = 2 ^ (Nat.card ↥(LBar z)).factorization 2 :=
    hR.card_eq
  rw [cnt_card_barOf hSC hS2] at hc1
  rw [cnt_card_barOf_RC hS] at hc2
  have hm : (RC S z).relIndex S * Nat.card ↥(RC S z) = Nat.card ↥S := by
    have := Subgroup.relIndex_mul_card (RC S z) S
    rwa [inf_eq_left.2 (show RC S z ≤ S from inf_le_left)] at this
  have hCbar : Nat.card (CentralizerBar z) = Nat.card ↥(LBar z) * (LBar z).index :=
    (Subgroup.card_mul_index _).symm
  have hf : (Nat.card (CentralizerBar z)).factorization 2 =
      (Nat.card ↥(LBar z)).factorization 2 + ((LBar z).index).factorization 2 := by
    rw [hCbar, Nat.factorization_mul Nat.card_pos.ne' Subgroup.FiniteIndex.index_ne_zero,
      Finsupp.add_apply]
  have hpos : 0 < Nat.card ↥(RC S z) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hm, hc1, hf, pow_add, hc2, mul_comm]

theorem card_le_two_pow_mul_relIndex (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) {P₁ : Subgroup G} {a : ℕ}
    (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype) (hPc : Nat.card ↥P₁ = 2 ^ a)
    {T : Subgroup G} (hT : IsPGroup 2 ↥T) (hTY : T ≤ centralizer ({t * z, z} : Set G)) :
    Nat.card ↥T ≤ 2 ^ a * (RC S z).relIndex S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC := S_le_Cen hS
  have htC : t ∈ Cen z := hSC ht
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht2 : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hYC : centralizer ({t * z, z} : Set G) ≤ Cen z := fun y hy =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_centralizer_iff.1 hy z (by simp))
  have hYt : ∀ y ∈ centralizer ({t * z, z} : Set G), y * t = t * y := by
    intro y hy
    have h1 : t * z * y = y * (t * z) := Subgroup.mem_centralizer_iff.1 hy (t * z) (by simp)
    have h2 : z * y = y * z := Subgroup.mem_centralizer_iff.1 hy z (by simp)
    calc y * t = y * t * (z * z) := by rw [hzz, mul_one]
      _ = (y * (t * z)) * z := by group
      _ = (t * z * y) * z := by rw [h1]
      _ = t * (z * y) * z := by group
      _ = t * (y * z) * z := by rw [h2]
      _ = t * y * (z * z) := by group
      _ = t * y := by rw [hzz, mul_one]
  have hTC : T ≤ Cen z := hTY.trans hYC
  set tb : CentralizerBar z := toBar z ⟨t, htC⟩ with htb
  let Yb : Subgroup (CentralizerBar z) := centralizer ({tb} : Set (CentralizerBar z))
  let ψ : ↥T →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hTC)
  have hψ : Function.Injective ψ := cnt_bar_injective hTC hT
  have hTb : ψ.range ≤ Yb := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show toBar z (Subgroup.inclusion hTC x) * toBar z ⟨t, htC⟩ =
      toBar z ⟨t, htC⟩ * toBar z (Subgroup.inclusion hTC x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYt x (hTY x.2))
  have hCL : CL z t = LBar z ⊓ Yb := by
    rw [Stage1.Main.CL_eq_centralizer htC hP.prod.1, hP.prod.1, inf_comm]
  have hcardT : Nat.card ↥T = Nat.card ↥ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  have hdvd : Nat.card ↥ψ.range ∣ Nat.card ↥Yb := Subgroup.card_dvd_of_le hTb
  have hYb : (LBar z).relIndex Yb * Nat.card ↥(CL z t) = Nat.card ↥Yb := by
    rw [hCL]; exact Subgroup.relIndex_mul_card (LBar z) Yb
  have := LBar_normal z
  have hrel : (LBar z).relIndex Yb ∣ (LBar z).index := Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨κ, hκ⟩ := (IsPGroup.iff_card).1 hT
  have hκle : κ ≤ (Nat.card ↥Yb).factorization 2 := by
    have h2 : 2 ^ κ ∣ Nat.card ↥Yb := by rw [← hκ, hcardT]; exact hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
  have hrel0 : (LBar z).relIndex Yb ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hYb
    exact Nat.card_pos.ne' hYb.symm
  have hf2 : (Nat.card ↥Yb).factorization 2 ≤ a + ((LBar z).index).factorization 2 := by
    rw [← hYb, Nat.factorization_mul hrel0 Nat.card_pos.ne', Finsupp.add_apply,
      factorization_card_CL hS hP hsw ht2 hP₁ hPc]
    have h3 := (Nat.factorization_le_iff_dvd hrel0 Subgroup.FiniteIndex.index_ne_zero).2 hrel
    have h4 := h3 2
    omega
  calc Nat.card ↥T = 2 ^ κ := hκ
    _ ≤ 2 ^ (a + ((LBar z).index).factorization 2) :=
        Nat.pow_le_pow_right (by norm_num) (hκle.trans hf2)
    _ = 2 ^ a * 2 ^ ((LBar z).index).factorization 2 := pow_add _ _ _
    _ = 2 ^ a * (RC S z).relIndex S := by rw [cnt_two_pow_index hS hP]

theorem isSylowOf_centralizer_of_card (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) {P₁ : Subgroup G} {a : ℕ}
    (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype) (hPc : Nat.card ↥P₁ = 2 ^ a)
    (hcard : 2 ^ a * (RC S z).relIndex S ≤ Nat.card ↥(S ⊓ centralizer ({t} : Set G))) :
    IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({t * z, z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hKY : S ⊓ centralizer ({t} : Set G) ≤ centralizer ({t * z, z} : Set G) := by
    rintro y ⟨hyS, hyt⟩
    have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.1 ((S_le_Cen hS) hyS) z (by simp)
    have hyt' : t * y = y * t := Subgroup.mem_centralizer_iff.1 hyt t (by simp)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · calc t * z * y = t * (z * y) := by group
        _ = t * (y * z) := by rw [hyz]
        _ = (t * y) * z := by group
        _ = (y * t) * z := by rw [hyt']
        _ = y * (t * z) := by group
    · exact hyz
  have hK2 : IsPGroup 2 ↥(S ⊓ centralizer ({t} : Set G)) := (S_isPGroup hS).to_le inf_le_left
  obtain ⟨P, hPY⟩ := exists_isSylowOf 2 (centralizer ({t * z, z} : Set G))
  have hPcard := hPY.card_eq
  have h1 : Nat.card ↥P ≤ 2 ^ a * (RC S z).relIndex S :=
    card_le_two_pow_mul_relIndex hz hS hP ht htc hsw hP₁ hPc hPY.isPGroup hPY.le
  have hKdvd := Subgroup.card_dvd_of_le hKY
  obtain ⟨κ, hκ⟩ := (IsPGroup.iff_card).1 hK2
  have hκle : κ ≤ (Nat.card ↥(centralizer ({t * z, z} : Set G))).factorization 2 := by
    have h2 : 2 ^ κ ∣ Nat.card ↥(centralizer ({t * z, z} : Set G)) := by rw [← hκ]; exact hKdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
  have hκν : (Nat.card ↥(centralizer ({t * z, z} : Set G))).factorization 2 ≤ κ := by
    have h2 : 2 ^ (Nat.card ↥(centralizer ({t * z, z} : Set G))).factorization 2 ≤ 2 ^ κ := by
      rw [← hPcard, ← hκ]
      exact h1.trans hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  refine isSylowOf_of_card hKY ?_
  rw [hκ]
  congr 1
  omega

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
