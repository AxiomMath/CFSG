module

public import CFSG.Quasithin.H13.U3S13473A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_iii_z_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hiii : Concl1347iii T H₁ H₂) :
    ∃ z : MulAut ↥(v0Of T H₁ H₂), z ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      fixAutU3 z = ⊥ ∧
      (∀ β ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), β * z * β⁻¹ = z ∨ β * z * β⁻¹ = z⁻¹) ∧
      ∃ β ∈ autOn T (v0Of T H₁ H₂), β * z * β⁻¹ = z⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, -, -, -, -, hc₁, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨h108, h4⟩ := s1347_iii_index S hH₀ hiii
  obtain ⟨hcent, hext, -, -⟩ := hiii
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hQT : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hT4 : Nat.card ↥T = 4 * Nat.card ↥(pCoreOf 2 (H₁ ⊔ H₂)) := by
    have h1 := relIndex_mul_card (pCoreOf 2 (H₁ ⊔ H₂)) T
    rw [inf_eq_left.2 hQT, h4] at h1
    exact h1.symm
  obtain ⟨K, hKX, hKn, hK⟩ := s1347_aut_structure S hH₀ hcent.symm hext
  obtain ⟨x, y, hz1, hzc, hexp, hzn⟩ := s1347_exists_z hKn hK
  have : IsMulCommutative ↥(v0Of T H₁ H₂) := hred.2.2.1.1
  have hW2 : ∀ w : ↥(v0Of T H₁ H₂), w ^ 2 = 1 := fun w => Subtype.ext (hred.2.2.1.2 w w.2)
  have h6k := card_range_commAutU3 hW2 hzc hexp
  set z : MulAut ↥(v0Of T H₁ H₂) := ((⁅x, y⁆ : ↥K) : MulAut ↥(v0Of T H₁ H₂)) with hzdef
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hz3 : z ^ 3 = 1 := by
    have := congrArg Subtype.val (hexp ⁅x, y⁆)
    simpa using this
  obtain ⟨-, hzfix⟩ := s1347_card_V0 S h hH₀ hc₁ hT4 hz1' hz3 hzn h6k
  refine ⟨z, hKX (⁅x, y⁆ : ↥K).2, hz3, hz1', hzfix, hzn, ?_⟩

  by_contra hno
  push Not at hno
  have hTX : autOn T (v0Of T H₁ H₂) ≤ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := fun β hβ => by
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hβ
    exact Setup.mem_autOn_iff.2 ⟨g, hH₀.1 hg, rfl⟩
  have hTz : ∀ β ∈ autOn T (v0Of T H₁ H₂), β * z * β⁻¹ = z := fun β hβ =>
    (hzn β (hTX hβ)).resolve_right (hno β hβ)
  set C := autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) ⊓ centralizer ({z} : Set (MulAut ↥(v0Of T H₁ H₂)))
    with hCdef
  have hKC : K ≤ C := fun κ hκ => ⟨hKX hκ, mem_centralizer_singleton_iff.2 (by
    have h1 := congrArg Subtype.val (hzc ⟨κ, hκ⟩).eq
    simpa only [Subgroup.coe_mul] using h1)⟩
  have hTC : autOn T (v0Of T H₁ H₂) ≤ C := fun β hβ => ⟨hTX hβ, by
    show β ∈ centralizer ({z} : Set (MulAut ↥(v0Of T H₁ H₂)))
    rw [mem_centralizer_singleton_iff]
    have h1 := hTz β hβ
    calc β * z = β * z * β⁻¹ * β := by group
      _ = z * β := by rw [h1]⟩
  have hX108 : Nat.card ↥(autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂)) = 108 := by
    rw [card_autOn_eq_relIndex hP, ← hcent, h108]
  have hT4' : Nat.card ↥(autOn T (v0Of T H₁ H₂)) = 4 := by
    rw [card_autOn_eq_relIndex (hH₀.1.trans hP), s1347_T_inf_centralizer S h hH₀, h4]
  have hK27 : Nat.card ↥K = 27 := by rw [hK.2.1]; norm_num
  have h27 : 27 ∣ Nat.card ↥C := hK27 ▸ card_dvd_of_le hKC
  have h4C : 4 ∣ Nat.card ↥C := hT4' ▸ card_dvd_of_le hTC
  have h108C : 108 ∣ Nat.card ↥C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 4) h27 h4C
  have hCeq : C = autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) := by
    refine eq_of_le_of_card_ge inf_le_left ?_
    rw [hX108]
    exact Nat.le_of_dvd Nat.card_pos h108C

  have hcomm : ∀ g : ↥(H₁ ⊔ H₂), Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g * z =
      z * Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g := by
    intro g
    have hm : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g ∈ C := by
      rw [hCeq]
      exact (Setup.mem_autOn_self_iff hP).2 ⟨g, rfl⟩
    exact (mem_centralizer_singleton_iff.1 hm.2)

  obtain ⟨w, hw, hw1⟩ := exists_ne_one_of_card_two hc₁
  have hwZ : w ∈ quasithinOmegaOneCenter T := (mem_inf.1 hw).1
  have hwV : w ∈ v0Of T H₁ H₂ := s1347_Z_le_V0 hwZ
  set w' : ↥(v0Of T H₁ H₂) := z ⟨w, hwV⟩ with hw'
  have hfix : ∀ g : ↥(H₁ ⊔ H₂), (g : G) * w * (g : G)⁻¹ = w →
      (g : G) * w' * (g : G)⁻¹ = w' := by
    intro g hg
    have h1 : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g ⟨w, hwV⟩ = ⟨w, hwV⟩ :=
      Subtype.ext (by rw [Setup.rho_apply_coe]; exact hg)
    have h2 : Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP g w' = w' := by
      rw [hw', ← MulAut.mul_apply, hcomm g, MulAut.mul_apply, h1]
    have := congrArg Subtype.val h2
    rwa [Setup.rho_apply_coe] at this
  have hw'C : (w' : G) ∈ cZ T H₁ := by
    refine mem_inf.2 ⟨s1347_centralizer_T_le S hH₀ w'.2 (mem_centralizer_iff.2 fun t ht => ?_),
      mem_centralizer_iff.2 fun g hg => ?_⟩
    · have h1 := hfix ⟨t, hH₀.1 ht⟩ (by
        show t * w * t⁻¹ = w
        rw [mem_centralizer_iff.1 (s134_Z_le_center T hwZ).2 t ht, mul_inv_cancel_right])
      calc t * (w' : G) = t * w' * t⁻¹ * t := by group
        _ = w' * t := by rw [h1]
    · have h1 := hfix ⟨g, mem_sup_left hg⟩ (by
        show g * w * g⁻¹ = w
        rw [mem_centralizer_iff.1 (mem_inf.1 hw).2 g hg, mul_inv_cancel_right])
      calc g * (w' : G) = g * w' * g⁻¹ * g := by group
        _ = w' * g := by rw [h1]
  have hw'1 : (w' : G) ≠ 1 := by
    intro h1
    have h2 : w' = 1 := Subtype.ext h1
    rw [hw', MulEquiv.map_eq_one_iff] at h2
    exact hw1 (congrArg Subtype.val h2)

  have hw2 : w ^ 2 = 1 := hred.2.2.1.2 w hwV
  have hzw : zpowers w = cZ T H₁ := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hw) ?_
    rw [hc₁, Nat.card_zpowers, orderOf_eq_prime hw2 hw1]
  have hw'w : (w' : G) = w := by
    rw [← hzw] at hw'C
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hw'C
    rw [← hn, zpow_eq_zpow_emod_two hw2 n]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0
    · exfalso
      apply hw'1
      rw [← hn, zpow_eq_zpow_emod_two hw2 n, h0, zpow_zero]
    · rw [h0, zpow_one]
  have hmem : (⟨w, hwV⟩ : ↥(v0Of T H₁ H₂)) ∈ fixAutU3 z := Subtype.ext hw'w
  rw [hzfix, mem_bot] at hmem
  exact hw1 (congrArg Subtype.val hmem)

theorem s1347_iii_Y2_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hiii : Concl1347iii T H₁ H₂) :
    ∃ Y₂ : Subgroup G, Y₂ ≤ H₁ ⊔ H₂ ∧ H₁ ⊔ H₂ ≤ normalizer (Y₂ : Set G) ∧ oTwoRes Y₂ = Y₂ ∧
      (∀ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G) →
        ∀ w ∈ v0Of T H₁ H₂, y * w * y⁻¹ = w → w = 1) ∧
      (∃ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G)) ∧
      Y₂ ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G) ∧ T.relIndex (Y₂ ⊔ T) = 3 ∧
      quasithinO2QuotientIso (Y₂ ⊔ T) (Perm (Fin 3)) ∧ ¬ Y₂ ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨z, hzX, hz3, hz1, hzfix, hzn, β₀, hβ₀, hβ₀z⟩ :=
    s1347_iii_z_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h hiii
  have hred := s1347_reduced S hH₀
  have hP : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  set ρ := Setup.rho (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP with hρ
  have hcent : (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) :=
    hiii.1.symm
  have hTH : T ≤ H₁ ⊔ H₂ := hH₀.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1

  have h2el : ∀ t (ht : t ∈ T), ∀ g : ↥(H₁ ⊔ H₂), (g : G) = t → ρ g ^ 3 = 1 → ρ g = 1 := by
    intro t ht g hg h3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨t, ht⟩
    have hk' : orderOf t = 2 ^ k := (Subgroup.orderOf_coe ⟨t, ht⟩).trans hk
    have hgo : orderOf g = 2 ^ k := by
      rw [← hk', ← hg, Subgroup.orderOf_coe]
    have h1 : orderOf (ρ g) ∣ 2 ^ k := hgo ▸ orderOf_map_dvd ρ g
    have h2 : orderOf (ρ g) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h3' : orderOf (ρ g) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))] at h3'
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3')

  have hzN : autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂) ≤ normalizer (zpowers z : Set (MulAut _)) := by
    intro β hβ
    have hmem : ∀ γ ∈ autOn (H₁ ⊔ H₂) (v0Of T H₁ H₂), γ * z * γ⁻¹ ∈ zpowers z := by
      intro γ hγ
      rcases hzn γ hγ with e | e <;> rw [e]
      · exact mem_zpowers z
      · exact inv_mem (mem_zpowers z)
    exact mem_normalizer_zpowers (hmem β hβ) (hmem β⁻¹ (inv_mem hβ))
  set YZ := Setup.rhoPreimage (v0Of T H₁ H₂) (H₁ ⊔ H₂) hP (zpowers z) with hYZ
  have hYZH : YZ ≤ H₁ ⊔ H₂ := Setup.rhoPreimage_le hP _
  have hYZN : H₁ ⊔ H₂ ≤ normalizer (YZ : Set G) := Setup.le_normalizer_rhoPreimage hP hzN
  set Y₂ := oTwoRes YZ with hY₂
  have hY₂YZ : Y₂ ≤ YZ := oTwoRes_le _
  have hY₂H : Y₂ ≤ H₁ ⊔ H₂ := hY₂YZ.trans hYZH
  have hY₂N : H₁ ⊔ H₂ ≤ normalizer (Y₂ : Set G) :=
    hYZN.trans (normalizer_le_normalizer_oTwoRes _)
  have hρY : ∀ y (hy : y ∈ Y₂), ρ ⟨y, hY₂H hy⟩ ∈ zpowers z := fun y hy =>
    Setup.mem_rhoPreimage.1 (hY₂YZ hy)

  obtain ⟨g, hg⟩ := (Setup.mem_autOn_self_iff hP).1 hzX
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set y₀ : ↥(H₁ ⊔ H₂) := g ^ 4 ^ a with hy₀
  have h4a : 4 ^ a * m = 2 ^ a * m * 2 ^ a := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring
  have hy₀m : y₀ ^ m = 1 := by
    rw [hy₀, ← pow_mul, h4a, ← hn, pow_mul, pow_orderOf_eq_one, one_pow]
  have hρy₀ : ρ y₀ = z := by
    rw [hy₀, map_pow, hg, ← pow_mod_orderOf, orderOf_eq_prime hz3 hz1, Nat.pow_mod]
    norm_num
  have hy₀Y : (y₀ : G) ∈ Y₂ := by
    refine mem_oTwoRes_of_odd (Setup.mem_rhoPreimage.2 ?_) hm (by
      rw [← Subgroup.coe_pow, hy₀m]; rfl)
    rw [hρy₀]
    exact mem_zpowers z
  have hy₀C : (y₀ : G) ∉ centralizer (v0Of T H₁ H₂ : Set G) := fun hc =>
    hz1 (hρy₀ ▸ (Setup.rho_eq_one_iff hP y₀).2 hc)

  have hY₂T : Y₂ ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
    rintro y ⟨hy, hyT⟩
    have h1 := hρY y hy
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h1
    have h3 : ρ ⟨y, hY₂H hy⟩ ^ 3 = 1 := by
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hz3]
    exact (Setup.rho_eq_one_iff hP _).1 (h2el y hyT _ rfl h3)

  have hfpf : ∀ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G) →
      ∀ w ∈ v0Of T H₁ H₂, y * w * y⁻¹ = w → w = 1 := by
    intro y hy hyC w hw hyw
    have h1 : ρ ⟨y, hY₂H hy⟩ ≠ 1 := fun h1 => hyC ((Setup.rho_eq_one_iff hP _).1 h1)
    have hle := fixAutU3_le_of_mem_zpowers hz3 (hρY y hy) h1
    have h2 : (⟨w, hw⟩ : ↥(v0Of T H₁ H₂)) ∈ fixAutU3 (ρ ⟨y, hY₂H hy⟩) :=
      Subtype.ext (by rw [Setup.rho_apply_coe]; exact hyw)
    have h3 := hle h2
    rw [hzfix, mem_bot] at h3
    exact congrArg Subtype.val h3

  have hTY₂ : T ≤ normalizer (Y₂ : Set G) := hTH.trans hY₂N
  have hautY : autOn Y₂ (v0Of T H₁ H₂) = zpowers z := by
    apply le_antisymm
    · intro β hβ
      obtain ⟨p, hp, rfl⟩ := (Setup.mem_autOn_iff_rho hP hY₂H).1 hβ
      exact hρY p hp
    · rw [zpowers_le]
      exact (Setup.mem_autOn_iff_rho hP hY₂H).2 ⟨y₀, hy₀Y, hρy₀⟩
  have hinf : Y₂ ⊓ T = Y₂ ⊓ centralizer (v0Of T H₁ H₂ : Set G) := by
    refine le_antisymm (le_inf inf_le_left hY₂T) fun y hy => ⟨hy.1, ?_⟩
    have h1 : y ∈ (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) := ⟨hY₂H hy.1, hy.2⟩
    rw [hcent] at h1
    exact pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hTH) h1
  have h3 : T.relIndex (Y₂ ⊔ T) = 3 := by
    rw [relIndex_sup_eq hTY₂, hinf, ← card_autOn_eq_relIndex (hY₂H.trans hP), hautY,
      Nat.card_zpowers, orderOf_eq_prime hz3 hz1]

  have hsyl : IsSylowTwoOf T (Y₂ ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hnN : ¬ Y₂ ⊔ T ≤ normalizer (T : Set G) := by
    intro hle
    obtain ⟨t, ht, htβ⟩ := (Setup.mem_autOn_iff_rho hP hTH).1 hβ₀
    have hyT : (y₀ : G) * t * (y₀ : G)⁻¹ ∈ T :=
      (mem_normalizer_iff.1 (hle (mem_sup_left hy₀Y)) t).1 ht
    have hc : (y₀ : G) * t * (y₀ : G)⁻¹ * (t : G)⁻¹ ∈ T := mul_mem hyT (inv_mem ht)
    set c : ↥(H₁ ⊔ H₂) := y₀ * t * y₀⁻¹ * t⁻¹ with hcdef
    have hρc : ρ c = z * z := by
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hρy₀, htβ]
      have e : β₀ * z⁻¹ * β₀⁻¹ = z := by
        rw [← inv_inj, show (β₀ * z⁻¹ * β₀⁻¹)⁻¹ = β₀ * z * β₀⁻¹ by group, hβ₀z]
      calc z * β₀ * z⁻¹ * β₀⁻¹ = z * (β₀ * z⁻¹ * β₀⁻¹) := by group
        _ = z * z := by rw [e]
    have h3c : ρ c ^ 3 = 1 := by
      rw [hρc, ← sq, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
    have h1 := h2el _ hc c rfl h3c
    rw [hρc] at h1
    apply hz1
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, h1]; group
  have hq := quot_S3_of_index_three hsyl h3 hnN

  have hnM : ¬ Y₂ ≤ normalizer (L : Set G) := by
    intro hle
    have hzV : S.zV ∈ quasithinOmegaOneCenter T := by
      refine subset_closure ⟨⟨S.V_le_T S.zV_mem_V, mem_centralizer_iff.2 fun t ht => ?_⟩,
        S.zV_sq⟩
      have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
      calc t * S.zV = t * S.zV * t⁻¹ * t := by group
        _ = S.zV * t := by rw [h1]
    have hyN : (y₀ : G) ∈ normalizer (V : Set G) := by
      rw [← ((S.lemma13_4_2_one_F4 h1222).1)]
      exact hle hy₀Y
    have h1 := S.conj_zV ⟨y₀, hyN⟩
    exact S.zV_ne_one (hfpf _ hy₀Y hy₀C _ (s1347_Z_le_V0 hzV) h1)
  exact ⟨Y₂, hY₂H, hY₂N, S14.oTwoRes_idem _, hfpf, ⟨_, hy₀Y, hy₀C⟩, hY₂T, h3, hq, hnM⟩

end CFSG.Quasithin.H13.U3
