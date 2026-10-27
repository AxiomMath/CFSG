module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Sat
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Bar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem F3.three_le_of_isCoverOf {Y : Type} [Group Y] {m p f : ℕ}
    (h : IsCoverOf .POmegaOdd m p f 2 Y) : 3 ≤ m := by
  obtain ⟨-, -, hm⟩ := h
  rcases hm with ⟨-, ⟨-, -, hn, -⟩, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact hn
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem false_of_spinOddThree (h412 : Harris82Lemma412Three) (h4 : Harris82FourGroupThree)
    (h58 : Harris82Lemma58bThree) (h73 : Harris82Theorem1SpinSevenThree) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) (hM : IsMTypeSchur 3 ↥L) {m : ℕ}
    (hcov : IsCoverOf .POmegaOdd m 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (F3.three_le_of_isCoverOf hcov).eq_or_lt with h3 | h4m
  · subst h3
    exact h73 G hnonab hK hcat z hz L hL hzL 3 1 Nat.prime_three (by norm_num) hM hcov
  obtain ⟨hcomp, -, ⟨E⟩⟩ := hatIn_spec hL
  set Lh := hatIn z L with hLh
  have hcovh : IsCoverOf .POmegaOdd m 3 1 2 ↥Lh := isCoverOf_of_mulEquiv E hcov
  obtain ⟨w, hw2, hZw, t, J₁, J₂, ht2, htZ, hJ₁, hJ₂, ⟨e₁⟩, ⟨e₂⟩, hc₁, hc₂⟩ :=
    h412 ↥Lh m h4m hcovh
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  set zh : MBar z := QuotientGroup.mk ⟨z, hzH⟩ with hzh
  have hzhL : zh ∈ Lh := mk_mem_hatIn hzL hzH
  have hzhc : ∀ y : MBar z, y * zh = zh * y := by
    intro y
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hzh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y₀.2)
  have hzh2 : orderOf zh = 2 :=
    orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥(centralizer ({z} : Set G)))
      (by rw [Subgroup.orderOf_mk]; exact hz)
  have hzh1 : zh ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzh2; exact absurd hzh2 (by norm_num)
  have hw : (w : MBar z) = zh := by
    have h1 : (⟨zh, hzhL⟩ : ↥Lh) ∈ center ↥Lh := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hzhc g)
    rw [hZw] at h1
    have hww : w * w = 1 := by
      have h3 := pow_orderOf_eq_one w
      rwa [hw2, sq] at h3
    rcases T23.eq_one_or_eq_of_mem_zpowers hww h1 with h2 | h2
    · exact absurd (congrArg Subtype.val h2) hzh1
    · exact (congrArg Subtype.val h2).symm
  have ht2' : orderOf (t : MBar z) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
  obtain ⟨u', hu'2, hu'1, hu'mk⟩ := T23.exists_involution_lift (H := ↥(centralizer ({z} : Set G)))
    (a := (t : MBar z)) (by have h1 := pow_orderOf_eq_one (t : MBar z); rwa [ht2', sq] at h1)
    (fun h1 => by rw [h1, orderOf_one] at ht2'; exact absurd ht2' (by norm_num))
  have hu : orderOf (u' : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hu'2]) hu'1
  set u : G := (u' : G) with hudef
  have huz : u ∈ centralizer ({z} : Set G) := u'.2
  have hûmk : (QuotientGroup.mk ⟨u, huz⟩ : MBar z) = t := hu'mk
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.mp huz
  have hzu : z ≠ u := by
    intro h1
    apply htZ
    have h2 : (t : MBar z) = zh := by rw [← hûmk, hzh]; congr 1; exact Subtype.ext h1.symm
    have h3 : t = w := Subtype.ext (h2.trans hw.symm)
    rw [h3, hZw]
    exact mem_zpowers w
  have hsec : ∀ {J : Subgroup ↥Lh}, IsSolvableTwoComponentIn J (centralizer {t}) →
      J.map Lh.subtype ≤ centralizer {(QuotientGroup.mk ⟨u, huz⟩ : MBar z)} ∧
        ((J.map Lh.subtype).subgroupOf
          (centralizer {(QuotientGroup.mk ⟨u, huz⟩ : MBar z)})).IsSubnormal := by
    intro J hJ
    obtain ⟨h1, h2⟩ := F3.map_inf_subnormal (le_top : Lh ≤ ⊤) hcomp.1.subgroupOf t hJ.1 hJ.2.1
    rw [top_inf_eq] at h1 h2
    rw [hûmk]
    exact ⟨h1, h2⟩
  have hq : ∀ {J : Subgroup ↥Lh}, (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) →
      (↥(J.map Lh.subtype) ⧸ pPrimeCore 2 ↥(J.map Lh.subtype) ≃* SL(2, ZMod 3)) := fun {J} e =>
    let eJ : ↥J ≃* ↥(J.map Lh.subtype) := J.equivMapOfInjective _ Lh.subtype_injective
    (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans e
  obtain ⟨𝒥₁, h𝒥₁, ⟨f₁⟩, hmem₁⟩ := F3.lift_solvable huz hu (hsec hJ₁).1 (hsec hJ₁).2 (hq e₁)
  obtain ⟨𝒥₂, h𝒥₂, ⟨f₂⟩, hmem₂⟩ := F3.lift_solvable huz hu (hsec hJ₂).1 (hsec hJ₂).2 (hq e₂)
  have huu : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have huJ₁ : u ∈ 𝒥₁ := hmem₁ u huz huu (by
    rw [hûmk]
    exact mem_map_of_mem Lh.subtype (mem_of_map_center_eq_zpowers hc₁))
  have huzz : u * z ∈ centralizer ({z} : Set G) := mul_mem huz hzH
  have huzu : u * z ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff, mul_assoc, ← hcomm, ← mul_assoc]
  have huz2 : orderOf (u * z) = 2 := F3.orderOf_mul_of_commute hu hz hcomm hzu
  have huzJ₂ : u * z ∈ 𝒥₂ := hmem₂ (u * z) huzz huzu (by
    have hprod : (QuotientGroup.mk ⟨u * z, huzz⟩ : MBar z) =
        QuotientGroup.mk ⟨u, huz⟩ * zh := by
      rw [hzh, ← QuotientGroup.mk_mul]
      rfl
    rw [hprod, hûmk, ← hw]
    exact mem_map_of_mem Lh.subtype (mem_of_map_center_eq_zpowers hc₂))
  have hCeq : centralizer ({z} : Set G) ⊓ centralizer {u} =
      centralizer {u} ⊓ centralizer {u * z} := by
    rw [T23.centralizer_inf_mul, inf_comm]
  have hne : u ≠ u * z := fun h1 => by
    have h2 : z = 1 := by
      calc z = u⁻¹ * (u * z) := by group
        _ = 1 := by rw [← h1, inv_mul_cancel]
    rw [h2, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hc : u * (u * z) = u * z * u := by rw [mul_assoc, ← hcomm, ← mul_assoc]
  have h𝒥₁' := hCeq ▸ h𝒥₁
  have h𝒥₂' := hCeq ▸ h𝒥₂
  obtain ⟨K, hKc, hO₁, hO₂, hN, hch, hz₂K, hz₂Z⟩ := h4 G hnonab hK hcat u (u * z) hu huz2 hne hc
    𝒥₁ 𝒥₂ h𝒥₁' (.inr h𝒥₂') huJ₁ huzJ₂ ⟨f₁⟩ (.inr ⟨rfl, .inr ⟨f₂⟩⟩)
  obtain ⟨hMK, -, hB, -⟩ := h58 G u (u * z) hu huz2 hne hc 𝒥₁ 𝒥₂ K h𝒥₁' (.inr h𝒥₂') huJ₁ huzJ₂
    ⟨f₁⟩ hKc hO₁ hO₂ hN hz₂K hz₂Z hch
  have huK : u ∈ K := hO₁ (F3.mem_oPrimeResidualOf huJ₁ hu)
  exact h73 G hnonab hK hcat u hu K hKc huK 3 1 Nat.prime_three (by norm_num) hMK (hB ⟨f₂⟩)

theorem false_of_generalThree (h54 : Harris82Lemma54Three) (h412 : Harris82Lemma412Three)
    (h4 : Harris82FourGroupThree) (h58 : Harris82Lemma58bThree)
    (h73 : Harris82Theorem1SpinSevenThree) [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {z : G}
    (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) (hM : IsMTypeSchur 3 ↥L) {τ : StatedLieTag} {n : ℕ}
    (hlie : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ n 3 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := mem_center_of_le_centralizer hL.1 hzL
  have hz' : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Open.fusionZStar ↥L := F3.mem_fusionZStar_of_mem_center hzc
  obtain ⟨u', hu'2, hu'Z, J₁, J₂, hJ₁, huJ₁, ⟨e₁⟩, hJ₂, -, hzJ₂⟩ :=
    h54 ↥L hL.2.2 hM τ n hlie ⟨z, hzL⟩ hz' hzZ
  set u : G := (u' : G) with hudef
  have huL : u ∈ L := u'.2
  have hu : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_coe]; exact hu'2
  have huz : u ∈ centralizer ({z} : Set G) := hL.1 huL
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.mp huz
  have hzu : z ≠ u := fun h1 => hu'Z (by
    have h2 : u' = ⟨z, hzL⟩ := Subtype.ext h1.symm
    rw [h2]
    exact hzZ)
  set M := centralizer ({z} : Set G) ⊓ centralizer {u} with hMdef
  have hsec : ∀ {J : Subgroup ↥L}, J ≤ centralizer {u'} →
      (J.subgroupOf (centralizer {u'})).IsSubnormal →
      J.map L.subtype ≤ M ∧ ((J.map L.subtype).subgroupOf M).IsSubnormal :=
    fun hJ hJs => F3.map_inf_subnormal hL.1 hL.2.1 u' hJ hJs
  have hq : ∀ {J : Subgroup ↥L}, (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) →
      (↥(J.map L.subtype) ⧸ pPrimeCore 2 ↥(J.map L.subtype) ≃* SL(2, ZMod 3)) := fun {J} e =>
    let eJ : ↥J ≃* ↥(J.map L.subtype) := J.equivMapOfInjective _ L.subtype_injective
    (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans e
  have hsat := F3.isSolvableTwoComponentIn_sup (hsec hJ₁.1 hJ₁.2.1).1 (hsec hJ₁.1 hJ₁.2.1).2
    (hq e₁)
  obtain ⟨𝒥₁, h𝒥₁, ⟨f₁⟩, hu𝒥₁⟩ : ∃ 𝒥₁ : Subgroup G, IsSolvableTwoComponentIn 𝒥₁ M ∧
      Nonempty (↥𝒥₁ ⧸ pPrimeCore 2 ↥𝒥₁ ≃* SL(2, ZMod 3)) ∧ u ∈ 𝒥₁ :=
    ⟨_, hsat.1, hsat.2, mem_sup_left ⟨u', huJ₁, rfl⟩⟩
  obtain ⟨𝒥₂, hle₂, h𝒥₂⟩ : ∃ 𝒥₂ : Subgroup G, J₂.map L.subtype ≤ 𝒥₂ ∧
      ((IsTwoComponentIn 𝒥₂ M ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
          Blueprint.LieModel (↥𝒥₂ ⧸ Open.fusionZStar ↥𝒥₂) τ' n' 3 1) ∨
        (IsSolvableTwoComponentIn 𝒥₂ M ∧
          Nonempty (↥𝒥₂ ⧸ pPrimeCore 2 ↥𝒥₂ ≃* SL(2, ZMod 3)))) := by
    rcases hJ₂ with ⟨hJ₂p, τ', n', hlie₂⟩ | ⟨hJ₂s, ⟨e₂⟩⟩
    · let eJ₂ : ↥J₂ ≃* ↥(J₂.map L.subtype) := J₂.equivMapOfInjective _ L.subtype_injective
      have hJ₂M : IsTwoComponentIn (J₂.map L.subtype) M := by
        have h1 := L35.isTwoComponentIn_map_of_injective L.subtype L.subtype_injective hJ₂p
        rw [map_subtype_centralizer_mem] at h1
        exact isTwoComponentIn_inf_of_subnormal hL.1 hL.2.1 (centralizer {u}) h1
      obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective eJ₂.toMonoidHom
        eJ₂.surjective (by
          rw [(MonoidHom.ker_eq_bot_iff _).mpr eJ₂.injective, Subgroup.card_bot]
          norm_num)
      exact ⟨_, le_rfl, .inl ⟨hJ₂M, τ', n', GSThmB.OddQuot.lieModel_of_equiv eZ hlie₂⟩⟩
    · obtain ⟨hs, ⟨f₂⟩⟩ := F3.isSolvableTwoComponentIn_sup (hsec hJ₂s.1 hJ₂s.2.1).1
        (hsec hJ₂s.1 hJ₂s.2.1).2 (hq e₂)
      exact ⟨_, le_sup_left, .inr ⟨hs, ⟨f₂⟩⟩⟩
  have finish : ∀ z₂ : G, orderOf z₂ = 2 → u ≠ z₂ → u * z₂ = z₂ * u →
      M = centralizer {u} ⊓ centralizer {z₂} → z₂ ∈ 𝒥₂ → False := by
    intro z₂ hz₂ hne hc hC hz₂J
    have hc₁ := hC ▸ h𝒥₁
    have hc₂ : IsTwoComponentIn 𝒥₂ (centralizer {u} ⊓ centralizer {z₂}) ∨
        IsSolvableTwoComponentIn 𝒥₂ (centralizer {u} ⊓ centralizer {z₂}) :=
      hC ▸ h𝒥₂.imp (fun h => h.1) (fun h => h.1)
    have hI₂ : InductionType 3 ↥𝒥₂ := .inr ⟨rfl, h𝒥₂.imp (fun h => h.2) (fun h => h.2)⟩
    obtain ⟨K, hKc, hO₁, hO₂, hN, hch, hz₂K, hz₂Z⟩ :=
      h4 G hnonab hK hcat u z₂ hu hz₂ hne hc 𝒥₁ 𝒥₂ hc₁ hc₂ hu𝒥₁ hz₂J ⟨f₁⟩ hI₂
    obtain ⟨hMK, hA, hB, -⟩ := h58 G u z₂ hu hz₂ hne hc 𝒥₁ 𝒥₂ K hc₁ hc₂ hu𝒥₁ hz₂J ⟨f₁⟩ hKc hO₁ hO₂
      hN hz₂K hz₂Z hch
    have huK : u ∈ K := hO₁ (F3.mem_oPrimeResidualOf hu𝒥₁ hu)
    rcases h𝒥₂ with ⟨hp, hl⟩ | ⟨-, ⟨f₂⟩⟩
    · obtain ⟨m, -, -, hcov⟩ := hA ⟨hC ▸ hp, hl⟩
      exact false_of_spinOddThree h412 h4 h58 h73 hnonab hK hcat hu hKc huK hMK hcov
    · exact h73 G hnonab hK hcat u hu K hKc huK 3 1 Nat.prime_three (by norm_num) hMK (hB ⟨f₂⟩)
  rcases hzJ₂ with hzJ | hzuJ
  · exact finish z hz (Ne.symm hzu) hcomm (inf_comm _ _) (hle₂ ⟨⟨z, hzL⟩, hzJ, rfl⟩)
  · have huz2 : orderOf (u * z) = 2 := F3.orderOf_mul_of_commute hu hz hcomm hzu
    have hne : u ≠ u * z := fun h1 => by
      have h2 : z = 1 := by
        calc z = u⁻¹ * (u * z) := by group
          _ = 1 := by rw [← h1, inv_mul_cancel]
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hc : u * (u * z) = u * z * u := by rw [mul_assoc, ← hcomm, ← mul_assoc]
    have hC : M = centralizer {u} ⊓ centralizer {u * z} := by
      rw [hMdef, T23.centralizer_inf_mul, inf_comm]
    refine finish (u * z) huz2 hne hc hC (hle₂ ?_)
    rw [hcomm]
    exact ⟨⟨z, hzL⟩ * u', hzuJ, rfl⟩

theorem harris82Theorem1FieldThree_of_inputs (h54 : Harris82Lemma54Three)
    (h4 : Harris82FourGroupThree) (h58 : Harris82Lemma58bThree) (h412 : Harris82Lemma412Three)
    (h73 : Harris82Theorem1SpinSevenThree) : Harris82Theorem1FieldThree :=
  fun _ _ _ _ hnonab hK hcat _ hz _ hL hzL hM _ _ hlie =>
    false_of_generalThree h54 h412 h4 h58 h73 hnonab hK hcat hz hL hzL hM hlie

end CFSG.ComponentClassification.HarrisLit.T1
