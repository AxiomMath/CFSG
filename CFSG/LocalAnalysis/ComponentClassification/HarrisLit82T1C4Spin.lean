module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step12
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isSimpleChevalleyOver_of_isMTypeSchur {K : Type} [Group K] {p : ℕ}
    (hK : Group.IsPerfect K) (hM : IsMTypeSchur p K) :
    IsSimpleChevalleyOver p (K ⧸ Open.fusionZStar K) := by
  have := hK
  rcases hM with ⟨-, hch, -, -⟩ | ⟨-, ⟨e⟩⟩
  · exact hch
  · exact absurd (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
      TBLit.not_isPerfect_sl2Three

theorem nonempty_fusionZStar_equiv {A B : Type} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  exact GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.toMonoidHom e.surjective (by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, Subgroup.card_bot]
    norm_num)

section Certified


theorem fourGroup_spinOdd (hI : C3Inputs) (h58 : Harris82Lemma58b) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z₁ z₂ : G} (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) {L₁ L₂ : Subgroup G}
    (hL₁ : IsTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (hz₂L : z₂ ∈ L₂) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ k)
    (hsl : IsSLTwoOver (p ^ k) (↥L₁ ⧸ pPrimeCore 2 ↥L₁))
    (hL₂c : IsSLTwoOver (p ^ k) (↥L₂ ⧸ pPrimeCore 2 ↥L₂) ∨
      ∃ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel (↥L₂ ⧸ Open.fusionZStar ↥L₂) τ n p k) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧ z₁ ∈ K ∧ IsMTypeSchur p ↥K ∧
      ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsCoverOf .POmegaOdd m p k 2 (↥K ⧸ pPrimeCore 2 ↥K) ∧
        (IsSLTwoOver (p ^ k) (↥L₂ ⧸ pPrimeCore 2 ↥L₂) → m = 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₁1 : z₁ ≠ 1 := fun h => by rw [h, orderOf_one] at hz₁; exact absurd hz₁ (by norm_num)
  have hz₂1 : z₂ ≠ 1 := fun h => by rw [h, orderOf_one] at hz₂; exact absurd hz₂ (by norm_num)
  have hz₁sq : z₁ ^ 2 = 1 := hz₁ ▸ pow_orderOf_eq_one z₁
  have hz₂sq : z₂ ^ 2 = 1 := hz₂ ▸ pow_orderOf_eq_one z₂
  set W := zpowers z₁ ⊔ zpowers z₂ with hWdef
  have hW4 : Nat.card W = 4 :=
    (FooteLit.isKleinFour_sup_zpowers hz₁sq hz₂sq hz₁1 hz₂1 hne.symm hc).card_four
  have hcomm : ∀ x ∈ zpowers z₁, ∀ y ∈ zpowers z₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute z₁ z₂ from hc) i j).eq
  have hW2 : ∀ a ∈ W, a * a = 1 := fun a ha => by
    rw [← sq]
    exact FooteLit.sq_eq_one_of_mem_sup (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hz₁sq hx)
      (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hz₂sq hx) hcomm a ha
  have hz₁W : z₁ ∈ W := mem_sup_left (mem_zpowers z₁)
  have hz₂W : z₂ ∈ W := mem_sup_right (mem_zpowers z₂)
  have hz₂n : z₂ ∉ zpowers z₁ := fun h =>
    (T23.eq_one_or_eq_of_mem_zpowers (hW2 z₁ hz₁W) h).elim hz₂1 hne.symm
  obtain ⟨-, -, -, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hz₁W hz₁1 hz₂W hz₂n
  have hL₁W : IsTwoComponentIn L₁ (centralizer (W : Set G)) := hCW ▸ hL₁
  have hL₂W : IsTwoComponentIn L₂ (centralizer (W : Set G)) := hCW ▸ hL₂
  obtain ⟨hKc, hL₁K, hL₂K, hMK, hz₂K, hz₂Z⟩ := fourGroup_slTwo hI.ci hI.ga hI.ident hnonab hK hcat
    hW2 hW4 hz₁W hz₂W hz₁1 hz₂1 hne hL₁W hL₂W hz₁L hz₂L hp hp2 (one_le_of_five_le_pow h5) h5 hsl
  set K := GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})) with hKdef
  have hle : K ⊓ centralizer {z₂} ≤ centralizer {z₁} ⊓ centralizer {z₂} :=
    inf_le_inf_right _ hKc.1
  have hL₂K' : IsTwoComponentIn L₂ (K ⊓ centralizer {z₂}) :=
    ⟨le_inf hL₂K (hL₂.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hL₂.2.1,
      hL₂.2.2⟩
  have hL₁K' : IsTwoComponentIn L₁ (K ⊓ centralizer {z₂}) :=
    ⟨le_inf hL₁K (hL₁.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hL₁.2.1,
      hL₁.2.2⟩
  have hz₁K : z₁ ∈ K := hL₁K hz₁L
  have hz₁c : (⟨z₁, hz₁K⟩ : ↥K) ∈ center ↥K := mem_center_of_le_centralizer hKc.1 hz₁K
  have hz₁' : orderOf (⟨z₁, hz₁K⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₁
  have hz₂' : orderOf (⟨z₂, hz₂K⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂
  let e₁ : ↥(L₁.subgroupOf K) ≃* ↥L₁ := subgroupOfEquivOfLe hL₁K
  let e₂ : ↥(L₂.subgroupOf K) ≃* ↥L₂ := subgroupOfEquivOfLe hL₂K
  have hsl' : IsSLTwoOver (p ^ k) (↥(L₁.subgroupOf K) ⧸ pPrimeCore 2 ↥(L₁.subgroupOf K)) :=
    isSLTwoOver_of_mulEquiv' (QuotientGroup.congr _ _ e₁.symm (pPrimeCore_map_iso 2 e₁.symm)) hsl
  have hch := isSimpleChevalleyOver_of_isMTypeSchur hKc.2.2.1 hMK
  obtain ⟨hA, hB⟩ := h58 ↥K hKc.2.2 p hp hp2 hch ⟨z₁, hz₁K⟩ ⟨z₂, hz₂K⟩ hz₁' hz₁c hz₂' hz₂Z
    (L₁.subgroupOf K) (L₂.subgroupOf K) (isTwoComponentIn_subgroupOf_inf hz₂K hL₁K')
    (isTwoComponentIn_subgroupOf_inf hz₂K hL₂K') hz₁L hz₂L k h5 hsl'
  refine ⟨K, hKc, hz₁K, hMK, ?_⟩
  by_cases hs₂ : IsSLTwoOver (p ^ k) (↥L₂ ⧸ pPrimeCore 2 ↥L₂)
  · have hs₂' : IsSLTwoOver (p ^ k) (↥(L₂.subgroupOf K) ⧸ pPrimeCore 2 ↥(L₂.subgroupOf K)) :=
      isSLTwoOver_of_mulEquiv' (QuotientGroup.congr _ _ e₂.symm (pPrimeCore_map_iso 2 e₂.symm))
        hs₂
    exact ⟨3, ⟨1, rfl⟩, le_rfl, hB hs₂', fun _ => rfl⟩
  · obtain ⟨τ, n, hlie⟩ := hL₂c.resolve_left hs₂
    obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv e₂
    obtain ⟨m, hmo, hm3, hcov⟩ := hA ⟨τ, n, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hlie⟩
    exact ⟨m, hmo, hm3, hcov, fun h => absurd h hs₂⟩

theorem false_of_spinOdd (hI : C3Inputs) (h58 : Harris82Lemma58b) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) {p f m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hcov : IsCoverOf .POmegaOdd m p f 2 (↥L ⧸ pPrimeCore 2 ↥L)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := one_le_of_five_le_pow h5
  obtain ⟨hcomp, -, ⟨E⟩⟩ := hatIn_spec hL
  set Lh := hatIn z L with hLh
  have hcovh : IsCoverOf .POmegaOdd m p f 2 ↥Lh := isCoverOf_of_mulEquiv E hcov
  obtain ⟨w, hw2, hZw, t, J₁, J₂, ht2, htZ, hJ₁, hJ₂, hs₁, hs₂, hc₁, hc₂⟩ :=
    lemma412_of_isCoverOf h5 hcovh
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
  have huL : u ∈ L := mem_of_mk_mem_hatIn hL huz (n := 1)
    (by rw [pow_one, ← hu, pow_orderOf_eq_one]) (by rw [hûmk]; exact t.2)
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.mp huz
  have hzu : z ≠ u := by
    intro h1
    apply htZ
    have h2 : (t : MBar z) = zh := by rw [← hûmk, hzh]; congr 1; exact Subtype.ext h1.symm
    have h3 : t = w := Subtype.ext (h2.trans hw.symm)
    rw [h3, hZw]
    exact mem_zpowers w
  have hJmap : ∀ {J : Subgroup ↥Lh}, IsTwoComponentIn J (centralizer {t}) →
      IsTwoComponentIn (J.map Lh.subtype)
        (centralizer {(QuotientGroup.mk ⟨u, huz⟩ : MBar z)}) := by
    intro J hJ
    have h1 := L35.isTwoComponentIn_map_of_injective Lh.subtype Lh.subtype_injective hJ
    rw [map_subtype_centralizer_mem] at h1
    have h2 := isTwoComponentIn_inf_of_subnormal (le_top : Lh ≤ ⊤) hcomp.1.subgroupOf
      (centralizer {(t : MBar z)}) h1
    rw [top_inf_eq] at h2
    rwa [hûmk]
  have hsmap : ∀ {J : Subgroup ↥Lh}, IsSLTwoOver (p ^ f) ↥J →
      IsSLTwoOver (p ^ f) ↥(J.map Lh.subtype) := fun {J} hs =>
    isSLTwoOver_of_mulEquiv' (J.equivMapOfInjective _ Lh.subtype_injective) hs
  obtain ⟨K₁, hK₁, hK₁mem, -, ⟨eK₁⟩⟩ := lift_twoComponent huz hu (hJmap hJ₁)
  obtain ⟨K₂, hK₂, hK₂mem, -, ⟨eK₂⟩⟩ := lift_twoComponent huz hu (hJmap hJ₂)
  have hsK₁ := isSLTwoOver_quot_of_equiv hp hp2 hf h5 eK₁ (hsmap hs₁)
  have hsK₂ := isSLTwoOver_quot_of_equiv hp hp2 hf h5 eK₂ (hsmap hs₂)
  have huu : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have huK₁ : u ∈ K₁ := hK₁mem u huz huu ⟨1, by rw [pow_one]; exact hu⟩ (by
    rw [hûmk]
    exact mem_map_of_mem Lh.subtype (mem_of_map_center_eq_zpowers hc₁))
  have huzz : u * z ∈ centralizer ({z} : Set G) := mul_mem huz hzH
  have huzu : u * z ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff, mul_assoc, ← hcomm, ← mul_assoc]
  have huz2 : orderOf (u * z) = 2 := orderOf_mul_of_commute hu hz hcomm hzu
  have huzK₂ : u * z ∈ K₂ := hK₂mem (u * z) huzz huzu ⟨1, by rw [pow_one]; exact huz2⟩ (by
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
  obtain ⟨K, hKc, huK, hMK, m', -, -, hcovK, himp⟩ := fourGroup_spinOdd hI h58 hnonab hK hcat hu
    huz2 hne hc (hCeq ▸ hK₁) (hCeq ▸ hK₂) huK₁ huzK₂ hp hp2 h5 hsK₁ (.inl hsK₂)
  rw [himp hsK₂] at hcovK
  exact false_of_spinSeven hI hnonab hK hcat hu hKc huK hp hp2 h5 hMK hcovK

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
