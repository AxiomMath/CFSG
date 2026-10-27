module

public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Eight
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists

public section

namespace CFSG.HardMathSupport.Dickson.I271.Amb

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.L2Plane CFSG.HardMathSupport.Dickson.I271

theorem l2Eight_center_eq_bot
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 8)
    {Λ : Type} [Group Λ] [Finite Λ] (hΛ : CFSG.Open.IsQuasisimple Λ)
    (e : Λ ⧸ Subgroup.center Λ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Subgroup.center Λ = ⊥ := by
  have : Fintype F := Fintype.ofFinite _
  have hk : Fintype.card F = 8 := by rw [Fintype.card_eq_nat_card, hF]
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
    (k := F) (by omega) (by omega)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hΛ.1⟩ e
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hk] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (by simpa using hdvd))

theorem l2Eight_balance_of_conj {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 8) {S : Type} [Group S] [Finite S] (e : S ≃* PSL2 F) {s : S}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) {T : Subgroup (MulAut S)} (hT3' : ¬ 3 ∣ Nat.card T)
    (hnorm : (MulAut.conj s : MulAut S) ∈ Subgroup.normalizer (T : Set (MulAut S))) : T = ⊥ := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hGal : Nat.card (F ≃+* F) = 3 := by
    have := card_ringAut F Nat.prime_two (show Nat.card F = 2 ^ 3 by rw [hF]; norm_num)
    exact this
  let φ : MulAut S ≃* PGammaL2 F := autEquiv e
  let y' : PSL2 F := e s
  have hy'3 : y' ^ 3 = 1 := by
    show (e s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hs1
    exact e.injective (h.trans (map_one e).symm)
  have hφa : φ (MulAut.conj s) = incl F y' := autEquiv_conj e s
  let Tb : Subgroup (PGammaL2 F) := T.map φ.toMonoidHom
  have hTb_right : ∀ x ∈ Tb, x.right = 1 := by
    rintro _ ⟨t, htT, rfl⟩
    have h1 : orderOf (φ t) ∣ Nat.card T := by
      rw [MulEquiv.orderOf_eq]
      exact Subgroup.orderOf_dvd_natCard T htT
    have hcop : Nat.Coprime 3 (orderOf (φ t)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hT3' (h.trans h1)
    have h2 : (φ t).right ^ orderOf (φ t) = 1 := by
      have := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))
        (pow_orderOf_eq_one (φ t))
      rw [map_pow, map_one] at this
      exact this
    have h3 : (φ t).right ^ 3 = 1 := by
      rw [← hGal]
      exact pow_card_eq_one'
    have h4 : orderOf (φ t).right ∣ Nat.gcd 3 (orderOf (φ t)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have hTb_in : ∀ x ∈ Tb, x ∈ (incl F).range := by
    intro x hx
    have hx' : x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl (hTb_right x hx)
    obtain ⟨z, hz⟩ := toPGL_surjective_charTwo x.left
    exact ⟨z, by rw [hx', incl_apply, hz]⟩
  let T' : Subgroup (PSL2 F) := Tb.comap (incl F)
  have hT'map : T'.map (incl F) = Tb := Subgroup.map_comap_eq_self (fun x hx => hTb_in x hx)
  have hT'card : Nat.card T' = Nat.card T := by
    calc Nat.card T' = Nat.card (T'.map (incl F)) :=
          (Subgroup.card_map_of_injective (incl_injective F)).symm
      _ = Nat.card Tb := by rw [hT'map]
      _ = Nat.card T := Subgroup.card_map_of_injective φ.injective
  have hnorm' : ∀ x ∈ T', y' * x * y'⁻¹ ∈ T' := by
    intro x hx
    have hxb : incl F x ∈ Tb := hx
    obtain ⟨t, htT, ht⟩ := hxb
    have h1 : MulAut.conj s * t * (MulAut.conj s)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 hnorm t).1 htT
    show incl F (y' * x * y'⁻¹) ∈ Tb
    rw [map_mul, map_mul, map_inv, ← hφa]
    refine ⟨MulAut.conj s * t * (MulAut.conj s)⁻¹, h1, ?_⟩
    show φ (MulAut.conj s * t * (MulAut.conj s)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
  have hT'bot : T' = ⊥ := core_eight (show Nat.card F = 8 from hF) hy'3 hy'1
    (by rw [hT'card]; exact hT3') hnorm'
  have : Tb = ⊥ := by rw [← hT'map, hT'bot, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective T (f := φ.toMonoidHom) φ.injective).1 this

section Case

variable {X : Type} [Group X] [Finite X]

theorem l2EightCase
    {K B : Subgroup X}
    (hcore : GLAPPrimeCore 3 X = ⊥) (hcomp : GLAPComponent 3 ⊤ K) (hscp : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 8) (e : ↥K ⧸ Subgroup.center ↥K ≃* PSL2 F) :
    IsStronglyBalancedIn 3 B K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hcore hcomp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have h3K : 3 ∣ Nat.card K := i116e_dvd_card hp hcore hcomp
  have hZ : Subgroup.center ↥K = ⊥ := l2Eight_center_eq_bot hF hq e
  obtain ⟨x, hxB, hxK, hx1, hxp⟩ := exists_mem_inf_of_isSCp hp hscp hBN h3K
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer hxK
  refine isStronglyBalancedIn_of_autImage hq.1 fun T hT hAN => ?_
  have hT3' : ¬ 3 ∣ Nat.card T := (Nat.Prime.coprime_iff_not_dvd hp).1 hT
  set s : ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk (⟨x, hxK⟩ : ↥K) with hs
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← QuotientGroup.mk_pow]
    have : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hxp)
    rw [this, QuotientGroup.mk_one]
  have hs1 : s ≠ 1 := by
    intro h
    rw [hs, QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot] at h
    exact hx1 (congrArg Subtype.val h)
  have hmem : (MulAut.conj s : MulAut (↥K ⧸ Subgroup.center ↥K)) ∈ autImage B K :=
    mem_autImage.2 ⟨x, hxN, hxB, actHom_of_mem K hxK⟩
  exact l2Eight_balance_of_conj hF e hs3 hs1 hT3' (hAN hmem)

end Case

end CFSG.HardMathSupport.Dickson.I271.Amb
