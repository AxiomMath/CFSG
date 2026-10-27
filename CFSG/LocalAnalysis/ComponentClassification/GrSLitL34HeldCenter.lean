module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34HeldCenterHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34HeldCenterCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.L34HeldCenter

open CFSG Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem orderOf_eq_four {H : Type*} [Group H] {x : H} (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) :
    orderOf x = 4 := by
  have hd : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [h4])
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hi2 : i = 2 := by
    by_contra hne
    apply h2
    rw [← orderOf_dvd_iff_pow_eq_one, hix]
    exact (pow_dvd_pow 2 (show i ≤ 1 by omega)).trans (by norm_num)
  rw [hix, hi2]
  norm_num

theorem false_of_comm {H : Type*} [Group H]
    (hH : ∀ x y : H, x * y = y * x → orderOf x = 4 → orderOf y = 5 → False)
    {M K J : Subgroup G} (hKM : K ≤ M) (hK : IsPComponent 2 (K.subgroupOf M))
    (e : K ⧸ pPrimeCore 2 K ≃* H) (hJM : J ≤ M) (hJKO : J ≤ K ⊔ oddIn M) {w v : G}
    (hwJ : w ∈ J) (hvJ : v ∈ J) (hvw : v * w = w * v) (hw4 : w ^ 4 = 1)
    (hw2 : w * w ∉ oddIn J) (hvO : v ∉ oddIn J) {n : ℕ} (hvn : v ^ 5 ^ n = 1) : False := by
  have hON : M ≤ normalizer ((oddIn M : Subgroup G) : Set G) := GrS4.self_le_normalizer_oddIn M
  have hOM : oddIn M ≤ M := map_subtype_le _
  have hdec : ∀ j ∈ J, ∃ o ∈ oddIn M, ∃ k ∈ K, o * k = j := by
    intro j hj
    have hj' : j ∈ ((oddIn M : Subgroup G) : Set G) * (K : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hKM.trans hON), sup_comm]
      exact hJKO hj
    obtain ⟨o, ho, k, hk, h⟩ := hj'
    exact ⟨o, ho, k, hk, h⟩
  obtain ⟨o₁, ho₁, k₁, hk₁, rfl⟩ := hdec w hwJ
  obtain ⟨o₂, ho₂, k₂, hk₂, rfl⟩ := hdec v hvJ
  have hπ : ∀ m : ↥M, QuotientGroup.mk' (pPrimeCore 2 ↥M) m = 1 ↔ (m : G) ∈ oddIn M := by
    intro m
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_map_iff_mem M.subtype_injective).symm
  set θ : ↥K →* H := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥K)) with hθdef
  set ψ : ↥K →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hKM) with hψdef
  have hker : ∀ k : ↥K, θ k = 1 ↔ ψ k = 1 := by
    intro k
    rw [hθdef, hψdef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquivClass.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hπ,
      ← mem_map_iff_mem K.subtype_injective]
    exact ⟨fun h => Sol25.oddIn_le_of_isPComponent hKM hK h,
      fun h => Sol25.inf_le_oddIn hKM (mem_inf.2 ⟨h, k.2⟩)⟩
  have hθψ : ∀ k k' : ↥K, θ k = θ k' ↔ ψ k = ψ k' := by
    intro k k'
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hker, map_mul, map_inv, inv_mul_eq_one]
  have hψ : ∀ (o k : G) (ho : o ∈ oddIn M) (hk : k ∈ K),
      ψ ⟨k, hk⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨o * k, mul_mem (hOM ho) (hKM hk)⟩ := by
    intro o k ho hk
    rw [show (⟨o * k, mul_mem (hOM ho) (hKM hk)⟩ : ↥M) = ⟨o, hOM ho⟩ * inclusion hKM ⟨k, hk⟩
      from rfl, map_mul, (hπ ⟨o, hOM ho⟩).2 ho, one_mul]
    rfl
  set W : ↥M := ⟨o₁ * k₁, mul_mem (hOM ho₁) (hKM hk₁)⟩ with hWdef
  set V : ↥M := ⟨o₂ * k₂, mul_mem (hOM ho₂) (hKM hk₂)⟩ with hVdef
  have hW : ψ ⟨k₁, hk₁⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥M) W := hψ o₁ k₁ ho₁ hk₁
  have hV : ψ ⟨k₂, hk₂⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥M) V := hψ o₂ k₂ ho₂ hk₂
  have hJO : ∀ m : ↥M, (m : G) ∈ J → QuotientGroup.mk' (pPrimeCore 2 ↥M) m = 1 →
      (m : G) ∈ oddIn J :=
    fun m hmJ h => Sol25.inf_le_oddIn hJM (mem_inf.2 ⟨(hπ m).1 h, hmJ⟩)
  have hx4 : θ ⟨k₁, hk₁⟩ ^ 4 = 1 := by
    rw [← map_pow, hker, map_pow, hW, ← map_pow, show W ^ 4 = 1 from Subtype.ext hw4, map_one]
  have hx2 : θ ⟨k₁, hk₁⟩ ^ 2 ≠ 1 := by
    rw [Ne, ← map_pow, hker, map_pow, hW, ← map_pow]
    intro h
    have hW2 : ((W ^ 2 : ↥M) : G) = o₁ * k₁ * (o₁ * k₁) := by
      rw [Subgroup.coe_pow, sq]
    have h' := hJO (W ^ 2) (hW2 ▸ mul_mem hwJ hwJ) h
    rw [hW2] at h'
    exact hw2 h'
  have hy₀n : θ ⟨k₂, hk₂⟩ ^ 5 ^ n = 1 := by
    rw [← map_pow, hker, map_pow, hV, ← map_pow, show V ^ 5 ^ n = 1 from Subtype.ext hvn,
      map_one]
  have hy₀1 : θ ⟨k₂, hk₂⟩ ≠ 1 := by
    rw [Ne, hker, hV]
    exact fun h => hvO (hJO V hvJ h)
  have hxy : θ ⟨k₁, hk₁⟩ * θ ⟨k₂, hk₂⟩ = θ ⟨k₂, hk₂⟩ * θ ⟨k₁, hk₁⟩ := by
    rw [← map_mul, ← map_mul, hθψ, map_mul, map_mul, hW, hV, ← map_mul, ← map_mul,
      show W * V = V * W from Subtype.ext hvw.symm]
  obtain ⟨i, -, hiy⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hy₀n)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hy₀1 (orderOf_eq_one_iff.1 (by rw [hiy, pow_zero]))
  have hdvd : 5 ^ (i - 1) ∣ orderOf (θ ⟨k₂, hk₂⟩) := by
    rw [hiy]
    exact pow_dvd_pow 5 (Nat.sub_le i 1)
  have hy5 : orderOf (θ ⟨k₂, hk₂⟩ ^ 5 ^ (i - 1)) = 5 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hiy,
      Nat.pow_div (Nat.sub_le i 1) (by norm_num), show i - (i - 1) = 1 by omega, pow_one]
  exact hH _ _ (Commute.pow_right hxy _).eq (orderOf_eq_four hx4 hx2) hy5

end CFSG.ComponentClassification.GrSLit.L34HeldCenter

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup L34HeldCenter

theorem l34HeldCenterFact :
    L34HeldCenterFact := by
  intro G _ _ M K J a hKM hK hKe _ _ hJMa _ hJl hJKO u hu
  obtain ⟨e⟩ := hKe
  have hJM : J ≤ M := hJMa.trans inf_le_left
  obtain ⟨u', hu', rfl⟩ := hu
  by_contra hne
  have hne' : u' * u' ∉ pPrimeCore 2 ↥J := fun h => hne ⟨u' * u', h, rfl⟩
  have hu'c : QuotientGroup.mk' (pPrimeCore 2 ↥J) u' ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [Sol78.fusionZStar_eq_comap] at hu'
    exact hu'
  obtain ⟨w, hwc, hw4, hw2⟩ := exists_orderOf_four hu'c hne'
  have hw : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hw4]; norm_num)
  have h5 : 5 ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) := by
    have h1 : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = 20160 := GSThmB.card_of_lieModel_L34 hJl
    have h2 : (Open.fusionZStar ↥J).index ∣ (pPrimeCore 2 ↥J).index :=
      index_dvd_of_le (Sol78.pPrimeCore_le_fusionZStar ↥J)
    rw [index_eq_card, index_eq_card, h1] at h2
    exact (show 5 ∣ 20160 by norm_num).trans h2
  obtain ⟨v, hvw, hvO, n, hvn⟩ := exists_five_comm hw hwc h5
  have hJsub : ∀ x : ↥J, (x : G) ∈ oddIn J ↔ x ∈ pPrimeCore 2 ↥J :=
    fun x => mem_map_iff_mem J.subtype_injective
  have hH : ∀ x y : ↥Sporadic.HeldB.heP, x * y = y * x → orderOf x = 4 → orderOf y = 5 →
      False := fun x y hxy h4 h5 => heP_no_twenty x.2 y.2 (congrArg Subtype.val hxy)
    (by rwa [Subgroup.orderOf_coe]) (by rwa [Subgroup.orderOf_coe])
  refine false_of_comm hH hKM hK (e.trans Sporadic.HeldB.heEquivP) hJM hJKO w.2 v.2
    (congrArg Subtype.val hvw) ?_ ?_ ?_ (n := n) ?_
  · rw [← Subgroup.coe_pow, ← hw4, pow_orderOf_eq_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, hJsub]
    exact hw2
  · rw [hJsub]
    exact hvO
  · rw [← Subgroup.coe_pow, ← hvn, pow_orderOf_eq_one, Subgroup.coe_one]

end CFSG.ComponentClassification.GrSLit
