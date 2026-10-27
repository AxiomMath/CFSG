module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropNineGW

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

namespace JankoFrame

variable {G : Type} [Group G] {z : G} (fr : JankoFrame G z)

theorem eq_z_of_mem_E_sup (hz : orderOf z = 2) {x : G} (hx : x ∈ fr.E ⊔ zpowers z)
    (hx2 : orderOf x = 2) : x = z := by
  have hEz : fr.E ≤ normalizer ((zpowers z : Subgroup G) : Set G) := fun e he =>
    centralizer_le_normalizer _ (by rw [centralizer_zpowers_eq_centralizer]; exact fr.E_le he)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hEz] at hx
  obtain ⟨e, he, w, hw, rfl⟩ := Set.mem_mul.mp hx
  have he3 := fr.E_pow_three e he
  have hc : Commute e z := mem_centralizer_singleton_iff.mp (fr.E_le he)
  rcases eq_one_or_eq_of_mem_zpowers hz hw with h | h <;> rw [h] at hx2 ⊢
  · rw [mul_one] at hx2
    exact absurd (eq_one_of_pow_three_of_sq he3 (hx2 ▸ pow_orderOf_eq_one e))
      (ne_one_of_orderOf_eq_two hx2)
  · have h2 : (e * z) ^ 2 = 1 := hx2 ▸ pow_orderOf_eq_one _
    rw [hc.mul_pow, ← hz, pow_orderOf_eq_one, mul_one, hz] at h2
    rw [eq_one_of_pow_three_of_sq he3 h2, one_mul]

theorem centralizer_E_eq (hC1 : centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) :
    centralizer (fr.E : Set G) = fr.E ⊔ zpowers z := by
  rw [← fr.centralizer_E]
  exact (inf_eq_left.mpr
    ((centralizer_le (SetLike.coe_subset_coe.mpr fr.P₁_le_E)).trans hC1)).symm

theorem normalizer_E_le (hz : orderOf z = 2)
    (hC1 : centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) :
    normalizer (fr.E : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have hzE : z ∈ centralizer (fr.E : Set G) := by
    rw [fr.centralizer_E_eq hC1]
    exact mem_sup_right (mem_zpowers z)
  have hw := (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer fr.E hn) z).mp hzE
  rw [fr.centralizer_E_eq hC1] at hw
  have h1 := fr.eq_z_of_mem_E_sup hz hw (by rw [orderOf_conj_eq, hz])
  rw [mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]

theorem E_le_centralizer_P₂ : fr.E ≤ centralizer (fr.P₂ : Set G) := fun x hx =>
  mem_centralizer_iff.mpr fun y hy => fr.E_comm y (fr.P₂_le_E hy) x hx

theorem z_mem_centralizer_P₂ : z ∈ centralizer (fr.P₂ : Set G) :=
  mem_centralizer_iff.mpr fun _ hy => mem_centralizer_singleton_iff.mp (fr.E_le (fr.P₂_le_E hy))

theorem conj_t_mul_mem_P₂ {e : G} (he : e ∈ fr.E) : fr.t * e * fr.t⁻¹ * e ∈ fr.P₂ := by
  have he' : fr.t * e * fr.t⁻¹ ∈ fr.E := (mem_normalizer_iff.mp fr.t_mem_normalizer_E e).mp he
  have ht2 := mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t
  have hcomm := fr.E_comm _ he' _ he
  rw [inv_eq_of_mul_eq_one_right ht2] at he' hcomm ⊢
  rw [← fr.E_inf_centralizer_t]
  refine ⟨mul_mem he' he, mem_centralizer_singleton_iff.mpr ?_⟩
  calc fr.t * e * fr.t * e * fr.t = e * (fr.t * e * fr.t) * fr.t := by rw [hcomm]
    _ = e * fr.t * e * (fr.t * fr.t) := by group
    _ = (fr.t * fr.t) * (e * fr.t * e) := by rw [ht2, mul_one, one_mul]
    _ = fr.t * (fr.t * e * fr.t * e) := by group

variable [Finite G]

theorem isSylowOf_E (hz : orderOf z = 2)
    (hC1 : centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) :
    IsSylowOf (centralizer (fr.P₂ : Set G)) 3 fr.E :=
  isSylowOf_of_normalizer_le (W := centralizer ({z} : Set G)) (n := 3) fr.E_le_centralizer_P₂
    (fr.normalizer_E_le hz hC1) (by rw [fr.card_E]; norm_num)
    (by rw [fr.centralizer_P₂_eq, fr.card_centralizer_s₂]; norm_num)

theorem exists_conj_eq_z (hz : orderOf z = 2)
    (hC1 : centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) {u : G} (hu : orderOf u = 2)
    (hcard : Nat.card (centralizer (fr.P₂ : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) =
      108) : ∃ c ∈ centralizer (fr.P₂ : Set G), c * u * c⁻¹ = z := by
  set D := centralizer (fr.P₂ : Set G) ⊓ centralizer ({u} : Set G)
  obtain ⟨X, hX⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 3)
    (by rw [hcard]; norm_num)
  have hXcard : Nat.card (X.map D.subtype) = Nat.card fr.E := by
    rw [Subgroup.card_map_of_injective D.subtype_injective, hX, fr.card_E]
    norm_num
  have hXD : X.map D.subtype ≤ D := Subgroup.map_subtype_le X
  obtain ⟨k, hkC, hk⟩ := exists_map_conj_eq_of_isSylowOf
    (isSylowOf_of_card_eq (fr.isSylowOf_E hz hC1) (hXD.trans inf_le_left) hXcard)
    (fr.isSylowOf_E hz hC1)
  have hkE : k * u * k⁻¹ ∈ centralizer (fr.E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    rw [← hk] at he
    obtain ⟨x, hx, rfl⟩ := he
    have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp (hXD hx).2
    change k * x * k⁻¹ * (k * u * k⁻¹) = k * u * k⁻¹ * (k * x * k⁻¹)
    calc k * x * k⁻¹ * (k * u * k⁻¹) = k * (x * u) * k⁻¹ := by group
      _ = k * (u * x) * k⁻¹ := by rw [hxu]
      _ = k * u * k⁻¹ * (k * x * k⁻¹) := by group
  rw [fr.centralizer_E_eq hC1] at hkE
  exact ⟨k, hkC, fr.eq_z_of_mem_E_sup hz hkE (by rw [orderOf_conj_eq, hu])⟩

omit [Finite G] in
theorem orderOf_z_mul_t (hz : orderOf z = 2) : orderOf (z * fr.t) = 2 := by
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz
  have ht2 := mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t
  refine orderOf_eq_prime ?_ fun h => fr.t_ne ?_
  · rw [Commute.mul_pow (a := z) (b := fr.t) fr.t_mul_z.symm, sq, sq, hz2, ht2, one_mul]
  · rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hz2]

theorem card_centralizer_P₂_z_mul_t (hset : JankoSetting G z) (p7 : JankoProp7 fr) :
    Nat.card (centralizer (fr.P₂ : Set G) ⊓ centralizer ({z * fr.t} : Set G) : Subgroup G) =
      108 := by
  have h1 : fr.s₂ * z = z * fr.s₂ := mem_centralizer_singleton_iff.mp (fr.E_le fr.s₂_mem_E)
  have h2 : fr.s₂ * fr.t = fr.t * fr.s₂ := mem_centralizer_singleton_iff.mp fr.s₂_mem_centralizer_t
  have hs : fr.s₂ ∈ centralizer ({z * fr.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc fr.s₂ * (z * fr.t) = z * (fr.s₂ * fr.t) := by rw [← mul_assoc, h1, mul_assoc]
      _ = z * fr.t * fr.s₂ := by rw [h2, mul_assoc]
  rw [fr.centralizer_P₂_eq]
  exact (p7.isConj_s₂_iff _ (fr.orderOf_z_mul_t hset.orderOf_z) _ hs fr.s₂_pow_three).mp
    (IsConj.refl _)

theorem oddCoreOf_centralizer_P₂ (hset : JankoSetting G z) (p7 : JankoProp7 fr)
    (hC1 : centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) :
    oddCoreOf (centralizer (fr.P₂ : Set G)) = fr.P₂ := by
  have hz := hset.orderOf_z
  set C := centralizer (fr.P₂ : Set G) with hCdef
  set W := oddCoreOf C
  have hWC : W ≤ C := oddCoreOf_le C
  have hCW : C ≤ normalizer (W : Set G) := le_normalizer_oddCoreOf C
  have hWodd : Odd (Nat.card W) := odd_card_oddCoreOf C
  obtain ⟨c₁, hc₁C, hc₁⟩ := fr.exists_conj_eq_z hz hC1 fr.orderOf_t p7.card_centralizer_P₂_t
  obtain ⟨c₂, hc₂C, hc₂⟩ := fr.exists_conj_eq_z hz hC1 (fr.orderOf_z_mul_t hz)
    (fr.card_centralizer_P₂_z_mul_t hset p7)
  have h1 : Nat.card (W ⊓ centralizer ({fr.t} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    have h := card_inf_centralizer_conj (hCW hc₁C) fr.t
    rw [hc₁] at h
    exact h.symm
  have h2 : Nat.card (W ⊓ centralizer ({z * fr.t} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    have h := card_inf_centralizer_conj (hCW hc₂C) (z * fr.t)
    rw [hc₂] at h
    exact h.symm
  have hBW := CFSG.Walter.J1.card_mul_card_sq_eq_mul (mul_self_eq_one_of_orderOf_eq_two hz)
    (mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t) (ne_one_of_orderOf_eq_two hz)
    (ne_one_of_orderOf_eq_two fr.orderOf_t) (Ne.symm fr.t_ne) fr.t_mul_z.symm W
    (hCW fr.z_mem_centralizer_P₂) (hCW fr.t_mem_centralizer_P₂) hWodd
  rw [h1, h2] at hBW
  have hdvd27 : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) ∣ 27 := by
    have h108 : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) ∣ 27 * 2 ^ 2 := by
      have h := Subgroup.card_dvd_of_le (inf_le_inf_right (centralizer ({z} : Set G)) hWC)
      rw [hCdef, fr.centralizer_P₂_eq, fr.card_centralizer_s₂] at h
      exact h
    exact (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr
      (Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le inf_le_left)))).dvd_of_dvd_mul_right h108
  have hW9 : Nat.card W ∣ 3 ^ 9 :=
    (Dvd.intro _ hBW).trans (by
      rw [show (3 : ℕ) ^ 9 = 27 * 27 * 27 by norm_num]
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul hdvd27 hdvd27) hdvd27)
  have hW3 : IsPGroup 3 W := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hW9
    exact IsPGroup.of_card hk
  have hWE : W ≤ fr.E := le_isSylowOf_of_le_normalizer (fr.isSylowOf_E hz hC1) hW3 hWC hCW
  have hWz : W ⊓ centralizer ({z} : Set G) = W := inf_eq_left.mpr (hWE.trans fr.E_le)
  have hWt : W ≤ centralizer ({fr.t} : Set G) := by
    have h : W ⊓ centralizer ({fr.t} : Set G) = W :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hWz])
    exact inf_eq_left.mp h
  refine le_antisymm ?_ ?_
  · rw [← fr.E_inf_centralizer_t]
    exact le_inf hWE hWt
  · exact le_oddCoreOf (fr.P₂_le_E.trans fr.E_le_centralizer_P₂) (centralizer_le_normalizer _)
      (by rw [fr.card_P₂]; decide)

theorem hasDihedralSylowTwo (hz : orderOf z = 2) :
    GorensteinWalter.HasDihedralSylowTwo (centralizer (fr.P₂ : Set G)) := by
  intro S
  obtain ⟨T, hT⟩ := fr.isSylowOf_V hz
  have := fr.isKleinFour_V hz
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := fr.V) (G₂ := DihedralGroup 2)
  refine ⟨1, le_rfl, ⟨?_⟩⟩
  rw [pow_one]
  exact ((Sylow.equiv S T).trans ((Subgroup.equivMapOfInjective _ _
    (centralizer (fr.P₂ : Set G)).subtype_injective).trans (MulEquiv.subgroupCongr hT))).trans e

theorem not_eight_dvd_card (hz : orderOf z = 2) :
    ¬ 8 ∣ Nat.card (centralizer (fr.P₂ : Set G)) := fun h => by
  obtain ⟨X, hX⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer (fr.P₂ : Set G)) 2
    (n := 3) (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h)
  have hcard : Nat.card (X.map (centralizer (fr.P₂ : Set G)).subtype) = 2 ^ 3 := by
    rw [Subgroup.card_map_of_injective (centralizer _).subtype_injective, hX]
  have h1 := card_le_of_isSylowOf (fr.isSylowOf_V hz) (IsPGroup.of_card hcard)
    (Subgroup.map_subtype_le X)
  rw [hcard, fr.card_V hz] at h1
  norm_num at h1

end JankoFrame

theorem jankoStep9
    : JankoStep9 := by
  intro G _ _ z fr hset _ p7 hC1
  have hz := hset.orderOf_z
  have hcore := fr.oddCoreOf_centralizer_P₂ hset p7 hC1
  set C := centralizer (fr.P₂ : Set G)
  have hmem : ∀ c : C, c ∈ CFSG.pPrimeCore 2 C ↔ (c : G) ∈ fr.P₂ := fun c => by
    rw [← hcore, oddCoreOf]
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).symm
  have hEC : fr.E ≤ C := fr.E_le_centralizer_P₂
  have hEP : ¬ fr.E ≤ fr.P₂ := fun h => by
    have := Subgroup.card_le_of_le h
    rw [fr.card_E, fr.card_P₂] at this
    norm_num at this
  rcases GorensteinWalter.gorensteinWalter C (fr.hasDihedralSylowTwo hz) with
    ⟨-, h2⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, K, hK, L, hLn, hLi, hLm⟩
  ·
    refine hEP fun e he => ?_
    obtain ⟨k, hk⟩ := h2 ((⟨e, hEC he⟩ : C) : C ⧸ CFSG.pPrimeCore 2 C)
    have h3 : ((⟨e, hEC he⟩ : C) : C ⧸ CFSG.pPrimeCore 2 C) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, show (⟨e, hEC he⟩ : C) ^ 3 = 1 from
        Subtype.ext (fr.E_pow_three e he), QuotientGroup.mk_one]
    have h := pow_gcd_eq_one.mpr ⟨h3, hk⟩
    rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one, pow_one,
      QuotientGroup.eq_one_iff, hmem] at h
    exact h
  ·
    have h8 : 8 ∣ Nat.card (C ⧸ CFSG.pPrimeCore 2 C) := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    exact fr.not_eight_dvd_card hz (h8.trans (Subgroup.card_quotient_dvd_card _))
  rcases hLm with hψ | hψ <;> obtain ⟨ψ⟩ := hψ
  ·
    have : L.Normal := hLn
    have hzC : z ∈ C := fr.z_mem_centralizer_P₂
    have htC : fr.t ∈ C := fr.t_mem_centralizer_P₂
    let f : C →* C ⧸ CFSG.pPrimeCore 2 C := QuotientGroup.mk' _
    have hf : ∀ c : C, f c = 1 ↔ (c : G) ∈ fr.P₂ := fun c => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmem]
    let g : fr.E →* C ⧸ CFSG.pPrimeCore 2 C := f.comp (Subgroup.inclusion hEC)
    have ht2 : (⟨fr.t, htC⟩ : C) ^ 2 = 1 :=
      Subtype.ext (by simpa [sq] using mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t)
    have hz2 : (⟨z, hzC⟩ : C) ^ 2 = 1 :=
      Subtype.ext (by simpa [sq] using mul_self_eq_one_of_orderOf_eq_two hz)
    have htL : f ⟨fr.t, htC⟩ ∈ L :=
      mem_of_sq_eq_one_of_odd_index hLi (by rw [← map_pow, ht2, map_one])
    have hgL : ∀ e, g e ∈ L := fun e => by
      refine mem_of_conj_eq_inv hLn htL ?_ ?_
      · rw [← mul_eq_one_iff_eq_inv]
        change f ⟨fr.t, htC⟩ * f (Subgroup.inclusion hEC e) * (f ⟨fr.t, htC⟩)⁻¹ *
          f (Subgroup.inclusion hEC e) = 1
        have h := (hf (⟨fr.t, htC⟩ * Subgroup.inclusion hEC e * (⟨fr.t, htC⟩ : C)⁻¹ *
          Subgroup.inclusion hEC e)).mpr (fr.conj_t_mul_mem_P₂ e.2)
        simpa only [map_mul, map_inv] using h
      · rw [← map_pow, show e ^ 3 = 1 from Subtype.ext (fr.E_pow_three _ e.2), map_one]
    have hgz : ∀ e, g e * f ⟨z, hzC⟩ = f ⟨z, hzC⟩ * g e := fun e => by
      change f (Subgroup.inclusion hEC e) * f ⟨z, hzC⟩ = f ⟨z, hzC⟩ * f (Subgroup.inclusion hEC e)
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp (fr.E_le e.2)))
    have hg3 : ∀ e, g e ^ 3 = 1 := fun e => by
      rw [← map_pow, show e ^ 3 = 1 from Subtype.ext (fr.E_pow_three _ e.2), map_one]
    have hz1 : f ⟨z, hzC⟩ ≠ 1 := fun h => by
      have hzP := (hf _).mp h
      exact ne_one_of_orderOf_eq_two hz (eq_one_of_pow_three_of_sq
        (fr.E_pow_three z (fr.P₂_le_E hzP)) (hz ▸ pow_orderOf_eq_one z))
    have hcard := card_le_three_mul_card_ker hK hLi ψ (by rw [← map_pow, hz2, map_one]) hz1 g
      hgL hgz hg3
    have hker : Nat.card g.ker ≤ 3 := by
      have hle : g.ker.map fr.E.subtype ≤ fr.P₂ := by
        rintro _ ⟨e, he, rfl⟩
        exact (hf _).mp he
      have h := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective fr.E.subtype_injective, fr.card_P₂] at h
    rw [fr.card_E] at hcard
    omega
  ·
    have h8 : 8 ∣ Nat.card L := by
      rw [Nat.card_congr ψ.toEquiv]
      exact eight_dvd_card_pgl2 (odd_of_isOddPrimePower hK)
    exact fr.not_eight_dvd_card hz ((h8.trans (Subgroup.card_subgroup_dvd_card L)).trans
      (Subgroup.card_quotient_dvd_card _))

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
