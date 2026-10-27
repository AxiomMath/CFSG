module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOProps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCov
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOZ
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOMain
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O
open scoped MatrixGroups

namespace P58b

variable {X : Type} [Group X] [Finite X]

theorem isPComponent_map_centralizer {S : Type} [Group S] [Finite S] (π : X →* S)
    (hπ : Function.Surjective π) (hker : π.ker = center X) {t : X} {L : Subgroup X}
    (hL : IsTwoComponentIn L (centralizer {t})) :
    L.map π ≤ centralizer {π t} ∧ IsPComponent 2 ((L.map π).subgroupOf (centralizer {π t})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  have hLt : L ≤ centralizer {t} := hL.1
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer {t})) := (isTwoComponentIn_iff hLt).mp hL
  have hcent : ∀ {x : X}, x ∈ centralizer ({t} : Set X) → π x ∈ centralizer ({π t} : Set S) :=
    fun {x} hx => by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, hx, map_mul]
  have hRv : L.map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent (hLt hx)
  have hH₁v : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent hx
  let πH : ↥(centralizer ({t} : Set X)) →* ↥((centralizer ({t} : Set X)).map π) :=
    (π.comp (centralizer ({t} : Set X)).subtype).codRestrict _ fun h => ⟨h, h.2, rfl⟩
  have hπHs : Function.Surjective πH := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have hπHc : πH.ker ≤ center ↥(centralizer ({t} : Set X)) := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 hx' y)
  have hR₁ : IsPComponent 2 ((L.map π).subgroupOf ((centralizer {t}).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 πH hπHs hπHc
      (L.subgroupOf (centralizer {t})) hLc
    have heq : (L.subgroupOf (centralizer {t})).map πH =
        (L.map π).subgroupOf ((centralizer {t}).map π) := by
      ext ⟨y, hy⟩
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨⟨x, hxH⟩, hxL, hxy⟩
        exact ⟨x, hxL, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hxL, rfl⟩
        exact ⟨⟨x, hLt hxL⟩, hxL, rfl⟩
    rwa [heq] at h
  exact ⟨hRv, UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (map_mono hLt) hH₁v
    (normal_map_centralizer_of_ker π hπ hker t).isSubnormal hR₁⟩

theorem nonempty_psl2_coreQuot (hX : IsQuasisimple X) {S : Type} [Group S] [Finite S]
    (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = center X) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) :
    Nonempty (↥(Q.map π) ⧸ pPrimeCore 2 ↥(Q.map π) ≃* PSL(2, GaloisField p k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  obtain ⟨-, -, hRv, hRc, N, hN, hNodd, ⟨eN⟩⟩ := exists_psl2_component hX π hπ hker hp2 hcfg
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hsimple : IsSimpleGroup PSL(2, GaloisField p k) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 (GaloisField p k) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  let eJ : ↥((Q.map π).subgroupOf (centralizer {π t})) ≃* ↥(Q.map π) :=
    Subgroup.subgroupOfEquivOfLe hRv
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1
    hRc
  have hqR : IsQuasisimple (↥(Q.map π) ⧸ pPrimeCore 2 ↥(Q.map π)) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hq
  have hO : pPrimeCore 2 ↥(Q.map π) = N :=
    pPrimeCore_eq_of_quotient hNodd eN (LocalCores.isQuasisimple_nontrivial hqR)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans eN⟩

theorem eq_one_of_mem_center_of_sl2 (hO : pPrimeCore 2 X = ⊥) {p k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : k ≠ 0) {t : X} (ht2 : orderOf t = 2) (htZ : t ∉ center X)
    {L : Subgroup X} (htL : t ∈ L) (hSL : IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)) {z : X}
    (hzL : z ∈ L) (hzZ : z ∈ center X) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_equiv_galoisField hk hSL
  have hF2 : (2 : GaloisField p k) ≠ 0 := Burgoyne.C.two_ne_zero_galoisField hp2
  have hcen : e (QuotientGroup.mk (⟨z, hzL⟩ : ↥L)) ∈ center SL(2, GaloisField p k) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L))) g
    change e (QuotientGroup.mk y) * e (QuotientGroup.mk ⟨z, hzL⟩) =
      e (QuotientGroup.mk ⟨z, hzL⟩) * e (QuotientGroup.mk y)
    have hyz : y * ⟨z, hzL⟩ = ⟨z, hzL⟩ * y := Subtype.ext (mem_center_iff.1 hzZ y)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hyz]
  have hsq := Burgoyne.C.sq_eq_one_of_mem_center_SL hcen
  have hzz : z * z = 1 := by
    have h1 : (⟨z, hzL⟩ : ↥L) ^ 2 ∈ pPrimeCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← map_eq_one_iff _ e.injective,
        map_pow]
      exact hsq
    have hodd : Odd (orderOf ((⟨z, hzL⟩ : ↥L) ^ 2)) := by
      have h2 : orderOf ((⟨z, hzL⟩ : ↥L) ^ 2) ∣ Nat.card ↥(pPrimeCore 2 ↥L) := by
        rw [← Subgroup.orderOf_mk _ h1]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h2
    have hpow : ∃ a : ℕ, orderOf ((⟨z, hzL⟩ : ↥L) ^ 2) = 2 ^ a := by
      have hZ2 : IsPGroup 2 (center X) := Sol78.center_isPGroup_two hO
      obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hZ2) ⟨z ^ 2, pow_mem hzZ 2⟩
      refine ⟨a, ?_⟩
      rw [← ha, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rfl
    obtain ⟨a, ha⟩ := hpow
    have ha0 : a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact h
      · exfalso
        rw [ha] at hodd
        exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' h.ne').mpr even_two)
    rw [ha0, pow_zero, orderOf_eq_one_iff] at ha
    have := congrArg Subtype.val ha
    rwa [SubgroupClass.coe_pow, pow_two] at this
  by_contra hz1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hneg : ∀ y : ↥L, orderOf (y : X) = 2 → e (QuotientGroup.mk y) = -1 := by
    intro y hy
    have hy' : orderOf y = 2 := by rwa [← Subgroup.orderOf_coe]
    have hyO := Burgoyne.C.not_mem_pPrimeCore_of_orderOf hy'
    have hyy : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy', pow_two] at this
    have hsq' : e (QuotientGroup.mk y) * e (QuotientGroup.mk y) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, hyy, QuotientGroup.mk_one, map_one]
    rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 _ hsq' with h1 | h1
    · exfalso
      rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact hyO h1
    · exact h1
  have hzt := (hneg ⟨z, hzL⟩ hz2).trans (hneg ⟨t, htL⟩ ht2).symm
  have hmem : (⟨z, hzL⟩ : ↥L)⁻¹ * ⟨t, htL⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 (e.injective hzt)
  have hzt2 : orderOf ((⟨z, hzL⟩ : ↥L)⁻¹ * ⟨t, htL⟩) = 2 := by
    rw [← Subgroup.orderOf_coe]
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    have hcomm : z * t = t * z := mem_center_iff.1 hzZ t |>.symm
    apply orderOf_eq_prime
    · change (z⁻¹ * t) ^ 2 = 1
      rw [hzinv, pow_two]
      calc z * t * (z * t) = z * z * (t * t) := by
            rw [mul_assoc, ← mul_assoc t z t, ← hcomm, mul_assoc, mul_assoc]
        _ = 1 := by rw [hzz, htt, one_mul]
    · change z⁻¹ * t ≠ 1
      rw [hzinv]
      intro h1
      apply htZ
      have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, hzinv]
      exact hzZ
  exact Burgoyne.C.not_mem_pPrimeCore_of_orderOf hzt2 hmem

theorem propCData_of_config (hX : IsQuasisimple X) (hO : pPrimeCore 2 X = ⊥) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q L : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) (hL : IsTwoComponentIn L (centralizer {t}))
    (htL : t ∈ L) (hSL : IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)) :
    Burgoyne.C.PropCData (QuotientGroup.mk' (center X) t) (Q.map (QuotientGroup.mk' (center X)))
      (L.map (QuotientGroup.mk' (center X))) p k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center X) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  obtain ⟨hxx, hx1, hRv, hRc, -⟩ := exists_psl2_component hX π hπ hker hp2 hcfg
  obtain ⟨hLv, hLc⟩ := isPComponent_map_centralizer π hπ hker hL
  have hinj : Function.Injective (π.subgroupMap L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hy' : π (y : X) = 1 := congrArg Subtype.val hy
    rw [← MonoidHom.mem_ker, hker] at hy'
    exact Subtype.ext (eq_one_of_mem_center_of_sl2 hO hp2 hk hcfg.2.2.1 hcfg.2.2.2.1 htL hSL y.2
      hy')
  let eL : ↥L ≃* ↥(L.map π) :=
    MulEquiv.ofBijective (π.subgroupMap L) ⟨hinj, MonoidHom.subgroupMap_surjective π L⟩
  obtain ⟨e⟩ := nonempty_equiv_galoisField hk hSL
  refine ⟨hp2, Nat.pos_of_ne_zero hk, orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1, hRv, hRc,
    hLv, hLc, nonempty_psl2_coreQuot hX π hπ hker hp2 hcfg,
    ⟨(Burgoyne.C.quotientPPrimeCoreEquiv eL).symm.trans e⟩, mem_map_of_mem _ htL⟩

end P58b

open P58b

theorem propC_POmegaOdd {S : Type} [Group S] [Finite S] {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hm : Blueprint.LieModel S .POmegaOdd n p' f') {x : S} {R₁ R₂ : Subgroup S} {p k : ℕ}
    [Fact p.Prime] (hC : Burgoyne.C.PropCData x R₁ R₂ p k) : n = 3 ∧ p ^ k = p' ^ f' := by
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
    (regular_coordinateQuadOdd n K h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  obtain ⟨hd7, hcard, -⟩ := Burgoyne.C.orth_propC_odd hK (by omega) ⟨n, rfl⟩ hR
    (hC.map ((coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁)))
  exact ⟨by omega, hcard.symm.trans hKc⟩

theorem propC_POmegaPlus {S : Type} [Group S] [Finite S] {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hm : Blueprint.LieModel S .POmegaPlus n p' f') {x : S} {R₁ R₂ : Subgroup S} {p k : ℕ}
    [Fact p.Prime] (hC : Burgoyne.C.PropCData x R₁ R₂ p k) : False := by
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K)
    (regular_coordinateQuadPlus n K (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact Burgoyne.C.orth_propC_even hK hp hKc hn hR
    (hC.map ((coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁)))

theorem propC_POmegaMinus {S : Type} [Group S] [Finite S] {n p' f' : ℕ} (hp2' : p' ≠ 2)
    (hm : Blueprint.LieModel S .POmegaMinus n p' f') {x : S} {R₁ R₂ : Subgroup S} {p k : ℕ}
    [Fact p.Prime] (hC : Burgoyne.C.PropCData x R₁ R₂ p k) : False := by
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : Fact p'.Prime := ⟨hp⟩
  have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K hn1 b c)
    (regular_coordinateQuadMinus n K b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadMinus n K hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact Burgoyne.C.orth_propC_even hK hp hKc hn hR
    (hC.map ((coordinateMinusWitnessEquiv K hn1 b c e).trans (oTransport 1 1 hS₁)))

theorem harris82Lemma58bRowSL_POmegaOdd (hGA : TBLit.GriessMultipliersAllModels) (n : ℕ) :
    Harris82Lemma58bRowSL .POmegaOdd n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q L hcfg hL htL hSL
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨rfl, hpk⟩ := propC_POmegaOdd hp2 hm (propCData_of_config hX hO hp2 hcfg hL htL hSL)
  have hk : k = f := Nat.pow_right_injective hp.two_le hpk
  subst hk
  exact ⟨hX, card_center_eq_two_of_POmegaOdd hGA hX hO hcfg.1 hcfg.2.1 hm, hm⟩

theorem harris82Lemma58bRowSL_POmegaPlus (n : ℕ) : Harris82Lemma58bRowSL .POmegaPlus n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q L hcfg hL htL hSL
  have : Fact p.Prime := ⟨hp⟩
  exact (propC_POmegaPlus hp2 hm (propCData_of_config hX hO hp2 hcfg hL htL hSL)).elim

theorem harris82Lemma58bRowSL_POmegaMinus (n : ℕ) : Harris82Lemma58bRowSL .POmegaMinus n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q L hcfg hL htL hSL
  have : Fact p.Prime := ⟨hp⟩
  exact (propC_POmegaMinus hp2 hm (propCData_of_config hX hO hp2 hcfg hL htL hSL)).elim

end CFSG.ComponentClassification.HarrisLit.T1
