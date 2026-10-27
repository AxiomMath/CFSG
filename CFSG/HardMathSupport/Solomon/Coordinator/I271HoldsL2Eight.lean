module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Plane
public import CFSG.GH74.Uniqueness.Bender.Core

public noncomputable section

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator.L2Plane

variable {F : Type} [Field F] [Finite F]

theorem toPGL_surjective_charTwo [CharP F 2] :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL2 F →* PGL2 F) := by
  intro g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  haveI : Fintype F := Fintype.ofFinite F
  exact (pgl2_mk_mem_psl2_range_iff_det_isSquare A).2
    (FiniteField.isSquare_of_char_two (ringChar.eq F 2) _)

theorem psl2_not_comm (K : Type) [Field K] [CharP K 2] : ∃ a b : PSL2 K, a * b ≠ b * a := by
  let u : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let v : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨slEquivPsl2 K u, slEquivPsl2 K v, fun h => ?_⟩
  have h1 : u * v = v * u := by
    apply (slEquivPsl2 K).injective
    rw [map_mul, map_mul]
    exact h
  have h2 := congrFun (congrFun (congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) K => (z : Matrix (Fin 2) (Fin 2) K)) h1) 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [u, v, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem isCyclic_sup_of_card_two {G : Type*} [Group G] [Finite G] {T : Subgroup G} {g : G}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hT : Nat.card T = 2)
    (hnorm : ∀ x ∈ T, g * x * g⁻¹ ∈ T) (hH : Nat.card ↥(T ⊔ Subgroup.zpowers g) = 6) :
    IsCyclic ↥(T ⊔ Subgroup.zpowers g) := by
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card T = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
    omega
  have hord2 : orderOf t = 2 := by
    have hd : orderOf t ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard T htT
      rwa [hT] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ht1
    · exact h
  have hTz : T = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 htT) ?_).symm
    rw [Nat.card_zpowers, hord2, hT]
  have hgt : g * t * g⁻¹ = t := by
    have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t := hTz ▸ hnorm t htT
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hne : g * t * g⁻¹ ≠ 1 := by
      intro h
      apply ht1
      have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [this, h]; group
    have hk2 : t ^ k = t ∨ t ^ k = 1 := by
      have hsq : t ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one t
      have : t ^ k = t ^ (k % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
        simp [hsq]
      rw [this]
      rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
    rcases hk2 with h | h
    · rw [← hk, h]
    · exact absurd (hk.symm.trans h) hne
  have hcomm : Commute g t := by
    show g * t = t * g
    exact mul_inv_eq_iff_eq_mul.1 hgt
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hw : orderOf (g * t) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hgord, hord2]; norm_num), hgord, hord2]
  have hwH : g * t ∈ T ⊔ Subgroup.zpowers g :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      (Subgroup.mem_sup_left htT)
  refine isCyclic_of_orderOf_eq_card (⟨g * t, hwH⟩ : ↥(T ⊔ Subgroup.zpowers g)) ?_
  rw [hH, ← hw, Subgroup.orderOf_mk]

theorem core_eight (hF : Nat.card F = 8) {g : PSL2 F}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {T : Subgroup (PSL2 F)} (hT3 : ¬ 3 ∣ Nat.card T)
    (hnorm : ∀ x ∈ T, g * x * g⁻¹ ∈ T) : T = ⊥ := by
  by_contra hTne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hF3 : Nat.card F = 2 ^ 3 := by rw [hF]; norm_num
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hTcard : Nat.card T ≠ 1 := fun h => hTne (Subgroup.eq_bot_of_card_eq _ h)
  have hg2 : g * g = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hg3)
  have hnorm' : ∀ x ∈ T, g⁻¹ * x * g ∈ T := by
    intro x hx
    have h2 := hnorm _ (hnorm x hx)
    have : g * (g * x * g⁻¹) * g⁻¹ = g⁻¹ * x * g := by
      calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g⁻¹ * g⁻¹) := by group
        _ = g⁻¹ * x * g := by
          rw [hg2, ← mul_inv_rev, hg2, inv_inv]
    rwa [this] at h2
  have hnormer : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set (PSL2 F)) := by
    refine (Subgroup.zpowers_le).2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hnorm x hx, fun hx => by
      have := hnorm' _ hx
      simpa [mul_assoc] using this⟩
  have hdisj : T ⊓ Subgroup.zpowers g = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card ↥(T ⊓ Subgroup.zpowers g) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(T ⊓ Subgroup.zpowers g) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ Subgroup.zpowers g ≤ _)
      rwa [Nat.card_zpowers, hgord] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact h
    · exact absurd (h ▸ h1) hT3
  have hHcard : Nat.card ↥(T ⊔ Subgroup.zpowers g) = Nat.card T * 3 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer (A := T)
      (B := Subgroup.zpowers g) hnormer hdisj, Nat.card_zpowers, hgord]
  have hgH : g ∈ T ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have h3H : 3 ∣ Nat.card ↥(T ⊔ Subgroup.zpowers g) := ⟨Nat.card T, by rw [hHcard]; ring⟩
  have hcycT2 : Nat.card T = 2 → IsCyclic ↥(T ⊔ Subgroup.zpowers g) := fun hT2 =>
    isCyclic_sup_of_card_two hg3 hg1 hT2 hnorm (by rw [hHcard, hT2])
  have hT1pos : 0 < Nat.card T := Nat.card_pos
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF3
    (T ⊔ Subgroup.zpowers g) with
    h | ⟨z, hz, hK, hcyc⟩ | ⟨z, hz, hK, ⟨e⟩⟩ | ⟨h4, -⟩ | ⟨h16, -⟩ | ⟨h5, -⟩ |
      ⟨m', t, ht1, ht2, N, C, hN, hNel, hNcard, hC, hCcard, hdisj', hsup⟩ | ⟨m', hm0, hm3, ⟨e⟩⟩ |
      ⟨m', hm0, hm2, -⟩
  · exfalso
    have h1 : orderOf (⟨g, hgH⟩ : ↥(T ⊔ Subgroup.zpowers g)) ∣
        Monoid.exponent ↥(T ⊔ Subgroup.zpowers g) :=
      Monoid.order_dvd_exponent _
    have h2' : Monoid.exponent ↥(T ⊔ Subgroup.zpowers g) ∣ 2 :=
      IsElementaryAbelian.exponent_dvd_p 2 _
    rw [Subgroup.orderOf_mk, hgord] at h1
    have := h1.trans h2'
    omega
  · exfalso
    rw [hF] at hz
    norm_num at hz
    have hz' : Nat.card T * 3 = z := by rw [← hHcard]; exact hK
    have hz9 : z ≤ 9 := by
      rcases hz with hz | hz <;> exact (Nat.le_of_dvd (by norm_num) hz).trans (by norm_num)
    interval_cases z <;> omega
  · exfalso
    rw [hF] at hz
    norm_num at hz
    have hz' : Nat.card T * 3 = 2 * z := by rw [← hHcard]; exact hK
    have hz9 : z ≤ 9 := by
      rcases hz with hz | hz <;> exact (Nat.le_of_dvd (by norm_num) hz).trans (by norm_num)
    have hz3 : z = 3 ∧ Nat.card T = 2 := by
      interval_cases z <;> omega
    obtain ⟨rfl, hTc⟩ := hz3
    haveI hcy : IsCyclic (DihedralGroup 3) := e.isCyclic.1 (hcycT2 hTc)
    have hnc : ¬ ∀ a b : DihedralGroup 3, a * b = b * a := by decide
    exact hnc (fun a b => (IsCyclic.commGroup (α := DihedralGroup 3)).mul_comm a b)
  · exfalso
    rcases h4 with h | h
    · exact h rfl
    · exact absurd h (by decide)
  · exfalso
    norm_num at h16
  · exfalso
    norm_num at h5
  · exfalso
    have hcompl : N.IsComplement' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj'
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hcard := hcompl.card_mul_card
    rw [hNcard, hCcard] at hcard
    have ht : t ∣ 7 := by simpa using ht2
    have h3t : 3 ∣ t := by
      have h3c : 3 ∣ 2 ^ m' * t := by rw [hcard]; exact h3H
      exact (Nat.Coprime.pow_right m' (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h3c
    have := h3t.trans ht
    omega
  · rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
    · exfalso
      have hc : Nat.card ↥(T ⊔ Subgroup.zpowers g) = 6 := by
        rw [Nat.card_congr e.toEquiv]
        haveI : CharP (GaloisField 2 1) 2 := inferInstance
        rw [card_psl2_of_charTwo (GaloisField.card 2 1 one_ne_zero)]
        norm_num
      have hTc : Nat.card T = 2 := by omega
      haveI hcy : IsCyclic (PSL2 (GaloisField 2 1)) := e.isCyclic.1 (hcycT2 hTc)
      obtain ⟨a, b, hab⟩ := psl2_not_comm (GaloisField 2 1)
      exact hab ((IsCyclic.commGroup (α := PSL2 (GaloisField 2 1))).mul_comm a b)
    · exfalso
      have hc : Nat.card ↥(T ⊔ Subgroup.zpowers g) = 504 := by
        rw [Nat.card_congr e.toEquiv]
        haveI : CharP (GaloisField 2 3) 2 := inferInstance
        rw [card_psl2_of_charTwo (GaloisField.card 2 3 (by norm_num))]
        norm_num
      omega
  · exfalso
    have : 2 ∣ 3 := (dvd_mul_right 2 m').trans hm2
    omega


end CFSG.HardMathSupport.Solomon.Coordinator.L2Plane

namespace CFSG.HardMathSupport.Solomon.Coordinator

open L2Plane

theorem autLTwoEightBalance_holds : AutLTwoEightBalance := by
  intro S _ _ hS A hAel h9 T hT3' hAT
  have hT3 : ¬ 3 ∣ Nat.card T := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hT3'
  obtain ⟨K, hK, hfin, hcard, ⟨e0⟩⟩ := hS
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  let e : S ≃* PSL2 K := e0.trans
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.trans (slEquivPsl2 K))
  let φ : MulAut S ≃* PGammaL2 K := autEquiv e
  have hGal : Nat.card (K ≃+* K) = 3 := by
    have := card_ringAut K Nat.prime_two (show Nat.card K = 2 ^ 3 by rw [hcard]; norm_num)
    exact this
  obtain ⟨a, haA, ha1, har⟩ : ∃ a ∈ A, a ≠ 1 ∧ (φ a).right = 1 := by
    let f : A →* (K ≃+* K) :=
      (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).comp
        ((φ : MulAut S ≃* PGammaL2 K).toMonoidHom.comp A.subtype)
    have hcardA := card_eq_card_ker_mul_card_range' f
    have hr : Nat.card f.range ≤ 3 := by
      refine card_le_three_of_cube_ringAut f.range ?_
      rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (hAel.2 x x.2)
      rw [this, map_one]
    have hker : Nat.card f.ker ≠ 1 := by
      intro h1
      rw [h1] at hcardA
      omega
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ f.ker, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hker
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (hcon a a.2 |>.trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
    exact ⟨x, x.2, fun h => hx1 (Subtype.ext h), by simpa [f] using hx⟩
  have hφa3 : (φ a) ^ 3 = 1 := by
    rw [← map_pow]
    have : a ^ 3 = 1 := hAel.2 a haA
    rw [this, map_one]
  have hy : φ a = SemidirectProduct.inl (φ a).left := SemidirectProduct.ext rfl har
  have hy3 : (φ a).left ^ 3 = 1 := by
    rw [hy, ← map_pow] at hφa3
    exact SemidirectProduct.inl_injective (by simpa using hφa3)
  have hy1 : (φ a).left ≠ 1 := by
    intro h
    apply ha1
    apply φ.injective
    rw [hy, h, map_one, map_one]
  obtain ⟨y', hy', hy'1, hy'3⟩ := exists_psl_lift hy3 hy1
  have hφa : φ a = incl K y' := by
    rw [incl_apply, hy', ← hy]
  let Tb : Subgroup (PGammaL2 K) := T.map φ.toMonoidHom
  have hTb_right : ∀ x ∈ Tb, x.right = 1 := by
    rintro _ ⟨t, htT, rfl⟩
    have h1 : orderOf (φ t) ∣ Nat.card T := by
      rw [MulEquiv.orderOf_eq]
      exact Subgroup.orderOf_dvd_natCard T htT
    have hcop : Nat.Coprime 3 (orderOf (φ t)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hT3 (h.trans h1)
    have h2 : (φ t).right ^ orderOf (φ t) = 1 := by
      have := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K))
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
  have hTb_in : ∀ x ∈ Tb, x ∈ (incl K).range := by
    intro x hx
    have hx' : x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl (hTb_right x hx)
    obtain ⟨z, hz⟩ := toPGL_surjective_charTwo x.left
    exact ⟨z, by rw [hx', incl_apply, hz]⟩
  let T' : Subgroup (PSL2 K) := Tb.comap (incl K)
  have hT'map : T'.map (incl K) = Tb := Subgroup.map_comap_eq_self (fun x hx => hTb_in x hx)
  have hT'card : Nat.card T' = Nat.card T := by
    calc Nat.card T' = Nat.card (T'.map (incl K)) :=
          (Subgroup.card_map_of_injective (incl_injective K)).symm
      _ = Nat.card Tb := by rw [hT'map]
      _ = Nat.card T := Subgroup.card_map_of_injective φ.injective
  have hnorm : ∀ x ∈ T', y' * x * y'⁻¹ ∈ T' := by
    intro x hx
    have hxb : incl K x ∈ Tb := hx
    obtain ⟨t, htT, ht⟩ := hxb
    have h1 : a * t * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hAT haA) t).1 htT
    show incl K (y' * x * y'⁻¹) ∈ Tb
    rw [map_mul, map_mul, map_inv, ← hφa]
    refine ⟨a * t * a⁻¹, h1, ?_⟩
    show φ (a * t * a⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
  have hT'bot : T' = ⊥ := core_eight (show Nat.card K = 8 from hcard) hy'3 hy'1
    (by rw [hT'card]; exact hT3) hnorm
  have : Tb = ⊥ := by rw [← hT'map, hT'bot, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective T (f := φ.toMonoidHom) φ.injective).1 this

end CFSG.HardMathSupport.Solomon.Coordinator
