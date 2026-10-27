module

public import CFSG.GH74.GLS.C3.Layer1.St1Theta
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped Pointwise commutatorElement

theorem exists_normalized_sylow_two {G : Type} [Group G] [Finite G] (E B : Subgroup G)
    (hB : IsPGroup 2 ↥B) (hBE : B ≤ normalizer (E : Set G)) :
    ∃ P : Subgroup G, P ≤ E ∧ IsPGroup 2 ↥P ∧ 2 ^ (Nat.card ↥E).factorization 2 = Nat.card ↥P ∧
      ∀ b ∈ B, ∀ e ∈ P, b * e * b⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (E : Set G) with hN
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  have hB'p : IsPGroup 2 ↥B' :=
    hB.of_injective (Subgroup.subgroupOfEquivOfLe hBE).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBE).injective
  obtain ⟨P, hP⟩ := hB'p.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥E)
    (not_dvd_card_sylow 2 ↥E)
  refine ⟨(P : Subgroup ↥E).map E.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact P.isPGroup'.map E.subtype
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact P.card_eq_multiplicity.symm
  · intro b hb e he
    have hbN : b ∈ N := hBE hb
    let m : ↥B' := ⟨⟨b, hbN⟩, by simpa [hB', Subgroup.mem_subgroupOf] using hb⟩
    have hm : m • P = P := MulAction.mem_fixedPoints.1 hP m
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
    have h1 : m • e' ∈ m • (P : Subgroup ↥E) := Subgroup.smul_mem_pointwise_smul e' m _ he'
    have h2 : m • (P : Subgroup ↥E) = (P : Subgroup ↥E) :=
      congrArg (fun S : Sylow 2 ↥E => (S : Subgroup ↥E)) hm
    rw [h2] at h1
    refine Subgroup.mem_map.2 ⟨m • e', h1, ?_⟩
    rfl

theorem eq_one_of_mem_of_coprime {G : Type} [Group G] {A P : Subgroup G}
    (hA : Nat.Coprime 2 (Nat.card ↥A)) (hP : IsPGroup 2 ↥P) {z : G} (hzA : z ∈ A) (hzP : z ∈ P) :
    z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨z, hzP⟩
  have h1 : orderOf z = 2 ^ n := by simpa [Subgroup.orderOf_coe] using hn
  have h2 : orderOf z ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A hzA
  rw [h1] at h2
  have h3 : 2 ^ n = 1 := (hA.pow_left n).eq_one_of_dvd h2
  rw [h3] at h1
  exact orderOf_eq_one_iff.1 h1

theorem isElementaryAbelian_two_of_mul_self {G : Type} [Group G] (Q : Subgroup G)
    (h : ∀ q ∈ Q, q * q = 1) : CFSG.IsElementaryAbelian 2 ↥Q :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (by
      have ha := h a a.2
      have hb := h b b.2
      have hab := h (a * b : ↥Q) (a * b).2
      have ha' : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
      have hb' : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
      have hab' : ((a : G) * b)⁻¹ = (a : G) * b := inv_eq_of_mul_eq_one_right hab
      calc (a : G) * b = ((a : G) * b)⁻¹ := hab'.symm
        _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
        _ = (b : G) * a := by rw [ha', hb'])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
        exact h x x.2) }


section KleinFour

open Equiv Equiv.Perm

def alt6a : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩

def alt6b : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by rw [mem_alternatingGroup]; decide⟩

def alt6V : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | x = 1 ∨ x = alt6a ∨ x = alt6b ∨ x = alt6a * alt6b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem alt6V_card : Nat.card ↥alt6V = 4 := by
  have h : (alt6V : Set (alternatingGroup (Fin 6))) =
      ↑({1, alt6a, alt6b, alt6a * alt6b} : Finset (alternatingGroup (Fin 6))) := by
    ext x
    simp [alt6V]
  have h2 : Nat.card ↥alt6V = Set.ncard (alt6V : Set (alternatingGroup (Fin 6))) :=
    Nat.card_coe_set_eq _
  rw [h2, h, Set.ncard_coe_finset]
  decide

theorem alt6V_sq : ∀ v ∈ alt6V, v * v = 1 := by
  intro v hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem klein_of_hasL2Model9 {K : Type} [Group K] (h : HasL2Model K (fun r => r = 9)) :
    ∃ V : Subgroup K, Nat.card ↥V = 4 ∧ (∀ v ∈ V, v * v = 1) ∧
      ∀ z : K, (∀ w : K, z * w = w * z) → z = 1 := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  have hp3 : p = 3 := by
    have h1 : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1)
  subst hp3
  have hf2 : f = 2 := by
    have : (3 : ℕ) ^ f = 3 ^ 2 := by rw [hP]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  subst hf2
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.alternating_six_of_model_nine
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL)
  refine ⟨alt6V.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact alt6V_card
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul, alt6V_sq w hw, map_one]
  · intro z hz
    have hc : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hz w]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])

end KleinFour


theorem exists_big_elemAbelian {G : Type} [Group G] [Finite G] (K B : Subgroup G)
    (hBea : CFSG.IsElementaryAbelian 2 ↥B)
    (hBsec : B ≤ centralizerSection K (pPrimeCoreOf 2 K))
    (V : Subgroup (kBar K)) (hVsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ∣ Nat.card ↥V)
    (hZ : ∀ z : kBar K, (∀ w : kBar K, z * w = w * z) → z = 1) :
    ∃ (m : ℕ) (Q : Subgroup G), 2 ≤ m ∧ (∀ q ∈ Q, q * q = 1) ∧
      Nat.card ↥Q = Nat.card ↥B * 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    rwa [sq] at this
  set YK : Subgroup ↥K := pPrimeCore 2 ↥K with hYK
  set π : ↥K →* kBar K := QuotientGroup.mk' YK with hπ
  set Y : Subgroup G := pPrimeCoreOf 2 K with hY
  set EK : Subgroup ↥K := V.comap π with hEK
  set E : Subgroup G := EK.map K.subtype with hE
  have hπker : ∀ k : ↥K, π k = 1 ↔ k ∈ YK := fun k => QuotientGroup.eq_one_iff k
  have hYmem : ∀ z : ↥K, (z : G) ∈ Y ↔ z ∈ YK := fun z =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  have hYcop : Nat.Coprime 2 (Nat.card ↥Y) := by
    have h1 : Nat.card ↥Y = Nat.card ↥YK := Subgroup.card_map_of_injective K.subtype_injective
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥K)
  have hEK_mem : ∀ k : ↥K, k ∈ EK ↔ π k ∈ V := fun k => Iff.rfl
  have hsec : ∀ g ∈ B, g ∈ normalizer (K : Set G) ∧ ∀ k ∈ K, ⁅k, g⁆ ∈ Y := fun g hg => by
    obtain ⟨hgK, -, hgc⟩ := hBsec hg
    exact ⟨hgK, hgc⟩
  have hconjE : ∀ g ∈ B, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨hgK, hgc⟩ := hsec g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 he
    have hkK : (k : G) ∈ K := k.2
    have hgk : g * (k : G) * g⁻¹ ∈ K := (mem_normalizer_iff.1 hgK _).1 hkK
    have hcomm : ⁅g, (k : G)⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (hgc _ hkK)
    obtain ⟨yK, hyK, hyKeq⟩ := Subgroup.mem_map.1 hcomm
    refine Subgroup.mem_map.2 ⟨⟨g * (k : G) * g⁻¹, hgk⟩, ?_, rfl⟩
    have hyk : (⟨g * (k : G) * g⁻¹, hgk⟩ : ↥K) = yK * k := by
      apply Subtype.ext
      have : (yK : G) = ⁅g, (k : G)⁆ := hyKeq
      simp only [Subgroup.coe_mul, this, commutatorElement_def]
      group
    rw [hEK_mem, hyk, map_mul, (hπker yK).2 hyK, one_mul]
    exact hk
  have hBnorm : B ≤ normalizer (E : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjE g hg h hh, fun hh => ?_⟩
    have := hconjE g⁻¹ (B.inv_mem hg) _ hh
    simpa [mul_assoc] using this
  obtain ⟨P, hPE, hPp, hPcard, hPinv⟩ := exists_normalized_sylow_two E B hBp hBnorm
  have hEK_le : E ≤ K := Subgroup.map_subtype_le _
  have hPK : P ≤ K := hPE.trans hEK_le
  have h4E : 2 ^ 2 ∣ Nat.card ↥E := by
    have h1 : Nat.card ↥E = Nat.card ↥EK := Subgroup.card_map_of_injective K.subtype_injective
    have h2 : EK.map π = V := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) V
    have h3 : Nat.card ↥(EK.map π) ∣ Nat.card ↥EK := Subgroup.card_map_dvd EK π
    rw [h2] at h3
    rw [h1]
    exact (by norm_num : 2 ^ 2 ∣ 4).trans (hV4.trans h3)
  have hm2 : 2 ≤ (Nat.card ↥E).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h4E
  have hPsq : ∀ e ∈ P, e * e = 1 := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 (hPE he)
    have hk2 : π (k * k) = 1 := by
      rw [map_mul]
      exact hVsq _ ((hEK_mem k).1 hk)
    have hkk : ((k * k : ↥K) : G) ∈ Y := (hYmem _).2 ((hπker _).1 hk2)
    exact eq_one_of_mem_of_coprime hYcop hPp (by simpa using hkk) (P.mul_mem he he)
  have hcomm : ∀ b ∈ B, ∀ e ∈ P, b * e = e * b := by
    intro b hb e he
    obtain ⟨hbK, hbc⟩ := hsec b hb
    have h1 : ⁅b, e⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (hbc e (hPK he))
    have h2 : ⁅b, e⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (hPinv b hb e he) (P.inv_mem he)
    have h3 : ⁅b, e⁆ = 1 := eq_one_of_mem_of_coprime hYcop hPp h1 h2
    rw [commutatorElement_def] at h3
    have h4 : b * e * b⁻¹ = e := by
      have := mul_inv_eq_one.1 h3
      exact this
    calc b * e = b * e * b⁻¹ * b := by group
      _ = e * b := by rw [h4]
  have hdisj : ∀ b ∈ B, b ∈ P → b = 1 := by
    intro b hb hbP
    obtain ⟨kb, hkb, hkbeq⟩ := Subgroup.mem_map.1 (hPE hbP)
    have hkb' : (kb : G) = b := hkbeq
    have hcen : ∀ w : kBar K, π kb * w = w * π kb := by
      intro w
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective w
      show π kb * π k' = π k' * π kb
      rw [← map_mul, ← map_mul]
      show ((kb * k' : ↥K) : ↥K ⧸ YK) = ((k' * kb : ↥K) : ↥K ⧸ YK)
      rw [QuotientGroup.eq]
      refine (hYmem _).1 ?_
      have h1 := (hsec b⁻¹ (B.inv_mem hb)).2 ((k' : G)⁻¹) (K.inv_mem k'.2)
      have h2 : (((kb * k')⁻¹ * (k' * kb) : ↥K) : G) = ⁅(k' : G)⁻¹, b⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, hkb']
        group
      rw [h2]
      exact h1
    have h1 : π kb = 1 := hZ _ hcen
    have h2 : (kb : G) ∈ Y := (hYmem _).2 ((hπker _).1 h1)
    rw [hkb'] at h2
    exact eq_one_of_mem_of_coprime hYcop hPp h2 hbP
  let φ : ↥B × ↥P →* G :=
    MonoidHom.noncommCoprod B.subtype P.subtype (fun b e => by
      show (b : G) * (e : G) = (e : G) * (b : G)
      exact hcomm b b.2 e e.2)
  have hφinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨B.subtype_injective, P.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxB hxP
    exact hdisj x hxB hxP
  refine ⟨(Nat.card ↥E).factorization 2, φ.range, hm2, ?_, ?_⟩
  · rintro _ ⟨⟨b, e⟩, rfl⟩
    have h : φ (b, e) = (b : G) * (e : G) := rfl
    rw [h]
    have hb2 := hBsq b b.2
    have he2 := hPsq e e.2
    have hbe : (e : G) * b = b * e := (hcomm b b.2 e e.2).symm
    calc (b : G) * e * ((b : G) * e) = b * (e * b) * e := by group
      _ = b * (b * e) * e := by rw [hbe]
      _ = (b * b) * (e * e) := by group
      _ = 1 := by rw [hb2, he2, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, ← hPcard]

theorem pRank_CxK_add_two_le_of_isIL2Pair_L29
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}
    (hxK : IsIL2Pair x K)
    (hL : HasL2Model (kBar K) (fun q => q = 9)) :
    pRank 2 ↥(CxK x K) + 2 ≤ pRank 2 G := by
  obtain ⟨B, hBle, hBea, hBcard⟩ := exists_elemAbelian_card_pRank (CxK x K)
  obtain ⟨V, hV4, hVsq, hZ⟩ := klein_of_hasL2Model9 hL
  obtain ⟨m, Q, hm, hQsq, hQcard⟩ :=
    exists_big_elemAbelian K B hBea (hBle.trans inf_le_right) V hVsq (by rw [hV4]) hZ
  have hQea := isElementaryAbelian_two_of_mul_self Q hQsq
  have := le_pRank_group_of_elem hQea (k := pRank 2 ↥(CxK x K) + m)
    (by rw [hQcard, hBcard, pow_add])
  omega


theorem b_ivk_rank_add_L29 : B_ivk_rank_add_L29 := by
  intro G _ _ _ x K hxK hL
  exact pRank_CxK_add_two_le_of_isIL2Pair_L29 hxK hL

end CFSG.GH74.GLS.IVK.Proofs2
