module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Avg
public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.LieType.ChevTwo (Chev2CoreCent autCentralizer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

theorem eq_bot_of_normal_two_subgroup (hCore : Chev2CoreCent) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hCh : IsChevTwo S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (R : Subgroup (MulAut S)) (hR : IsPGroup p R) (Cb Ub : Subgroup S)
    (hCW : Cb ≤ autCentralizer R) (hCn : autCentralizer R ≤ Subgroup.normalizer (Cb : Set S))
    (hUC : Ub ≤ Cb) (hUn : Cb ≤ Subgroup.normalizer (Ub : Set S)) (hU2 : IsPGroup 2 Ub) :
    Ub = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Ub ≤ pCoreOf 2 Cb :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUC hUn hU2
  have h2 : pCoreOf 2 Cb ≤ pCoreOf 2 (autCentralizer R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Cb).trans hCW)
      (fun w hw => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Cb (hCn hw))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Cb)
  rw [hCore S hs hna hCh p hp hp2 R hR] at h2
  exact eq_bot_iff.2 (h1.trans h2)

section Inter

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

@[expose] def CKE (K : Subgroup X) (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) : Subgroup ↥K where
  carrier := {y | ∀ e ∈ E, K.normalizerMonoidHom e y = y}
  mul_mem' := fun {a b} ha hb e he => by rw [map_mul, ha e he, hb e he]
  one_mem' := fun e _ => map_one _
  inv_mem' := fun {a} ha e he => by rw [map_inv, ha e he]

@[expose] noncomputable def Cb (K : Subgroup X)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) : Subgroup (Kbar K) :=
  (CKE K E).map (QuotientGroup.mk' (Subgroup.center ↥K))

@[expose] noncomputable def Ub (K : Subgroup X)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) : Subgroup (Kbar K) :=
  ((pCoreOf 2 (Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X))))).map
    (rhoK K)).comap (MulAut.conj : Kbar K →* MulAut (Kbar K))

theorem mem_Ub {E : Subgroup ↥(Subgroup.normalizer (K : Set X))} {a : Kbar K} :
    a ∈ Ub K E ↔ MulAut.conj a ∈
      (pCoreOf 2 (Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X))))).map
        (rhoK K) := Iff.rfl

theorem mem_centralizer_of_mem_CKE {E : Subgroup ↥(Subgroup.normalizer (K : Set X))} {y : ↥K}
    (hy : y ∈ CKE K E) :
    (⟨(y : X), Subgroup.le_normalizer y.2⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
      Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := congrArg (fun z : ↥K => (z : X)) (hy e he)
  have h2 : (e : X) * (y : X) * (e : X)⁻¹ = (y : X) := h1
  apply Subtype.ext
  show (e : X) * (y : X) = (y : X) * (e : X)
  calc (e : X) * (y : X) = ((e : X) * (y : X) * (e : X)⁻¹) * (e : X) := by group
    _ = (y : X) * (e : X) := by rw [h2]

theorem Cb_le_autCentralizer (K : Subgroup X)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    Cb K E ≤ autCentralizer (E.map (rhoK K)) := by
  rintro _ ⟨y, hy, rfl⟩
  intro α hα
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hα
  show rhoK K e (QuotientGroup.mk y) = QuotientGroup.mk y
  rw [rhoK_mk, hy e he]

theorem autCentralizer_le_normalizer_Cb (K : Subgroup X)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    autCentralizer (E.map (rhoK K)) ≤ Subgroup.normalizer (Cb K E : Set (Kbar K)) := by
  have hconj : ∀ b ∈ autCentralizer (E.map (rhoK K)), ∀ c ∈ Cb K E, b * c * b⁻¹ ∈ Cb K E := by
    intro b hb c hc
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨kb, rfl⟩ := QuotientGroup.mk_surjective b
    have hz : ∀ e ∈ E, kb⁻¹ * K.normalizerMonoidHom e kb ∈ Subgroup.center ↥K := by
      intro e he
      have h1 : rhoK K e (QuotientGroup.mk kb) = QuotientGroup.mk kb :=
        hb (rhoK K e) (Subgroup.mem_map_of_mem _ he)
      rw [rhoK_mk] at h1
      exact (QuotientGroup.eq.1 h1.symm)
    refine ⟨kb * y * kb⁻¹, ?_, ?_⟩
    · intro e he
      have hze := hz e he
      have hk : K.normalizerMonoidHom e kb = kb * (kb⁻¹ * K.normalizerMonoidHom e kb) := by group
      have hcomm : (kb⁻¹ * K.normalizerMonoidHom e kb) * y =
          y * (kb⁻¹ * K.normalizerMonoidHom e kb) := (Subgroup.mem_center_iff.1 hze y).symm
      rw [map_mul, map_mul, map_inv, hy e he]
      set z := kb⁻¹ * K.normalizerMonoidHom e kb with hzdef
      rw [hk]
      calc kb * z * y * (kb * z)⁻¹ = kb * (z * y) * z⁻¹ * kb⁻¹ := by group
        _ = kb * (y * z) * z⁻¹ * kb⁻¹ := by rw [hcomm]
        _ = kb * y * kb⁻¹ := by group
    · show QuotientGroup.mk (kb * y * kb⁻¹) = QuotientGroup.mk kb * QuotientGroup.mk y *
        (QuotientGroup.mk kb)⁻¹
      rfl
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact hconj b hb c hc
  · intro hc
    have hbinv : b⁻¹ ∈ autCentralizer (E.map (rhoK K)) := (autCentralizer _).inv_mem hb
    have h1 := hconj b⁻¹ hbinv _ hc
    have e : b⁻¹ * (b * c * b⁻¹) * b⁻¹⁻¹ = c := by group
    rwa [e] at h1

theorem Cb_le_normalizer_Ub (K : Subgroup X) (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) :
    Cb K E ≤ Subgroup.normalizer (Ub K E : Set (Kbar K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hone : ∀ c ∈ Cb K E, ∀ a ∈ Ub K E, c * a * c⁻¹ ∈ Ub K E := by
    intro c hc a ha
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨q, hq, hqa⟩ := Subgroup.mem_map.1 (mem_Ub.1 ha)
    set yN : ↥(Subgroup.normalizer (K : Set X)) :=
      ⟨(y : X), Subgroup.le_normalizer y.2⟩ with hyN
    have hyC := mem_centralizer_of_mem_CKE hy
    have hqm : yN * q * yN⁻¹ ∈ pCoreOf 2
        (Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X)))) :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyC) q).1 hq
    rw [mem_Ub]
    refine ⟨yN * q * yN⁻¹, hqm, ?_⟩
    rw [map_mul, map_mul, map_inv, hqa, rhoK_conj y]
    simp [map_mul, map_inv]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact hone c hc a ha
  · intro ha
    have h1 := hone c⁻¹ ((Cb K E).inv_mem hc) _ ha
    have e : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
    rwa [e] at h1

theorem isPGroup_Ub (K : Subgroup X) (hK : IsComponentOf K ⊤)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) : IsPGroup 2 (Ub K E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map (rhoK K)).comap_of_injective
    (MulAut.conj : Kbar K →* MulAut (Kbar K)) (conj_injective_of_center_bot (center_Kbar hK))

theorem conj_mem_centralizer {n : ↥(Subgroup.normalizer (K : Set X))} {c : X}
    (hc : c ∈ Subgroup.centralizer (K : Set X)) :
    (n : X) * c * (n : X)⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : (n : X)⁻¹ * k * (n : X) ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n.2) k).1 hk
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hk'
  calc k * ((n : X) * c * (n : X)⁻¹)
      = (n : X) * (((n : X)⁻¹ * k * (n : X)) * c) * (n : X)⁻¹ := by group
    _ = (n : X) * (c * ((n : X)⁻¹ * k * (n : X))) * (n : X)⁻¹ := by rw [h1]
    _ = ((n : X) * c * (n : X)⁻¹) * k := by group

theorem Ub_le_Cb (hK : IsComponentOf K ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hE : IsPGroup p E) :
    Ub K E ≤ Cb K E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥E := Fintype.ofFinite _
  intro a ha
  obtain ⟨q, hq, hqa⟩ := Subgroup.mem_map.1 (mem_Ub.1 ha)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
  set kN : ↥(Subgroup.normalizer (K : Set X)) := ⟨(k : X), Subgroup.le_normalizer k.2⟩ with hkN
  have hρk : rhoK K kN = MulAut.conj (QuotientGroup.mk k : Kbar K) := rhoK_conj k
  have hc : rhoK K (kN⁻¹ * q) = 1 := by rw [map_mul, map_inv, hρk, hqa, inv_mul_cancel]
  have hcC : ((kN⁻¹ * q : ↥(Subgroup.normalizer (K : Set X))) : X) ∈
      Subgroup.centralizer (K : Set X) := (rhoK_eq_one_iff hK (kN⁻¹ * q).2).1 hc
  have hq' : q ∈ Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X))) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have hqX : (q : X) = (k : X) * ((kN⁻¹ * q : ↥(Subgroup.normalizer (K : Set X))) : X) := by
    have : q = kN * (kN⁻¹ * q) := by group
    exact congrArg Subtype.val this
  have hz : ∀ e : ↥E, k⁻¹ * K.normalizerMonoidHom (e : ↥(Subgroup.normalizer (K : Set X))) k ∈
      Subgroup.center ↥K := by
    intro e
    have hcomm : ((e : ↥(Subgroup.normalizer (K : Set X))) : X) * (q : X) =
        (q : X) * ((e : ↥(Subgroup.normalizer (K : Set X))) : X) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hq' _ e.2)
    set cX : X := ((kN⁻¹ * q : ↥(Subgroup.normalizer (K : Set X))) : X) with hcX
    set eX : X := ((e : ↥(Subgroup.normalizer (K : Set X))) : X) with heX
    have hcomm' : eX * ((k : X) * cX) * eX⁻¹ = (k : X) * cX := by
      rw [← hqX]
      calc eX * (q : X) * eX⁻¹ = (q : X) * eX * eX⁻¹ := by rw [hcomm]
        _ = (q : X) := by group
    have hzX : (k : X)⁻¹ * (eX * (k : X) * eX⁻¹) = cX * (eX * cX * eX⁻¹)⁻¹ := by
      calc (k : X)⁻¹ * (eX * (k : X) * eX⁻¹)
          = (k : X)⁻¹ * (eX * ((k : X) * cX) * eX⁻¹) * (eX * cX * eX⁻¹)⁻¹ := by group
        _ = (k : X)⁻¹ * ((k : X) * cX) * (eX * cX * eX⁻¹)⁻¹ := by rw [hcomm']
        _ = cX * (eX * cX * eX⁻¹)⁻¹ := by group
    have hzC : (k : X)⁻¹ * (eX * (k : X) * eX⁻¹) ∈ Subgroup.centralizer (K : Set X) := by
      rw [hzX]
      exact Subgroup.mul_mem _ hcC (Subgroup.inv_mem _ (conj_mem_centralizer hcC))
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 hzC (g : X) g.2
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, heX] using this
  obtain ⟨y, hyfix, w, hw, hyw⟩ := average_fixed (K.normalizerMonoidHom.comp E.subtype) k hz
  have hy : y ∈ CKE K E := fun e he => hyfix ⟨e, he⟩
  obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X))))) ⟨q, hq⟩
  have hqb : q ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
  have hkb : (QuotientGroup.mk k : Kbar K) ^ (2 ^ b) = 1 := by
    apply conj_injective_of_center_bot (center_Kbar hK)
    rw [map_pow, ← hqa, ← map_pow, hqb, map_one, map_one]
  have hm : Odd (Fintype.card ↥E) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE
    rw [← Nat.card_eq_fintype_card, hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hcop : Nat.Coprime (Fintype.card ↥E) (orderOf (QuotientGroup.mk k : Kbar K)) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hkb) ?_
    refine Nat.Coprime.pow_right b ?_
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h))).symm
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have hmy : (QuotientGroup.mk y : Kbar K) = (QuotientGroup.mk k) ^ Fintype.card ↥E := by
    rw [hyw, QuotientGroup.mk_mul, QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff w).2 hw,
      mul_one]
  refine ⟨y ^ t, Subgroup.pow_mem _ hy t, ?_⟩
  show QuotientGroup.mk (y ^ t) = QuotientGroup.mk k
  rw [QuotientGroup.mk_pow, hmy, ht]

theorem rho_pCore_inner_eq_one (hCore : Chev2CoreCent) (hK : IsComponentOf K ⊤)
    (hCh : IsChevTwo (Kbar K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup ↥(Subgroup.normalizer (K : Set X))) (hE : IsPGroup p E)
    {q : ↥(Subgroup.normalizer (K : Set X))}
    (hq : q ∈ pCoreOf 2 (Subgroup.centralizer (E : Set ↥(Subgroup.normalizer (K : Set X)))))
    (hqI : rhoK K q ∈ Kinn K) : rhoK K q = 1 := by
  obtain ⟨a, ha⟩ := hqI
  have haU : a ∈ Ub K E := mem_Ub.2 ⟨q, hq, ha.symm⟩
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  have hU : Ub K E = ⊥ :=
    eq_bot_of_normal_two_subgroup hCore inferInstance (isQuasisimple_of_comp hK).2.2 hCh hp hp2
      (E.map (rhoK K)) (hE.map _) (Cb K E) (Ub K E) (Cb_le_autCentralizer K E)
      (autCentralizer_le_normalizer_Cb K E) (Ub_le_Cb hK hp hp2 E hE)
      (Cb_le_normalizer_Ub K E) (isPGroup_Ub K hK E)
  rw [hU, Subgroup.mem_bot] at haU
  rw [← ha, haU, map_one]

end Inter

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
