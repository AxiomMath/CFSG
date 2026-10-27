module

public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74.GLS Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem oPrimeResidualOf_two_eq_closure (I : Subgroup G) :
    oPrimeResidualOf 2 I = Subgroup.closure {g : G | g ∈ I ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1} := by
  unfold oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨k, hk⟩, rfl⟩
    exact ⟨hx, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hg, k, hk⟩
    exact ⟨⟨g, hg⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem isPGroup_zpowers_of_pow_two_pow_eq_one {a : G} {k : ℕ} (h : a ^ (2 ^ k) = 1) :
    IsPGroup 2 (zpowers a) := fun y =>
  ⟨k, Subtype.ext (by
    simpa using orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one h)))⟩

theorem orderOf_eq_two_of_mem {D : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D) {d : G}
    (hd : d ∈ D) (hd1 : d ≠ 1) : orderOf d = 2 :=
  orderOf_eq_prime (((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 D).mp hD).2 d hd) hd1

theorem sup_zpowers_eq_of_card [Finite G] {S E : Subgroup G} (hSE : S ≤ E)
    (hcard : Nat.card ↥E = 2 * Nat.card ↥S) {e : G} (heE : e ∈ E) (heS : e ∉ S) :
    S ⊔ zpowers e = E := by
  have hle : S ⊔ zpowers e ≤ E := sup_le hSE (zpowers_le.mpr heE)
  have hSle : S ≤ S ⊔ zpowers e := le_sup_left
  have hne : S ≠ S ⊔ zpowers e := fun h => heS (h ▸ mem_sup_right (mem_zpowers e))
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hSle
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  have hdvd : Nat.card ↥(S ⊔ zpowers e) ∣ 2 * Nat.card ↥S := hcard ▸ Subgroup.card_dvd_of_le hle
  rw [hm] at hdvd
  have hm2 : m ∣ 2 := by
    have : Nat.card ↥S * m ∣ Nat.card ↥S * 2 := by rwa [mul_comm 2] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with rfl | rfl
  · exact absurd (Subgroup.eq_of_le_of_card_ge hSle (by rw [hm]; simp)) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hm]; omega)

theorem commutator_le_commutator_commutator_of_oPrimeResidual [Finite G] {I Y : Subgroup G}
    (hIY : I ≤ normalizer (Y : Set G)) (hY : Nat.Coprime 2 (Nat.card ↥Y))
    (hI : oPrimeResidualOf 2 I = I) : ⁅Y, I⁆ ≤ ⁅⁅Y, I⁆, I⁆ := by
  set W := ⁅⁅Y, I⁆, I⁆ with hW
  have hIW : I ≤ normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right _ _
  have hcl : Subgroup.closure {g : G | g ∈ I ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1} ≤ I :=
    (Subgroup.closure_le I).mpr fun g hg => hg.1
  rw [Subgroup.commutator_le]
  intro y hy i hi
  have hi' : i ∈ Subgroup.closure {g : G | g ∈ I ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1} := by
    rw [← oPrimeResidualOf_two_eq_closure, hI]; exact hi
  refine Subgroup.closure_induction (p := fun i _ => ⁅y, i⁆ ∈ W) ?_ ?_ ?_ ?_ hi'
  · rintro a ⟨haI, k, hk⟩
    have hzp : IsPGroup 2 (zpowers a) := isPGroup_zpowers_of_pow_two_pow_eq_one hk
    have hzY : zpowers a ≤ normalizer (Y : Set G) := zpowers_le.mpr (hIY haI)
    have hid := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2
      Nat.prime_two (zpowers a) Y hzp hzY hY
    have h1 : ⁅y, a⁆ ∈ ⁅Y, zpowers a⁆ := commutator_mem_commutator hy (mem_zpowers a)
    rw [← hid] at h1
    have hza : zpowers a ≤ I := zpowers_le.mpr haI
    exact commutator_mono (commutator_mono le_rfl hza) hza h1
  · simp
  · intro a b ha hb iha ihb
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem iha ((mem_normalizer_iff.mp (hIW (hcl ha)) _).mp ihb)
  · intro a ha iha
    have e : ⁅y, a⁻¹⁆ = a⁻¹ * ⁅y, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (hIW (I.inv_mem (hcl ha))) _).mp (W.inv_mem iha)

theorem commutator_inf_centralizer_le_commutator_AG [Finite G] {E I X F : Subgroup G}
    (hFE : F ≤ E) (hIE : I ≤ centralizer (E : Set G)) (hI2 : oPrimeResidualOf 2 I = I)
    (hXodd : Nat.Coprime 2 (Nat.card ↥X)) (hIX : I ≤ normalizer (X : Set G))
    (hloc : ∀ e ∈ E, e ≠ 1 →
      ⁅I, X ⊓ centralizer ({e} : Set G)⁆ ≤ pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    ⁅I, X ⊓ centralizer (F : Set G)⁆ ≤ ⁅I, AG F⁆ := by
  set Y := X ⊓ centralizer (F : Set G) with hY
  have hIY : I ≤ normalizer (Y : Set G) := fun i hi =>
    inf_normalizer_le_normalizer_inf ⟨hIX hi,
      le_normalizer (centralizer_le (SetLike.coe_subset_coe.mpr hFE) (hIE hi))⟩
  have hYodd : Nat.Coprime 2 (Nat.card ↥Y) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hXodd
  have h1 : ⁅I, Y⁆ ≤ AG F := by
    refine Th2Sig6.le_AG fun f hf hf1 => ?_
    refine (commutator_mono le_rfl ?_).trans (hloc f (hFE hf) hf1)
    exact inf_le_inf_left X (centralizer_le (Set.singleton_subset_iff.mpr hf))
  calc ⁅I, Y⁆ = ⁅Y, I⁆ := commutator_comm I Y
    _ ≤ ⁅⁅Y, I⁆, I⁆ := commutator_le_commutator_commutator_of_oPrimeResidual hIY hYodd hI2
    _ = ⁅⁅I, Y⁆, I⁆ := by rw [commutator_comm Y I]
    _ ≤ ⁅AG F, I⁆ := commutator_mono h1 le_rfl
    _ = ⁅I, AG F⁆ := commutator_comm _ _

theorem commutator_eq_bot_of_stability [Finite G] {E I X : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hk : 2 ≤ pRank 2 ↥E)
    (hIE : I ≤ centralizer (E : Set G)) (hI2 : oPrimeResidualOf 2 I = I)
    (hXodd : Nat.Coprime 2 (Nat.card ↥X)) (hEX : E ≤ normalizer (X : Set G))
    (hIX : I ≤ normalizer (X : Set G))
    (hloc : ∀ e ∈ E, e ≠ 1 →
      ⁅I, X ⊓ centralizer ({e} : Set G)⁆ ≤ pPrimeCoreOf 2 (centralizer ({e} : Set G)))
    (hθ : ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ = ⊥) :
    ⁅I, X⁆ = ⊥ := by
  have hE' : CFSG.Open.IsElemAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hE
  have hlarge : 2 ^ (pRank 2 ↥E - 1 + 1) ≤ Nat.card ↥E := Th2Sig6.two_pow_le_card hE (by omega)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
    (pRank 2 ↥E - 1) Nat.prime_two E X hE' hlarge hEX hXodd
  have h2D : ∀ F : Subgroup G, F ≤ E → ⁅I, X ⊓ centralizer (F : Set G)⁆ ≤ ⁅I, AG F⁆ :=
    fun F hFE => commutator_inf_centralizer_le_commutator_AG hFE hIE hI2 hXodd hIX hloc
  have hEI : ⁅E, I⁆ = ⊥ := by
    rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hIE
  have hCXE : X ⊓ centralizer (E : Set G) ≤ centralizer (I : Set G) := by
    have : ⁅I, X ⊓ centralizer (E : Set G)⁆ = ⊥ :=
      le_bot_iff.mp ((h2D E le_rfl).trans
        ((commutator_mono le_rfl Th2Sig10.AG_le_thetaHalf_self).trans hθ.le))
    rw [commutator_comm] at this
    exact commutator_eq_bot_iff_le_centralizer.mp this
  have hhyp : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 (pRank 2 ↥E - 1) E,
      X ⊓ centralizer (S : Set G) ≤ centralizer (I : Set G) := by
    rintro S ⟨hSE, hScard⟩
    have hSe : IsE (pRank 2 ↥E - 1) E S := Th2Sig6.isE_of_card hE hSE hScard
    have hEcard : Nat.card ↥E = 2 * Nat.card ↥S := by
      rw [Th2Sig6.card_eq_two_pow_pRank hE, hScard, ← pow_succ']
      congr 1; omega
    obtain ⟨e, heE, heS⟩ : ∃ e ∈ E, e ∉ S := by
      by_contra hcon
      have hle : E ≤ S := fun e he => by_contra fun heS => hcon ⟨e, he, heS⟩
      have := Subgroup.card_le_of_le hle
      have hpos : 0 < Nat.card ↥S := Nat.card_pos
      omega
    have hSup : S ⊔ zpowers e = E := sup_zpowers_eq_of_card hSE hEcard heE heS
    set Y := X ⊓ centralizer (S : Set G) with hY
    have hAGS : ⁅⁅AG S, E⁆, I⁆ = ⊥ := by
      refine le_bot_iff.mp ((commutator_mono
        (Th2Sig10.commutator_AG_le_thetaHalf_self hSe) le_rfl).trans ?_)
      rw [commutator_comm]; exact hθ.le
    have hthree1 : ⁅⁅I, AG S⁆, E⁆ = ⊥ := by
      refine commutator_commutator_eq_bot_of_rotate (H₁ := I) (H₂ := AG S) (H₃ := E) hAGS ?_
      rw [hEI]; exact commutator_bot_left _
    have hIYE : ⁅⁅I, Y⁆, E⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono (h2D S hSE) le_rfl).trans hthree1.le)
    have hthree2 : ⁅⁅Y, E⁆, I⁆ = ⊥ := by
      refine commutator_commutator_eq_bot_of_rotate (H₁ := Y) (H₂ := E) (H₃ := I) ?_ hIYE
      rw [hEI]; exact commutator_bot_left _
    have hYE : ⁅Y, E⁆ ≤ centralizer (I : Set G) := commutator_eq_bot_iff_le_centralizer.mp hthree2
    have heC : e ∈ centralizer (S : Set G) := mem_centralizer_iff.mpr fun s hs =>
      Th2Sig6.mul_comm_of_isElementaryAbelian hE (hSE hs) heE
    have hzp : IsPGroup 2 (zpowers e) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (k := 1) (by simpa using hE'.2 e heE)
    have hezY : zpowers e ≤ normalizer (Y : Set G) :=
      zpowers_le.mpr (inf_normalizer_le_normalizer_inf ⟨hEX heE, le_normalizer heC⟩)
    have hYodd : Nat.Coprime 2 (Nat.card ↥Y) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hXodd
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
      Nat.prime_two (zpowers e) Y hzp hezY hYodd
    refine hfac.symm.le.trans (sup_le ?_ ?_)
    · exact (commutator_mono le_rfl (zpowers_le.mpr heE)).trans hYE
    · refine le_trans (fun g hg => ?_) hCXE
      obtain ⟨⟨hgX, hgS⟩, hge⟩ := hg
      refine ⟨hgX, ?_⟩
      have hSg : S ≤ centralizer ({g} : Set G) := fun s hs =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgS s hs)
      have hzg : zpowers e ≤ centralizer ({g} : Set G) := zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hge e (mem_zpowers e)))
      have hEg : E ≤ centralizer ({g} : Set G) := hSup ▸ sup_le hSg hzg
      exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hEg hh)
  have hXI : X ≤ centralizer (I : Set G) := hgen.symm.le.trans (iSup₂_le hhyp)
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hXI

theorem stability_special [Finite G] {D E I : Subgroup G}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hE : CFSG.IsElementaryAbelian 2 ↥E) (hk : 2 ≤ pRank 2 ↥E)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d * e = e * d)
    (hI : I ≤ centralizer ((D ⊔ E : Subgroup G) : Set G)) (hI2 : oPrimeResidualOf 2 I = I)
    (h2C : ∀ d ∈ D ⊔ E, ∀ e ∈ D ⊔ E, orderOf d = 2 → orderOf e = 2 → d * e = e * d →
       ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
         pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    (∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) ∨
      ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ ≠ ⊥ := by
  by_cases hθ : ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ = ⊥
  · left
    intro d hd hd1
    have hIE : I ≤ centralizer (E : Set G) :=
      hI.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
    refine commutator_eq_bot_of_stability hE hk hIE hI2 ?_ ?_ ?_ ?_ hθ
    · exact Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd _)
    · exact fun e he => TwoThin.mem_normalizer_pPrimeCoreOf
        (le_normalizer (mem_centralizer_singleton_iff.mpr (hDE d hd e he).symm))
    · exact fun i hi => TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_left hd)) (hI hi)))
    · exact fun e he he1 => h2C d (mem_sup_left hd) e (mem_sup_right he)
        (orderOf_eq_two_of_mem hD hd hd1) (orderOf_eq_two_of_mem hE he he1) (hDE d hd e he)
  · exact Or.inr hθ

theorem stability [Finite G] {D E I : Subgroup G}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hE : CFSG.IsElementaryAbelian 2 ↥E)
    (_hDnE : D ≤ normalizer (E : Set G))
    (hCE : 2 ≤ pRank 2 ↥(E ⊓ centralizer (D : Set G)))
    (hI : I ≤ centralizer ((D ⊔ E : Subgroup G) : Set G)) (hI2 : oPrimeResidualOf 2 I = I)
    (h2C : ∀ d ∈ D ⊔ E, ∀ e ∈ D ⊔ E, orderOf d = 2 → orderOf e = 2 → d * e = e * d →
       ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
         pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    (∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) ∨
      ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ ≠ ⊥ := by
  have hEC : CFSG.IsElementaryAbelian 2 ↥(E ⊓ centralizer (D : Set G)) :=
    Th2Sig6.isElementaryAbelian_of_le hE inf_le_left
  obtain ⟨E₀, hE₀le, hE₀card⟩ := Th2Sig6.exists_sub_card hEC hCE
  have hE₀E : E₀ ≤ E := hE₀le.trans inf_le_left
  have hE₀D : E₀ ≤ centralizer (D : Set G) := hE₀le.trans inf_le_right
  have hE₀ : CFSG.IsElementaryAbelian 2 ↥E₀ := Th2Sig6.isElementaryAbelian_of_le hE hE₀E
  have hr₀ : pRank 2 ↥E₀ = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hE₀card
  have hsub : D ⊔ E₀ ≤ D ⊔ E := sup_le_sup_left hE₀E D
  have hspec := stability_special hD hE₀ hr₀.ge
    (fun d hd e he => mem_centralizer_iff.mp (hE₀D he) d hd)
    (hI.trans (centralizer_le (SetLike.coe_subset_coe.mpr hsub))) hI2
    (fun d hd e he => h2C d (hsub hd) e (hsub he))
  by_cases hleft : ∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥
  · exact Or.inl hleft
  · right
    have hθ₀ : ⁅I, thetaHalf 1 E₀⁆ ≠ ⊥ := by
      have := hspec.resolve_left hleft
      rwa [hr₀] at this
    obtain ⟨e, heE₀, he1, hIe⟩ : ∃ e ∈ E₀, e ≠ 1 ∧
        ⁅I, pPrimeCoreOf 2 (centralizer ({e} : Set G))⁆ ≠ ⊥ := by
      by_contra hcon
      have hall : ∀ e ∈ E₀, e ≠ 1 →
          pPrimeCoreOf 2 (centralizer ({e} : Set G)) ≤ centralizer (I : Set G) := by
        intro e he he1
        have h : ⁅I, pPrimeCoreOf 2 (centralizer ({e} : Set G))⁆ = ⊥ :=
          by_contra fun h => hcon ⟨e, he, he1, h⟩
        rw [commutator_comm] at h
        exact commutator_eq_bot_iff_le_centralizer.mp h
      have hθle : thetaHalf 1 E₀ ≤ centralizer (I : Set G) := by
        unfold thetaHalf
        refine sup_le (iSup₂_le fun D' hD' => ?_) ?_
        · obtain ⟨d', hd'D', hd'1⟩ := Th2Sig8.exists_ne_one hD'.2.1 hD'.2.2
          have hd'E₀ : d' ∈ E₀ := hD'.1 hd'D'
          have hN : E₀ ≤ normalizer
              (pPrimeCoreOf 2 (centralizer ({d'} : Set G)) : Set G) := fun x hx =>
            TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer (mem_centralizer_singleton_iff.mpr
              (Th2Sig6.mul_comm_of_isElementaryAbelian hE₀ hx hd'E₀)))
          exact ((commutator_mono (Th2Sig6.AG_le_pPrimeCoreOf hd'D' hd'1) le_rfl).trans
            (le_normalizer_iff_commutator_le_left.mp hN)).trans (hall d' hd'E₀ hd'1)
        · obtain ⟨s, hs, hs1⟩ := Th2Sig6.exists_ne_one_of_card (k := 2) (by norm_num) hE₀card
          exact (Th2Sig6.AG_le_pPrimeCoreOf hs hs1).trans (hall s hs hs1)
      apply hθ₀
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hθle
    have hE₀sup : E₀ ⊔ E = E := sup_eq_right.mpr hE₀E
    have hsub' : E₀ ⊔ E ≤ D ⊔ E := by rw [hE₀sup]; exact le_sup_right
    have hrE : 2 ≤ pRank 2 ↥E := by
      have h4 : 2 ^ 2 ≤ Nat.card ↥E := by
        have := Subgroup.card_le_of_le hE₀E
        rwa [hE₀card] at this
      by_contra hlt
      have h2 : Nat.card ↥E ≤ 2 ^ 1 := by
        rw [Th2Sig6.card_eq_two_pow_pRank hE]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hspec2 := stability_special hE₀ hE hrE
      (fun d hd e he => Th2Sig6.mul_comm_of_isElementaryAbelian hE (hE₀E hd) he)
      (by rw [hE₀sup]; exact hI.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)))
      hI2 (fun d hd e he => h2C d (hsub' hd) e (hsub' he))
    exact hspec2.resolve_left fun h => hIe (h e heE₀ he1)

end CFSG.GH74.Generic.BProg
