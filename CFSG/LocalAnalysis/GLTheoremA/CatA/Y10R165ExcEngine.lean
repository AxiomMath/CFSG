module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Conj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

theorem concl165Avoid_of_layers {K : Type} [Group K] [Finite K] {p q : ℕ} (hp : p.Prime)
    {A : Subgroup K} {x z : K} (hA : IsElemAbelian p A) (hx : x ∈ A) (hz : z ∈ A)
    (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J : Subgroup K} (hJx : J ≤ Subgroup.centralizer ({x} : Set K))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({x} : Set K))).Normal)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    {Q : Subgroup K} (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({z} : Set K))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set K))).Normal)
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    {F : Subgroup K} (hF : IsElemAbelian q F) (hFx : F ≤ Subgroup.centralizer ({x} : Set K))
    (hFJ : F ≤ Subgroup.normalizer (J : Set K)) (hF3 : 3 ≤ CFSG.Open.pRank q F)
    {Z : Subgroup K} (hFZ : F ⊓ Z = ⊥) :
    Concl165Avoid K p q A Z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := fun h => hzx (h ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have hxord : orderOf x = p := orderOf_eq_prime (hA.2 x hx) hx1
  have hzord : orderOf z = p := orderOf_eq_prime (hA.2 z hz) hz1
  set D : Subgroup K := Subgroup.zpowers x with hD
  set E : Subgroup K := D ⊔ Subgroup.zpowers z with hE
  have hDcard : Nat.card D = p := by rw [hD, Nat.card_zpowers, hxord]
  have hDE : D ≤ E := by rw [hE]; exact le_sup_left
  have hEA : E ≤ A := by
    rw [hE]
    exact sup_le (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hz)
  have hzE : z ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hEcard : Nat.card E = p ^ 2 := by
    have hcomm : ∀ a ∈ D, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (show Commute x z from hA.comm hx hz).zpow_zpow i j
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D
      (Subgroup.zpowers z) hcomm).1
    have hinf : D ⊓ Subgroup.zpowers z = ⊥ := by
      have hdvd : Nat.card ↥(D ⊓ Subgroup.zpowers z) ∣ p := by
        rw [← hDcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : D ⊓ Subgroup.zpowers z = Subgroup.zpowers z := by
          refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
          rw [Nat.card_zpowers, hzord, hp']
        have hzI : z ∈ D ⊓ Subgroup.zpowers z := by
          rw [heq]
          exact Subgroup.mem_zpowers z
        exact hzx (by simpa [hD] using (Subgroup.mem_inf.mp hzI).1)
    rw [hinf, Subgroup.card_bot, mul_one, hDcard, Nat.card_zpowers, hzord] at hprod
    calc Nat.card E = Nat.card ↥(D ⊔ Subgroup.zpowers z) := rfl
      _ = p * p := hprod
      _ = p ^ 2 := by rw [pow_two]
  have hAC : A ≤ Subgroup.centralizer ({x} : Set K) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hA.comm ha hx)
  have hcentD : Subgroup.centralizer (D : Set K) = Subgroup.centralizer ({x} : Set K) := by
    rw [hD]
    exact CFSG.centralizer_zpowers_eq_centralizer_singleton x
  have hJcomp : GLAPComponent p (Subgroup.centralizer (D : Set K)) J := by
    rw [hcentD]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hJ hpJ hJx hJn
  have hAJ : A ≤ Subgroup.normalizer (J : Set K) :=
    hAC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJx).mp hJn)
  have hQx : Q ≤ Subgroup.centralizer ({x} : Set K) := hQJ.trans hJx
  have hCE : Subgroup.centralizer (E : Set K) = Subgroup.centralizer ({x} : Set K) ⊓
      Subgroup.centralizer ({z} : Set K) := by
    rw [hE, CFSG.centralizer_sup_zpowers_eq, hcentD]
  have hQCE : Q ≤ Subgroup.centralizer (E : Set K) := by
    rw [hCE]
    exact le_inf hQx hQz
  have hQle : Q ≤ J ⊓ Subgroup.centralizer (E : Set K) := le_inf hQJ hQCE
  have hCEle : Subgroup.centralizer (E : Set K) ≤ Subgroup.centralizer ({z} : Set K) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzE)
  have hQnE : (Q.subgroupOf (J ⊓ Subgroup.centralizer (E : Set K))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQle]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff (le_inf hQJ hQz)).mp hQn h k hh
      ⟨hk.1, hCEle hk.2⟩
  have hQcomp : GLAPComponent p (J ⊓ Subgroup.centralizer (E : Set K)) Q :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hQ hpQ hQle hQnE
  have hlay : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711.glaPLayer_ne_bot_of_glaPComponent
      hQcomp
  have hFD : F ≤ Subgroup.centralizer (D : Set K) := by
    rw [hcentD]
    exact hFx
  exact ⟨D, E, F, J, hDE, hEA, hDcard, hEcard, hJcomp, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩

theorem concl165_of_layers {K : Type} [Group K] [Finite K] {p q : ℕ} (hp : p.Prime)
    {A : Subgroup K} {x z : K} (hA : IsElemAbelian p A) (hx : x ∈ A) (hz : z ∈ A)
    (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J : Subgroup K} (hJx : J ≤ Subgroup.centralizer ({x} : Set K))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({x} : Set K))).Normal)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    {Q : Subgroup K} (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({z} : Set K))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set K))).Normal)
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    {F : Subgroup K} (hF : IsElemAbelian q F) (hFx : F ≤ Subgroup.centralizer ({x} : Set K))
    (hFJ : F ≤ Subgroup.normalizer (J : Set K)) (hF3 : 3 ≤ CFSG.Open.pRank q F) :
    Concl165 K p q A := by
  obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, -⟩ :=
    concl165Avoid_of_layers hp hA hx hz hx1 hzx hJx hJn hJ hpJ hQJ hQz hQn hQ hpQ
      hF hFx hFJ hF3 (by simp : F ⊓ (⊥ : Subgroup K) = ⊥)
  exact ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3⟩

theorem concl165Avoid_of_mulEquiv {K R : Type} [Group K] [Finite K] [Group R] [Finite R]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : K ≃* R) {A Z : Subgroup K}
    (h : Concl165Avoid R p q (A.map e.toMonoidHom) (Z.map e.toMonoidHom)) :
    Concl165Avoid K p q A Z := by
  obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ := h
  classical
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
    ext x
    simp
  have hmapA : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [Subgroup.map_map A e.symm.toMonoidHom e.toMonoidHom, hcomp, Subgroup.map_id]
  have hcoe : ∀ X : Subgroup R, ((X.map e.symm.toMonoidHom : Subgroup K) : Set K) =
      e.symm '' (X : Set R) := fun X => Subgroup.coe_map _ _
  have hD' : Nat.card (D.map e.symm.toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hD]
  have hE' : Nat.card (E.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE]
  have hEA' : E.map e.symm.toMonoidHom ≤ A := by
    have hmono := Subgroup.map_mono (f := e.symm.toMonoidHom) hEA
    rwa [hmapA] at hmono
  have hcentD : Subgroup.centralizer
      ((D.map e.symm.toMonoidHom : Subgroup K) : Set K) =
      (Subgroup.centralizer (D : Set R)).map e.symm.toMonoidHom := by
    rw [hcoe D]
    exact CFSG.GF2Type.Smith1979W3.Cert690.map_centralizer_mulEquiv e.symm (D : Set R)
  have hk : e.symm.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff e.symm.toMonoidHom).mpr e.symm.injective
  have hJ' : GLAPComponent p
      (Subgroup.centralizer ((D.map e.symm.toMonoidHom : Subgroup K) : Set K))
      (J.map e.symm.toMonoidHom) := by
    rw [hcentD]
    have hcop : Nat.Coprime p (Nat.card ↥(Subgroup.centralizer (D : Set R) ⊓
        e.symm.toMonoidHom.ker)) := by
      rw [hk, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp e.symm.toMonoidHom hcop hJ
  have hcentE : Subgroup.centralizer
      ((E.map e.symm.toMonoidHom : Subgroup K) : Set K) =
      (Subgroup.centralizer (E : Set R)).map e.symm.toMonoidHom := by
    rw [hcoe E]
    exact CFSG.GF2Type.Smith1979W3.Cert690.map_centralizer_mulEquiv e.symm (E : Set R)
  have hinf : J.map e.symm.toMonoidHom ⊓
      Subgroup.centralizer ((E.map e.symm.toMonoidHom : Subgroup K) : Set K) =
      (J ⊓ Subgroup.centralizer (E : Set R)).map e.symm.toMonoidHom := by
    rw [hcentE, ← Subgroup.map_inf _ _ e.symm.toMonoidHom e.symm.injective]
  have hlay' : GLAPLayer p (J.map e.symm.toMonoidHom ⊓
      Subgroup.centralizer ((E.map e.symm.toMonoidHom : Subgroup K) : Set K)) ≠ ⊥ := by
    rw [hinf]
    have hcop : Nat.Coprime p (Nat.card ↥((J ⊓ Subgroup.centralizer (E : Set R)) ⊓
        e.symm.toMonoidHom.ker)) := by
      rw [hk, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    exact (CFSG.glaPLayer_ne_bot_iff_map_ne_bot_of_coprime_ker hp e.symm.toMonoidHom
      hcop).mp hlay
  have hconjJ : ∀ a ∈ A, ∀ y ∈ (J.map e.symm.toMonoidHom : Subgroup K),
      a * y * a⁻¹ ∈ J.map e.symm.toMonoidHom := by
    intro a ha y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : e a ∈ Subgroup.normalizer (J : Set R) :=
      hAJ (Subgroup.mem_map_of_mem e.toMonoidHom ha)
    rw [Subgroup.mem_normalizer_iff] at hmem
    exact ⟨e a * y₀ * (e a)⁻¹, (hmem _).mp hy₀, by simp⟩
  have hAJ' : A ≤ Subgroup.normalizer ((J.map e.symm.toMonoidHom : Subgroup K) : Set K) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconjJ a ha y hy
    · intro hy
      have h := hconjJ a⁻¹ (A.inv_mem ha) _ hy
      have hy' : a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ = y := by group
      rwa [hy'] at h
  have hFD' : F.map e.symm.toMonoidHom ≤ Subgroup.centralizer
      ((D.map e.symm.toMonoidHom : Subgroup K) : Set K) := by
    rw [hcentD]
    exact Subgroup.map_mono hFD
  have hF' : IsElemAbelian q (F.map e.symm.toMonoidHom) := hF.map e.symm.toMonoidHom
  have hconjF : ∀ a ∈ F.map e.symm.toMonoidHom,
      ∀ y ∈ (J.map e.symm.toMonoidHom : Subgroup K),
      a * y * a⁻¹ ∈ J.map e.symm.toMonoidHom := by
    intro a ha y hy
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : a₀ ∈ Subgroup.normalizer (J : Set R) := hFJ ha₀
    rw [Subgroup.mem_normalizer_iff] at hmem
    exact ⟨a₀ * y₀ * a₀⁻¹, (hmem _).mp hy₀, by simp⟩
  have hFJ' : F.map e.symm.toMonoidHom ≤
      Subgroup.normalizer ((J.map e.symm.toMonoidHom : Subgroup K) : Set K) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconjF a ha y hy
    · intro hy
      have h := hconjF a⁻¹ ((F.map e.symm.toMonoidHom).inv_mem ha) (a * y * a⁻¹) hy
      have hy' : a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ = y := by group
      rwa [hy'] at h
  have hF3' : 3 ≤ CFSG.Open.pRank q (F.map e.symm.toMonoidHom) := by
    rw [CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt
      e.symm.toMonoidHom e.symm.injective]
    exact hF3
  have hFZ' : F.map e.symm.toMonoidHom ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxZ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hxF
    have hxZ' : f ∈ Z.map e.toMonoidHom := by
      have := Subgroup.mem_map_of_mem e.toMonoidHom hxZ
      simpa using this
    have hf1 : f = 1 := by
      have hmem : f ∈ F ⊓ Z.map e.toMonoidHom := ⟨hf, hxZ'⟩
      rw [hFZ, Subgroup.mem_bot] at hmem
      exact hmem
    subst hf1
    simp
  exact ⟨D.map e.symm.toMonoidHom, E.map e.symm.toMonoidHom, F.map e.symm.toMonoidHom,
    J.map e.symm.toMonoidHom, Subgroup.map_mono hDE, hEA', hD', hE', hJ', hAJ', hlay',
    hFD', hF', hFJ', hF3', hFZ'⟩

theorem concl165Avoid_of_conj {K : Type} [Group K] [Finite K] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) {A Z : Subgroup K} (hZ : Z.Normal) (g : K)
    (h : Concl165Avoid K p q (A.map (MulAut.conj g).toMonoidHom) Z) :
    Concl165Avoid K p q A Z := by
  have hZmap : Z.map (MulAut.conj g).toMonoidHom = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer_eq_top_iff.mpr hZ) ▸ Subgroup.mem_top g)
  refine concl165Avoid_of_mulEquiv hp hq (MulAut.conj g) ?_
  rwa [hZmap]

theorem concl165_of_conj {K : Type} [Group K] [Finite K] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) {A : Subgroup K} (g : K)
    (h : Concl165 K p q (A.map (MulAut.conj g).toMonoidHom)) : Concl165 K p q A :=
  concl165_of_mulEquiv hp hq (MulAut.conj g) h

end CFSG.LocalAnalysis.GLTheoremA.Y10F
