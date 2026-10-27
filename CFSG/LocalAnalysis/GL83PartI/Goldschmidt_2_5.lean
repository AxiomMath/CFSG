module

public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace GL83.Goldschmidt

open CFSG CFSG.LocalCores CFSG.HallHigman Subgroup

universe u

section PiCoreOf

variable {T : Type u} [Group T]

@[expose] def piCoreOf (σ : Set Nat.Primes) (A : Subgroup T) : Subgroup T :=
  (piCore σ ↥A).map A.subtype

theorem piCoreOf_le (σ : Set Nat.Primes) (A : Subgroup T) : piCoreOf σ A ≤ A :=
  Subgroup.map_subtype_le _

instance piCoreOf_normal (σ : Set Nat.Primes) (X : Subgroup T) [X.Normal] :
    (piCoreOf σ X).Normal := by
  unfold piCoreOf
  infer_instance

theorem le_normalizer_piCoreOf (σ : Set Nat.Primes) (A : Subgroup T) :
    A ≤ Subgroup.normalizer (piCoreOf σ A : Set T) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (piCoreOf_le σ A)]
  have h : (piCoreOf σ A).subgroupOf A = piCore σ ↥A :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  rw [h]
  infer_instance

theorem isPiSubgroup_piCoreOf [Finite T] (σ : Set Nat.Primes) (A : Subgroup T) :
    IsPiSubgroup σ (piCoreOf σ A) :=
  isPiSubgroup_map (piCore_isPiSubgroup σ) A.subtype

end PiCoreOf

section Transport

theorem map_piCoreOf {A B : Type u} [Group A] [Group B] (σ : Set Nat.Primes) (f : A →* B)
    (hf : Function.Injective f) (S : Subgroup A) :
    (piCoreOf σ S).map f = piCoreOf σ (S.map f) := by
  let e := S.equivMapOfInjective f hf
  have h1 := piCore_map_mulEquiv σ e
  have h2 : (S.map f).subtype.comp e.toMonoidHom = f.comp S.subtype := by
    ext x
    rfl
  unfold piCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map, h2]

theorem isPiSeparable_of_injective {A B : Type u} [Group A] [Group B] [Finite B]
    {π : Set Nat.Primes} (hB : IsPiSeparable π B) (f : A →* B) (hf : Function.Injective f) :
    IsPiSeparable π A := fun H _ T _ hs =>
  IsPiSeparable.section_index _ rfl hB (f.comp H.subtype) (hf.comp H.subtype_injective) T hs

theorem isPiSeparable_of_isSolvable {X : Type*} [Group X] (π : Set Nat.Primes)
    (hX : Group.IsSolvable X) : IsPiSeparable π X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  have hidx : T.index = Nat.card (↥H ⧸ T) := rfl
  by_cases hmem : (⟨Nat.card (↥H ⧸ T), hq⟩ : Nat.Primes) ∈ π
  · refine Or.inl fun ℓ hℓ => ?_
    have : ℓ.val = Nat.card (↥H ⧸ T) := (Nat.prime_dvd_prime_iff_eq ℓ.2 hq).1 (hidx ▸ hℓ)
    have h : ℓ = ⟨Nat.card (↥H ⧸ T), hq⟩ := Subtype.ext this
    rwa [h]
  · refine Or.inr fun ℓ hℓ hℓπ => hmem ?_
    have : ℓ.val = Nat.card (↥H ⧸ T) := (Nat.prime_dvd_prime_iff_eq ℓ.2 hq).1 (hidx ▸ hℓ)
    have h : ℓ = ⟨Nat.card (↥H ⧸ T), hq⟩ := Subtype.ext this
    rwa [h] at hℓπ

end Transport

section Elements

variable {G : Type*} [Group G]

theorem eq_one_of_isPiSubgroup {π : Set Nat.Primes} {K L : Subgroup G}
    (hK : IsPiSubgroup π K) (hL : IsPiSubgroup πᶜ L) {x : G} (hxK : x ∈ K) (hxL : x ∈ L) :
    x = 1 := by
  by_contra hx
  have hord : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.1 h)
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hord
  have h1 : ℓ ∣ Nat.card K := hdvd.trans (Subgroup.orderOf_dvd_natCard K hxK)
  have h2 : ℓ ∣ Nat.card L := hdvd.trans (Subgroup.orderOf_dvd_natCard L hxL)
  exact hL ⟨ℓ, hℓ⟩ h2 (hK ⟨ℓ, hℓ⟩ h1)

theorem exists_ne_one_mem {r : ℕ} (hr : r.Prime) {E : Subgroup G} (hE2 : r ^ 2 ≤ Nat.card E) :
    ∃ e ∈ E, e ≠ 1 := by
  by_contra h
  have hEbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun x hx => by
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  rw [hEbot, Subgroup.card_bot] at hE2
  have : 2 ≤ r := hr.two_le
  nlinarith

end Elements

section Lifting

variable {T : Type u} [Group T] [Finite T]

theorem exists_lift_commute {r : ℕ} [Fact r.Prime] {O : Subgroup T} [O.Normal]
    (hrO : ¬ r ∣ Nat.card O) {e : T} (he : e ^ r = 1) (y : T ⧸ O)
    (hy : y * (e : T ⧸ O) = (e : T ⧸ O) * y) :
    ∃ c : T, c * e = e * c ∧ (c : T ⧸ O) = y := by
  have hQ : IsPGroup r (Subgroup.zpowers e) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hlift :=
    (CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting hrO hQ).2.2
  have hy' : y ∈ Subgroup.centralizer
      (((Subgroup.zpowers e).map (QuotientGroup.mk' O) : Subgroup (T ⧸ O)) : Set (T ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : Commute y (e : T ⧸ O) := hy
    have := (hc.zpow_right k).symm.eq
    simpa [map_zpow] using this
  rw [hlift] at hy'
  obtain ⟨c, hc, rfl⟩ := hy'
  exact ⟨c, (Subgroup.mem_centralizer_iff.1 hc e (Subgroup.mem_zpowers e)).symm, rfl⟩

end Lifting

section Quotient

variable {T : Type u} [Group T] (σ : Set Nat.Primes) (X : Subgroup T) [X.Normal]

theorem ker_restrict_eq :
    ((QuotientGroup.mk' (piCoreOf σ X)).comp X.subtype).ker = piCore σ ↥X := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    Subgroup.coe_subtype, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := X.subtype_injective hyx
    exact this ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem range_restrict_eq :
    ((QuotientGroup.mk' (piCoreOf σ X)).comp X.subtype).range =
      X.map (QuotientGroup.mk' (piCoreOf σ X)) := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

noncomputable def quotEquiv :
    ↥X ⧸ piCore σ ↥X ≃* ↥(X.map (QuotientGroup.mk' (piCoreOf σ X))) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_restrict_eq σ X).symm).trans
    (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr (range_restrict_eq σ X))

variable [Finite T]

theorem piCore_map_quotient_eq_bot :
    piCore σ ↥(X.map (QuotientGroup.mk' (piCoreOf σ X))) = ⊥ := by
  rw [← piCore_map_mulEquiv σ (quotEquiv σ X), prime_set_core_quotient σ, Subgroup.map_bot]

theorem isPiSeparable_map_quotient {π : Set Nat.Primes} (hX : IsPiSeparable π ↥X) :
    IsPiSeparable π ↥(X.map (QuotientGroup.mk' (piCoreOf σ X))) :=
  isPiSeparable_of_injective (hX.quotient (piCore σ ↥X)) (quotEquiv σ X).symm.toMonoidHom
    (quotEquiv σ X).symm.injective

theorem mem_piCoreOf_of_commute {π : Set Nat.Primes} (hX : IsPiSeparable π ↥X) :
    ∀ y ∈ X.map (QuotientGroup.mk' (piCoreOf πᶜ X)),
      (∀ h ∈ piCoreOf π (X.map (QuotientGroup.mk' (piCoreOf πᶜ X))), y * h = h * y) →
        y ∈ piCoreOf π (X.map (QuotientGroup.mk' (piCoreOf πᶜ X))) := by
  intro y hy hcomm
  set X' := X.map (QuotientGroup.mk' (piCoreOf πᶜ X)) with hX'
  have h := centralizer_piCore_le_piCore (isPiSeparable_map_quotient πᶜ X hX)
    (piCore_map_quotient_eq_bot πᶜ X)
  have hy' : (⟨y, hy⟩ : ↥X') ∈ Subgroup.centralizer (piCore π ↥X' : Set ↥X') := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact (hcomm z ⟨z, hz, rfl⟩).symm
  exact ⟨_, h hy', rfl⟩

end Quotient

section Engine

variable {T : Type u} [Group T] [Finite T]

theorem iInf_piCoreOf_le_of_normal {π : Set Nat.Primes} {r : ℕ} (hr : r.Prime)
    {X E : Subgroup T} [X.Normal] (hX : IsPiSeparable π ↥X)
    (hE : CFSG.Open.IsElemAbelian r E) (hE2 : r ^ 2 ≤ Nat.card E) (hXr : ¬ r ∣ Nat.card X) :
    (⨅ (e : T) (_ : e ∈ E) (_ : e ≠ 1),
      piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set T))) ≤ piCoreOf πᶜ X := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨e₀, he₀, he₀1⟩ := exists_ne_one_mem hr hE2
  intro q hq
  have hqe : ∀ e ∈ E, e ≠ 1 →
      q ∈ piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set T)) :=
    fun e he he1 => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hq e) he) he1
  have hqX : q ∈ X := (piCoreOf_le _ _ (hqe e₀ he₀ he₀1)).1
  set O := piCoreOf πᶜ X with hO
  set φ := QuotientGroup.mk' O with hφ
  set X' := X.map φ with hX'
  have hrO : ¬ r ∣ Nat.card O := fun h =>
    hXr (h.trans (Subgroup.card_dvd_of_le (piCoreOf_le _ X)))
  have hX'n : X'.Normal := Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective O)
  set H := piCoreOf π X' with hH
  have hHn : H.Normal := piCoreOf_normal π X'
  have hHX' : H ≤ X' := piCoreOf_le π X'
  have hHπ : IsPiSubgroup π H := isPiSubgroup_piCoreOf π X'
  have hEp : IsPGroup r E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hinj : Function.Injective (φ.comp E.subtype) :=
    (CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting hrO hEp).1
  have hEcard : Nat.card (E.map φ) = Nat.card E := by
    have h1 : E.map φ = (φ.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hEel : CFSG.IsElementaryAbelian r ↥(E.map φ) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).2
      (CFSG.SectionRank.isElemAbelian_map hE φ)
  have hrH : ¬ r ∣ Nat.card H := fun h =>
    hXr ((h.trans (Subgroup.card_dvd_of_le hHX')).trans (Subgroup.card_map_dvd X φ))
  have hnorm : E.map φ ≤ Subgroup.normalizer (H : Set (T ⧸ O)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcomm : ∀ b ∈ E.map φ, b ≠ 1 →
      H ⊓ Subgroup.centralizer ({b} : Set (T ⧸ O)) ≤
        Subgroup.centralizer ({φ q} : Set (T ⧸ O)) := by
    intro b hb hb1 h hh
    obtain ⟨e, he, rfl⟩ := hb
    have he1 : e ≠ 1 := fun h1 => hb1 (by rw [h1, map_one])
    have hhe : h * (e : T ⧸ O) = (e : T ⧸ O) * h :=
      (Subgroup.mem_centralizer_iff.1 hh.2 (φ e) rfl).symm
    obtain ⟨c, hce, rfl⟩ := exists_lift_commute hrO (hE.2 e he) h hhe
    have hcX : c ∈ X := by
      obtain ⟨x, hx, hxc⟩ := hHX' hh.1
      have h2 : x⁻¹ * c ∈ O := QuotientGroup.eq.1 hxc
      have := X.mul_mem hx (piCoreOf_le _ X h2)
      rwa [mul_inv_cancel_left] at this
    have hcZ : c ∈ X ⊓ Subgroup.centralizer ({e} : Set T) :=
      ⟨hcX, Subgroup.mem_centralizer_iff.2 fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hce.symm⟩
    have hq' := hqe e he he1
    have hcn := le_normalizer_piCoreOf πᶜ _ hcZ
    have hconj : c⁻¹ * q⁻¹ * c ∈ piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set T)) := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcn) q⁻¹).1 (inv_mem hq')
      simpa using this
    have hw := Subgroup.mul_mem _ hconj hq'
    have hwφ : (c : T ⧸ O)⁻¹ * (φ q)⁻¹ * (c : T ⧸ O) * φ q ∈
        (piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set T))).map φ :=
      ⟨_, hw, by simp [φ]⟩
    have hwH : (c : T ⧸ O)⁻¹ * (φ q)⁻¹ * (c : T ⧸ O) * φ q ∈ H := by
      have h1 : (φ q)⁻¹ * (c : T ⧸ O) * (φ q)⁻¹⁻¹ ∈ H := hHn.conj_mem _ hh.1 _
      have e : (c : T ⧸ O)⁻¹ * (φ q)⁻¹ * (c : T ⧸ O) * φ q =
          (c : T ⧸ O)⁻¹ * ((φ q)⁻¹ * (c : T ⧸ O) * (φ q)⁻¹⁻¹) := by group
      rw [e]
      exact H.mul_mem (H.inv_mem hh.1) h1
    have h1 := eq_one_of_isPiSubgroup hHπ
      (isPiSubgroup_map (isPiSubgroup_piCoreOf πᶜ _) φ) hwH hwφ
    have h2 : ((φ q) * (c : T ⧸ O))⁻¹ * ((c : T ⧸ O) * φ q) = 1 := by
      have e : ((φ q) * (c : T ⧸ O))⁻¹ * ((c : T ⧸ O) * φ q) =
          (c : T ⧸ O)⁻¹ * (φ q)⁻¹ * (c : T ⧸ O) * φ q := by group
      rw [e]
      exact h1
    exact Subgroup.mem_centralizer_iff.2 fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact inv_mul_eq_one.1 h2
  have hHle := CFSG.RankThree.GroupTheory.SteinbergBM.le_of_forall_inf_centralizer_le hEel
    (hEcard ▸ hE2) hrH hnorm hcomm
  have hyH : φ q ∈ H := mem_piCoreOf_of_commute X hX (φ q) ⟨q, hqX, rfl⟩ fun h hh =>
    Subgroup.mem_centralizer_iff.1 (hHle hh) (φ q) rfl
  have hy1 := eq_one_of_isPiSubgroup hHπ
    (isPiSubgroup_map (isPiSubgroup_piCoreOf πᶜ _) φ) hyH ⟨q, hqe e₀ he₀ he₀1, rfl⟩
  exact (QuotientGroup.eq_one_iff q).1 hy1

end Engine

section Ambient

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_inf_centralizer {L X : Subgroup G} (hXL : X ≤ L) (e : L) :
    ((X.subgroupOf L) ⊓ Subgroup.centralizer ({e} : Set L)).map L.subtype =
      X ⊓ Subgroup.centralizer ({(e : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨a, ⟨haX, haC⟩, rfl⟩
    refine ⟨haX, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 haC e rfl)
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hXL hgX⟩, ⟨hgX, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgC _ rfl)

theorem iInf_piCoreOf_le {π : Set Nat.Primes} {r : ℕ} (hr : r.Prime) {X E : Subgroup G}
    (hX : IsPiSeparable π ↥X) (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hE : CFSG.Open.IsElemAbelian r E) (hE2 : r ^ 2 ≤ Nat.card E) (hXr : ¬ r ∣ Nat.card X) :
    (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set G))) ≤ piCoreOf πᶜ X := by
  set L := Subgroup.normalizer (X : Set G) with hL
  have hXL : X ≤ L := Subgroup.le_normalizer
  set X₀ := X.subgroupOf L with hX₀
  set E₀ := E.subgroupOf L with hE₀
  have hX₀n : X₀.Normal := Subgroup.normal_in_normalizer
  have hmapX : X₀.map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
  have hX₀sep : IsPiSeparable π ↥X₀ :=
    isPiSeparable_of_injective hX (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXL).injective
  have hE₀ab : CFSG.Open.IsElemAbelian r E₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subtype.ext (by simpa using hE.2 x hx)⟩
    exact (Subgroup.subgroupOfEquivOfLe hEX).injective (by
      rw [map_mul, map_mul]
      exact hE.1.is_comm.comm _ _)
  have hE₀card : r ^ 2 ≤ Nat.card E₀ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv) ▸ hE2
  have hX₀r : ¬ r ∣ Nat.card X₀ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv) ▸ hXr
  have key := iInf_piCoreOf_le_of_normal hr hX₀sep hE₀ab hE₀card hX₀r
  obtain ⟨e₀, he₀, he₀1⟩ := exists_ne_one_mem hr hE2
  intro w hw
  have hwe : ∀ e ∈ E, e ≠ 1 → w ∈ piCoreOf πᶜ (X ⊓ Subgroup.centralizer ({e} : Set G)) :=
    fun e he he1 => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hw e) he) he1
  have hwX : w ∈ X := (piCoreOf_le _ _ (hwe e₀ he₀ he₀1)).1
  obtain ⟨w₀, hw₀eq⟩ : ∃ w₀ : L, (w₀ : G) = w := ⟨⟨w, hXL hwX⟩, rfl⟩
  have hw₀ : ∀ e : L, e ∈ E₀ → e ≠ 1 →
      w₀ ∈ piCoreOf πᶜ (X₀ ⊓ Subgroup.centralizer ({e} : Set L)) := by
    intro e he he1
    have h1 := hwe (e : G) he (fun h => he1 (Subtype.ext h))
    rw [← map_subtype_inf_centralizer hXL e,
      ← map_piCoreOf πᶜ L.subtype L.subtype_injective] at h1
    obtain ⟨a, ha, haw⟩ := h1
    have : a = w₀ := L.subtype_injective (haw.trans hw₀eq.symm)
    exact this ▸ ha
  have h2 : w₀ ∈ piCoreOf πᶜ X₀ :=
    key (Subgroup.mem_iInf.2 fun e => Subgroup.mem_iInf.2 fun he =>
      Subgroup.mem_iInf.2 fun he1 => hw₀ e he he1)
  have h3 := Subgroup.mem_map_of_mem L.subtype h2
  rw [map_piCoreOf πᶜ L.subtype L.subtype_injective, hmapX] at h3
  rwa [← hw₀eq]

theorem pCoreOf_eq_piCoreOf (q : ℕ) [Fact q.Prime] (A : Subgroup G) :
    CFSG.Open.pCoreOf q A = piCoreOf {t : Nat.Primes | t.val = q} A := by
  unfold CFSG.Open.pCoreOf piCoreOf
  rw [CFSG.pCore_eq_piCore]

end Ambient

end GL83.Goldschmidt

namespace GL83

open CFSG.HallHigman GL83.Goldschmidt

universe u

variable {G : Type u} [Group G] [Finite G]

theorem Goldschmidt_2_5_pCore {q r : ℕ} (hq : q.Prime) (hr : r.Prime) {X E : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hE : CFSG.Open.IsElemAbelian r E) (hE2 : r ^ 2 ≤ Nat.card E) (hXr : ¬ r ∣ Nat.card X) :
    (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      CFSG.Open.pCoreOf q (X ⊓ Subgroup.centralizer ({e} : Set G))) ≤ CFSG.Open.pCoreOf q X := by
  have : Fact q.Prime := ⟨hq⟩
  have key := iInf_piCoreOf_le hr (π := {t : Nat.Primes | t.val ≠ q})
    (isPiSeparable_of_isSolvable _ hX) hEX hE hE2 hXr
  have hc : ({t : Nat.Primes | t.val ≠ q}ᶜ : Set Nat.Primes) = {t | t.val = q} := by
    ext t
    simp
  rw [hc] at key
  simpa only [pCoreOf_eq_piCoreOf] using key

end GL83
