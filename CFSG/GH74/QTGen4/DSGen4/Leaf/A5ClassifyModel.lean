module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyCore
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyAlt
public import Certificates.Data.A5GL42
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 a5_card)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

structure A5Pre (P L E K : Subgroup G) : Prop where
  le : L ≤ P
  norm_L : P ≤ Subgroup.normalizer (L : Set G)
  norm_E : P ≤ Subgroup.normalizer (E : Set G)
  norm_K : P ≤ Subgroup.normalizer (K : Set G)
  sec : IsElemSec K E
  card : K.relIndex E = 16
  core : ∀ q ∈ pCoreOf 2 P, ∀ e ∈ E, ⁅q, e⁆ ∈ K
  quot : IsL2Quot 2 (oTwoQuot ↥L)
  nontriv : ∃ l ∈ L, ∃ e ∈ E, ⁅l, e⁆ ∉ K

theorem A5Chief.toPre {P L E K : Subgroup G} (h : A5Chief P L E K) : A5Pre P L E K :=
  ⟨h.le, h.norm_L, h.norm_E, h.norm_K, h.sec, h.card, h.core, h.quot, h.nontriv⟩

structure A5Model (P L E K : Subgroup G) (H : Finset Certificates.A5GL42.Mat4) where
  F : ElemFrame P E K
  imgL : ∀ l : ↥P, (l : G) ∈ L → glMat (F.M l) ∈ H
  surjL : ∀ m ∈ H, ∃ l : ↥P, (l : G) ∈ L ∧ glMat (F.M l) = m
  kerL : ∀ l : ↥P, (l : G) ∈ L → (F.M l = 1 ↔ (l : G) ∈ pCoreOf 2 L)
  core : ∀ q : ↥P, (q : G) ∈ pCoreOf 2 P → F.M q = 1
  normP : ∀ p : ↥P, ∀ m ∈ H, ∃ m' ∈ H, glMat (F.M p) * m = m' * glMat (F.M p)

section Existence

variable [Finite G] {P L E K : Subgroup G}

noncomputable def iotaOf (F : ElemFrame P E K) (h : A5Pre P L E K)
    (hker : ∀ y : ↥L, y ∈ CFSG.Open.pCore 2 ↥L → F.M (Subgroup.inclusion h.le y) = 1)
    (e : oTwoQuot ↥L ≃* Alt5) : Alt5 →* GL (Fin 4) (ZMod 2) :=
  (QuotientGroup.lift (CFSG.Open.pCore 2 ↥L) (F.M.comp (Subgroup.inclusion h.le)) hker).comp
    e.symm.toMonoidHom

theorem iotaOf_mk (F : ElemFrame P E K) (h : A5Pre P L E K)
    (hker : ∀ y : ↥L, y ∈ CFSG.Open.pCore 2 ↥L → F.M (Subgroup.inclusion h.le y) = 1)
    (e : oTwoQuot ↥L ≃* Alt5) (l : ↥L) :
    iotaOf F h hker e (e (QuotientGroup.mk l)) = F.M (Subgroup.inclusion h.le l) := by
  simp [iotaOf]
  rfl

theorem iotaOf_injective (F : ElemFrame P E K) (h : A5Pre P L E K)
    (hker : ∀ y : ↥L, y ∈ CFSG.Open.pCore 2 ↥L → F.M (Subgroup.inclusion h.le y) = 1)
    (e : oTwoQuot ↥L ≃* Alt5) : Function.Injective (iotaOf F h hker e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup_five
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (iotaOf F h hker e).ker with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨l, hl, e', he', hne⟩ := h.nontriv
    have hM : F.M (Subgroup.inclusion h.le ⟨l, hl⟩) = 1 := by
      rw [← iotaOf_mk F h hker e ⟨l, hl⟩]
      have : (e (QuotientGroup.mk ⟨l, hl⟩) : Alt5) ∈ (iotaOf F h hker e).ker := by
        rw [h1]; trivial
      exact this
    have := F.comm_mem_of_M_eq_one h.norm_E _ hM he'
    exact hne this

end Existence

section Closure

open Certificates.A5GL42 (Mat4 Vec4 GroupFacts)

theorem glMat_conj_eq {g u : GL (Fin 4) (ZMod 2)} {m : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : glMat g * glMat u = m * glMat g) : glMat (g * u * g⁻¹) = m := by
  simp only [glMat, Units.val_mul] at h ⊢
  rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem glMat_mem_of_closure {H : Finset Mat4} (hH : GroupFacts H) {a₀ b₀ : Mat4} (ha₀ : a₀ ∈ H)
    (hb₀ : b₀ ∈ H) (ι' : Alt5 →* GL (Fin 4) (ZMod 2)) (hx : glMat (ι' x0) = a₀)
    (hy : glMat (ι' y0) = b₀) : ∀ σ : Alt5, glMat (ι' σ) ∈ H := by
  obtain ⟨h1, hmul, hinv, -, -, -⟩ := hH
  intro σ
  have hσ : σ ∈ Subgroup.closure ({x0, y0} : Set Alt5) := by rw [closure_x0_y0]; trivial
  induction hσ using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · rw [hx]; exact ha₀
    · rw [hy]; exact hb₀
  | one => simpa [glMat] using h1
  | mul z w _ _ hz hw =>
    rw [map_mul, show glMat (ι' z * ι' w) = glMat (ι' z) * glMat (ι' w) from Units.val_mul _ _]
    exact hmul _ hz _ hw
  | inv z _ hz =>
    obtain ⟨y, hy', hzy⟩ := hinv _ hz
    have : glMat (ι' z⁻¹) = y := by
      rw [map_inv]
      calc glMat (ι' z)⁻¹ = glMat (ι' z)⁻¹ * (glMat (ι' z) * y) := by rw [hzy, mul_one]
        _ = y := by rw [← mul_assoc, show glMat (ι' z)⁻¹ * glMat (ι' z) = 1 from Units.inv_mul _,
          one_mul]
    rw [this]; exact hy'

theorem exists_eq_of_injective {H : Finset Mat4} (hH : GroupFacts H) (f : Alt5 → Mat4)
    (hf : Function.Injective f) (hmem : ∀ σ, f σ ∈ H) : ∀ m ∈ H, ∃ σ, f σ = m := by
  obtain ⟨-, -, -, hcard, -, -⟩ := hH
  classical
  haveI : Fintype Alt5 := Fintype.ofFinite _
  have h60 : Fintype.card Alt5 = 60 := by rw [← Nat.card_eq_fintype_card]; exact a5_card
  have hsub : (Finset.univ : Finset Alt5).image f ⊆ H := by
    intro m hm
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hm
    exact hmem σ
  have hc : H.card ≤ ((Finset.univ : Finset Alt5).image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, h60, hcard]
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  intro m hm
  rw [← heq] at hm
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨σ, rfl⟩

end Closure

section Model

variable [Finite G] {P L E K : Subgroup G}

open Certificates.A5GL42 (Mat4 Vec4 GroupFacts)

theorem exists_model_of_conj {H : Finset Mat4} (hH : GroupFacts H) {a₀ b₀ : Mat4} (ha₀ : a₀ ∈ H)
    (hb₀ : b₀ ∈ H) (h : A5Pre P L E K) (F₀ : ElemFrame P E K)
    (hcoreM : ∀ q : ↥P, (q : G) ∈ pCoreOf 2 P → F₀.M q = 1)
    (hker : ∀ y : ↥L, y ∈ CFSG.Open.pCore 2 ↥L → F₀.M (Subgroup.inclusion h.le y) = 1)
    (e : oTwoQuot ↥L ≃* Alt5) (g : GL (Fin 4) (ZMod 2))
    (hga : glMat g * glMat (iotaOf F₀ h hker e x0) = a₀ * glMat g)
    (hgb : glMat g * glMat (iotaOf F₀ h hker e y0) = b₀ * glMat g) :
    Nonempty (A5Model P L E K H) := by
  set ι := iotaOf F₀ h hker e with hιdef
  have hι : Function.Injective ι := iotaOf_injective F₀ h hker e
  let ι' : Alt5 →* GL (Fin 4) (ZMod 2) := (MulAut.conj g).toMonoidHom.comp ι
  have hι'inj : Function.Injective ι' := (MulAut.conj g).injective.comp hι
  have hι'x : glMat (ι' x0) = a₀ := glMat_conj_eq hga
  have hι'y : glMat (ι' y0) = b₀ := glMat_conj_eq hgb
  have hall := glMat_mem_of_closure hH ha₀ hb₀ ι' hι'x hι'y
  have hsurj := exists_eq_of_injective hH (fun σ => glMat (ι' σ))
    (fun a b hab => hι'inj (Units.ext hab)) hall
  have hMι : ∀ l : ↥L, (F₀.conj g).M (Subgroup.inclusion h.le l) = ι' (e (QuotientGroup.mk l)) := by
    intro l
    rw [ElemFrame.conj_M]
    have h1 : ι (e (QuotientGroup.mk l)) = F₀.M (Subgroup.inclusion h.le l) :=
      iotaOf_mk F₀ h hker e l
    show g * F₀.M (Subgroup.inclusion h.le l) * g⁻¹ = g * ι (e (QuotientGroup.mk l)) * g⁻¹
    rw [h1]
  have himgL : ∀ l : ↥P, (l : G) ∈ L → glMat ((F₀.conj g).M l) ∈ H := by
    intro l hl
    have := hMι ⟨l, hl⟩
    have e1 : Subgroup.inclusion h.le (⟨l, hl⟩ : ↥L) = l := Subtype.ext rfl
    rw [e1] at this
    rw [this]
    exact hall _
  have hsurjL : ∀ m ∈ H, ∃ l : ↥P, (l : G) ∈ L ∧ glMat ((F₀.conj g).M l) = m := by
    intro m hm
    obtain ⟨σ, hσ⟩ := hsurj m hm
    obtain ⟨q, rfl⟩ := e.surjective σ
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨Subgroup.inclusion h.le l', l'.2, ?_⟩
    rw [hMι]; exact hσ
  refine ⟨{
    F := F₀.conj g
    imgL := himgL
    surjL := hsurjL
    kerL := ?_
    core := ?_
    normP := ?_ }⟩
  · intro l hl
    have hMl := hMι ⟨l, hl⟩
    have e1 : Subgroup.inclusion h.le (⟨l, hl⟩ : ↥L) = l := Subtype.ext rfl
    rw [e1] at hMl
    constructor
    · intro h1
      rw [hMl] at h1
      have h2 : e (QuotientGroup.mk ⟨l, hl⟩) = 1 := hι'inj (by rw [h1, map_one])
      rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h2
      exact ⟨⟨l, hl⟩, h2, rfl⟩
    · intro h1
      have h3 : F₀.M l = 1 := hcoreM l (pCoreOf_le_pCoreOf h.le h.norm_L h1)
      rw [ElemFrame.conj_M, h3]; simp
  · intro q hq
    rw [ElemFrame.conj_M, hcoreM q hq]; simp
  · intro p m hm
    obtain ⟨l, hl, rfl⟩ := hsurjL m hm
    have hl2 : ((p * l * p⁻¹ : ↥P) : G) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (h.norm_L p.2) (l : G)).mp hl
      simpa using this
    refine ⟨glMat ((F₀.conj g).M (p * l * p⁻¹)), himgL _ hl2, ?_⟩
    rw [map_mul, map_mul, map_inv]
    simp only [glMat, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

theorem not_mem_pCoreOf_of_orderOf_three {x : G} (hx3 : orderOf x = 3) : x ∉ pCoreOf 2 L := by
  intro hx
  have hp : IsPGroup 2 (pCoreOf 2 L) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  rcases k with _ | k
  · simp at hk
  · have : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    omega

theorem fixFree_iff (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G)) (x : ↥P) :
    FixFree K E (x : G) ↔ ∀ v : Fin 4 → ZMod 2, glMat (F.M x) *ᵥ v = v → v = 0 := by
  constructor
  · intro hff v hv
    obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
    have hv' : v = Multiplicative.toAdd (F.φ e) := by rw [he]; rfl
    let c : ↥E := ⟨⁅(e : G), (x : G)⁆, ElemFrame.comm_right_mem hPE x.2 e.2⟩
    have hc := F.phi_comm hPE x e c rfl
    rw [← hv', hv, sub_self] at hc
    have hcK : (c : G) ∈ K := (F.ker c).mp (by
      apply Multiplicative.toAdd.injective
      simpa using hc)
    have heK : (e : G) ∈ K := hff e e.2 hcK
    have := (F.ker e).mpr heK
    rw [hv', this]; rfl
  · intro hv e he hcK
    let e' : ↥E := ⟨e, he⟩
    let c : ↥E := ⟨⁅e, (x : G)⁆, ElemFrame.comm_right_mem hPE x.2 he⟩
    have hc := F.phi_comm hPE x e' c rfl
    have hc0 : F.φ c = 1 := (F.ker c).mpr hcK
    rw [hc0, toAdd_one] at hc
    have hfix : glMat (F.M x) *ᵥ Multiplicative.toAdd (F.φ e') = Multiplicative.toAdd (F.φ e') :=
      (sub_eq_zero.mp hc.symm).symm
    have h0 := hv _ hfix
    have : F.φ e' = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h0
    exact (F.ker e').mp this

theorem A5Model.order3 {H : Finset Mat4} (M : A5Model P L E K H) {x : G} (hxL : x ∈ L)
    (hxP : x ∈ P) (hx3 : orderOf x = 3) :
    glMat (M.F.M ⟨x, hxP⟩) ∈ H ∧ glMat (M.F.M ⟨x, hxP⟩) ≠ 1 ∧
      glMat (M.F.M ⟨x, hxP⟩) * glMat (M.F.M ⟨x, hxP⟩) * glMat (M.F.M ⟨x, hxP⟩) = 1 := by
  refine ⟨M.imgL ⟨x, hxP⟩ hxL, ?_, ?_⟩
  · intro h1
    have h2 : M.F.M ⟨x, hxP⟩ = 1 := Units.ext h1
    exact not_mem_pCoreOf_of_orderOf_three hx3 ((M.kerL ⟨x, hxP⟩ hxL).mp h2)
  · have h3 : x * x * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx3] at this
      simpa [pow_succ, mul_assoc] using this
    have h4 : (⟨x, hxP⟩ : ↥P) * ⟨x, hxP⟩ * ⟨x, hxP⟩ = 1 := Subtype.ext h3
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, h4, map_one, Units.val_one]

theorem exists_orderOf_three (h : A5Pre P L E K) : ∃ x ∈ L, orderOf x = 3 := by
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h.quot
  have h60 : Nat.card (oTwoQuot ↥L) = 60 := by rw [Nat.card_congr e.toEquiv]; exact a5_card
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L)
  have h3 : 3 ∣ Nat.card ↥L := by
    rw [hcard]
    exact Dvd.dvd.mul_right (by rw [show Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) = 60 from h60]; norm_num) _
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem natSec_of_model_N (hF : Certificates.A5GL42.Facts) (h : A5Pre P L E K)
    (M : A5Model P L E K Certificates.A5GL42.HN) : NatSec L K E := by
  intro x hxL hx3
  have hxP : x ∈ P := h.le hxL
  have := M.order3 hxL hxP hx3
  have hfix := hF.fixN _ this.1 this.2.1 this.2.2
  exact (fixFree_iff M.F h.norm_E ⟨x, hxP⟩).mpr hfix

theorem not_natSec_of_model_O (hF : Certificates.A5GL42.Facts) (h : A5Pre P L E K)
    (M : A5Model P L E K Certificates.A5GL42.HO) : ¬ NatSec L K E := by
  intro hnat
  obtain ⟨x, hxL, hx3⟩ := exists_orderOf_three h
  have hxP : x ∈ P := h.le hxL
  have := M.order3 hxL hxP hx3
  obtain ⟨v, hv0, hv⟩ := hF.fixO _ this.1 this.2.1 this.2.2
  have hff := (fixFree_iff M.F h.norm_E ⟨x, hxP⟩).mp (hnat x hxL hx3) v hv
  exact hv0 hff

theorem A5Pre.exists_model (hF : Certificates.A5GL42.Facts) (h : A5Pre P L E K) :
    (NatSec L K E ∧ Nonempty (A5Model P L E K Certificates.A5GL42.HN)) ∨
      (¬ NatSec L K E ∧ Nonempty (A5Model P L E K Certificates.A5GL42.HO)) := by
  obtain ⟨F₀⟩ := exists_elemFrame h.sec h.card h.norm_E h.norm_K
  have hcoreM : ∀ q : ↥P, (q : G) ∈ pCoreOf 2 P → F₀.M q = 1 := fun q hq =>
    F₀.M_eq_one h.norm_E q (fun e he => h.core q hq e he)
  have hker : ∀ y : ↥L, y ∈ CFSG.Open.pCore 2 ↥L → F₀.M (Subgroup.inclusion h.le y) = 1 := by
    intro y hy
    exact hcoreM _ (pCoreOf_le_pCoreOf h.le h.norm_L ⟨y, hy, rfl⟩)
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h.quot
  set ι := iotaOf F₀ h hker e with hιdef
  have hι : Function.Injective ι := iotaOf_injective F₀ h hker e
  have hx0 : glMat (ι x0) * glMat (ι x0) = 1 := by
    rw [← Units.val_mul, ← map_mul, x0_sq, map_one, Units.val_one]
  have hx1 : glMat (ι x0) ≠ 1 := fun h1 => x0_ne_one (hι (by rw [map_one]; exact Units.ext h1))
  have hy3 : glMat (ι y0) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, y0_cube, map_one, Units.val_one]
  have hxy : (glMat (ι x0) * glMat (ι y0)) ^ 5 = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← map_mul, ← map_pow, x0_y0_pow_five, map_one,
      Units.val_one]
  obtain ⟨g, hg, hcase⟩ := hF.classify _ _ hx0 hx1 hy3 hxy
  let gGL : GL (Fin 4) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' g (by rw [hg]; exact isUnit_one)
  have hgl : glMat gGL = g := rfl
  rcases hcase with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
  · left
    have hM := exists_model_of_conj hF.groupN hF.gens.1 hF.gens.2.1 h F₀ hcoreM hker e gGL
      (by rw [hgl]; exact hga) (by rw [hgl]; exact hgb)
    obtain ⟨M⟩ := hM
    exact ⟨natSec_of_model_N hF h M, ⟨M⟩⟩
  · right
    have hM := exists_model_of_conj hF.groupO hF.gens.2.2.1 hF.gens.2.2.2 h F₀ hcoreM hker e gGL
      (by rw [hgl]; exact hga) (by rw [hgl]; exact hgb)
    obtain ⟨M⟩ := hM
    exact ⟨not_natSec_of_model_O hF h M, ⟨M⟩⟩

end Model

end CFSG.GH74.QTGen4.DSGen4
