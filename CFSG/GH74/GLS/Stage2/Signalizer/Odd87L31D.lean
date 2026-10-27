module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Red
public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIG
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section D0

variable {G : Type} [Group G] [Finite G]

theorem l31_pPrimeCoreOf_map_inj {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (K : Subgroup A) :
    pPrimeCoreOf 2 (K.map f) = (pPrimeCoreOf 2 K).map f := by
  let ψ : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
  have h1 : (pPrimeCore 2 ↥K).map ψ.toMonoidHom = pPrimeCore 2 ↥(K.map f) := pPrimeCore_map_iso 2 ψ
  have h2 : (K.map f).subtype.comp ψ.toMonoidHom = f.comp K.subtype := by ext g; rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

omit [Finite G] in
theorem l31_mem_normalizer_pPrimeCoreOf {J : Subgroup G} {t : G}
    (ht : t ∈ normalizer (J : Set G)) :
    t ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) := by
  have h1 : J.map (MulAut.conj t).toMonoidHom = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  have h2 := l31_pPrimeCoreOf_map_inj (MulAut.conj t).toMonoidHom (MulAut.conj t).injective J
  rw [h1] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2.symm

theorem l31_inf_pPrimeCoreOf_le {H J : Subgroup G} (hJH : J ≤ H) :
    J ⊓ pPrimeCoreOf 2 H ≤ pPrimeCoreOf 2 J := by
  let N : Subgroup ↥J := (J ⊓ pPrimeCoreOf 2 H).subgroupOf J
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2)
    · exact conj_mem_pPrimeCoreOf_of_mem (hJH g.2) hn.2
  have hcop : Nat.Coprime 2 (Nat.card ↥N) := by
    have h1 : Nat.card ↥N ∣ Nat.card ↥(pPrimeCoreOf 2 H) := by
      have e : Nat.card ↥N = Nat.card ↥(J ⊓ pPrimeCoreOf 2 H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ pPrimeCoreOf 2 H ≤ J)).toEquiv
      rw [e]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.coprime_two_left.mpr (odd_card_pPrimeCoreOf_J H))
  have hN : N ≤ pPrimeCore 2 ↥J := le_sSup (show N ∈ normalPPrimeSubgroups 2 ↥J from ⟨hNn, hcop⟩)
  intro x hx
  exact ⟨⟨x, hx.1⟩, hN (Subgroup.mem_subgroupOf.mpr hx), rfl⟩


theorem mem_centralizerSection_of_bar {H J : Subgroup G} (hJ : IsPCompIn 2 H J) {b : G} (hb : b ∈ H)
    (hc : ∀ y ∈ barIn H J, QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨b, hb⟩ * y =
      y * QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨b, hb⟩) :
    b ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJH : J ≤ H := hJ.1
  set π : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  have hJx : IsPComponent 2 (J.subgroupOf H) := hJ.2
  have hmap : barIn H J = (J.subgroupOf H).map π := rfl
  have hcinv : ∀ y ∈ barIn H J, (π ⟨b, hb⟩)⁻¹ * y = y * (π ⟨b, hb⟩)⁻¹ := by
    intro y hy
    have h := hc y hy
    calc (π ⟨b, hb⟩)⁻¹ * y = (π ⟨b, hb⟩)⁻¹ * (y * π ⟨b, hb⟩) * (π ⟨b, hb⟩)⁻¹ := by group
      _ = (π ⟨b, hb⟩)⁻¹ * (π ⟨b, hb⟩ * y) * (π ⟨b, hb⟩)⁻¹ := by rw [h]
      _ = y * (π ⟨b, hb⟩)⁻¹ := by group
  have hnorm1 : π ⟨b, hb⟩ ∈ normalizer (((J.subgroupOf H).map π : Subgroup (HBar H)) : Set (HBar H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' : y ∈ barIn H J := hy
      have : π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹ = y := by rw [hc y hy']; group
      rw [this]; exact hy
    · intro hy
      have hy' : π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹ ∈ barIn H J := hy
      have h2 := hcinv _ hy'
      have hyeq : y = π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹ := by
        calc y = (π ⟨b, hb⟩)⁻¹ * (π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹) * π ⟨b, hb⟩ := by group
          _ = (π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹) * (π ⟨b, hb⟩)⁻¹ * π ⟨b, hb⟩ := by rw [h2]
          _ = π ⟨b, hb⟩ * y * (π ⟨b, hb⟩)⁻¹ := by group
      rw [← hyeq] at hy
      exact hy
  have hnormX : (⟨b, hb⟩ : ↥H) ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJx hnorm1
  have hnormG : b ∈ normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h := Subgroup.mem_normalizer_iff.mp hnormX
    constructor
    · intro hg
      exact (h ⟨g, hJH hg⟩).mp hg
    · intro hg
      have hgH : g ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem hb) (hJH hg)) hb
        simpa [mul_assoc] using this
      have := (h ⟨g, hgH⟩).mpr (by
        show b * g * b⁻¹ ∈ J
        exact hg)
      exact this
  refine ⟨hnormG, l31_mem_normalizer_pPrimeCoreOf hnormG, ?_⟩
  intro k hk
  have hkH : k ∈ H := hJH hk
  have h1 : ⁅k, b⁆ ∈ J := by
    have : b * k⁻¹ * b⁻¹ ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp hnormG k⁻¹).mp (J.inv_mem hk)
      exact this
    have h2 := J.mul_mem hk this
    simpa [commutatorElement_def, mul_assoc] using h2
  have h2 : ⁅k, b⁆ ∈ pPrimeCoreOf 2 H := by
    have hk' : π ⟨k, hkH⟩ ∈ barIn H J := ⟨⟨k, hkH⟩, hk, rfl⟩
    have hcomm : (⟨k, hkH⟩ : ↥H) * ⟨b, hb⟩ * (⟨k, hkH⟩ : ↥H)⁻¹ * (⟨b, hb⟩ : ↥H)⁻¹ ∈
        pPrimeCore 2 ↥H := by
      apply (QuotientGroup.eq_one_iff _).mp
      show π ((⟨k, hkH⟩ : ↥H) * ⟨b, hb⟩ * (⟨k, hkH⟩ : ↥H)⁻¹ * (⟨b, hb⟩ : ↥H)⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← (hc _ hk')]
      group
    exact ⟨_, hcomm, rfl⟩
  exact l31_inf_pPrimeCoreOf_le hJH ⟨h1, h2⟩


omit [Finite G] in
theorem l31_exists_mul_of_mem_sup {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem l31_isPGroup_two_sup {A B : Subgroup G} (hA : IsPGroup 2 ↥A) (hB : IsPGroup 2 ↥B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 ↥(A ⊔ B) := by
  exact hA.to_sup_of_normal_right' hB
    (le_normalizer_of_commute fun b hb a ha => (h a ha b hb).symm)

end D0

section DCore

variable {G : Type} [Group G] [Finite G]

theorem l31_aschb_of_cyclic_quat_dihedral {R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (ha : IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R) :
    IsCyclic ↥R ∨ CFSG.ComponentClassification.AschbacherTheorem3.IsDihedralTwoGroup R ∨
      CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup R := by
  rcases ha with h | ⟨n, hn3, hn⟩ | ⟨m, k, hm, hk, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨n, hn3, hn⟩)
  · right; left
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hR
    have hk0 : NeZero k := ⟨by omega⟩
    have hcard : Nat.card ↥R = 2 * k := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    have h2k : 2 * k = 2 ^ a := by rw [← hcard]; exact ha
    have ha2 : 2 ≤ a := by
      by_contra hlt
      push Not at hlt
      interval_cases a <;> omega
    have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hk2 : k = 2 ^ (a - 1) := by omega
    subst hk2
    exact ⟨a, ha2, ⟨e⟩⟩


theorem l31_d_core {H J R : Subgroup G} (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    (ha : IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R)
    {C₂ C₃ : Subgroup (HBar H)} (h₂ : IsComponent C₂) (h₃ : IsComponent C₃)
    (hne₂ : C₂ ≠ barIn H J) (hne₃ : C₃ ≠ barIn H J) : C₂ = C₃ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set π : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hJbar : IsComponent (barIn H J) := by
    obtain ⟨K₀, hK₀, -, hLK₀, -⟩ := hJ.2
    change IsComponent ((J.subgroupOf H).map π)
    rw [hLK₀]; exact hK₀
  have comm_of : ∀ {A B : Subgroup (HBar H)}, IsComponent A → IsComponent B → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hAB a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
    · exact absurd h hAB
    · have : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hc₂J := comm_of h₂ hJbar hne₂
  have hc₃J := comm_of h₃ hJbar hne₃
  have hc₂₃ := comm_of h₂ h₃ hne
  have hperf₂ : Group.IsPerfect ↥C₂ := h₂.1.1
  have hperf₃ : Group.IsPerfect ↥C₃ := h₃.1.1
  have hbot₂ : C₂ ≠ ⊥ := by
    intro h
    have := CFSG.LocalCores.isQuasisimple_nontrivial h₂.1
    exact (Subgroup.nontrivial_iff_ne_bot C₂).mp this h
  have hbot₃ : C₃ ≠ ⊥ := by
    intro h
    have := CFSG.LocalCores.isQuasisimple_nontrivial h₃.1
    exact (Subgroup.nontrivial_iff_ne_bot C₃).mp this h
  obtain ⟨P₂, hP₂⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 C₂
  obtain ⟨P₃, hP₃⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 C₃
  have hP₂c : ¬ IsCyclic ↥P₂ :=
    CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.sylow_not_cyclic_of_perfect
      hperf₂ hbot₂ hP₂
  have hP₃c : ¬ IsCyclic ↥P₃ :=
    CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.sylow_not_cyclic_of_perfect
      hperf₃ hbot₃ hP₃
  have hcomm₂₃ : ∀ a ∈ P₂, ∀ b ∈ P₃, a * b = b * a := fun a ha b hb =>
    hc₂₃ a (hP₂.le ha) b (hP₃.le hb)
  have hB : IsPGroup 2 ↥(P₂ ⊔ P₃) :=
    l31_isPGroup_two_sup hP₂.isPGroup hP₃.isPGroup hcomm₂₃
  obtain ⟨Pl⟩ : Nonempty (Sylow 2 ↥((P₂ ⊔ P₃).comap π)) := inferInstance
  have himg := map_sylow_comap_eq π hπsurj (P₂ ⊔ P₃) hB Pl
  set B₀ : Subgroup ↥H := (Pl : Subgroup ↥((P₂ ⊔ P₃).comap π)).map
    ((P₂ ⊔ P₃).comap π).subtype with hB₀
  have hB₀pg : IsPGroup 2 ↥B₀ := Pl.isPGroup'.map _
  have hπB₀ : B₀.map π = P₂ ⊔ P₃ := himg
  have hker : Odd (Nat.card π.ker) := by
    have : π.ker = pPrimeCore 2 ↥H := QuotientGroup.ker_mk' _
    rw [this]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hinj : ∀ x ∈ B₀, ∀ y ∈ B₀, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ B₀ ⊓ π.ker := by
      refine Subgroup.mem_inf.mpr ⟨B₀.mul_mem (B₀.inv_mem hx) hy, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [isPGroup_two_inf_eq_bot_of_odd B₀ π.ker hB₀pg hker, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hB₀C : B₀.map H.subtype ≤ H ⊓ centralizerSection J (pPrimeCoreOf 2 J) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have hxB : π x ∈ P₂ ⊔ P₃ := by rw [← hπB₀]; exact ⟨x, hx, rfl⟩
    obtain ⟨a, ha₂, b, hb₃, hab⟩ := l31_exists_mul_of_mem_sup hcomm₂₃ hxB
    refine mem_centralizerSection_of_bar hJ x.2 ?_
    intro y hy
    have e1 : a * y = y * a := hc₂J a (hP₂.le ha₂) y hy
    have e2 : b * y = y * b := hc₃J b (hP₃.le hb₃) y hy
    show π x * y = y * π x
    rw [hab]
    calc a * b * y = a * (b * y) := by group
      _ = a * (y * b) := by rw [e2]
      _ = (a * y) * b := by group
      _ = (y * a) * b := by rw [e1]
      _ = y * (a * b) := by group
  obtain ⟨m, hmC, hmB⟩ := exists_conj_le_of_isSylowOf hR hB₀C (hB₀pg.map H.subtype)
  set R' : Subgroup G := R.map (MulAut.conj m).toMonoidHom with hR'
  let eR : ↥R ≃* ↥R' := Subgroup.equivMapOfInjective R (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective
  have hR'pg : IsPGroup 2 ↥R' := hR.isPGroup.of_equiv eR
  have ha' : IsCyclic ↥R' ∨ IsQuat ↥R' ∨ IsDihedral ↥R' := by
    rcases ha with h | ⟨n, hn3, ⟨e⟩⟩ | ⟨mm, k, hm, hk, ⟨e⟩⟩
    · exact Or.inl (isCyclic_of_surjective eR.toMonoidHom eR.surjective)
    · exact Or.inr (Or.inl ⟨n, hn3, ⟨eR.symm.trans e⟩⟩)
    · exact Or.inr (Or.inr ⟨mm, k, hm, hk, ⟨eR.symm.trans e⟩⟩)
  have haschb := l31_aschb_of_cyclic_quat_dihedral hR'pg ha'
  let Q₂ : Subgroup ↥H := B₀ ⊓ P₂.comap π
  let Q₃ : Subgroup ↥H := B₀ ⊓ P₃.comap π
  have hQ₂π : Q₂.map π = P₂ := by
    ext p
    constructor
    · rintro ⟨x, ⟨-, hxP⟩, rfl⟩
      exact hxP
    · intro hp
      have hp' : p ∈ B₀.map π := by rw [hπB₀]; exact Subgroup.mem_sup_left hp
      obtain ⟨x, hx, rfl⟩ := hp'
      exact ⟨x, ⟨hx, hp⟩, rfl⟩
  have hQ₃π : Q₃.map π = P₃ := by
    ext p
    constructor
    · rintro ⟨x, ⟨-, hxP⟩, rfl⟩
      exact hxP
    · intro hp
      have hp' : p ∈ B₀.map π := by rw [hπB₀]; exact Subgroup.mem_sup_right hp
      obtain ⟨x, hx, rfl⟩ := hp'
      exact ⟨x, ⟨hx, hp⟩, rfl⟩
  have hQ₂c : ¬ IsCyclic ↥Q₂ := by
    intro hc
    apply hP₂c
    rw [← hQ₂π]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective π Q₂)
  have hQ₃c : ¬ IsCyclic ↥Q₃ := by
    intro hc
    apply hP₃c
    rw [← hQ₃π]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective π Q₃)
  have hcommQ : ∀ x ∈ Q₂, ∀ y ∈ Q₃, x * y = y * x := by
    intro x hx y hy
    apply hinj (x * y) (B₀.mul_mem hx.1 hy.1) (y * x) (B₀.mul_mem hy.1 hx.1)
    rw [map_mul, map_mul]
    exact hcomm₂₃ _ hx.2 _ hy.2
  have hQ₂g : Q₂.map H.subtype ≤ R' := (Subgroup.map_mono inf_le_left).trans hmB
  have hQ₃g : Q₃.map H.subtype ≤ R' := (Subgroup.map_mono inf_le_left).trans hmB
  have hQ₂gc : ¬ IsCyclic ↥(Q₂.map H.subtype) := by
    intro hc
    exact hQ₂c (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q₂ H.subtype H.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _))
  have hQ₃gc : ¬ IsCyclic ↥(Q₃.map H.subtype) := by
    intro hc
    exact hQ₃c (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q₃ H.subtype H.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _))
  have hcommG : ∀ x ∈ Q₂.map H.subtype, ∀ y ∈ Q₃.map H.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcommQ x hx y hy)
  have heqG := CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.commuting_noncyclic_eq
    haschb hQ₂g hQ₃g hQ₂gc hQ₃gc hcommG
  have heqQ : Q₂ = Q₃ := Subgroup.map_injective H.subtype_injective heqG
  have hPeq : P₂ = P₃ := by rw [← hQ₂π, ← hQ₃π, heqQ]
  refine CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.sylow_not_le_centralizer_of_perfect
    hperf₂ hbot₂ hP₂ ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hxC₃ : x ∈ C₃ := hP₃.le (hPeq ▸ hx)
  exact hc₂₃ c hc x hxC₃

theorem l31_d {H J R : Subgroup G} (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    (ha : IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R)
    (hJK : J ≤ pLayerOf 2 H) (hne : J ≠ pLayerOf 2 H) :
    ∃ K₁ K₂ : Subgroup (HBar H), K₁ ⊔ K₂ = barIn H (pLayerOf 2 H) ∧
      (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
      (Group.IsSolvable ↥K₁ ∨ IsQuasisimple ↥K₁) ∧ (Group.IsSolvable ↥K₂ ∨ IsQuasisimple ↥K₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp_of : ∀ {J' : Subgroup G}, IsPCompIn 2 H J' → IsComponent (barIn H J') := by
    intro J' hJ'
    obtain ⟨K₀, hK₀, -, hLK₀, -⟩ := hJ'.2
    change IsComponent ((J'.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))
    rw [hLK₀]; exact hK₀
  have hJbar := hcomp_of hJ
  have hlay : barIn H (pLayerOf 2 H) = layer (HBar H) := hat_map_pLayerOf_subgroupOf H
  obtain ⟨J₂, hJ₂, hJ₂ne⟩ : ∃ J₂, IsPCompIn 2 H J₂ ∧ J₂ ≠ J := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hJK (sSup_le fun L hL => (hcon L hL).le))
  have hJ₂bar := hcomp_of hJ₂
  have hJ₂barne : barIn H J₂ ≠ barIn H J := by
    intro heq
    apply hJ₂ne
    have h1 := CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq hJ₂.2 hJ.2 heq
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rw [inf_eq_left.mpr hJ₂.1, inf_eq_left.mpr hJ.1] at h2
    exact h2
  have hsing : ∀ C : Subgroup (HBar H), IsComponent C → C ≠ barIn H J → C = barIn H J₂ :=
    fun C hC hCJ => l31_d_core hJ hR ha hC hJ₂bar hCJ hJ₂barne
  refine ⟨barIn H J, barIn H J₂, ?_, ?_, Or.inr hJbar.1, Or.inr hJ₂bar.1⟩
  · rw [hlay]
    simp only [CFSG.layer.eq_sSup]
    apply le_antisymm
    · exact sup_le (le_sSup hJbar) (le_sSup hJ₂bar)
    · refine sSup_le fun C hC => ?_
      by_cases hCJ : C = barIn H J
      · rw [hCJ]; exact le_sup_left
      · rw [hsing C hC hCJ]; exact le_sup_right
  · intro a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute hJbar hJ₂bar with h | h
    · exact absurd h.symm hJ₂barne
    · have : ⁅a, b⁆ ∈ ⁅barIn H J, barIn H J₂⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this

end DCore



end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
