module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalWeak
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SixLocalResults

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem eq_one_of_mem_core {x : G} (hx : x ∈ aschbacherThm5Core D)
    (hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hx2
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (orderOf x) :=
    (core_odd D).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem normalizer_le_conj (hC : Counterexample G D r Abar) {i : Fin r} {g : G}
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    (hPL : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g) :
    Subgroup.normalizer (P : Set G) ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  obtain ⟨⟨t, htP⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨j, hji⟩ := exists_other hC i
  intro n hn
  rw [mem_rightConjugate_iff]
  have ht2 := twoElt_of_mem hP2 htP
  have hs := (mem_rightConjugate_iff _ _ _).mp (hPL htP)
  have hs1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1'
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  apply mem_normalizer_of_fusion hC j j (twoElt_conj ht2 g) hs1
    (cross_factor_centralizes D Abar hC.hyp.hcomm j i hji _ hs)
  have hnt : n⁻¹ * t * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t).mp htP
    simpa using this
  have hs' := (mem_rightConjugate_iff _ _ _).mp (hPL hnt)
  have heq : (g * n * g⁻¹)⁻¹ * (g * t * g⁻¹) * (g * n * g⁻¹) = g * (n⁻¹ * t * n) * g⁻¹ := by
    group
  rw [heq]
  exact cross_factor_centralizes D Abar hC.hyp.hcomm j i hji _ hs'

theorem isMulCommutative_of_le_conj_factorZStar {i : Fin r} {g : G} {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPZ : P ≤ rightConjugate (factorZStar D Abar i) g) :
    IsMulCommutative P := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx := (mem_rightConjugate_iff _ _ _).mp (hPZ x.2)
  have hy := (mem_rightConjugate_iff _ _ _).mp (hPZ y.2)
  have hc := centralizes_of_mem_centralizing hx.2 _ hy.1
  have hcomm : (x : G)⁻¹ * (y : G)⁻¹ * x * y ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem x.2) (P.inv_mem y.2)) x.2) y.2
  have hcore : g * ((x : G)⁻¹ * (y : G)⁻¹ * x * y) * g⁻¹ ∈ aschbacherThm5Core D := by
    have heq : g * ((x : G)⁻¹ * (y : G)⁻¹ * x * y) * g⁻¹ =
        (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact hc
  have h1 := eq_one_of_mem_core hcore (twoElt_conj (twoElt_of_mem hP2 hcomm) g)
  have h2 : (x : G)⁻¹ * (y : G)⁻¹ * x * y = 1 := by
    calc (x : G)⁻¹ * (y : G)⁻¹ * x * y =
        g⁻¹ * (g * ((x : G)⁻¹ * (y : G)⁻¹ * x * y) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have h3 : (x : G)⁻¹ * (y : G)⁻¹ * x * y = ((y : G) * x)⁻¹ * (x * y) := by group
  rw [h3, inv_mul_eq_one] at h2
  exact h2.symm


omit [Finite G] in
theorem commutator_sup_le {C T : Subgroup G} (hC : IsMulCommutative C)
    (hCT : ∀ c ∈ C, ∀ t ∈ T, c * t = t * c) : ⁅C ⊔ T, C ⊔ T⁆ ≤ T := by
  have hCC : C ≤ Subgroup.centralizer (T : Set G) :=
    fun c hc => Subgroup.mem_centralizer_iff.mpr fun t ht => (hCT c hc t ht).symm
  have hCN : C ≤ Subgroup.normalizer (T : Set G) :=
    hCC.trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ ((C ⊔ T : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((C ⊔ T : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right C T hCN] at hx' hy'
  obtain ⟨c₁, hc₁, t₁, ht₁, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨c₂, hc₂, t₂, ht₂, rfl⟩ := Set.mem_mul.mp hy'
  have h5 : c₁ * c₂ = c₂ * c₁ := congrArg Subtype.val (hC.is_comm.comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩)
  set τ := t₁ * t₂ * t₁⁻¹ * t₂⁻¹ with hτ
  have hτT : τ ∈ T := T.mul_mem (T.mul_mem (T.mul_mem ht₁ ht₂) (T.inv_mem ht₁)) (T.inv_mem ht₂)
  have hxy : c₁ * t₁ * (c₂ * t₂) = c₁ * c₂ * (t₁ * t₂) := by
    calc c₁ * t₁ * (c₂ * t₂) = c₁ * (t₁ * c₂) * t₂ := by group
      _ = c₁ * (c₂ * t₁) * t₂ := by rw [hCT c₂ hc₂ t₁ ht₁]
      _ = c₁ * c₂ * (t₁ * t₂) := by group
  have hyx : c₂ * t₂ * (c₁ * t₁) = c₁ * c₂ * (t₂ * t₁) := by
    calc c₂ * t₂ * (c₁ * t₁) = c₂ * (t₂ * c₁) * t₁ := by group
      _ = c₂ * (c₁ * t₂) * t₁ := by rw [hCT c₁ hc₁ t₂ ht₂]
      _ = c₂ * c₁ * (t₂ * t₁) := by group
      _ = c₁ * c₂ * (t₂ * t₁) := by rw [h5]
  have hγτ : c₁ * c₂ * τ = τ * (c₁ * c₂) := by
    calc c₁ * c₂ * τ = c₁ * (c₂ * τ) := by group
      _ = c₁ * (τ * c₂) := by rw [hCT c₂ hc₂ τ hτT]
      _ = (c₁ * τ) * c₂ := by group
      _ = (τ * c₁) * c₂ := by rw [hCT c₁ hc₁ τ hτT]
      _ = τ * (c₁ * c₂) := by group
  have heq : ⁅c₁ * t₁, c₂ * t₂⁆ = τ := by
    rw [commutatorElement_def]
    calc c₁ * t₁ * (c₂ * t₂) * (c₁ * t₁)⁻¹ * (c₂ * t₂)⁻¹ =
        (c₁ * t₁ * (c₂ * t₂)) * (c₂ * t₂ * (c₁ * t₁))⁻¹ := by group
      _ = (c₁ * c₂ * (t₁ * t₂)) * (c₁ * c₂ * (t₂ * t₁))⁻¹ := by rw [hxy, hyx]
      _ = (c₁ * c₂ * τ) * (c₁ * c₂)⁻¹ := by rw [hτ]; group
      _ = τ := by rw [hγτ]; group
  rw [heq]
  exact hτT


theorem le_normalizer_factor (hC : Counterexample G D r Abar) (i : Fin r) :
    D ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
    (canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen i)

omit [Finite G] in
theorem datum_g_not_mem {a : Fin r} (d : DeltaDatum D Abar a) :
    d.g ∉ Subgroup.normalizer (D : Set G) := fun h =>
  d.ne (AschbacherTheorem3.rightConjugate_eq_of_mem h)

theorem datum_T_abelian (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a)
    (hWab : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G)) :
    IsMulCommutative d.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set Hg := rightConjugate H d.g with hHgdef
  have hT2 : IsPGroup 2 d.T := d.sylowT.isPGroup
  have hTL : d.T ≤ L := d.sylowT.le.trans inf_le_left
  have hTA : d.T ≤ Subgroup.normalizer (A : Set G) := d.sylowT.le.trans inf_le_right
  have hg := datum_g_not_mem d
  by_cases hTZ : d.T ≤ rightConjugate (factorZStar D Abar a) d.g
  · exact isMulCommutative_of_le_conj_factorZStar hT2 hTZ
  by_cases hAN : A ⊓ Hg ≤ Subgroup.normalizer (L : Set G)
  swap
  · obtain ⟨y, -, -, -, -, -, hab⟩ := hloc.lemma_6_10 hC d hAN hTZ
    exact AschbacherTheorem3.isMulCommutative_of_le le_sup_left hab
  have hT1 : d.T ≠ ⊥ := fun h => hTZ (h ▸ bot_le)
  have hTA1 : d.T ⊓ A = ⊥ :=
    eq_bot_of_le_inf_conj hC hg hT2.to_inf_left inf_le_right (inf_le_left.trans hTL)
  have hnot : ¬ ∀ x ∈ d.T, aschbacherThm5Centralizes (aschbacherThm5Core D) A x := by
    intro hall
    obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    exact not_centralizes_of_mem_conj hC a hg (twoElt_of_mem hT2 htT)
      (fun h => ht1 (Subtype.ext h)) (hTL htT) (hall t htT)
  have hTH : d.T ≤ H := hTA.trans (factor_normalizer_le D r Abar hC.hyp.hii a)
  obtain ⟨c, hcA, hcle, hcne⟩ := exists_conj_le_normalizer (preimage_le D _)
    (core_le_preimage D _) (le_normalizer_factor hC a) hTH hTA hT2 hTA1 d.sylowS
    d.invariant hnot
  have hF : AschbacherTheorem3.Frame d.S d.T :=
    ⟨d.invariant, le_bot_iff.mp ((inf_le_inf_left _ d.sylowS.le).trans hTA1.le), hT2⟩
  obtain ⟨hdec, -, hcomm⟩ := AschbacherTheorem3.lemma_4_1 hF (S := d.S ⊔ d.T) le_rfl le_sup_right
  set C := (d.S ⊔ d.T) ⊓ Subgroup.normalizer (d.T : Set G) ⊓ d.S with hCdef
  have hCN : C ≤ d.S ⊓ Subgroup.normalizer (L : Set G) := by
    refine le_inf inf_le_right fun x hx => hAN ⟨d.sylowS.le hx.2, ?_⟩
    exact normalizer_le_conj hC hT2 hT1 hTL hx.1.2
  have hCab : IsMulCommutative C := AschbacherTheorem3.isMulCommutative_of_le hCN hWab
  have hCT : ∀ x ∈ C, ∀ t ∈ d.T, x * t = t * x := by
    intro x hx t ht
    have h1 : ⁅t, x⁆ ∈ ⁅d.T, C⁆ := Subgroup.commutator_mem_commutator ht hx
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hsup : d.T ⊔ C = C ⊔ d.T := sup_comm _ _
  have hTcle : rightConjugate d.T c ≤ C ⊔ d.T := by
    rw [← hsup, ← hdec]
    exact hcle
  have hcHg : c ∉ Hg := by
    intro hcHg
    apply hcne
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN ⟨hcA, hcHg⟩
    apply Subgroup.eq_of_le_of_card_ge _ (by rw [rightConjugate_card])
    intro x hx
    have hxL : x ∈ L := by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hTL c hx
      rwa [(rightConjugate_eq_self_iff L c).mpr hcN] at this
    have hCC : C ≤ Subgroup.centralizer (d.T : Set G) :=
      fun x hx => Subgroup.mem_centralizer_iff.mpr fun t ht => (hCT x hx t ht).symm
    have hCTN : C ≤ Subgroup.normalizer (d.T : Set G) :=
      hCC.trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((C ⊔ d.T : Subgroup G) : Set G) := hTcle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C d.T hCTN] at hx'
    obtain ⟨y, hyC, t, htT, rfl⟩ := Set.mem_mul.mp hx'
    have hyL : y ∈ L := by
      have := L.mul_mem hxL (L.inv_mem (hTL htT))
      simpa using this
    have hy1 : y = 1 := eq_one_of_mem_inf_conj hC hg
      (twoElt_of_mem d.sylowS.isPGroup hyC.2) (d.sylowS.le hyC.2) hyL
    rw [hy1, one_mul]
    exact htT
  have hTTc : d.T ⊓ rightConjugate d.T c = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have ht2 := twoElt_of_mem hT2 ht.1
    have hs1 : d.g * t * d.g⁻¹ ∈ A := (mem_rightConjugate_iff _ _ _).mp (hTL ht.1)
    have hs2 : d.g * t * d.g⁻¹ ∈ rightConjugate A (d.g * c * d.g⁻¹) := by
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hTL c ht.2
      rw [rightConjugate_mul, mem_rightConjugate_iff] at h1
      rw [mem_rightConjugate_iff]
      have heq : d.g * c * d.g⁻¹ * (d.g * t * d.g⁻¹) * (d.g * c * d.g⁻¹)⁻¹ =
          d.g * c * t * (d.g * c)⁻¹ := by group
      rw [heq]
      exact h1
    have hgc : d.g * c * d.g⁻¹ ∉ H := fun h => hcHg ((mem_rightConjugate_iff _ _ _).mpr h)
    have h1 := eq_one_of_mem_inf_conj hC hgc (twoElt_conj ht2 d.g) hs1 hs2
    calc t = d.g⁻¹ * (d.g * t * d.g⁻¹) * d.g := by group
      _ = 1 := by rw [h1]; group
  have hTcab : IsMulCommutative (rightConjugate d.T c) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxy : ⁅(x : G), (y : G)⁆ ∈ d.T ⊓ rightConjugate d.T c := by
      refine ⟨commutator_sup_le hCab hCT (Subgroup.commutator_mem_commutator
        (hTcle x.2) (hTcle y.2)), ?_⟩
      exact (rightConjugate d.T c).mul_mem ((rightConjugate d.T c).mul_mem
        ((rightConjugate d.T c).mul_mem x.2 y.2) ((rightConjugate d.T c).inv_mem x.2))
        ((rightConjugate d.T c).inv_mem y.2)
    rw [hTTc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
    exact hxy
  have h := AschbacherTheorem3.isMulCommutative_rightConjugate hTcab c⁻¹
  rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
