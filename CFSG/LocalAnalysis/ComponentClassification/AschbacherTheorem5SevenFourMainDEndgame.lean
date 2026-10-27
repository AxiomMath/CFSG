module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools SectionSix.Exclusion
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_lt {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q < P) :
    ∃ g ∈ P, g ∈ Subgroup.normalizer (Q : Set G) ∧ g ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hQP' : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hQP.ne
    apply le_antisymm hQP.le
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ Q.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hQP')
  refine ⟨y, y.2, ?_, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : (⟨x, hQP.le hx⟩ : P) ∈ Q.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mp hx')
  · intro hx
    have hxP : x ∈ P := by
      have h1 := P.mul_mem (P.mul_mem (P.inv_mem y.2) (hQP.le hx)) y.2
      simpa [mul_assoc] using h1
    have hx' : y * ⟨x, hxP⟩ * y⁻¹ ∈ Q.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mpr hx')

theorem exists_sylow_index_two {A R T₀ : Subgroup G} {r t ρ₁ f : G}
    (hR : IsSylowOf 2 R (A ⊓ Subgroup.centralizer ({t} : Set G)))
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRr : CFSG.Open.pRank 2 R ≤ 1)
    (hrR : r ∈ R) (hr2 : orderOf r = 2) (hρ₁ : ρ₁ ∈ R) (hρ₁sq : ρ₁ ^ 2 = r)
    (hT₀2 : IsPGroup 2 T₀) (hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set G))
    (hT₀A : T₀ ≤ Subgroup.normalizer (A : Set G)) (hT₀inf : T₀ ⊓ A = ⊥)
    (hT₀comm : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a) (hT₀r : CFSG.Open.pRank 2 T₀ ≤ 1)
    (htT₀ : t ∈ T₀) (ht2 : orderOf t = 2) (hf : f ∈ T₀) (hfsq : f ^ 2 = t)
    (hRT : ∀ a ∈ R, ∀ b ∈ T₀, a * b = b * a) (hA2 : 2 ≤ CFSG.Open.pRank 2 A) :
    ∃ P : Subgroup G, IsSylowOf 2 P A ∧ R ≤ P ∧ R.relIndex P = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA : R ≤ A := hR.le.trans inf_le_left
  have hR2 := hR.isPGroup
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr2
    omega
  have hTA1 : ∀ x ∈ T₀, x ∈ A → x = 1 := fun x hxT hxA => by
    have hmem : x ∈ T₀ ⊓ A := ⟨hxT, hxA⟩
    rwa [hT₀inf, Subgroup.mem_bot] at hmem
  have htA : t ∉ A := fun h => ht1 (hTA1 t htT₀ h)
  have hrA : r ∈ A := hRA hrR
  have hT₀NR : T₀ ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hRT y hy x hx))
  have hRNT : R ≤ Subgroup.normalizer (T₀ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hRT x hx y hy).symm)
  have hframeRT : AschbacherTheorem3.Frame R T₀ :=
    ⟨hT₀NR, eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hTA1 x hx.1 (hRA hx.2)), hT₀2⟩
  have hframeAT : AschbacherTheorem3.Frame A T₀ := ⟨hT₀A, hT₀inf, hT₀2⟩
  set U := R ⊔ T₀ with hUdef
  have hU2 : IsPGroup 2 U := IsPGroup.to_sup_of_normal_right' hR2 hT₀2 hRNT
  have hRU : R ≤ U := le_sup_left
  have hTU : T₀ ≤ U := le_sup_right
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    obtain ⟨τ, hτ, ρ, hρ, rfl⟩ := hframeRT.mem_sup_iff.mp ha
    obtain ⟨τ', hτ', ρ', hρ', rfl⟩ := hframeRT.mem_sup_iff.mp hb
    have h1 : Commute (τ * ρ) τ' :=
      Commute.mul_left (hT₀comm τ hτ τ' hτ') (hRT ρ hρ τ' hτ')
    have h2 : Commute (τ * ρ) ρ' :=
      Commute.mul_left (hRT ρ' hρ' τ hτ).symm (hRcomm ρ hρ ρ' hρ')
    exact (Commute.mul_right h1 h2).eq
  have hUA : ∀ u ∈ U, u ∈ A → u ∈ R := by
    intro u hu huA
    obtain ⟨τ, hτ, ρ, hρ, rfl⟩ := hframeRT.mem_sup_iff.mp hu
    have hτA : τ ∈ A := by
      have h1 := A.mul_mem huA (A.inv_mem (hRA hρ))
      rwa [mul_inv_cancel_right] at h1
    rw [hTA1 τ hτ hτA, one_mul]
    exact hρ
  have hUinv : ∀ u ∈ U, orderOf u = 2 → u = r ∨ u = t ∨ u = r * t := by
    intro u hu hu2
    obtain ⟨τ, hτ, ρ, hρ, rfl⟩ := hframeRT.mem_sup_iff.mp hu
    have hsq : (τ * ρ) ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one _
    have hτρ : τ * ρ = ρ * τ := (hRT ρ hρ τ hτ).symm
    have hsq' : τ ^ 2 * ρ ^ 2 = 1 := by
      have hc : Commute τ ρ := hτρ
      rw [← hc.mul_pow]
      exact hsq
    have hτ2 : τ ^ 2 = 1 := by
      have h1 : τ ^ 2 = (ρ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq'
      have hmemT : τ ^ 2 ∈ T₀ := T₀.pow_mem hτ 2
      have hmemA : τ ^ 2 ∈ A := by rw [h1]; exact A.inv_mem (A.pow_mem (hRA hρ) 2)
      exact hTA1 _ hmemT hmemA
    have hρ2 : ρ ^ 2 = 1 := by rw [hτ2, one_mul] at hsq'; exact hsq'
    have hτc : τ = 1 ∨ τ = t := by
      by_cases h1 : τ = 1
      · exact Or.inl h1
      · exact Or.inr (eq_of_pRank_le_one hT₀2 hT₀r hτ htT₀ (orderOf_eq_prime hτ2 h1) ht2)
    have hρc : ρ = 1 ∨ ρ = r := by
      by_cases h1 : ρ = 1
      · exact Or.inl h1
      · exact Or.inr (eq_of_pRank_le_one hR2 hRr hρ hrR (orderOf_eq_prime hρ2 h1) hr2)
    rcases hτc with h | h <;> rcases hρc with h' | h' <;> rw [h, h'] at hu2 ⊢
    · rw [one_mul, orderOf_one] at hu2
      omega
    · exact Or.inl (one_mul r)
    · exact Or.inr (Or.inl (mul_one t))
    · exact Or.inr (Or.inr (hRT r hrR t htT₀).symm)
  have hUAT : U ≤ A ⊔ T₀ := sup_le (hRA.trans le_sup_left) le_sup_right
  obtain ⟨S, hS, hUS⟩ := exists_isSylowOf_le hUAT hU2
  have hS2 := hS.isPGroup
  have hSA : ∀ s ∈ S, s ∈ Subgroup.normalizer (A : Set G) := fun s hs =>
    (sup_le Subgroup.le_normalizer hT₀A : A ⊔ T₀ ≤ Subgroup.normalizer (A : Set G)) (hS.le hs)
  have hCSt : ∀ s ∈ S, s * t = t * s → s ∈ U := by
    intro s hs hst
    obtain ⟨τ, hτ, a, haA, rfl⟩ := hframeAT.mem_sup_iff.mp (hS.le hs)
    have haS : a ∈ S := by
      have h1 := S.mul_mem (S.inv_mem (hUS (hTU hτ))) hs
      rwa [inv_mul_cancel_left] at h1
    have hat : a * t = t * a := by
      have hτt : τ * t = t * τ := Subgroup.mem_centralizer_singleton_iff.mp (hT₀t hτ)
      have h1 : τ * (a * t) = τ * (t * a) := by
        calc τ * (a * t) = τ * a * t := by group
          _ = t * (τ * a) := hst
          _ = τ * (t * a) := by rw [← mul_assoc, ← hτt, mul_assoc]
      exact mul_left_cancel h1
    have hW : S ⊓ (A ⊓ Subgroup.centralizer ({t} : Set G)) = R :=
      hR.eq_of_le (le_inf (hRU.trans hUS) hR.le) inf_le_right hS2.to_inf_left
    have haR : a ∈ R := by
      rw [← hW]
      exact ⟨haS, haA, Subgroup.mem_centralizer_singleton_iff.mpr hat⟩
    exact U.mul_mem (hTU hτ) (hRU haR)
  have hSAsyl : IsSylowOf 2 (S ⊓ A) A :=
    hS.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hT₀A)
  have hUlt : U < S := by
    refine lt_of_le_of_ne hUS fun hUeq => ?_
    have hSAR : S ⊓ A = R := by
      apply le_antisymm
      · rintro x ⟨hxS, hxA⟩
        exact hUA x (hUeq ▸ hxS) hxA
      · exact le_inf (hRU.trans hUS) hRA
    rw [hSAR] at hSAsyl
    obtain ⟨T', hT'⟩ := hSAsyl
    have h1 := AschbacherKnownGroup.Lemma38.pRank_sylow_map T'
    rw [hT'] at h1
    omega
  obtain ⟨g, hgS, hgN, hgU⟩ := exists_mem_normalizer_of_lt hS2 hUlt
  have hgr : g * r * g⁻¹ = r := by
    have h1 : g * r * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgN r).mp (hRU hrR)
    have h2 : g * r * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hSA g hgS) r).mp hrA
    have h3 : orderOf (g * r * g⁻¹) = 2 := by
      rw [← hr2]; exact MulEquiv.orderOf_eq (MulAut.conj g) r
    exact eq_of_pRank_le_one hR2 hRr (hUA _ h1 h2) hrR h3 hr2
  have hgt : g * t * g⁻¹ = r * t := by
    have h1 : g * t * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgN t).mp (hTU htT₀)
    have h3 : orderOf (g * t * g⁻¹) = 2 := by
      rw [← ht2]; exact MulEquiv.orderOf_eq (MulAut.conj g) t
    rcases hUinv _ h1 h3 with h | h | h
    · exfalso
      apply htA
      have h4 : t = g⁻¹ * r * g := by rw [← h]; group
      rw [h4]
      have h5 : g⁻¹ * r * g = r := by
        calc g⁻¹ * r * g = g⁻¹ * (g * r * g⁻¹) * g := by rw [hgr]
          _ = r := by group
      rw [h5]
      exact hrA
    · exfalso
      apply hgU
      apply hCSt g hgS
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h]
    · exact h
  have hrr : r * r = 1 := by rw [← sq, ← hr2]; exact pow_orderOf_eq_one r
  let W : Subgroup G :=
    { carrier := {x | x * r * x⁻¹ = r ∧ (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = r * t)}
      mul_mem' := by
        rintro x y ⟨hxr, hxt⟩ ⟨hyr, hyt⟩
        refine ⟨?_, ?_⟩
        · calc x * y * r * (x * y)⁻¹ = x * (y * r * y⁻¹) * x⁻¹ := by group
            _ = r := by rw [hyr, hxr]
        · have hx : x * (r * t) * x⁻¹ = r * (x * t * x⁻¹) := by
            calc x * (r * t) * x⁻¹ = (x * r * x⁻¹) * (x * t * x⁻¹) := by group
              _ = r * (x * t * x⁻¹) := by rw [hxr]
          have hxy : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
          rcases hyt with h | h
          · rw [hxy, h]
            exact hxt
          · rw [hxy, h, hx]
            rcases hxt with h' | h'
            · exact Or.inr (by rw [h'])
            · left
              rw [h', ← mul_assoc, hrr, one_mul]
      one_mem' := ⟨by group, Or.inl (by group)⟩
      inv_mem' := by
        rintro x ⟨hxr, hxt⟩
        have hxr' : x⁻¹ * r * x = r := by
          calc x⁻¹ * r * x = x⁻¹ * (x * r * x⁻¹) * x := by rw [hxr]
            _ = r := by group
        refine ⟨by rw [inv_inv]; exact hxr', ?_⟩
        rw [inv_inv]
        rcases hxt with h | h
        · left
          calc x⁻¹ * t * x = x⁻¹ * (x * t * x⁻¹) * x := by rw [h]
            _ = t := by group
        · right
          have h1 : t = (x⁻¹ * r * x) * (x⁻¹ * t * x) := by
            calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
              _ = x⁻¹ * (r * t) * x := by rw [h]
              _ = (x⁻¹ * r * x) * (x⁻¹ * t * x) := by group
          rw [hxr'] at h1
          calc x⁻¹ * t * x = r * (r * (x⁻¹ * t * x)) := by rw [← mul_assoc, hrr, one_mul]
            _ = r * t := by rw [← h1] }
  have hmemW : ∀ x, x ∈ W ↔ x * r * x⁻¹ = r ∧ (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = r * t) :=
    fun x => Iff.rfl
  have hUW : U ≤ W := by
    intro u hu
    rw [hmemW]
    refine ⟨?_, Or.inl ?_⟩
    · rw [hUcomm u hu r (hRU hrR), mul_inv_cancel_right]
    · rw [hUcomm u hu t (hTU htT₀), mul_inv_cancel_right]
  have hgW : g ∈ W := ⟨hgr, Or.inr hgt⟩
  set X := U ⊔ Subgroup.zpowers g with hXdef
  have hXW : X ≤ W := sup_le hUW (Subgroup.zpowers_le.mpr hgW)
  have hXS : X ≤ S := sup_le hUS (Subgroup.zpowers_le.mpr hgS)
  have hgt' : g⁻¹ * (r * t) * g = t := by
    calc g⁻¹ * (r * t) * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [hgt]
      _ = t := by group
  have hSW : ∀ x ∈ S, x ∈ W → x ∈ U ∨ g⁻¹ * x ∈ U := by
    intro x hxS hxW
    rcases hxW.2 with h | h
    · left
      apply hCSt x hxS
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [h]
    · right
      apply hCSt _ (S.mul_mem (S.inv_mem hgS) hxS)
      have h1 : g⁻¹ * x * t * (g⁻¹ * x)⁻¹ = t := by
        calc g⁻¹ * x * t * (g⁻¹ * x)⁻¹ = g⁻¹ * (x * t * x⁻¹) * g := by group
          _ = t := by rw [h, hgt']
      calc g⁻¹ * x * t = (g⁻¹ * x * t * (g⁻¹ * x)⁻¹) * (g⁻¹ * x) := by group
        _ = t * (g⁻¹ * x) := by rw [h1]
  have hXdec : ∀ x ∈ X, x ∈ U ∨ g⁻¹ * x ∈ U := fun x hx => hSW x (hXS hx) (hXW hx)
  have hg2 : g * g ∈ U := by
    apply hCSt _ (S.mul_mem hgS hgS)
    have h1 : g * g * t * (g * g)⁻¹ = t := by
      calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
        _ = g * (r * t) * g⁻¹ := by rw [hgt]
        _ = (g * r * g⁻¹) * (g * t * g⁻¹) := by group
        _ = r * (r * t) := by rw [hgr, hgt]
        _ = t := by rw [← mul_assoc, hrr, one_mul]
    calc g * g * t = (g * g * t * (g * g)⁻¹) * (g * g) := by group
      _ = t * (g * g) := by rw [h1]
  have hXsq : ∀ x ∈ X, x * x ∈ U := by
    intro x hx
    rcases hXdec x hx with h | h
    · exact U.mul_mem h h
    · have h1 : x * x = (g * (g⁻¹ * x) * g⁻¹) * (g * g) * (g⁻¹ * x) := by group
      rw [h1]
      exact U.mul_mem (U.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp h) hg2) h
  have hNX : ∀ n ∈ S, n ∈ Subgroup.normalizer (X : Set G) → n ∈ X := by
    intro n hnS hnN
    have hconjX : ∀ x ∈ X, n * x * n⁻¹ ∈ X := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
    have hnr : n * r * n⁻¹ = r := by
      have h1 : n * r * n⁻¹ = (n * ρ₁ * n⁻¹) * (n * ρ₁ * n⁻¹) := by
        rw [← hρ₁sq, sq]; group
      have h2 : n * r * n⁻¹ ∈ U := by
        rw [h1]
        exact hXsq _ (hconjX ρ₁ (le_sup_left (a := U) (hRU hρ₁)))
      have h3 : n * r * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hSA n hnS) r).mp hrA
      have h4 : orderOf (n * r * n⁻¹) = 2 := by
        rw [← hr2]; exact MulEquiv.orderOf_eq (MulAut.conj n) r
      exact eq_of_pRank_le_one hR2 hRr (hUA _ h2 h3) hrR h4 hr2
    have hnt : n * t * n⁻¹ = t ∨ n * t * n⁻¹ = r * t := by
      have h1 : n * t * n⁻¹ = (n * f * n⁻¹) * (n * f * n⁻¹) := by
        rw [← hfsq, sq]; group
      have h2 : n * t * n⁻¹ ∈ U := by
        rw [h1]
        exact hXsq _ (hconjX f (le_sup_left (a := U) (hTU hf)))
      have h4 : orderOf (n * t * n⁻¹) = 2 := by
        rw [← ht2]; exact MulEquiv.orderOf_eq (MulAut.conj n) t
      rcases hUinv _ h2 h4 with h | h | h
      · exfalso
        apply htA
        have h5 : t = n⁻¹ * (n * t * n⁻¹) * n := by group
        rw [h5, h]
        have h6 : n⁻¹ * r * n = r := by
          calc n⁻¹ * r * n = n⁻¹ * (n * r * n⁻¹) * n := by rw [hnr]
            _ = r := by group
        rw [h6]
        exact hrA
      · exact Or.inl h
      · exact Or.inr h
    rcases hSW n hnS ⟨hnr, hnt⟩ with h | h
    · exact le_sup_left (a := U) h
    · have h1 : n = g * (g⁻¹ * n) := by group
      rw [h1]
      exact X.mul_mem (le_sup_right (b := Subgroup.zpowers g) (Subgroup.mem_zpowers g))
        (le_sup_left (a := U) h)
  have hXeq : X = S := by
    by_contra hne
    obtain ⟨n, hnS, hnN, hnX⟩ := exists_mem_normalizer_of_lt hS2 (lt_of_le_of_ne hXS hne)
    exact hnX (hNX n hnS hnN)
  have hgX : g ∈ X := le_sup_right (b := Subgroup.zpowers g) (Subgroup.mem_zpowers g)
  have hUX : U ≤ X := le_sup_left
  have hcardX : Nat.card X = 2 * Nat.card U := by
    have hle : Nat.card X ≤ 2 * Nat.card U := by
      classical
      let φ : X → U ⊕ U := fun x =>
        if h : (x : G) ∈ U then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨g⁻¹ * x, (hXdec x x.2).resolve_left h⟩
      have hφ : Function.Injective φ := by
        intro x y hxy
        by_cases hx : (x : G) ∈ U <;> by_cases hy : (y : G) ∈ U <;> simp [φ, hx, hy] at hxy
        · exact hxy
        · exact hxy
      have h1 := Nat.card_le_card_of_injective φ hφ
      rwa [Nat.card_sum, ← two_mul] at h1
    have hdvd : Nat.card U ∣ Nat.card X := Subgroup.card_dvd_of_le hUX
    have hlt : Nat.card U < Nat.card X :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hUX fun h => hgU (h ▸ hgX))
    obtain ⟨k, hk⟩ := hdvd
    have hU0 : 0 < Nat.card U := Nat.card_pos
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · omega
      · rcases Nat.lt_or_ge 2 k with h' | h'
        · have : Nat.card U * 3 ≤ Nat.card U * k := Nat.mul_le_mul_left _ h'
          omega
        · omega
    rw [hk, hk2, mul_comm]
  have hcardU : Nat.card U = Nat.card R * Nat.card T₀ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R T₀ hT₀NR
      (disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        (hTA1 x hx.2 (hRA hx.1))))
  have hSsup : (S ⊓ A) ⊔ T₀ = S := by
    apply le_antisymm (sup_le inf_le_left (hTU.trans hUS))
    intro s hs
    obtain ⟨τ, hτ, a, haA, rfl⟩ := hframeAT.mem_sup_iff.mp (hS.le hs)
    have haS : a ∈ S := by
      have h1 := S.mul_mem (S.inv_mem (hUS (hTU hτ))) hs
      rwa [inv_mul_cancel_left] at h1
    rw [show τ * a = (τ * a * τ⁻¹) * τ by group]
    refine Subgroup.mul_mem _ (le_sup_left (b := T₀) ⟨?_, ?_⟩) (le_sup_right (a := S ⊓ A) hτ)
    · exact S.mul_mem (S.mul_mem (hUS (hTU hτ)) haS) (S.inv_mem (hUS (hTU hτ)))
    · exact (Subgroup.mem_normalizer_iff.mp (hT₀A hτ) a).mp haA
  have hcardS : Nat.card S = Nat.card (S ⊓ A : Subgroup G) * Nat.card T₀ := by
    have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (S ⊓ A) T₀
      (fun τ hτ => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (hUS (hTU hτ)), hT₀A hτ⟩)
      (disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        (hTA1 x hx.2 hx.1.2)))
    rwa [hSsup] at h1
  have hcardSA : Nat.card (S ⊓ A : Subgroup G) = 2 * Nat.card R := by
    have hT0 : 0 < Nat.card T₀ := Nat.card_pos
    have h2 : Nat.card S = 2 * Nat.card U := by
      rw [← hXeq]
      exact hcardX
    have h1 : Nat.card (S ⊓ A : Subgroup G) * Nat.card T₀ = 2 * Nat.card R * Nat.card T₀ := by
      rw [← hcardS, h2, hcardU]; ring
    exact Nat.eq_of_mul_eq_mul_right hT0 h1
  refine ⟨S ⊓ A, hSAsyl, le_inf (hRU.trans hUS) hRA, ?_⟩
  have hRSA : R ≤ S ⊓ A := le_inf (hRU.trans hUS) hRA
  have h1 := Subgroup.relIndex_mul_card R (S ⊓ A)
  rw [inf_eq_left.mpr hRSA, hcardSA] at h1
  have hR0 : 0 < Nat.card R := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hR0 (by rw [h1])

variable {D : Subgroup G} {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_mul_core_of_mem_factor (hC : Counterexample G D 2 Abar) (i : Fin 2) {a : G}
    (ha : a ∈ aschbacherThm5Preimage D (Abar i)) :
    ∃ c ∈ ⁅aschbacherThm5Preimage D (Abar i), aschbacherThm5Preimage D (Abar i)⁆,
      ∃ o ∈ aschbacherThm5Core D, a = c * o := by
  set π := QuotientGroup.mk' (aschbacherThm5OddCore D) with hπ
  set A' := (Abar i).comap π with hA'
  have hperf : Group.IsPerfect (Abar i) := semisimple_perfect _ (hC.hyp.hsemisimple i)
  have hcomm : ⁅Abar i, Abar i⁆ = Abar i := by
    have h1 := congrArg (Subgroup.map (Abar i).subtype) hperf.commutator_eq_top
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
  have hA'map : A'.map π = Abar i :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  obtain ⟨d, hdA', rfl⟩ := ha
  have hπd : π d ∈ ⁅A', A'⁆.map π := by
    rw [Subgroup.map_commutator, hA'map, hcomm]
    exact hdA'
  obtain ⟨c', hc', hc'd⟩ := hπd
  refine ⟨c', ?_, (c'⁻¹ * d : D), ?_, by simp⟩
  · have h1 : ⁅A', A'⁆.map D.subtype = ⁅A'.map D.subtype, A'.map D.subtype⁆ :=
      Subgroup.map_commutator _ _ _
    change (c' : G) ∈ ⁅A'.map D.subtype, A'.map D.subtype⁆
    rw [← h1]
    exact ⟨c', hc', rfl⟩
  · have hker : c'⁻¹ * d ∈ aschbacherThm5OddCore D := by
      rw [← QuotientGroup.ker_mk' (aschbacherThm5OddCore D), MonoidHom.mem_ker, map_mul,
        map_inv, ← hπ, hc'd, inv_mul_cancel]
    exact ⟨_, hker, rfl⟩

theorem false_of_sylow_index_two (hC : Counterexample G D 2 Abar) {i i' : Fin 2} (hii' : i ≠ i')
    {P R : Subgroup G} {r : G} (hP : IsSylowOf 2 P (aschbacherThm5Preimage D (Abar i)))
    (hRP : R ≤ P) (hidx : R.relIndex P = 2) (hRinv : ∀ s ∈ R, orderOf s = 2 → s = r)
    (hrA' : r ∈ aschbacherThm5Preimage D (Abar i'))
    (hA2 : 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  have hP2 := hP.isPGroup
  have hrankP : 2 ≤ CFSG.Open.pRank 2 P := by
    obtain ⟨T', hT'⟩ := hP
    have h1 := AschbacherKnownGroup.Lemma38.pRank_sylow_map T'
    rw [hT'] at h1
    omega
  obtain ⟨u, huP, hu2, huR⟩ : ∃ u ∈ P, orderOf u = 2 ∧ u ∉ R := by
    obtain ⟨s, hsP, s', hs'P, hs, hs', hss'⟩ := exists_two_involutions hrankP
    by_cases hsR : s ∈ R
    · refine ⟨s', hs'P, hs', fun hs'R => hss' ?_⟩
      rw [hRinv s hsR hs, hRinv s' hs'R hs']
    · exact ⟨s, hsP, hs, hsR⟩
  have hQu : ∀ x ∈ A, x⁻¹ * u * x ∉ R := by
    intro x hx hmem
    have h2 : orderOf (x⁻¹ * u * x) = 2 := by
      rw [← hu2]
      have h3 := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) u
      simpa [MulAut.conj_apply] using h3
    have h3 : x⁻¹ * u * x = r := hRinv _ hmem h2
    have hrR : r ∈ R := h3 ▸ hmem
    have hux : u = x * r * x⁻¹ := by rw [← h3]; group
    have hcore := cross_factor_centralizes D Abar hC.hyp.hcomm i i' hii' r hrA' x⁻¹ (A.inv_mem hx)
    have h4 : r⁻¹ * u ∈ aschbacherThm5Core D := by
      rw [hux]
      convert hcore using 1
      group
    have h5 : r⁻¹ * u ∈ P := P.mul_mem (P.inv_mem (hRP hrR)) huP
    have h6 := eq_one_of_mem_core_of_isPGroup hP2 h5 h4
    apply huR
    have h7 : u = r := by
      calc u = r * (r⁻¹ * u) := by group
        _ = r := by rw [h6, mul_one]
    rw [h7]
    exact hrR
  obtain ⟨-, -, hPidx⟩ := isSylowOf_iff.mp hP
  obtain ⟨N, hNA, hNn, hsq, huN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
    hP.le hP2 hPidx hRP hidx (hP.le huP) hu2 hQu
  apply huN
  have hconj : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn => by
    have h1 := hNn.conj_mem ⟨n, hNA hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨a, ha⟩
    exact Subgroup.mem_subgroupOf.mp h1
  have hcomm : ⁅A, A⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * a⁻¹ ^ 2 * b) * b⁻¹ ^ 2 := by
      rw [commutatorElement_def, sq, sq, sq]
      group
    rw [h1]
    refine N.mul_mem (N.mul_mem (hsq _ (A.mul_mem ha hb)) ?_) (hsq _ (A.inv_mem hb))
    have h2 := hconj b⁻¹ (A.inv_mem hb) _ (hsq _ (A.inv_mem ha))
    simpa using h2
  have hcore : aschbacherThm5Core D ≤ N := by
    intro o ho
    have hoA : o ∈ A := core_le_preimage D (Abar i) ho
    obtain ⟨k, hk⟩ : Odd (orderOf o) :=
      (core_odd D).of_dvd_nat (Subgroup.orderOf_dvd_natCard (aschbacherThm5Core D) ho)
    have h1 : o = (o ^ (k + 1)) ^ 2 := by
      rw [← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    rw [h1]
    exact hsq _ (A.pow_mem hoA _)
  obtain ⟨c, hc, o, ho, hu⟩ := exists_mul_core_of_mem_factor hC i (hP.le huP)
  rw [hu]
  exact N.mul_mem (hcomm hc) (hcore ho)

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
