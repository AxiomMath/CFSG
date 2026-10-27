module

public import CFSG.GH74.E2.CaseIInner
public import CFSG.GH74.E2.Final
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.Cl2Glue
public import CFSG.GH74.E2.Q8Main
public import CFSG.GH74.E2.TermLeaves

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.Generic CFSG.GH74.GLS

structure LocalData {G : Type} [Group G] (t : G) (K : Subgroup G) (c : G) : Prop where
  order_t : orderOf t = 2
  comp : IsCompCen t K
  quat : Nonempty (↥(Qt t) ≃* QuaternionGroup 2)
  mem_cen : c ∈ Cen t
  order_c : orderOf c = 3
  centralizes : ∀ k ∈ K, c * k = k * c

structure M11Tables : Prop where
  tables : ∀ (K : Type) [Group K] [Finite K], ShapeM11 K → SD16Tables K
  aut_inner : ∀ (K : Type) [Group K] [Finite K], ShapeM11 K → ∀ φ : MulAut K,
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹

structure L33Tables : Prop where
  tables : ∀ (K : Type) [Group K] [Finite K], ShapeL33 K → SD16Tables K

@[expose] def NoLocalA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G) (c : G),
    LocalData t K c → ShapeA6 ↥K → False

@[expose] def NoLocalL33Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G) (c : G),
    LocalData t K c → ShapeL33 ↥K →
    (¬ ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) → False

@[expose] def NoLocalGL23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G) (c : G),
    LocalData t K c → (ShapeL33 ↥K ∨ ShapeM11 ↥K) →
    (∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) →
    (∃ P : Sylow 2 ↥(Cen t ⊓ Subgroup.centralizer (K : Set G)),
      Nonempty (↥(P : Subgroup ↥(Cen t ⊓ Subgroup.centralizer (K : Set G))) ≃*
        CFSG.Open.SemidihedralGroup 4)) → False

section Inner

theorem noLocal_inner_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables)
    (hL : L33Tables) (hGL : NoLocalGL23) {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    {K : Subgroup G} {c : G} (hd : LocalData t K c) (hsh : ShapeL33 ↥K ∨ ShapeM11 ↥K)
    (hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) : False := by
  obtain ⟨-, huniq⟩ := hComp G hH t hd.order_t K hd.comp
  have hcen : Subgroup.center ↥K = ⊥ := hD3.center_bot ↥K (by
    rcases hsh with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hT : SD16Tables ↥K := by
    rcases hsh with h | h
    · exact hL.tables ↥K h
    · exact hM.tables ↥K h
  by_cases hSD : ∃ P : Sylow 2 ↥(Cen t ⊓ Subgroup.centralizer (K : Set G)),
      Nonempty (↥(P : Subgroup ↥(Cen t ⊓ Subgroup.centralizer (K : Set G))) ≃*
        CFSG.Open.SemidihedralGroup 4)
  · exact hGL G hH t K c hd hsh hinner hSD
  · exact inner_two_core hH hd.order_t hd.comp huniq hcen hT hinner hd.quat hd.order_c hd.mem_cen
      hd.centralizes (fun P hP => hSD ⟨P, hP⟩)

theorem noLocalM11_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables) (hL : L33Tables)
    (hGL : NoLocalGL23) {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G} {K : Subgroup G}
    {c : G} (hd : LocalData t K c) (hsh : ShapeM11 ↥K) : False := by
  obtain ⟨-, huniq⟩ := hComp G hH t hd.order_t K hd.comp
  exact noLocal_inner_of hComp hD3 hM hL hGL hH hd (Or.inr hsh)
    (inner_of_aut_inner hd.comp huniq (hM.aut_inner ↥K hsh))

theorem noLocalL33_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables) (hL : L33Tables)
    (hGL : NoLocalGL23) (hOut : NoLocalL33Outer) {G : Type} [Group G] [Finite G] (hH : Hyp G)
    {t : G} {K : Subgroup G} {c : G} (hd : LocalData t K c) (hsh : ShapeL33 ↥K) : False := by
  by_cases hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹
  · exact noLocal_inner_of hComp hD3 hM hL hGL hH hd (Or.inl hsh) hinner
  · exact hOut G hH t K c hd hsh hinner

end Inner

section BetaC

theorem exists_c_of_beta (hComp : ComponentList) (hD3 : K0Data3) {G : Type} [Group G] [Finite G]
    (hH : Hyp G) {t t' a : G} {A B K : Subgroup G} (hc : CaseII t t' a A B)
    (hK : IsCompCen t K) (hsh : ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K)
    (hcard : Nat.card ↥(B ⊓ centralizer ((Qt t : Subgroup G) : Set G)) = 3) :
    ∃ c : G, c ∈ Cen t ∧ orderOf c = 3 ∧ ∀ k ∈ K, c * k = k * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht := hc.order_t
  obtain ⟨-, huniq⟩ := hComp G hH t ht K hK
  have hcen : Subgroup.center ↥K = ⊥ := hD3.center_bot ↥K (by
    rcases hsh with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hex : ∃ b ∈ B, ∃ q ∈ Qt t, b * q ≠ q * b := by
    by_contra hcon
    have hall : ∀ b ∈ B, ∀ q ∈ Qt t, b * q = q * b := fun b hb q hq => by
      by_contra h
      exact hcon ⟨b, hb, q, hq, h⟩
    have hle : B ≤ B ⊓ centralizer ((Qt t : Subgroup G) : Set G) := fun b hb =>
      ⟨hb, Subgroup.mem_centralizer_iff.2 fun q hq => (hall b hb q hq).symm⟩
    have h9 := Subgroup.card_le_of_le hle
    rw [hc.card_B, hcard] at h9
    omega
  obtain ⟨b, hbB, q, hq, hbq⟩ := hex
  have hbC : b ∈ Cen t := mem_Cen'.2 (hc.centralizes_t b hbB)
  have hb3 : b ^ 3 = 1 := hc.elemAb.2 b (hc.B_le hbB)
  have hconj : conjugate K b = K := conjugate_eq_of_unique hK huniq hbC
  have hnorm : b ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := AS16.mem_conjugate_iff' K b x
    rw [hconj] at h
    exact h
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥K, φ = K.normalizerMonoidHom ⟨b, hnorm⟩ := ⟨_, rfl⟩
  have hφapp : ∀ x : ↥K, ((φ x : ↥K) : G) = b * x * b⁻¹ := fun x => by
    rw [hφ]
    rfl
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨b, hnorm⟩ : normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    calc φ ^ 3 = K.normalizerMonoidHom ((⟨b, hnorm⟩ : normalizer (K : Set G)) ^ 3) := by
          rw [hφ, map_pow]
      _ = 1 := by rw [h1, map_one]
  obtain ⟨k, hk⟩ := hD3.inner3 ↥K hsh φ hφ3
  have hk' : ∀ x ∈ K, b * x * b⁻¹ = (k : G) * x * (k : G)⁻¹ := fun x hx => by
    have := congrArg (fun y : ↥K => (y : G)) (hk ⟨x, hx⟩)
    simpa [hφapp] using this
  have hkb : (k : G) * b = b * (k : G) := by
    have h := hk' k k.2
    calc (k : G) * b = (k * k * (k : G)⁻¹) * b := by group
      _ = (b * k * b⁻¹) * b := by rw [h]
      _ = b * k := by group
  have hdK : ∀ x ∈ K, (k : G)⁻¹ * b * x = x * ((k : G)⁻¹ * b) := by
    intro x hx
    have h1 := hk' x hx
    calc (k : G)⁻¹ * b * x = (k : G)⁻¹ * (b * x * b⁻¹) * b := by group
      _ = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * b := by rw [h1]
      _ = x * ((k : G)⁻¹ * b) := by group
  have hkinv : (k : G)⁻¹ ∈ K := Subgroup.inv_mem _ k.2
  have hd3 : ((k : G)⁻¹ * b) ^ 3 = 1 := by
    have hcom : Commute ((k : G)⁻¹) b := (Commute.inv_left (show Commute (k : G) b from hkb))
    have hpow : ((k : G)⁻¹ * b) ^ 3 = ((k : G)⁻¹) ^ 3 := by
      rw [hcom.mul_pow, hb3, mul_one]
    have hmem : ((k : G)⁻¹) ^ 3 ∈ K := Subgroup.pow_mem _ hkinv 3
    have hz : (⟨((k : G)⁻¹) ^ 3, hmem⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := (Commute.pow_left (show Commute ((k : G)⁻¹ * b) (y : G) from hdK y y.2) 3).eq
      rw [hpow] at this
      exact this.symm
    rw [hcen, Subgroup.mem_bot] at hz
    rw [hpow]
    exact congrArg Subtype.val hz
  have hd1 : (k : G)⁻¹ * b ≠ 1 := by
    intro h1
    have hbk : (k : G) = b := inv_mul_eq_one.1 h1
    have hbK : b ∈ K := hbk ▸ k.2
    exact hbq (Qt_commute_comp hH ht hK huniq q hq b hbK).symm
  refine ⟨(k : G)⁻¹ * b, Subgroup.mul_mem _ (Subgroup.inv_mem _ (hK.1 k.2)) hbC,
    orderOf_eq_prime hd3 hd1, fun x hx => (hdK x hx)⟩

end BetaC

section Wrappers

theorem noCaseIA6_of (h : NoLocalA6) : NoCaseIA6 := by
  intro G _ _ hH t K hK hsh hQ A hA B c hBA hBK hB hcA hc3 hcK hdec
  exact h G hH t K c ⟨hA.1, hK, hQ, hA.2.1 hcA, hc3, hcK⟩ hsh

theorem noCaseIL33_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables) (hL : L33Tables)
    (hGL : NoLocalGL23) (hOut : NoLocalL33Outer) : NoCaseIL33 := by
  intro G _ _ hH t K hK hsh hQ A hA B c hBA hBK hB hcA hc3 hcK hdec
  exact noLocalL33_of hComp hD3 hM hL hGL hOut hH ⟨hA.1, hK, hQ, hA.2.1 hcA, hc3, hcK⟩ hsh

theorem noCaseIM11_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables) (hL : L33Tables)
    (hGL : NoLocalGL23) : NoCaseIM11 := by
  intro G _ _ hH t K hK hsh hQ A hA B c hBA hBK hB hcA hc3 hcK hdec
  exact noLocalM11_of hComp hD3 hM hL hGL hH ⟨hA.1, hK, hQ, hA.2.1 hcA, hc3, hcK⟩ hsh

theorem noCaseIIBetaA6_of (hComp : ComponentList) (hD3 : K0Data3) (h : NoLocalA6) :
    NoCaseIIBetaA6 := by
  intro G _ _ hH t t' a A B K hc hK hsh hQ hcard
  obtain ⟨c, hcC, hc3, hcK⟩ := exists_c_of_beta hComp hD3 hH hc hK (Or.inl hsh) hcard
  exact h G hH t K c ⟨hc.order_t, hK, hQ, hcC, hc3, hcK⟩ hsh

theorem noCaseIIBetaL33_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables)
    (hL : L33Tables) (hGL : NoLocalGL23) (hOut : NoLocalL33Outer) : NoCaseIIBetaL33 := by
  intro G _ _ hH t t' a A B K hc hK hsh hQ hcard
  obtain ⟨c, hcC, hc3, hcK⟩ := exists_c_of_beta hComp hD3 hH hc hK (Or.inr (Or.inl hsh)) hcard
  exact noLocalL33_of hComp hD3 hM hL hGL hOut hH ⟨hc.order_t, hK, hQ, hcC, hc3, hcK⟩ hsh

theorem noCaseIIBetaM11_of
    (hComp : ComponentList) (hD3 : K0Data3) (hM : M11Tables)
    (hL : L33Tables) (hGL : NoLocalGL23) : NoCaseIIBetaM11 := by
  intro G _ _ hH t t' a A B K hc hK hsh hQ hcard
  obtain ⟨c, hcC, hc3, hcK⟩ := exists_c_of_beta hComp hD3 hH hc hK (Or.inr (Or.inr hsh)) hcard
  exact noLocalM11_of hComp hD3 hM hL hGL hH ⟨hc.order_t, hK, hQ, hcC, hc3, hcK⟩ hsh

end Wrappers

theorem s_restrictedEvenThin_of_localLeaves
    (hGKF : GenericKnownFacts) (hF : E2ComponentFacts)
    (hD : K0Data) (hD3 : K0Data3) (hP : PumpUpData) (hM : M11Tables) (hL : L33Tables)
    (hA6 : NoLocalA6) (hOut : NoLocalL33Outer) (hGL : NoLocalGL23)
    (hαL33 : NoCaseIIAlphaL33) (hαM11 : NoCaseIIAlphaM11) (hβA5 : NoCaseIIBetaA5) :
    S_restrictedEvenThin :=
  have hComp : ComponentList := evenType_components hGKF hF hD
  s_restrictedEvenThin_of_local cl2Statement_of_wrap hComp hD hD3 q8Lemma
    (noCaseIQ8_of_shapes (noCaseIA6_of hA6) (noCaseIL33_of hComp hD3 hM hL hGL hOut)
      (noCaseIM11_of hComp hD3 hM hL hGL))
    (noCaseIIAlpha_of_shapes (noCaseIIAlphaA6_of hComp hP) hαL33 hαM11)
    (noCaseIIBeta_of_shapes hβA5 (noCaseIIBetaL27_of hComp hP) (noCaseIIBetaA6_of hComp hD3 hA6)
      (noCaseIIBetaL217_of hComp hP) (noCaseIIBetaL33_of hComp hD3 hM hL hGL hOut)
      (noCaseIIBetaM11_of hComp hD3 hM hL hGL))

end CFSG.GH74.E2
