module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveE8
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.Sporadic.HN.Local.Main

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance Subgroup

section Data

variable {G : Type} [Group G]

theorem invertedByTwoA_data' (hE : MonsterExistenceStatement G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : orderOf s = p) (hinv : InvertedByTwoA s) :
    Finite G ∧ ∃ α : G, orderOf α = 2 ∧
      Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder ∧
      α * s * α⁻¹ = s⁻¹ ∧ ∃ i : Fin 9, suborbitClassOrder i = p ∧
        TwoPointShape
          (Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) i := by
  obtain ⟨hfin, a, hcls, -, hshape⟩ := twoA_data_of_existence hE
  obtain ⟨α, hα2, hαc, hαs⟩ := hinv
  have hαA : IsConj a α := hcls α hα2 hαc
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsodd : Odd (orderOf s⁻¹) := by rw [orderOf_inv, hs]; exact hpodd
  have hinv' : α * s⁻¹ * α⁻¹ = (s⁻¹)⁻¹ := by
    have := conj_inv (a := s) (b := α)
    rw [hαs, inv_inv] at this
    rw [inv_inv]
    exact this.symm
  have hβ : IsConj a (s⁻¹ * α) := hαA.trans (isConj_mul_of_inverts_odd hinv' hsodd)
  have hαβ : α * (s⁻¹ * α) = s := by
    calc α * (s⁻¹ * α) = α * s⁻¹ * α⁻¹ := by rw [hαi]; group
      _ = s := by rw [hinv', inv_inv]
  refine ⟨hfin, α, hα2, hαc, hαs, ?_⟩
  obtain ⟨i, hi, hsh⟩ := hshape α (s⁻¹ * α) hαA hβ
  rw [hαβ, hs] at hi
  refine ⟨i, hi, ?_⟩
  have := centralizer_inf_centralizer_mul_eq α (s⁻¹ * α)
  rw [hαβ] at this
  rw [← this]
  exact hsh

structure HNInvolutions (H : Subgroup G) : Prop where
  card : Nat.card ↥H = 273030912000000
  cases : ∀ t ∈ H, orderOf t = 2 →
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 177408000 ∨
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 3686400
  conj : ∀ t ∈ H, ∀ u ∈ H, orderOf t = 2 → orderOf u = 2 →
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) → ∃ g ∈ H, g * u * g⁻¹ = t
  exists_A : ∃ t ∈ H, orderOf t = 2 ∧
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 177408000
  exists_B : ∃ t ∈ H, orderOf t = 2 ∧
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 3686400
  exists_E8 : ∃ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
    8 ≤ Nat.card ↥A ∧ A ≤ H

structure HNClassData (K : Type) [Group K] : Prop where
  card : Nat.card K = 273030912000000
  stab : ∃ S : Subgroup K, Nonempty (↥S ≃* alternatingGroup (Fin 12))
  cls : ∃ t₂ t₄ : K, t₂ ^ 2 = 1 ∧ t₂ ≠ 1 ∧ t₄ ^ 2 = 1 ∧ t₄ ≠ 1 ∧
    (∀ g : K, g ^ 2 = 1 → g ≠ 1 → IsConj t₂ g ∨ IsConj t₄ g) ∧
    Nat.card ↥(Subgroup.centralizer ({t₂} : Set K)) = 177408000 ∧
    Nat.card ↥(Subgroup.centralizer ({t₄} : Set K)) = 3686400

theorem hnClassData :
    HNClassData NativeSporadic.HN := by
  obtain ⟨θ, t₂, t₄, h₂, h₄, -, -, sq₂, ne₂, sq₄, ne₄, hcov, -, hc₂, hc₄⟩ :=
    CFSG.Sporadic.HN.Local.hn_involution_classes
  exact ⟨CFSG.Sporadic.HN.card_HN, ⟨_, ⟨θ⟩⟩, t₂, t₄, sq₂, ne₂, sq₄, ne₄, hcov, hc₂, hc₄⟩

theorem HNInvolutions.of_classData {K : Type} [Group K] (hK : HNClassData K) {H : Subgroup G}
    (e : ↥H ≃* K) : HNInvolutions H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, ⟨S, ⟨θ⟩⟩, t₂, t₄, sq₂, ne₂, sq₄, ne₄, hcov, hc₂, hc₄⟩ := hK
  have hcent : ∀ s : ↥H, Nat.card ↥(H ⊓ Subgroup.centralizer ({(s : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({e s} : Set K)) := fun s =>
    (card_centralizer_subtype s).symm.trans (natCard_centralizer_mulEquiv e s).symm
  have hcls : ∀ u : K, orderOf u = 2 →
      (IsConj t₂ u ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set K)) = 177408000) ∨
      (IsConj t₄ u ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set K)) = 3686400) := by
    intro u hu
    have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu
      norm_num at hu
    rcases hcov u hu2 hu1 with h | h
    · left
      exact ⟨h, by rw [← TabMSeven.card_centralizer_eq_of_isConj h]; exact hc₂⟩
    · right
      exact ⟨h, by rw [← TabMSeven.card_centralizer_eq_of_isConj h]; exact hc₄⟩
  have hord : ∀ (t : G) (ht : t ∈ H), orderOf t = 2 → orderOf (e ⟨t, ht⟩) = 2 := by
    intro t ht ho
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact hcard
  · intro t ht ho
    have h1 := hcent ⟨t, ht⟩
    rcases hcls _ (hord t ht ho) with ⟨-, hc⟩ | ⟨-, hc⟩
    · left
      exact h1.trans hc
    · right
      exact h1.trans hc
  · intro t ht u hu hto huo hcard'
    have h1 := hcent ⟨t, ht⟩
    have h2 := hcent ⟨u, hu⟩
    have key : IsConj (e ⟨u, hu⟩) (e ⟨t, ht⟩) := by
      rcases hcls _ (hord t ht hto) with ⟨hct, hct'⟩ | ⟨hct, hct'⟩ <;>
        rcases hcls _ (hord u hu huo) with ⟨hcu, hcu'⟩ | ⟨hcu, hcu'⟩
      · exact hcu.symm.trans hct
      · exfalso
        rw [h1, h2, hct', hcu'] at hcard'
        norm_num at hcard'
      · exfalso
        rw [h1, h2, hct', hcu'] at hcard'
        norm_num at hcard'
      · exact hcu.symm.trans hct
    obtain ⟨c, hc⟩ := isConj_iff.1 ((CFSG.Sporadic.HN.Local.isConj_equiv_iff e _ _).1 key)
    refine ⟨(c : G), c.2, ?_⟩
    exact congrArg Subtype.val hc
  · have ho : orderOf (e.symm t₂) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime sq₂ ne₂
    refine ⟨((e.symm t₂ : ↥H) : G), (e.symm t₂).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact ho
    · rw [hcent (e.symm t₂), MulEquiv.apply_symm_apply]
      exact hc₂
  · have ho : orderOf (e.symm t₄) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime sq₄ ne₄
    refine ⟨((e.symm t₄ : ↥H) : G), (e.symm t₄).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact ho
    · rw [hcent (e.symm t₄), MulEquiv.apply_symm_apply]
      exact hc₄
  · let ψ : alternatingGroup (Fin 12) →* G :=
      H.subtype.comp (e.symm.toMonoidHom.comp (S.subtype.comp θ.symm.toMonoidHom))
    have hψ : Function.Injective ψ :=
      H.subtype_injective.comp (e.symm.injective.comp
        (S.subtype_injective.comp θ.symm.injective))
    obtain ⟨A, hAc, hAs, hA8, hAr⟩ := exists_e8_map ψ hψ
    refine ⟨A, hAc, hAs, hA8, hAr.trans ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (e.symm _).2

theorem HNInvolutions.of_equiv
    {H : Subgroup G}
    (e : ↥H ≃* NativeSporadic.HN) : HNInvolutions H :=
  HNInvolutions.of_classData hnClassData e

end Data

section Main

variable {G : Type} [Group G]

theorem centFiveA_of_bounds'
    (hE : MonsterExistenceStatement G)
    (h2A : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder →
      orderOf k = 5 → t * k = k * t → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G) →
      Nat.card ↥L = 887040000 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        887040000)
    (h2B : ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      orderOf k = 5 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        18432000)
    (hG5 : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = twoBCentralizerOrder) :
    ∀ k : G, orderOf k = 5 → InvertedByTwoA k →
      Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 5 * 273030912000000 := by
  intro k hk hinv
  obtain ⟨hfin, α, hα2, hαc, hαk, i, hi, hsh⟩ :=
    invertedByTwoA_data' hE Nat.prime_five (by norm_num) hk hinv
  haveI : Finite G := hfin
  have hHN : Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({k} : Set G)) ≃* NativeSporadic.HN) := by
    fin_cases i <;> first | exact hsh | (exfalso; simp [suborbitClassOrder] at hi)
  obtain ⟨e⟩ := hHN
  set H : Subgroup G := Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)
    with hH
  have hHI : HNInvolutions H := HNInvolutions.of_equiv e
  have hHα : H ≤ Subgroup.centralizer ({α} : Set G) := inf_le_left
  have hHk : H ≤ Subgroup.centralizer ({k} : Set G) := inf_le_right
  obtain ⟨-, a, z, -, -, -, hcls, -, hB, -⟩ := id hE
  have hαA : IsConj a α := by
    rcases hcls α hα2 with h | h
    · exact h
    · exfalso
      have h2 := (hB α h).2.2.2.2.1
      rw [hαc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  have hclsA : ∀ t : G, IsConj a t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * monsterBabyOrder := fun t ht => by
    rw [← hαc]
    exact (TabMSeven.card_centralizer_eq_of_isConj (hαA.symm.trans ht)).symm
  have hclsB : ∀ t : G, IsConj z t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder := fun t ht =>
    (hB t ht).2.2.2.2.1
  have hcomm : ∀ t ∈ H, t * k = k * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)
  have hlow : ∀ t ∈ H, 5 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) :=
    fun t ht => mul_card_le_cent_inf Nat.prime_five (by norm_num) hk hαk hHα hHk ht
  have hnotA : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder →
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 3686400 := by
    intro t ht ho hc
    rcases hHI.cases t ht ho with h | h
    · exfalso
      have h1 := hlow t ht
      have h2 := h2B t k ho hc hk (hcomm t ht)
      rw [h] at h1
      omega
    · exact h
  obtain ⟨A, hAc, hAs, hA8, hAH⟩ := hHI.exists_E8
  obtain ⟨u, huA, huo, huc⟩ := hG5 A hAc hAs hA8
  have huH : u ∈ H := hAH huA
  have hu3 : Nat.card ↥(H ⊓ Subgroup.centralizer ({u} : Set G)) = 3686400 :=
    hnotA u huH huo huc
  have hBcls : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) = 3686400 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder := by
    intro t ht ho hc
    obtain ⟨g, -, hgu⟩ := hHI.conj t ht u huH ho huo (hc.trans hu3.symm)
    rw [← hgu, TabMSeven.card_centralizer_conj]
    exact huc
  have hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        5 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) := by
    intro t ht ho
    rcases hHI.cases t ht ho with h | h
    · rw [h]
      have h1 := hlow t ht
      rw [h] at h1
      rcases hcls t ho with hta | htz
      ·
        have hH'k : H ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({k} : Set G) :=
          fun x hx => hHk hx.1
        have hkL : k ∈ prodSub k _ hH'k := ⟨1, 1, Subgroup.one_mem _, by simp⟩
        have hlo := mul_card_le_of_prod Nat.prime_five (by norm_num) hk hαk
          (H' := H ⊓ Subgroup.centralizer ({t} : Set G)) (fun x hx => hHα hx.1) hkL le_prodSub
        have hhi : Nat.card ↥(prodSub k _ hH'k) ≤
            5 * Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) := by
          let f : Fin 5 × ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) → ↥(prodSub k _ hH'k) :=
            fun x =>
            ⟨k ^ (x.1 : ℕ) * (x.2 : G), ⟨((x.1 : ℕ) : ℤ), x.2, x.2.2, by rw [zpow_natCast]⟩⟩
          have hf : Function.Surjective f := by
            rintro ⟨d, i, u, hu, rfl⟩
            have hnn : 0 ≤ i % 5 := Int.emod_nonneg _ (by norm_num)
            have hlt : (i % 5).toNat < 5 := by
              have := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 5)
              omega
            refine ⟨(⟨(i % 5).toNat, hlt⟩, ⟨u, hu⟩), Subtype.ext ?_⟩
            show k ^ (i % 5).toNat * u = k ^ i * u
            rw [← zpow_natCast, Int.toNat_of_nonneg hnn, show (5 : ℤ) = (orderOf k : ℤ) by
              rw [hk]; rfl, zpow_mod_orderOf]
          have := Nat.card_le_card_of_surjective f hf
          rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at this
        have hLle : prodSub k _ hH'k ≤
            Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G) :=
          prodSub_le ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm t ht).symm,
            Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ fun x hx => ⟨hx.2, hHk hx.1⟩
        rw [h] at hlo hhi
        exact (h2A t k ho (hclsA t hta) hk (hcomm t ht) _ hLle (le_antisymm hhi hlo)).trans
          (by norm_num)
      · exfalso
        have h2 := h2B t k ho (hclsB t htz) hk (hcomm t ht)
        omega
    · rw [h]
      exact (h2B t k ho (hBcls t ht ho h) hk (hcomm t ht)).trans (by norm_num)
  obtain ⟨t₀, ht₀, ho₀, hc₀⟩ := hHI.exists_A
  obtain ⟨t₁, ht₁, ho₁, hc₁⟩ := hHI.exists_B
  have hrec := card_centralizer_le_of_involutions Nat.prime_five (by norm_num) hk hαk hHα hHk hup
    hHI.conj ht₀ ht₁ ho₀ ho₁ (by rw [hc₀, hc₁]; norm_num)
  have h5 := hrec.2
  rw [hHI.card] at h5
  exact h5

end Main

end CFSG.HardMathSupport.Dickson.I271.TabMFive
