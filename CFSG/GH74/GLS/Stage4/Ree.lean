module

public import CFSG.GH74.GLS.Stage12.Interface
import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

theorem le_two_of_two_pow_dvd {q m : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (h : 2 ^ m ∣ q * (q ^ 2 - 1) / 2) : m ≤ 2 := by
  by_contra hm
  have hm' : 3 ≤ m := by omega
  have h8 : 8 ∣ q * (q ^ 2 - 1) / 2 := by
    have h3 : (2 : ℕ) ^ 3 ∣ 2 ^ m := pow_dvd_pow 2 hm'
    exact (show (8 : ℕ) = 2 ^ 3 by norm_num) ▸ h3.trans h
  have h16 : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
  have hsq : q ^ 2 % 16 = 9 := by
    rcases h16 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsub : (q ^ 2 - 1) % 16 = 8 := by omega
  have hN : (q * (q ^ 2 - 1)) % 16 = 8 := by
    rw [Nat.mul_mod, hsub]
    rcases h16 with h | h | h | h <;> simp [h]
  obtain ⟨c, hc⟩ := h8
  have hev : q * (q ^ 2 - 1) = 2 * (q * (q ^ 2 - 1) / 2) := by
    have : 2 ∣ q * (q ^ 2 - 1) := by omega
    exact (Nat.mul_div_cancel' this).symm
  omega

theorem card_statedProj_statedSL_two_of_odd {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) :
    Nat.card (StatedProj (StatedSL 2 F)) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
  CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hF

theorem isMulCommutative_of_card_le_four {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (h : Nat.card T ≤ 4) : IsMulCommutative T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hT
  have hm2 : m ≤ 2 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m
  · have h1 : Nat.card T = 1 := by simpa using hm
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime (Nat.card T)) := ⟨by rw [hm]; simpa using Nat.prime_two⟩
    have := isCyclic_of_prime_card (α := T) (p := Nat.card T) rfl
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hm

theorem isMulCommutative_of_isPGroup_psl2 {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (e : K ≃* StatedProj (StatedSL 2 F)) (hq : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (T : Subgroup K) (hT : IsPGroup 2 T) : IsMulCommutative T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    omega
  have hcard : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two_of_odd hodd]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hT
  have hdvd : Nat.card T ∣ Nat.card K := Subgroup.card_subgroup_dvd_card T
  rw [hm, hcard] at hdvd
  have hm2 : m ≤ 2 := le_two_of_two_pow_dvd hq hdvd
  refine isMulCommutative_of_card_le_four hT ?_
  rw [hm]
  calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 4 := by norm_num

theorem exists_model_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (X ≃* StatedProj (StatedSL 2 F)) := by
  rcases h with ⟨-, -, K, hK, hfin, hcard, he⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨K, hK, hfin, hcard, he⟩
  all_goals omega

theorem exists_mul_of_mem_sup_of_commute {X : Type} [Group X] (A K : Subgroup X)
    (h : ∀ a ∈ A, ∀ b ∈ K, a * b = b * a) {x : X} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ b ∈ K, a * b = x := by
  have hc : A ≤ centralizer (K : Set X) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm
  have hn : A ≤ normalizer (K : Set X) := hc.trans (Subgroup.centralizer_le_normalizer _)
  have := Subgroup.coe_mul_of_left_le_normalizer_right A K hn
  rw [← SetLike.mem_coe, this] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem not_ree_branch {G : Type} [Group G] [Finite G]
    (hnonab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G))
    {z : G} (hz : IsCentralInvolution z)
    {K : Subgroup ↥(centralizer ({z} : Set G))}
    (hK : IsInternalDirectProduct (zpowers (zElt z)) K
      (oPrimeResidual 2 ↥(centralizer ({z} : Set G))))
    {p f : ℕ} (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (hL : LieModel ↥K .PSL 2 p f) : False := by
  obtain ⟨-, S, hzS, hSz⟩ := hz
  obtain ⟨F, _, _, hFcard, ⟨eK⟩⟩ := exists_model_of_lieModel_psl_two hL
  have h8' : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by rwa [hFcard]
  refine hnonab S ?_
  obtain ⟨hAK, hcomm, -⟩ := hK
  have hSX : ∀ s : G, s ∈ (S : Subgroup G) → s ∈ centralizer ({z} : Set G) := fun s hs => by
    rw [mem_centralizer_singleton_iff]
    exact hSz s hs
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hord : ∀ s : G, s ∈ (S : Subgroup G) → ∃ n : ℕ, s ^ (2 ^ n) = 1 := fun s hs => by
    obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hzc : ∀ x : ↥(centralizer ({z} : Set G)), x * zElt z = zElt z * x := fun x => by
    apply Subtype.ext
    have := mem_centralizer_singleton_iff.1 x.2
    simpa [zElt] using this
  have hAc : ∀ a ∈ zpowers (zElt z), ∀ x : ↥(centralizer ({z} : Set G)), a * x = x * a := by
    intro a ha x
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_right (hzc x) m).symm.eq
  let T : Subgroup K := (S : Subgroup G).comap
    ((centralizer ({z} : Set G)).subtype.comp K.subtype)
  have hT : IsPGroup 2 T := fun k => by
    obtain ⟨n, hn⟩ := hord _ k.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa [map_pow] using hn
  have hTc : IsMulCommutative T := isMulCommutative_of_isPGroup_psl2 eK h8' T hT
  have hdec : ∀ s : G, ∀ hs : s ∈ (S : Subgroup G), ∃ a ∈ zpowers (zElt z), ∃ k : K,
      (k : ↥(centralizer ({z} : Set G))) ∈ K ∧ ((k : ↥(centralizer ({z} : Set G))) : G) ∈ S ∧
        a * (k : ↥(centralizer ({z} : Set G))) = ⟨s, hSX s hs⟩ := by
    intro s hs
    have hmem : (⟨s, hSX s hs⟩ : ↥(centralizer ({z} : Set G))) ∈
        oPrimeResidual 2 ↥(centralizer ({z} : Set G)) := by
      obtain ⟨n, hn⟩ := hord s hs
      exact Subgroup.subset_closure ⟨n, Subtype.ext hn⟩
    rw [← hAK] at hmem
    obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup_of_commute _ _ hcomm hmem
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    have hzS' : ((zElt z ^ m : ↥(centralizer ({z} : Set G))) : G) ∈ (S : Subgroup G) := by
      have : ((zElt z ^ m : ↥(centralizer ({z} : Set G))) : G) = z ^ m := by simp [zElt]
      rw [this]
      exact zpow_mem hzS m
    have hkS : (k : G) ∈ (S : Subgroup G) := by
      have h1 : (k : G) = ((zElt z ^ m : ↥(centralizer ({z} : Set G))) : G)⁻¹ * s := by
        have := congrArg Subtype.val hak
        simp only [Subgroup.coe_mul] at this
        rw [← this]
        group
      rw [h1]
      exact mul_mem (inv_mem hzS') hs
    exact ⟨zElt z ^ m, mem_zpowers_iff.2 ⟨m, rfl⟩, ⟨k, hk⟩, hk, hkS, hak⟩
  refine ⟨⟨fun s t => ?_⟩⟩
  obtain ⟨a₁, ha₁, k₁, hk₁, hk₁S, h₁⟩ := hdec s s.2
  obtain ⟨a₂, ha₂, k₂, hk₂, hk₂S, h₂⟩ := hdec t t.2
  have hkk : k₁ * k₂ = k₂ * k₁ := by
    have := hTc.is_comm.comm (⟨k₁, hk₁S⟩ : T) ⟨k₂, hk₂S⟩
    exact congrArg Subtype.val this
  have haa : a₁ * a₂ = a₂ * a₁ := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha₁
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ha₂
    exact ((Commute.refl (zElt z)).zpow_zpow m n).eq
  apply Subtype.ext
  have hst : (⟨(s : G), hSX s s.2⟩ : ↥(centralizer ({z} : Set G))) *
      ⟨(t : G), hSX t t.2⟩ = ⟨(t : G), hSX t t.2⟩ * ⟨(s : G), hSX s s.2⟩ := by
    rw [← h₁, ← h₂]
    have e1 : a₁ * (k₁ : ↥(centralizer ({z} : Set G))) *
        (a₂ * (k₂ : ↥(centralizer ({z} : Set G)))) =
        a₁ * a₂ * ((k₁ : ↥(centralizer ({z} : Set G))) * k₂) := by
      have hk : (k₁ : ↥(centralizer ({z} : Set G))) * a₂ = a₂ * k₁ := (hAc a₂ ha₂ k₁).symm
      calc a₁ * (k₁ : ↥(centralizer ({z} : Set G))) * (a₂ * (k₂ : ↥(centralizer ({z} : Set G))))
          = a₁ * ((k₁ : ↥(centralizer ({z} : Set G))) * a₂) * k₂ := by simp only [mul_assoc]
        _ = a₁ * (a₂ * (k₁ : ↥(centralizer ({z} : Set G)))) * k₂ := by rw [hk]
        _ = a₁ * a₂ * ((k₁ : ↥(centralizer ({z} : Set G))) * k₂) := by simp only [mul_assoc]
    have e2 : a₂ * (k₂ : ↥(centralizer ({z} : Set G))) *
        (a₁ * (k₁ : ↥(centralizer ({z} : Set G)))) =
        a₂ * a₁ * ((k₂ : ↥(centralizer ({z} : Set G))) * k₁) := by
      have hk : (k₂ : ↥(centralizer ({z} : Set G))) * a₁ = a₁ * k₂ := (hAc a₁ ha₁ k₂).symm
      calc a₂ * (k₂ : ↥(centralizer ({z} : Set G))) * (a₁ * (k₁ : ↥(centralizer ({z} : Set G))))
          = a₂ * ((k₂ : ↥(centralizer ({z} : Set G))) * a₁) * k₁ := by simp only [mul_assoc]
        _ = a₂ * (a₁ * (k₂ : ↥(centralizer ({z} : Set G)))) * k₁ := by rw [hk]
        _ = a₂ * a₁ * ((k₂ : ↥(centralizer ({z} : Set G))) * k₁) := by simp only [mul_assoc]
    rw [e1, e2, haa]
    congr 1
    exact congrArg Subtype.val hkk
  have hfin := congrArg Subtype.val hst
  exact hfin

end CFSG.GH74.GLS.Stage4
