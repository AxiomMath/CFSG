module

public import CFSG.LocalAnalysis.GH72.G3bTen
public import CFSG.LocalAnalysis.GH72.InvolutionCentralizer
public import CFSG.LocalAnalysis.GH72.DDLocal

public section

namespace CFSG.GH72

open Subgroup
open MulAction
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace Sec3Setting

theorem lemma_3_5 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (h₃ : ∃ n : ℕ, ∃ u ∈ normalizer ((𝔖.S : Subgroup G) : Set G), orderOf u = 3 ^ n ∧
      u ∈ normalizer (𝔖.S₁ : Set G) ∧ u ∉ centralizer (𝔖.S₁ : Set G))
    (A : Subgroup G) (hAS : A ≤ 𝔖.S) (hA : IsE16 A) :
    (∃ Q : Subgroup G, Subgroup.centralizer (A : Set G) ≤ Q ∧
      Q ≤ Subgroup.normalizer (A : Set G) ∧
      (Q.subgroupOf (Subgroup.normalizer (A : Set G))).Normal ∧
      (Subgroup.centralizer (A : Set G)).relIndex Q = 9 ∧
      ∃ n : ℕ, Q.relIndex (Subgroup.normalizer (A : Set G)) = 2 ^ n) ∧
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (𝔖.S₁ : Set G) ∧
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((𝔖.S₂ ⊓ A : Subgroup G) : Set G) ∧
    ∀ v ∈ A, ∀ w ∈ A, orderOf v = 2 → orderOf w = 2 → v ∉ 𝔖.S₁ → v ∉ 𝔖.S₂ → w ∉ 𝔖.S₁ →
      w ∉ 𝔖.S₂ → ∃ g ∈ Subgroup.normalizer (A : Set G), g * v * g⁻¹ = w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := (𝔖.S : Subgroup G) with hSdef
  set S₁ : Subgroup G := 𝔖.S₁ with hS₁def
  set S₂ : Subgroup G := 𝔖.S₂ with hS₂def
  have hd : DDDecomp S S₁ S₂ := 𝔖.decomp
  have hAS' : A ≤ S := hAS
  have h₁' : IsKleinFour ↥S₁ := h₁
  have h₂' : ∀ x ∈ S₂, ∀ y ∈ S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y := h₂
  obtain ⟨hAsplit, hV₁, hV₂⟩ := hd.e16_split hAS' hA
  have hA₁eq : A ⊓ S₁ = S₁ := CFSG.GH72.IsDih.four_eq_of_isKleinFour h₁' hV₁
  have hS₁A : S₁ ≤ A := by rw [← hA₁eq]; exact inf_le_left
  have hAsplit' : A = S₁ ⊔ (A ⊓ S₂) := by simpa [hA₁eq] using hAsplit
  obtain ⟨z₂, hz₂S₂, hz₂ord, hz₂Z⟩ := hd.dih₂.exists_inf_centralizer_self_eq
  have hz₂2 : z₂ * z₂ = 1 := by rw [← pow_two, ← hz₂ord]; exact pow_orderOf_eq_one _
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₂ord
    norm_num at hz₂ord
  have hz₂centS₂ : ∀ y ∈ S₂, y * z₂ = z₂ * y := by
    intro y hy
    have hz : z₂ ∈ S₂ ⊓ centralizer (S₂ : Set G) := by
      rw [hz₂Z]; exact Subgroup.mem_zpowers z₂
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hy
  have hz₂centS : S ≤ Subgroup.centralizer ({z₂} : Set G) := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hd.mem_iff.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x₁ * z₂ = z₂ * x₁ := hd.comm hx₁ hz₂S₂
    have h2 : x₂ * z₂ = z₂ * x₂ := hz₂centS₂ x₂ hx₂
    calc x₁ * x₂ * z₂ = x₁ * (x₂ * z₂) := by group
      _ = x₁ * (z₂ * x₂) := by rw [h2]
      _ = x₁ * z₂ * x₂ := by group
      _ = z₂ * x₁ * x₂ := by rw [h1]
      _ = z₂ * (x₁ * x₂) := by group
  have hz₂S : z₂ ∈ S := hd.le_right hz₂S₂
  have hz₂A : z₂ ∈ A := hd.center_le hAS' hA hz₂S hz₂centS
  have hz₂A₂ : z₂ ∈ A ⊓ S₂ := ⟨hz₂A, hz₂S₂⟩
  have hA₂card : Nat.card ↥(A ⊓ S₂) = 4 := hV₂.2.2
  have hlt : (Subgroup.zpowers z₂ : Set G).ncard < ((A ⊓ S₂ : Subgroup G) : Set G).ncard := by
    have h1 : Nat.card ↥(Subgroup.zpowers z₂) = 2 := by
      rw [Nat.card_zpowers]; exact hz₂ord
    have h2 : Nat.card ↥(A ⊓ S₂) = 4 := hA₂card
    have h1' : ((Subgroup.zpowers z₂ : Subgroup G) : Set G).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]
      exact h1
    have h2' : (((A ⊓ S₂ : Subgroup G)) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h2
    rw [h1', h2']
    norm_num
  obtain ⟨c, hcA₂, hcNotZp⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hcA : c ∈ A := (Subgroup.mem_inf.mp hcA₂).1
  have hcS₂ : c ∈ S₂ := (Subgroup.mem_inf.mp hcA₂).2
  have hc1 : c ≠ 1 := by
    intro h
    exact hcNotZp (h ▸ Subgroup.one_mem (Subgroup.zpowers z₂))
  have hc2 : c * c = 1 := hV₂.2.1 c hcA₂
  have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  have hcz₂ : c ≠ z₂ := by
    intro h
    exact hcNotZp (h ▸ Subgroup.mem_zpowers z₂)
  have hA₂eq : A ⊓ S₂ = Subgroup.zpowers c ⊔ Subgroup.zpowers z₂ := by
    apply le_antisymm
    · intro y hy
      haveI : Fintype ↥(A ⊓ S₂) := Fintype.ofFinite _
      haveI : IsKleinFour ↥(A ⊓ S₂) := isKleinFour_of_isFourIn hV₂
      have hy' : (⟨y, hy⟩ : ↥(A ⊓ S₂)) ∈ (Finset.univ : Finset ↥(A ⊓ S₂)) :=
        Finset.mem_univ _
      have huniv := IsKleinFour.eq_finset_univ (G := ↥(A ⊓ S₂))
        (x := (⟨c, hcA₂⟩ : ↥(A ⊓ S₂))) (y := (⟨z₂, hz₂A₂⟩ : ↥(A ⊓ S₂)))
        (by intro h; exact hc1 (congrArg Subtype.val h))
        (by intro h; exact hz₂1 (congrArg Subtype.val h))
        (by intro h; exact hcz₂ (congrArg Subtype.val h))
      rw [← huniv] at hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
      rcases hy' with h1c | h2c | h3c | h4c
      · have hyc : y = c * z₂ := congrArg Subtype.val h1c
        rw [hyc]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂))
      · have hyc : y = c := congrArg Subtype.val h2c
        rw [hyc]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · have hyc : y = z₂ := congrArg Subtype.val h3c
        rw [hyc]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₂)
      · have hyc : y = 1 := congrArg Subtype.val h4c
        rw [hyc]; exact Subgroup.one_mem _
    · exact sup_le (Subgroup.zpowers_le.mpr hcA₂) (Subgroup.zpowers_le.mpr hz₂A₂)
  have hAeq : A = S₁ ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers z₂) := by
    rw [hAsplit', hA₂eq]
  have hS₁ab : ⁅S₁, S₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val
      (IsKleinFour.isMulCommutative.is_comm.comm (⟨x, hx⟩ : S₁) ⟨y, hy⟩)).symm
  have hSS' : ⁅S, S⁆ = ⁅S₂, S₂⁆ := by
    rw [← hd.sup_eq]
    rw [CFSG.GH72.commutator_sup_eq_of_commute (fun a ha b hb => hd.comm ha hb), hS₁ab, bot_sup_eq]
  have hz₂S' : z₂ ∈ ⁅S, S⁆ := by
    rw [hSS']
    exact hd.dih₂.mem_commutator_of_central hz₂S₂ hz₂1 hz₂centS₂
  obtain ⟨n, u, huS, huord, huS₁, huC⟩ := h₃
  have hu1 : u ≠ 1 := by
    intro h
    exact huC (h ▸ Subgroup.one_mem _)
  have hodd_u : Odd (orderOf u) := by
    rw [huord]
    exact (show Odd 3 by decide).pow
  have hσu_odd : Odd (orderOf (S.normalizerMonoidHom ⟨u, huS⟩)) :=
    (Subgroup.orderOf_mk u huS ▸ hodd_u).of_dvd_nat (orderOf_map_dvd _ _)
  have hmodZ : ∀ x ∈ S, x⁻¹ * (u * x * u⁻¹) ∈ S ⊓ centralizer (S : Set G) := by
    intro x hx
    let z : ↥S := (⟨x, hx⟩ : ↥S)⁻¹ * S.normalizerMonoidHom ⟨u, huS⟩ ⟨x, hx⟩
    have hz : z ∈ Subgroup.center ↥S :=
      hd.mul_inv_mem_center_of_odd (S.normalizerMonoidHom ⟨u, huS⟩) hσu_odd ⟨x, hx⟩
    have hzcoe : (z : G) = x⁻¹ * (u * x * u⁻¹) := rfl
    constructor
    · rw [← hzcoe]; exact z.2
    · rw [← hzcoe]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      have hcomm := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
      have hcomm' := congrArg Subtype.val hcomm
      simpa only [Subgroup.coe_mul] using hcomm'
  have hZS : S ⊓ centralizer (S : Set G) = S₁ ⊔ Subgroup.zpowers z₂ := by
    rw [hd.inf_centralizer_self, hz₂Z]
    have hZ₁ : S₁ ⊓ centralizer (S₁ : Set G) = S₁ := by
      rw [inf_of_le_left]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val
        (IsKleinFour.isMulCommutative.is_comm.comm (⟨y, hy⟩ : S₁) ⟨x, hx⟩)
    rw [hZ₁]
  have huz₂ : u * z₂ * u⁻¹ = z₂ := by
    let f : G →* G := (MulAut.conj u).toMonoidHom
    have hf : ∀ x : G, f x = u * x * u⁻¹ := fun x => MulAut.conj_apply u x
    have hSmap : S.map f = S := by
      simpa [f] using CFSG.CGT.Foote81L6.TStruct.map_conj_eq_self_of_mem_normalizer huS
    have hmap : (⁅S, S⁆).map f = ⁅S, S⁆ := by
      rw [Subgroup.map_commutator, hSmap]
    have hmem : u * z₂ * u⁻¹ ∈ ⁅S, S⁆ := by
      have h : f z₂ ∈ (⁅S, S⁆).map f := Subgroup.mem_map.mpr ⟨z₂, hz₂S', rfl⟩
      have h' : u * z₂ * u⁻¹ ∈ (⁅S, S⁆).map f := by rwa [hf z₂] at h
      rwa [hmap] at h'
    have hsq : (u * z₂ * u⁻¹) * (u * z₂ * u⁻¹) = 1 := by
      have h := congrArg (fun t => u * t * u⁻¹) hz₂2
      simpa [mul_assoc] using h
    have hmem' : u * z₂ * u⁻¹ ∈ ⁅S₂, S₂⁆ := by rwa [hSS'] at hmem
    have hS₂'le : ⁅S₂, S₂⁆ ≤ S₂ := Subgroup.commutator_le.mpr fun g hg h hh => by
      rw [commutatorElement_def]
      exact S₂.mul_mem (S₂.mul_mem (S₂.mul_mem hg hh) (S₂.inv_mem hg)) (S₂.inv_mem hh)
    have hmem2 : u * z₂ * u⁻¹ ∈ S₂ ⊓ centralizer (S₂ : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hS₂'le hmem', ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hd.dih₂.mem_centralizer_of_mem_commutator hmem' hsq y hy
    rw [hz₂Z] at hmem2
    have hne : u * z₂ * u⁻¹ ≠ 1 := by
      intro h
      apply hz₂1
      have h2 := congrArg (fun t => u⁻¹ * t * u) h
      simpa [mul_assoc] using h2
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hz₂2 hmem2 with h | h
    · exact absurd h hne
    · exact h
  have hZSA : S₁ ⊔ Subgroup.zpowers z₂ ≤ A :=
    sup_le hS₁A (Subgroup.zpowers_le.mpr hz₂A)
  have huA₂ : ∀ a ∈ A ⊓ S₂, u * a * u⁻¹ ∈ A := by
    intro a ha
    have haS : a ∈ S := hd.le_right (Subgroup.mem_inf.mp ha).2
    have hz := hmodZ a haS
    rw [hZS] at hz
    have hzA : a⁻¹ * (u * a * u⁻¹) ∈ A := hZSA hz
    have : u * a * u⁻¹ = a * (a⁻¹ * (u * a * u⁻¹)) := by group
    rw [this]
    exact A.mul_mem (Subgroup.mem_inf.mp ha).1 hzA
  have huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A := by
    intro a ha
    have hcomm : ∀ x ∈ S₁, ∀ y ∈ A ⊓ S₂, x * y = y * x := fun x hx y hy =>
      hd.comm hx (Subgroup.mem_inf.mp hy).2
    rw [hAsplit'] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 ha
    have hxS₁ : u * x * u⁻¹ ∈ S₁ := (Subgroup.mem_normalizer_iff.mp huS₁ x).mp hx
    have hyA : u * y * u⁻¹ ∈ A := huA₂ y hy
    rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group]
    exact Subgroup.mul_mem (H := A) (hS₁A hxS₁) hyA
  have huK : u ∈ Subgroup.normalizer (A : Set G) := by
    apply CFSG.CGT.Foote81L6.TStruct.mem_normalizer_of_map_conj_eq
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact huA a ha
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]

  let K : Subgroup G := Subgroup.normalizer (A : Set G)
  let Cc : Subgroup G := Subgroup.centralizer (A : Set G)
  let φ : K →* MulAut A := A.normalizerMonoidHom
  let L : Subgroup (MulAut A) := φ.range
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hC_le_K : Cc ≤ K := Subgroup.centralizer_le_normalizer (A : Set G)
  have hA_le_C : A ≤ Cc := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAcomm y hy x hx
  have hA_le_K : A ≤ K := hA_le_C.trans hC_le_K
  have huCA : u ∉ Cc := by
    intro h
    apply huC
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro y hy
    exact h y (hS₁A hy)
  obtain ⟨d', hd'S₂, hd'2, hd'NotA₂, hN₂⟩ := hd.dih₂.exists_inf_normalizer_four_eq hV₂
  have hd'N_A₂ : d' ∈ Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
    have h : d' ∈ S₂ ⊓ Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
      rw [hN₂]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d')
    exact (Subgroup.mem_inf.mp h).2
  have hd'N_S₁ : d' ∈ Subgroup.normalizer (S₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x; constructor
    · intro hx
      rw [← hd.comm hx hd'S₂]
      simpa [mul_assoc] using hx
    · intro hx
      have hconv : d'⁻¹ * (d' * x * d'⁻¹) * d' = x := by group
      rw [← hconv]
      have hcomm' : d'⁻¹ * (d' * x * d'⁻¹) = (d' * x * d'⁻¹) * d'⁻¹ :=
        (hd.comm hx (Subgroup.inv_mem (H := S₂) hd'S₂)).symm
      rw [hcomm']
      simpa [mul_assoc] using hx
  have d'_conj_mem : ∀ {e : G}, e ∈ S₂ → (∀ y ∈ S₁, e * y = y * e) →
      (∀ y ∈ A ⊓ S₂, e * y * e⁻¹ ∈ A ⊓ S₂) → ∀ x ∈ A, e * x * e⁻¹ ∈ A := by
    intro e heS₂ hecent heN₂ x hx
    have hcomm : ∀ u ∈ S₁, ∀ v ∈ A ⊓ S₂, u * v = v * u :=
      fun u hu v hv => hd.comm hu (Subgroup.mem_inf.mp hv).2
    rw [hAsplit'] at hx
    obtain ⟨s, hs, w, hw, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hx
    have hw' : e * w * e⁻¹ ∈ A ⊓ S₂ := heN₂ w hw
    have hs' : e * s * e⁻¹ = s := by rw [hecent s hs]; group
    have hprod : e * (s * w) * e⁻¹ = (e * s * e⁻¹) * (e * w * e⁻¹) := by group
    rw [hprod, hs', hAsplit']
    exact Subgroup.mul_mem (H := S₁ ⊔ (A ⊓ S₂)) (Subgroup.mem_sup_left hs)
      (Subgroup.mem_sup_right hw')
  have hd'A_le : ∀ x ∈ A, d' * x * d'⁻¹ ∈ A :=
    d'_conj_mem hd'S₂ (fun y hy => (hd.comm hy hd'S₂).symm)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp hd'N_A₂ y).mp hy)
  have hd'A_le' : ∀ x ∈ A, d'⁻¹ * x * d' ∈ A := by
    have h := d'_conj_mem (Subgroup.inv_mem (H := S₂) hd'S₂)
      (fun y hy => (hd.comm hy (Subgroup.inv_mem (H := S₂) hd'S₂)).symm)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem (H := Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G)) hd'N_A₂)
        y).mp hy)
    simpa using h
  have hd'K : d' ∈ K := by
    rw [Subgroup.mem_normalizer_iff]
    intro x; constructor
    · exact hd'A_le x
    · intro hx
      have h := hd'A_le' (d' * x * d'⁻¹) hx
      simpa [mul_assoc] using h
  let τ : MulAut A := φ ⟨d', hd'K⟩
  have hτ2 : τ * τ = 1 := by
    change φ ⟨d', hd'K⟩ * φ ⟨d', hd'K⟩ = 1
    have hmul : (⟨d', hd'K⟩ : K) * ⟨d', hd'K⟩ = 1 := by
      apply Subtype.ext
      simpa using hd'2
    rw [← map_mul, hmul, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have hd'C : d' ∈ Cc := (CFSG.GH72.normalizerMonoidHom_eq_one_iff hd'K).mp h
    have hd'C₂ : d' ∈ Subgroup.centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hd'C y (Subgroup.mem_inf.mp hy).1
    have hmem : d' ∈ S₂ ⊓ centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := ⟨hd'S₂, hd'C₂⟩
    rw [hd.isDih₂.inf_centralizer_four hV₂] at hmem
    exact hd'NotA₂ hmem
  have hτL : τ ∈ L := ⟨⟨d', hd'K⟩, rfl⟩
  let Psub : Subgroup (MulAut A) := Subgroup.zpowers τ
  have hPsub_le_L : Psub ≤ L := Subgroup.zpowers_le.mpr hτL
  have hPsub_card : Nat.card Psub = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1]
  let P : Subgroup G := S ⊓ K
  have hP_sylow : CFSG.ABGLocalTools.IsSylowOf 2 P K := hd.isSylowOf_normalizer_e16 hAS' hA
  have hP_card : Nat.card P = 32 := (hd.inf_normalizer_e16_of_isKleinFour h₁' hAS' hA).2
  have hP_eq : P = A ⊔ Subgroup.zpowers d' := by
    change S ⊓ normalizer (A : Set G) = _
    rw [(hd.inf_normalizer_e16_of_isKleinFour h₁' hAS' hA).1, hN₂, ← sup_assoc, ← hAsplit']
  have hP_notdvd : ¬ 2 ∣ P.relIndex K :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hP_sylow).2.2
  have hP_odd : Odd (P.relIndex K) := by
    rcases Nat.even_or_odd (P.relIndex K) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hP_notdvd
    · exact ho
  have hKnormC : K ≤ Subgroup.normalizer (Cc : Set G) := by
    have hNC : (Cc.subgroupOf K).Normal := by
      change (Subgroup.centralizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G)) |>.Normal
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).mp hNC
  have hPnormC : P ≤ Subgroup.normalizer (Cc : Set G) := fun x hx => hKnormC hx.2
  have hPCC : P ⊓ Cc = A := by
    change (S ⊓ K) ⊓ Cc = A
    have hKC : K ⊓ Cc = Cc := inf_eq_right.mpr fun x hx =>
      Subgroup.centralizer_le_normalizer (A : Set G) hx
    rw [inf_assoc, hKC]
    exact hd.inf_centralizer_e16 hAS' hA
  have hrel_sup : Cc.relIndex (P ⊔ Cc) = 2 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := P) (K := Cc) hPnormC).2
    rw [h, hPCC]
    have hAP : A ≤ P := by rw [hP_eq]; exact le_sup_left
    have hmul : A.relIndex P * Nat.card A = Nat.card P := by
      simpa [inf_eq_left.mpr hAP] using (Subgroup.relIndex_mul_card (H := A) (K := P))
    rw [hA.2, hP_card] at hmul
    omega
  have hPC_odd : Odd ((P ⊔ Cc).relIndex K) := by
    have hdvd : (P ⊔ Cc).relIndex K ∣ P.relIndex K :=
      Subgroup.relIndex_dvd_of_le_left (H := P) (K := P ⊔ Cc) (L := K) le_sup_left
    exact hP_odd.of_dvd_nat hdvd
  have hφker : φ.ker = Cc.subgroupOf K := by
    change A.normalizerMonoidHom.ker = Cc.subgroupOf K
    rw [Subgroup.normalizerMonoidHom_ker]
  have hL_card : Nat.card L = Cc.relIndex K := by
    change Nat.card φ.range = Cc.relIndex K
    rw [← Subgroup.index_ker φ, hφker]
    rfl
  have hL_card' : Nat.card L = 2 * (P ⊔ Cc).relIndex K := by
    rw [hL_card, ← Subgroup.relIndex_mul_relIndex (H := Cc) (K := P ⊔ Cc) (L := K)
      (show Cc ≤ P ⊔ Cc from le_sup_right)
      (show P ⊔ Cc ≤ K from sup_le inf_le_right fun x hx => hC_le_K hx), hrel_sup]
  have hPsub_relIndex_card : Psub.relIndex L * Nat.card Psub = Nat.card L := by
    simpa [inf_eq_left.mpr hPsub_le_L] using
      (Subgroup.relIndex_mul_card (H := Psub) (K := L))
  have hPsub_relIndex_odd : Odd (Psub.relIndex L) := by
    have hmul : Psub.relIndex L * 2 = 2 * (P ⊔ Cc).relIndex K := by
      rw [← hPsub_card, hPsub_relIndex_card, hL_card', hPsub_card]
    have hcancel : Psub.relIndex L = (P ⊔ Cc).relIndex K := by omega
    rw [hcancel]
    exact hPC_odd
  have hPsub_sylow : CFSG.ABGLocalTools.IsSylowOf 2 Psub L := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hPsub_le_L, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 1) (by rw [hPsub_card]; norm_num)
    · rcases hPsub_relIndex_odd with ⟨m, hm⟩
      omega

  obtain ⟨Psyl, hPsyl_coe⟩ := hPsub_sylow.exists_sylow_eq_subgroupOf
  have hτL2 : (⟨τ, hτL⟩ : L) * ⟨τ, hτL⟩ = 1 := by
    apply Subtype.ext
    simpa using hτ2
  have hτL1 : (⟨τ, hτL⟩ : L) ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  have hPsyl_eq : (Psyl : Subgroup L) = Subgroup.zpowers (⟨τ, hτL⟩ : L) := by
    rw [hPsyl_coe]
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (show (x : MulAut A) ∈ Psub from hx)
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext hm⟩
    · intro hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, congrArg Subtype.val hm⟩
  have hN_syl : Subgroup.normalizer (Psyl : Set L) ≤ Subgroup.centralizer (Psyl : Set L) := by
    change Subgroup.normalizer ((Psyl : Subgroup L) : Set L) ≤
      Subgroup.centralizer ((Psyl : Subgroup L) : Set L)
    rw [show ((Psyl : Subgroup L) : Set L) =
      ((Subgroup.zpowers (⟨τ, hτL⟩ : L)) : Set L)
        from congrArg (fun H : Subgroup L => (H : Set L)) hPsyl_eq]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxτ : x * (⟨τ, hτL⟩ : L) * x⁻¹ ∈ Subgroup.zpowers (⟨τ, hτL⟩ : L) :=
      (Subgroup.mem_normalizer_iff.mp hx (⟨τ, hτL⟩ : L)).mp (Subgroup.mem_zpowers _)
    have hxτ1 : x * (⟨τ, hτL⟩ : L) * x⁻¹ ≠ 1 := by
      intro h
      apply hτL1
      have h' := congrArg (fun z => x⁻¹ * z * x) h
      simpa [mul_assoc] using h'
    have hfix : x * (⟨τ, hτL⟩ : L) * x⁻¹ = (⟨τ, hτL⟩ : L) := by
      rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hτL2 hxτ with h | h
      · exact absurd h hxτ1
      · exact h
    have hxτ : x * (⟨τ, hτL⟩ : L) = (⟨τ, hτL⟩ : L) * x := by
      calc x * (⟨τ, hτL⟩ : L) = (x * (⟨τ, hτL⟩ : L) * x⁻¹) * x := by group
        _ = (⟨τ, hτL⟩ : L) * x := by rw [hfix]
    have hcomm : Commute (⟨τ, hτL⟩ : L) x := hxτ.symm
    exact (hcomm.zpow_left m).eq
  obtain ⟨Qbar, hQbar_normal, hQbar_notdvd, hQbar_index, -, -, hQbar_compl, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement Psyl hN_syl
  let QbarAmb : Subgroup (MulAut A) := Qbar.map L.subtype
  let Q : Subgroup G := (QbarAmb.comap φ).map K.subtype
  have hQ_le_K : Q ≤ K := Subgroup.map_subtype_le _
  have hC_le_Q : Cc ≤ Q := by
    intro x hx
    have hxK : x ∈ K := hC_le_K hx
    have hxφ : φ ⟨x, hxK⟩ = 1 :=
      (CFSG.GH72.normalizerMonoidHom_eq_one_iff hxK).mpr hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    change φ ⟨x, hxK⟩ ∈ Qbar.map L.subtype
    rw [hxφ]
    exact Subgroup.mem_map_of_mem _ Qbar.one_mem
  have hQsub_eq : Q.subgroupOf K = QbarAmb.comap φ := by
    change Subgroup.comap K.subtype ((QbarAmb.comap φ).map K.subtype) = QbarAmb.comap φ
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hQbarAmb_le_L : QbarAmb ≤ L := by
    rintro y ⟨q, hq, rfl⟩
    exact q.2
  have hQbarAmb_conj : ∀ l ∈ L, ∀ q ∈ QbarAmb, l * q * l⁻¹ ∈ QbarAmb := by
    intro l hl q hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
    have hconj : (⟨l, hl⟩ : L) * q' * (⟨l, hl⟩ : L)⁻¹ ∈ Qbar :=
      hQbar_normal.conj_mem q' hq' ⟨l, hl⟩
    exact Subgroup.mem_map_of_mem L.subtype hconj
  have hQbarAmb_norm : L ≤ Subgroup.normalizer (QbarAmb : Set (MulAut A)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hQbarAmb_conj l hl q hq
    · intro hq
      have := hQbarAmb_conj l⁻¹ (Subgroup.inv_mem (H := L) hl) (l * q * l⁻¹) hq
      simpa [mul_assoc] using this
  have hQnorm_sub : (Q.subgroupOf K).Normal := by
    rw [hQsub_eq]
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hφk : φ k ∈ L := MonoidHom.mem_range.mpr ⟨k, rfl⟩
    have h := hQbarAmb_conj (φ k) hφk (φ n) hn
    simpa [map_mul, map_inv] using h
  have hKnormQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_K).mp hQnorm_sub
  have hQ_index_card : Cc.relIndex Q = Nat.card Qbar := by
    calc Cc.relIndex Q = (Cc.subgroupOf K).relIndex (Q.subgroupOf K) :=
          (Subgroup.relIndex_subgroupOf (H := Cc) (K := Q) (L := K) hQ_le_K).symm
      _ = (φ.ker).relIndex (QbarAmb.comap φ) := by rw [hQsub_eq, hφker]
      _ = Nat.card ((QbarAmb.comap φ).map φ) := Subgroup.relIndex_ker (f := φ) _
      _ = Nat.card QbarAmb := by rw [Subgroup.map_comap_eq_self hQbarAmb_le_L]
      _ = Nat.card Qbar := Subgroup.card_map_of_injective L.subtype_injective
  have hQbar_odd : Odd (Nat.card Qbar) := by
    rcases Nat.even_or_odd (Nat.card Qbar) with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hQbar_notdvd
    · exact ho
  have hQ_index_odd : Odd (Cc.relIndex Q) := hQ_index_card ▸ hQbar_odd
  have hQbarAmb_card' : Nat.card QbarAmb = Nat.card Qbar :=
    Subgroup.card_map_of_injective L.subtype_injective
  let τu : MulAut A := φ (⟨u, huK⟩ : K)
  have hτu_memL : τu ∈ L := ⟨⟨u, huK⟩, rfl⟩
  let τuL : L := ⟨τu, hτu_memL⟩
  have hτu_dvd : orderOf τu ∣ 3 ^ n := by
    rw [← huord]
    have h := orderOf_map_dvd φ (⟨u, huK⟩ : K)
    rwa [Subgroup.orderOf_mk u huK] at h
  have hτu_ne : τu ≠ 1 := by
    intro h
    exact huCA ((CFSG.GH72.normalizerMonoidHom_eq_one_iff huK).mp h)
  have hτu_odd : Odd (orderOf τuL) := by
    rw [← Subgroup.orderOf_coe τuL]
    exact hodd_u.of_dvd_nat (huord ▸ hτu_dvd)
  have hOdd_in_Qbar : ∀ {x : L}, Odd (orderOf x) → x ∈ Qbar := by
    intro x hxodd
    by_contra hx
    have hq1 : QuotientGroup.mk' Qbar x ≠ 1 := fun h => hx ((QuotientGroup.eq_one_iff x).mp h)
    have hcard : Nat.card (L ⧸ Qbar) = 2 := by
      rw [← Subgroup.index_eq_card, hQbar_index]
      rw [hPsyl_eq, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact hτL2) hτL1]
    have hdvd2 : orderOf (QuotientGroup.mk' Qbar x) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk' Qbar x)
      rwa [hcard] at this
    have hdvdx : orderOf (QuotientGroup.mk' Qbar x) ∣ orderOf x := orderOf_map_dvd _ _
    have hoddq : Odd (orderOf (QuotientGroup.mk' Qbar x)) := hxodd.of_dvd_nat hdvdx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact hq1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hoddq
      exact absurd hoddq (by decide)
  have hτu_memQbar : τuL ∈ Qbar := hOdd_in_Qbar hτu_odd
  have hτu_memQbarAmb : τu ∈ QbarAmb :=
    Subgroup.mem_map.mpr ⟨τuL, hτu_memQbar, rfl⟩
  have huQ : u ∈ Q := by
    have huK' : u ∈ K := huK
    have hmem : (⟨u, huK'⟩ : K) ∈ QbarAmb.comap φ := Subgroup.mem_comap.mpr hτu_memQbarAmb
    rw [← hQsub_eq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have h3dvdQbar : 3 ∣ Nat.card Qbar := by
    obtain ⟨k, hk, hkord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hτu_dvd
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', pow_zero] at hkord
      exact hτu_ne (orderOf_eq_one_iff.mp hkord)
    have h3dvdτ : 3 ∣ orderOf τu := by
      rw [hkord]
      exact dvd_pow_self 3 (by omega)
    have h3dvdτL : 3 ∣ orderOf τuL := by
      rwa [Subgroup.orderOf_coe τuL] at h3dvdτ
    exact h3dvdτL.trans (Subgroup.orderOf_dvd_natCard (s := Qbar) (x := τuL) hτu_memQbar)
  have h3dvd : 3 ∣ Cc.relIndex Q := hQ_index_card ▸ h3dvdQbar
  have hz₂cK : ∃ k ∈ K, k * z₂ * k⁻¹ = c := by
    obtain ⟨g, hgK, hg⟩ :=
      CFSG.GH72.Sec3Setting.exists_conj_mem_normalizer_of_isConj_center 𝔖 hAS hA
        hcA hz₂A hz₂centS hcord hz₂ord (h₂ c hcS₂ z₂ hz₂S₂ hcord hz₂ord)
    refine ⟨g⁻¹, Subgroup.inv_mem (H := K) hgK, ?_⟩
    rw [← hg]
    group
  have hfixC : ∀ x ∈ Cc, x * z₂ * x⁻¹ = z₂ := by
    intro x hx
    have h := Subgroup.mem_centralizer_iff.mp hx z₂ hz₂A
    rw [← h]; group
  have hfixd' : d' * z₂ * d'⁻¹ = z₂ := by
    rw [hz₂centS₂ d' hd'S₂]; group
  have hL_decomp : L = QbarAmb ⊔ Psub := by
    calc L = (⊤ : Subgroup L).map L.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (Qbar ⊔ Psyl).map L.subtype := by rw [hQbar_compl.sup_eq_top]
      _ = QbarAmb ⊔ Psub := by
          rw [Subgroup.map_sup, hPsyl_coe,
            show Qbar.map L.subtype = QbarAmb from rfl,
            Subgroup.map_subgroupOf_eq_of_le hPsub_le_L]

  have hfree : ∀ x ∈ S₁, u * x * u⁻¹ = x → x = 1 := by
    intro x hx hfix
    by_contra hx1
    have hα1 : S₁.normalizerMonoidHom ⟨u, huS₁⟩ = 1 :=
      CFSG.GH72.kleinFour_mulAut_eq_one_of_odd (S₁.normalizerMonoidHom ⟨u, huS₁⟩)
        (u := ⟨x, hx⟩) (fun h => hx1 (congrArg Subtype.val h))
        (by apply Subtype.ext; simpa using hfix)
        ((Subgroup.orderOf_mk u huS₁ ▸ hodd_u).of_dvd_nat (orderOf_map_dvd _ _))
    exact huC ((CFSG.GH72.normalizerMonoidHom_eq_one_iff huS₁).mp hα1)
  have hK_decomp : ∀ k ∈ K, ∃ c₀ ∈ Cc, ∃ q ∈ Q, ∃ ε : ℤ, k = c₀ * (q * d' ^ ε) := by
    intro k hk
    have hφkL : φ ⟨k, hk⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    have hPsub_norm : Psub ≤ Subgroup.normalizer (QbarAmb : Set (MulAut A)) :=
      hPsub_le_L.trans hQbarAmb_norm
    rw [hL_decomp] at hφkL
    obtain ⟨p, hp, a, ha, hpa⟩ := (mem_sup_iff_of_le_normalizer hPsub_norm).1 hφkL
    obtain ⟨ε, hε⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hQmap : (Q.subgroupOf K).map φ = QbarAmb := by
      rw [hQsub_eq, Subgroup.map_comap_eq_self hQbarAmb_le_L]
    rw [← hQmap] at hp
    obtain ⟨q, hqQ, hqφ⟩ := Subgroup.mem_map.mp hp
    have hqGQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hqQ
    have hqG : (q : G) ∈ K := q.2
    have hε' : a = φ ((⟨d', hd'K⟩ : K) ^ ε) := by
      rw [← hε, map_zpow]
    have hφk : φ ⟨k, hk⟩ = φ (q * (⟨d', hd'K⟩ : K) ^ ε) := by
      rw [map_mul, hpa, hqφ, hε']
    have hmulK : (q : G) * d' ^ ε ∈ K :=
      K.mul_mem hqG (Subgroup.zpow_mem (K := K) hd'K ε)
    have hk' : k * ((q : G) * d' ^ ε)⁻¹ ∈ K :=
      K.mul_mem hk (Subgroup.inv_mem (H := K) hmulK)
    have hc₀ : k * ((q : G) * d' ^ ε)⁻¹ ∈ Cc := by
      have h1 : φ (⟨k * ((q : G) * d' ^ ε)⁻¹, hk'⟩ : K) =
          φ (⟨k, hk⟩ * (q * (⟨d', hd'K⟩ : K) ^ ε)⁻¹) := rfl
      have h2 : φ (⟨k, hk⟩ * (q * (⟨d', hd'K⟩ : K) ^ ε)⁻¹) = 1 := by
        rw [map_mul, map_inv, hφk, mul_inv_cancel]
      exact (CFSG.GH72.normalizerMonoidHom_eq_one_iff hk').mp (h1.trans h2)
    refine ⟨k * ((q : G) * d' ^ ε)⁻¹, hc₀, (q : G), hqGQ, ε, ?_⟩
    group
  have hQbar_zp : Nat.card Qbar = 3 → QbarAmb = Subgroup.zpowers τu := by
    intro h3
    have hτuL1 : τuL ≠ 1 := fun h => hτu_ne (congrArg Subtype.val h)
    have hτu_ord : orderOf τuL = 3 := by
      have hdvd : orderOf τuL ∣ Nat.card Qbar :=
        Subgroup.orderOf_dvd_natCard (s := Qbar) (x := τuL) hτu_memQbar
      rw [h3] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hτuL1
      · exact h
    have hQbar_eq : Qbar = Subgroup.zpowers τuL := by
      apply le_antisymm
      · intro x hx
        have hcard_zp : Nat.card (Subgroup.zpowers τuL) = 3 := by
          rw [Nat.card_zpowers, hτu_ord]
        have hle : Subgroup.zpowers τuL ≤ Qbar := Subgroup.zpowers_le.mpr hτu_memQbar
        have heq : Qbar = Subgroup.zpowers τuL :=
          (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_zp, h3])).symm
        rw [heq] at hx
        exact hx
      · exact Subgroup.zpowers_le.mpr hτu_memQbar
    calc QbarAmb = Qbar.map L.subtype := rfl
      _ = (Subgroup.zpowers τuL).map L.subtype := by rw [hQbar_eq]
      _ = Subgroup.zpowers (L.subtype τuL) := MonoidHom.map_zpowers _ _
      _ = Subgroup.zpowers τu := rfl
  have hfix3 : Nat.card Qbar = 3 → ∀ k ∈ K, k * z₂ * k⁻¹ = z₂ := by
    intro h3 k hk
    have hQbar_zp' := hQbar_zp h3
    let Stab : Subgroup (MulAut A) :=
      MulAction.stabilizer (MulAut A) (⟨z₂, hz₂A⟩ : A)
    have hτu_fix : τu ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      apply Subtype.ext
      change u * z₂ * u⁻¹ = z₂
      exact huz₂
    have hτu_stab : τu ∈ Stab := by
      rw [MulAction.mem_stabilizer_iff]
      exact hτu_fix
    have hτ_fix : τ ⟨z₂, hz₂A⟩ = ⟨z₂, hz₂A⟩ := by
      apply Subtype.ext
      change d' * z₂ * d'⁻¹ = z₂
      exact hfixd'
    have hτ_stab : τ ∈ Stab := by
      rw [MulAction.mem_stabilizer_iff]
      exact hτ_fix
    have hQbar_stab : QbarAmb ≤ Stab := by
      rw [hQbar_zp']
      exact Subgroup.zpowers_le.mpr hτu_stab
    have hPsub_stab : Psub ≤ Stab := Subgroup.zpowers_le.mpr hτ_stab
    have hL_stab : L ≤ Stab := by
      rw [hL_decomp]
      exact sup_le hQbar_stab hPsub_stab
    have hφkL : φ ⟨k, hk⟩ ∈ L := MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    have hstab := hL_stab hφkL
    rw [MulAction.mem_stabilizer_iff] at hstab
    exact congrArg Subtype.val hstab
  have h3case : Cc.relIndex Q = 3 → False := by
    intro h3r
    have h3card : Nat.card Qbar = 3 := by rw [← hQ_index_card]; exact h3r
    obtain ⟨k, hkK, hkc⟩ := hz₂cK
    have h := hfix3 h3card k hkK
    rw [h] at hkc
    exact hcz₂ hkc.symm
  have hxcentS : ∀ x ∈ S₁, x ∈ Subgroup.centralizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hd.mem_iff.1 hy
    have h1 : y₁ * x = x * y₁ :=
      congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
        (⟨y₁, hy₁⟩ : S₁) ⟨x, hx⟩)
    have h2 : y₂ * x = x * y₂ := (hd.comm (x := x) (y := y₂) hx hy₂).symm
    calc y₁ * y₂ * x = y₁ * (y₂ * x) := by group
      _ = y₁ * (x * y₂) := by rw [h2]
      _ = y₁ * x * y₂ := by group
      _ = x * y₁ * y₂ := by rw [h1]
      _ = x * (y₁ * y₂) := by group
  have hnoXz₂ : ∀ x ∈ S₁, orderOf x = 2 → ¬ IsConj x z₂ := by
    intro x hx hxord hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hxcent : x ∈ Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G) := hxcentS x hx
    have hz₂cent : z₂ ∈ Subgroup.centralizer ((𝔖.S : Subgroup G) : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hz₂centS hy)
    have hg' : (g⁻¹)⁻¹ * x * g⁻¹ = z₂ := by simpa using hg
    obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer
      (p := 2) 𝔖.S x g⁻¹ hxcent (hg' ▸ hz₂cent)
    have hn' : z₂ = n⁻¹ * x * n := hg' ▸ hn
    have hx_eq : x = n * z₂ * n⁻¹ := by
      rw [hn']; group
    have hmem' : x ∈ ⁅S, S⁆ := by
      rw [hx_eq]
      have hSmap : S.map (MulAut.conj n).toMonoidHom = S :=
        CFSG.CGT.Foote81L6.TStruct.map_conj_eq_self_of_mem_normalizer hnN
      have hmap : (⁅S, S⁆).map (MulAut.conj n).toMonoidHom = ⁅S, S⁆ := by
        rw [Subgroup.map_commutator, hSmap]
      let f : G →* G := (MulAut.conj n).toMonoidHom
      have hf : f z₂ = n * z₂ * n⁻¹ := MulAut.conj_apply n z₂
      have h : f z₂ ∈ (⁅S, S⁆).map f := Subgroup.mem_map.mpr ⟨z₂, hz₂S', rfl⟩
      have h' : n * z₂ * n⁻¹ ∈ (⁅S, S⁆).map f := by rwa [hf] at h
      have hmap' : (⁅S, S⁆).map f = ⁅S, S⁆ := by
        rw [Subgroup.map_commutator]
        have : S.map f = S := by
          simpa [f] using CFSG.CGT.Foote81L6.TStruct.map_conj_eq_self_of_mem_normalizer hnN
        rw [this]
      rwa [hmap'] at h'
    have hxS₂ : x ∈ S₂ := by
      rw [hSS'] at hmem'
      exact (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact S₂.mul_mem (S₂.mul_mem (S₂.mul_mem ha hb) (S₂.inv_mem ha)) (S₂.inv_mem hb)) hmem'
    have hxbot : x ∈ S₁ ⊓ S₂ := ⟨hx, hxS₂⟩
    rw [hd.inf_eq, Subgroup.mem_bot] at hxbot
    rw [hxbot, orderOf_one] at hxord
    norm_num at hxord
  have h15case : Cc.relIndex Q = 15 → False := by
    intro h15
    haveI : Fintype ↥S₁ := Fintype.ofFinite _
    have hcardS₁ : Fintype.card ↥S₁ = 4 := by
      rw [← Nat.card_eq_fintype_card]; exact h₁.card_four
    obtain ⟨x, hx1⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥S₁) (by omega) (1 : ↥S₁)
    have hxS₁ : (x : G) ∈ S₁ := x.2
    have hxord : orderOf (x : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      refine orderOf_eq_prime ?_ (fun h => hx1 (Subtype.ext (by simpa using h)))
      rw [pow_two]
      simpa using IsKleinFour.mul_self x
    have hxA : (x : G) ∈ A := hS₁A hxS₁
    have hx1G : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨q, hqQ, hq⟩ := CFSG.GH72.exists_conj_eq_of_relIndex_eq_fifteen hA hQ_le_K h15
      z₂ hz₂A (x : G) hxA hz₂1 hx1G
    exact hnoXz₂ (x : G) hxS₁ hxord (isConj_iff.mpr ⟨q⁻¹, by
      rw [inv_inv, ← hq]; group⟩)

  have hd'C : d' ∉ Cc := by
    intro h
    have hd'C₂ : d' ∈ Subgroup.centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp h y (Subgroup.mem_inf.mp hy).1
    have hmem : d' ∈ S₂ ⊓ centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := ⟨hd'S₂, hd'C₂⟩
    rw [hd.isDih₂.inf_centralizer_four hV₂] at hmem
    exact hd'NotA₂ hmem
  have hd'c_mem : d' * c * d'⁻¹ ∈ A ⊓ S₂ :=
    (Subgroup.mem_normalizer_iff.mp hd'N_A₂ c).mp hcA₂
  have hunivA₂ : ∀ {y : G}, y ∈ A ⊓ S₂ → y = c * z₂ ∨ y = c ∨ y = z₂ ∨ y = 1 := by
    intro y hy
    haveI : Fintype ↥(A ⊓ S₂) := Fintype.ofFinite _
    haveI : IsKleinFour ↥(A ⊓ S₂) := isKleinFour_of_isFourIn hV₂
    have hy' : (⟨y, hy⟩ : ↥(A ⊓ S₂)) ∈ (Finset.univ : Finset ↥(A ⊓ S₂)) := Finset.mem_univ _
    have huniv := IsKleinFour.eq_finset_univ (G := ↥(A ⊓ S₂))
      (x := (⟨c, hcA₂⟩ : ↥(A ⊓ S₂))) (y := (⟨z₂, hz₂A₂⟩ : ↥(A ⊓ S₂)))
      (by intro h; exact hc1 (congrArg Subtype.val h))
      (by intro h; exact hz₂1 (congrArg Subtype.val h))
      (by intro h; exact hcz₂ (congrArg Subtype.val h))
    rw [← huniv] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with h1 | h2 | h3 | h4
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h2))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h3)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h4)))
  have hcz₂1 : c * z₂ ≠ 1 := by
    intro h
    apply hcz₂
    have h' := congrArg (fun t => t * z₂) h
    simpa [mul_assoc, hz₂2] using h'
  have hd'c_ne_c : d' * c * d'⁻¹ ≠ c := by
    intro h
    have hfixA₂ : ∀ w ∈ A ⊓ S₂, d' * w * d'⁻¹ = w := by
      intro w hw
      rcases hunivA₂ hw with h1 | h1 | h1 | h1
      · rw [h1]
        calc d' * (c * z₂) * d'⁻¹ = (d' * c * d'⁻¹) * (d' * z₂ * d'⁻¹) := by group
          _ = c * z₂ := by rw [h, hfixd']
      · rw [h1]; exact h
      · rw [h1]; exact hfixd'
      · rw [h1]; group
    have hd'C₂ : d' ∈ Subgroup.centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := hfixA₂ y hy
      have h' : d' * y = y * d' := by
        have hc := congrArg (fun t => t * d') h
        simpa [mul_assoc, hd'2] using hc
      exact h'.symm
    have hmem : d' ∈ S₂ ⊓ centralizer ((A ⊓ S₂ : Subgroup G) : Set G) := ⟨hd'S₂, hd'C₂⟩
    rw [hd.isDih₂.inf_centralizer_four hV₂] at hmem
    exact hd'NotA₂ hmem
  have hd'c_eq : d' * c * d'⁻¹ = c * z₂ := by
    rcases hunivA₂ hd'c_mem with h1 | h1 | h1 | h1
    · exact h1
    · exact absurd h1 hd'c_ne_c
    · exfalso
      have h2 : d' * (c * z₂) * d'⁻¹ = 1 := by
        calc d' * (c * z₂) * d'⁻¹ = (d' * c * d'⁻¹) * (d' * z₂ * d'⁻¹) := by group
          _ = 1 := by rw [h1, hfixd', hz₂2]
      have h3 : c * z₂ = 1 := by
        have h := congrArg (fun t => d'⁻¹ * t * d') h2
        simpa [mul_assoc] using h
      exact hcz₂1 h3
    · exfalso
      have h3 : c = 1 := by
        have h := congrArg (fun t => d'⁻¹ * t * d') h1
        simpa [mul_assoc] using h
      exact hc1 h3
  have hd'cz₂_eq : d' * (c * z₂) * d'⁻¹ = c := by
    calc d' * (c * z₂) * d'⁻¹ = (d' * c * d'⁻¹) * (d' * z₂ * d'⁻¹) := by group
      _ = c := by rw [hd'c_eq, hfixd', mul_assoc, hz₂2, mul_one]
  have hA₂_fix_d' : A ⊓ S₂ ⊓ Subgroup.centralizer ({d'} : Set G) =
      Subgroup.zpowers z₂ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyA₂, hyd'⟩ := Subgroup.mem_inf.mp hy
      have hfixy : d' * y * d'⁻¹ = y := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hyd'
        rw [← h]; group
      rcases hunivA₂ hyA₂ with h1 | h1 | h1 | h1
      · exfalso
        rw [h1, hd'cz₂_eq] at hfixy
        have h2 : z₂ = 1 := by
          have h := congrArg (fun t => c⁻¹ * t) hfixy
          simp only [← mul_assoc, inv_mul_cancel, one_mul] at h
          first | exact h | exact h.symm
        exact hz₂1 h2
      · exfalso
        rw [h1, hd'c_eq] at hfixy
        have h2 : z₂ = 1 := by
          have h := congrArg (fun t => c⁻¹ * t) hfixy
          simp only [← mul_assoc, inv_mul_cancel, one_mul] at h
          first | exact h | exact h.symm
        exact hz₂1 h2
      · rw [h1]; exact Subgroup.mem_zpowers z₂
      · rw [h1]; exact Subgroup.one_mem _
    · refine Subgroup.zpowers_le.mpr ⟨hz₂A₂, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hz₂centS₂ d' hd'S₂).symm
  have hCAd' : A ⊓ Subgroup.centralizer ({d'} : Set G) = S₁ ⊔ Subgroup.zpowers z₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxd⟩ := Subgroup.mem_inf.mp hx
      have hcomm : ∀ u ∈ S₁, ∀ v ∈ A ⊓ S₂, u * v = v * u :=
        fun u hu v hv => hd.comm hu (Subgroup.mem_inf.mp hv).2
      rw [hAsplit'] at hxA
      obtain ⟨s, hs, w, hw, rfl⟩ :=
        (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hxA
      have hxd' : d' * (s * w) * d'⁻¹ = s * w := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hxd
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      have hsd' : d' * s * d'⁻¹ = s := by rw [← hd.comm hs hd'S₂]; group
      have hwd' : d' * w * d'⁻¹ = w := by
        have hprod : d' * (s * w) * d'⁻¹ = (d' * s * d'⁻¹) * (d' * w * d'⁻¹) := by group
        rw [hprod, hsd'] at hxd'
        exact mul_left_cancel hxd'
      have hwd'' : d' * w = w * d' := by
        have := congrArg (fun t => t * d') hwd'
        simpa [mul_assoc] using this
      have hw' : w ∈ A ⊓ S₂ ⊓ Subgroup.centralizer ({d'} : Set G) :=
        ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr hwd''.symm⟩
      rw [hA₂_fix_d'] at hw'
      exact Subgroup.mul_mem (H := S₁ ⊔ Subgroup.zpowers z₂)
        (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hw')
    · refine sup_le (fun x hx => ⟨hS₁A hx, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hz₂A, ?_⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hd.comm hx hd'S₂)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz₂centS₂ d' hd'S₂).symm
  have hfix_u_S₁z₂ : ∀ x ∈ S₁ ⊔ Subgroup.zpowers z₂, u * x * u⁻¹ = x →
      x ∈ Subgroup.zpowers z₂ := by
    intro x hx hfixx
    have hcomm : ∀ s ∈ S₁, ∀ w ∈ Subgroup.zpowers z₂, s * w = w * s := by
      intro s hs w hw
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hm]
      have hc : Commute s z₂ := hd.comm hs hz₂S₂
      exact (hc.zpow_right m).eq
    obtain ⟨s, hs, w, hw, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hx
    have hcu : Commute u z₂ := by
      show u * z₂ = z₂ * u
      calc u * z₂ = u * z₂ * u⁻¹ * u := by group
        _ = z₂ * u := by rw [huz₂]
    have hwfix : u * w * u⁻¹ = w := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hm]
      rw [(hcu.zpow_right m).eq]
      group
    have hprod : u * (s * w) * u⁻¹ = (u * s * u⁻¹) * (u * w * u⁻¹) := by group
    have hsu : u * s * u⁻¹ = s := by
      rw [hprod, hwfix] at hfixx
      exact mul_right_cancel hfixx
    have hs1 : s = 1 := hfree s hs hsu
    simpa [hs1] using hw

  have hQ_fwd : ∀ e ∈ K, ∀ x, x ∈ A ⊓ centralizer (Q : Set G) →
      e * x * e⁻¹ ∈ A ⊓ centralizer (Q : Set G) := by
    intro e he x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp he x).mp hxA, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro y hy
    have hy' : e⁻¹ * y * e ∈ Q := by
      have hN : e⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.inv_mem (H := Subgroup.normalizer (Q : Set G)) (hKnormQ he)
      simpa using (Subgroup.mem_normalizer_iff.mp hN y).mp hy
    have hcomm := hxC (e⁻¹ * y * e) hy'
    calc y * (e * x * e⁻¹) = e * ((e⁻¹ * y * e) * x) * e⁻¹ := by group
      _ = e * (x * (e⁻¹ * y * e)) * e⁻¹ := by rw [hcomm]
      _ = (e * x * e⁻¹) * y := by group
  have hQ_iff : ∀ e ∈ K, ∀ x, (x ∈ A ⊓ centralizer (Q : Set G) ↔
      e * x * e⁻¹ ∈ A ⊓ centralizer (Q : Set G)) := by
    intro e he x
    constructor
    · exact hQ_fwd e he x
    · intro hx
      have h := hQ_fwd e⁻¹ (Subgroup.inv_mem (H := K) he) (e * x * e⁻¹) hx
      simpa [mul_assoc] using h
  have h21case : Cc.relIndex Q = 21 → False := by
    intro h21
    have hA₀card : Nat.card ↥(A ⊓ centralizer (Q : Set G)) = 2 :=
      CFSG.GH72.card_inf_centralizer_eq_two_of_relIndex_eq_twentyOne hA hQ_le_K h21
    obtain ⟨t, htA₀, ht1⟩ : ∃ t ∈ A ⊓ centralizer (Q : Set G), t ≠ 1 := by
      haveI : Fintype ↥(A ⊓ centralizer (Q : Set G)) := Fintype.ofFinite _
      have hcard : Fintype.card ↥(A ⊓ centralizer (Q : Set G)) = 2 := by
        rw [← Nat.card_eq_fintype_card]; exact hA₀card
      obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card
        (α := ↥(A ⊓ centralizer (Q : Set G))) (by omega)
        (1 : ↥(A ⊓ centralizer (Q : Set G)))
      exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
    have htA : t ∈ A := (Subgroup.mem_inf.mp htA₀).1
    have ht2 : t * t = 1 := congrArg Subtype.val (CFSG.GH72.mul_self_eq_one_of_isE16 hA ⟨t, htA⟩)
    have htord : orderOf t = 2 := orderOf_eq_prime (x := t) (p := 2)
      (by rw [pow_two]; exact ht2) ht1
    have hA₀eq : A ⊓ centralizer (Q : Set G) = Subgroup.zpowers t := by
      apply le_antisymm
      · intro y hy
        have hle : Subgroup.zpowers t ≤ A ⊓ centralizer (Q : Set G) :=
          Subgroup.zpowers_le.mpr htA₀
        have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by
          rw [Nat.card_zpowers]; exact htord
        have heq : Subgroup.zpowers t = A ⊓ centralizer (Q : Set G) :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hcardt, hA₀card])
        rw [heq]
        exact hy
      · exact Subgroup.zpowers_le.mpr htA₀
    have ht_d' : d' * t * d'⁻¹ = t := by
      have hmem : d' * t * d'⁻¹ ∈ A ⊓ centralizer (Q : Set G) := hQ_fwd d' hd'K t htA₀
      rw [hA₀eq] at hmem
      have hne : d' * t * d'⁻¹ ≠ 1 := by
        intro h
        apply ht1
        have h' := congrArg (fun s => d'⁻¹ * s * d') h
        simpa [mul_assoc] using h'
      rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers ht2 hmem with h | h
      · exact absurd h hne
      · exact h
    have ht_Cd' : t ∈ A ⊓ Subgroup.centralizer ({d'} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨htA, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have h := congrArg (fun s => s * d') ht_d'
        have h2 : d' * t = t * d' := by simpa [mul_assoc] using h
        exact h2.symm)
    have ht_sup : t ∈ S₁ ⊔ Subgroup.zpowers z₂ := by
      rw [hCAd'] at ht_Cd'
      exact ht_Cd'
    have ht_u : u * t * u⁻¹ = t := by
      have htCQ : t ∈ Subgroup.centralizer (Q : Set G) := (Subgroup.mem_inf.mp htA₀).2
      have h := Subgroup.mem_centralizer_iff.mp htCQ u huQ
      calc u * t * u⁻¹ = t * u * u⁻¹ := by rw [h]
        _ = t := by group
    have ht_z₂ : t = z₂ := by
      have hz := hfix_u_S₁z₂ t ht_sup ht_u
      rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hz₂2 hz with h | h
      · exact absurd h ht1
      · exact h
    have hA₀z₂ : A ⊓ centralizer (Q : Set G) = Subgroup.zpowers z₂ := by
      rw [hA₀eq, ht_z₂]
    obtain ⟨k, hkK, hkc⟩ := hz₂cK
    have hz₂A₀ : z₂ ∈ A ⊓ centralizer (Q : Set G) := by
      rw [hA₀z₂]; exact Subgroup.mem_zpowers z₂
    have hk_mem : k * z₂ * k⁻¹ ∈ A ⊓ centralizer (Q : Set G) :=
      (hQ_iff k hkK z₂).mp hz₂A₀
    rw [hA₀z₂] at hk_mem
    have hk_ne1 : k * z₂ * k⁻¹ ≠ 1 := by
      intro h
      apply hz₂1
      have h' := congrArg (fun s => k⁻¹ * s * k) h
      simpa [mul_assoc] using h'
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hz₂2 hk_mem with h | h
    · exact absurd h hk_ne1
    · rw [h] at hkc
      exact hcz₂ hkc.symm
  have hQ9 : Cc.relIndex Q = 9 := by
    rcases CFSG.GH72.relIndex_centralizer_mem_of_odd hA hQ_le_K hQ_index_odd with
      h1 | h3 | h5 | h7 | h9 | h15 | h21
    · exfalso
      rw [h1] at h3dvd
      omega
    · exact absurd h3 h3case
    · exfalso
      rw [h5] at h3dvd
      omega
    · exfalso
      rw [h7] at h3dvd
      omega
    · exact h9
    · exact absurd h15 h15case
    · exact absurd h21 h21case
  have hQbarAmb_abelian : IsMulCommutative ↥QbarAmb := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    rw [hQbarAmb_card', ← hQ_index_card, hQ9]
    norm_num
  obtain ⟨hVcard, hVinv, hVorb⟩ :=
    CFSG.GH72.conj_orbit_eq_of_relIndex_eq_nine hA hQ_le_K hQ9 huQ huCA hz₂A hz₂1 huz₂
  have hK_orbit : ∀ k ∈ K, ∃ q ∈ Q, k * z₂ * k⁻¹ = q * z₂ * q⁻¹ := by
    intro k hk
    obtain ⟨c₀, hc₀C, q, hqQ, ε, hk_eq⟩ := hK_decomp k hk
    refine ⟨q, hqQ, ?_⟩
    have hc₀z : c₀ * z₂ * c₀⁻¹ = z₂ := hfixC c₀ hc₀C
    have hd'z : d' ^ ε * z₂ * (d' ^ ε)⁻¹ = z₂ := by
      have hc : Commute d' z₂ := hz₂centS₂ d' hd'S₂
      rw [(hc.zpow_left ε).eq]
      group
    have hqzA : q * z₂ * q⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hQ_le_K hqQ) z₂).mp hz₂A
    have hc₀comm : c₀ * (q * z₂ * q⁻¹) * c₀⁻¹ = q * z₂ * q⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp hc₀C (q * z₂ * q⁻¹) hqzA
      calc c₀ * (q * z₂ * q⁻¹) * c₀⁻¹ = (q * z₂ * q⁻¹) * c₀ * c₀⁻¹ := by rw [h]
        _ = q * z₂ * q⁻¹ := by group
    rw [hk_eq]
    calc c₀ * (q * d' ^ ε) * z₂ * (c₀ * (q * d' ^ ε))⁻¹
        = c₀ * (q * (d' ^ ε * z₂ * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹ := by group
      _ = c₀ * (q * z₂ * q⁻¹) * c₀⁻¹ := by rw [hd'z]
      _ = q * z₂ * q⁻¹ := hc₀comm
  have huz₂' : z₂ * u = u * z₂ := by
    have h := congrArg (fun t => t * u) huz₂
    simpa [mul_assoc] using h.symm
  have hz₂V : z₂ ∈ A ⊓ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hz₂A, Subgroup.mem_centralizer_singleton_iff.mpr huz₂'⟩
  have hcV : c ∈ A ⊓ Subgroup.centralizer ({u} : Set G) := by
    obtain ⟨k, hkK, hkc⟩ := hz₂cK
    obtain ⟨q, hqQ, hq⟩ := hK_orbit k hkK
    have hc_orbit : c ∈ {b : G | ∃ q ∈ Q, q * z₂ * q⁻¹ = b} :=
      ⟨q, hqQ, by rw [← hq, hkc]⟩
    rw [hVorb] at hc_orbit
    exact hc_orbit.1
  have hA₂_le_V : A ⊓ S₂ ≤ A ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [hA₂eq]
    exact sup_le (Subgroup.zpowers_le.mpr hcV) (Subgroup.zpowers_le.mpr hz₂V)
  have hVeq : A ⊓ Subgroup.centralizer ({u} : Set G) = A ⊓ S₂ :=
    (Subgroup.eq_of_le_of_card_ge hA₂_le_V (by rw [hVcard, hA₂card])).symm
  have hQY : ∀ q ∈ Q, ∀ y ∈ A ⊓ S₂, q * y * q⁻¹ ∈ A ⊓ S₂ := by
    intro q hq y hy
    rw [← hVeq]
    exact hVinv q hq y (hVeq.symm ▸ hy)
  have hQX : ∀ q ∈ Q, ∀ x ∈ S₁, q * x * q⁻¹ ∈ S₁ := by
    intro q hq x hx
    have hqK : q ∈ K := hQ_le_K hq
    have hqbar : φ ⟨q, hqK⟩ ∈ QbarAmb := by
      have hqsub : (⟨q, hqK⟩ : K) ∈ Q.subgroupOf K := hq
      rw [hQsub_eq] at hqsub
      exact Subgroup.mem_comap.mp hqsub
    have hcomm_auto : φ ⟨q, hqK⟩ * φ ⟨u, huK⟩ = φ ⟨u, huK⟩ * φ ⟨q, hqK⟩ :=
      congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨φ ⟨q, hqK⟩, hqbar⟩ : ↥QbarAmb) ⟨φ ⟨u, huK⟩, hτu_memQbarAmb⟩)
    have hgu : ∀ a ∈ A, q * (u * a * u⁻¹) * q⁻¹ = u * (q * a * q⁻¹) * u⁻¹ :=
      (CFSG.GH72.normalizerMonoidHom_commute_iff huK hqK).mp hcomm_auto
    have hcard : Nat.card ↥S₁ * Nat.card ↥(A ⊓ Subgroup.centralizer ({u} : Set G)) = 16 := by
      rw [hVcard, h₁.card_four]
    exact CFSG.GH72.conj_mem_of_commute_of_inf_centralizer hA huK hqK hS₁A
      (fun y hy => (Subgroup.mem_normalizer_iff.mp huS₁ y).mp hy) hfree hcard hgu x hx
  have hK_S₁_fwd : ∀ k ∈ K, ∀ x ∈ S₁, k * x * k⁻¹ ∈ S₁ := by
    intro k hk x hx
    obtain ⟨c₀, hc₀C, q, hqQ, ε, rfl⟩ := hK_decomp k hk
    have hx₁ : d' ^ ε * x * (d' ^ ε)⁻¹ = x := by
      have hc : Commute d' x := (hd.comm (x := x) (y := d') hx hd'S₂).symm
      rw [(hc.zpow_left ε).eq]
      group
    have hx₂ : q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹ ∈ S₁ := by
      rw [hx₁]; exact hQX q hqQ x hx
    have hx₃ : c₀ * (q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹ =
        q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hc₀C
        (q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹) (hS₁A hx₂)
      calc c₀ * (q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹
          = (q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹) * c₀ * c₀⁻¹ := by rw [hcomm]
        _ = q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹ := by group
    have hfinal : c₀ * (q * d' ^ ε) * x * (c₀ * (q * d' ^ ε))⁻¹ =
        c₀ * (q * (d' ^ ε * x * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹ := by group
    rw [hfinal, hx₃]
    exact hx₂
  have hKS₁ : K ≤ Subgroup.normalizer (S₁ : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x; constructor
    · exact hK_S₁_fwd k hk x
    · intro hx
      have h := hK_S₁_fwd k⁻¹ (Subgroup.inv_mem (H := K) hk) (k * x * k⁻¹) hx
      simpa [mul_assoc] using h
  have hK_A₂_fwd : ∀ k ∈ K, ∀ y ∈ A ⊓ S₂, k * y * k⁻¹ ∈ A ⊓ S₂ := by
    intro k hk y hy
    obtain ⟨c₀, hc₀C, q, hqQ, ε, rfl⟩ := hK_decomp k hk
    have hpow : d' ^ ε ∈ Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G) :=
      Subgroup.zpow_mem (Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G)) hd'N_A₂ ε
    have hy₁ : d' ^ ε * y * (d' ^ ε)⁻¹ ∈ A ⊓ S₂ :=
      (Subgroup.mem_normalizer_iff.mp hpow y).mp hy
    have hy₂ : q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹ ∈ A ⊓ S₂ :=
      hQY q hqQ (d' ^ ε * y * (d' ^ ε)⁻¹) hy₁
    have hc₀A₂ : c₀ * (q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹ =
        q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹ := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hc₀C
        (q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹) (Subgroup.mem_inf.mp hy₂).1
      calc c₀ * (q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹
          = (q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹) * c₀ * c₀⁻¹ := by rw [hcomm]
        _ = q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹ := by group
    have hfinal : c₀ * (q * d' ^ ε) * y * (c₀ * (q * d' ^ ε))⁻¹ =
        c₀ * (q * (d' ^ ε * y * (d' ^ ε)⁻¹) * q⁻¹) * c₀⁻¹ := by group
    rw [hfinal, hc₀A₂]
    exact hy₂
  have hKA₂ : K ≤ Subgroup.normalizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y; constructor
    · exact hK_A₂_fwd k hk y
    · intro hy
      have h := hK_A₂_fwd k⁻¹ (Subgroup.inv_mem (H := K) hk) (k * y * k⁻¹) hy
      simpa [mul_assoc] using h

  have hKA₂' : K ≤ Subgroup.normalizer ((S₂ ⊓ A : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact hKA₂
  refine ⟨⟨Q, hC_le_Q, hQ_le_K, hQnorm_sub, hQ9, 1, ?_⟩, hKS₁, hKA₂', ?_⟩
  · have hmul : Cc.relIndex Q * Q.relIndex K = Cc.relIndex K :=
      Subgroup.relIndex_mul_relIndex (H := Cc) (K := Q) (L := K) hC_le_Q hQ_le_K
    have hL18 : Nat.card L = 18 := by
      have hcard := hQbar_compl.card_mul_card
      rw [hPsyl_eq, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact hτL2) hτL1] at hcard
      rw [← hQ_index_card, hQ9] at hcard
      omega
    have hKcard : Cc.relIndex K = 18 := by rw [← hL_card]; exact hL18
    change Q.relIndex K = 2
    have h9 : 9 * Q.relIndex K = 9 * 2 := by
      calc 9 * Q.relIndex K = Cc.relIndex Q * Q.relIndex K := by rw [hQ9]
        _ = Cc.relIndex K := hmul
        _ = 18 := hKcard
        _ = 9 * 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9) h9
  · intro v hv w hw hv2 hw2 hvS₁ hvS₂ hwS₁ hwS₂
    have hXbot : S₁ ⊓ (A ⊓ S₂) = ⊥ := by
      rw [eq_bot_iff]
      calc S₁ ⊓ (A ⊓ S₂) ≤ S₁ ⊓ S₂ := inf_le_inf_left S₁ inf_le_right
        _ = ⊥ := hd.inf_eq
    have hvA₂ : v ∉ A ⊓ S₂ := fun h => hvS₂ (Subgroup.mem_inf.mp h).2
    have hwA₂ : w ∉ A ⊓ S₂ := fun h => hwS₂ (Subgroup.mem_inf.mp h).2
    obtain ⟨q, hqQ, hq⟩ := CFSG.GH72.exists_conj_eq_of_relIndex_eq_nine hA hQ_le_K hQ9
      hS₁A (inf_le_left : A ⊓ S₂ ≤ A) h₁.card_four hA₂card hXbot hQX hQY
      v hv w hw hvS₁ hvA₂ hwS₁ hwA₂
    exact ⟨q, hQ_le_K hqQ, hq⟩

end Sec3Setting

end CFSG.GH72
