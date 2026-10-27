module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped Pointwise

private theorem elemAvoid_card_sup_mul_card_of_inf_eq_bot {X : Type*} [Group X]
    (A B : Subgroup X) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun x =>
    ⟨(x.1 : X) * (x.2 : X), Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      have h' : (a1 : X) * (b1 : X) = (a2 : X) * (b2 : X) := Subtype.ext_iff.mp h
      have hd : (a2 : X)⁻¹ * (a1 : X) = (b2 : X) * (b1 : X)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc (a2 : X)⁻¹ * (a1 : X) * (b1 : X)
            = (a2 : X)⁻¹ * ((a1 : X) * (b1 : X)) := by group
          _ = (a2 : X)⁻¹ * ((a2 : X) * (b2 : X)) := by rw [h']
          _ = (b2 : X) := by group
      have hm : (a2 : X)⁻¹ * (a1 : X) ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a2.2) a1.2, by
          rw [hd]; exact B.mul_mem b2.2 (B.inv_mem b1.2)⟩
      rw [hinf] at hm
      have h1 : (a2 : X)⁻¹ * (a1 : X) = 1 := Subgroup.mem_bot.mp hm
      have ha : (a1 : X) = (a2 : X) := by
        calc (a1 : X) = (a2 : X) * ((a2 : X)⁻¹ * (a1 : X)) := by group
          _ = (a2 : X) * 1 := by rw [h1]
          _ = (a2 : X) := mul_one _
      have hb : (b1 : X) = (b2 : X) := by
        have hh := h'
        rw [ha] at hh
        exact mul_left_cancel hh
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · intro x
      let M : Subgroup X :=
        { carrier := (A : Set X) * (B : Set X)
          mul_mem' := by
            rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
            exact ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, by
              calc (a1 * a2) * (b1 * b2) = a1 * (a2 * b1) * b2 := by group
                _ = a1 * (b1 * a2) * b2 := by rw [hcomm a2 ha2 b1 hb1]
                _ = (a1 * b1) * (a2 * b2) := by group⟩
          one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
          inv_mem' := by
            rintro _ ⟨a, ha, b, hb, rfl⟩
            exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb,
              (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).trans (by group)⟩ }
      have hMsup : A ⊔ B ≤ M :=
        sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
               (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
      have hx : (x : X) ∈ (A : Set X) * (B : Set X) := hMsup x.2
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

theorem exists_isElemTwo_three_avoiding {G : Type} [Group G] {F : Subgroup G} (hF : IsElemTwo 5 F)
    {u : G} (hu : u ∈ F) (hu1 : u ≠ 1) : ∃ E : Subgroup G, E ≤ F ∧ IsElemTwo 3 E ∧ u ∉ E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFab : CFSG.Open.IsElemAbelian 2 F := hF.1
  have hFcomm : IsMulCommutative ↥F := hFab.1
  have hFsq : ∀ x ∈ F, x ^ 2 = 1 := hFab.2
  have hFcard : Nat.card ↥F = 32 := by simpa using hF.2
  haveI : IsMulCommutative ↥F := hFcomm
  have hFel : IsElementaryAbelian 2 ↥F :=
    { toIsMulCommutative := hFcomm
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        fun x => Subtype.ext (hFsq x x.2) }
  haveI : IsElementaryAbelian 2 ↥F := hFel
  let uF : ↥F := ⟨u, hu⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 ↥F (Subgroup.zpowers uF)
  have huF2 : uF ^ 2 = 1 := Subtype.ext (hFsq u hu)
  have huF1 : uF ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have huForder : orderOf uF = 2 := orderOf_eq_prime huF2 huF1
  have huFcard : Nat.card (Subgroup.zpowers uF) = 2 := by rw [Nat.card_zpowers uF, huForder]
  have hcomm1 : ∀ a ∈ Subgroup.zpowers uF, ∀ b ∈ C, a * b = b * a :=
    fun a _ b _ => mul_comm' a b
  have hprod1 :=
    elemAvoid_card_sup_mul_card_of_inf_eq_bot (Subgroup.zpowers uF) C hcomm1 hC.inf_eq_bot
  rw [hC.sup_eq_top, Subgroup.card_top] at hprod1
  have hCcard : Nat.card ↥C = 16 := by
    rw [hFcard, huFcard] at hprod1
    omega
  have huF_notMem_C : uF ∉ C := by
    intro huFC
    have hmem : uF ∈ Subgroup.zpowers uF ⊓ C := ⟨Subgroup.mem_zpowers uF, huFC⟩
    rw [hC.inf_eq_bot] at hmem
    exact huF1 (Subgroup.mem_bot.mp hmem)
  have hC_ne_bot : C ≠ ⊥ := by
    intro hCbot
    have htop : (⊤ : Subgroup ↥F) = Subgroup.zpowers uF := by
      rw [← hC.sup_eq_top, hCbot, sup_bot_eq]
    have hcard : Nat.card ↥F = 2 := by
      calc Nat.card ↥F = Nat.card (⊤ : Subgroup ↥F) := (Subgroup.card_top).symm
        _ = Nat.card (Subgroup.zpowers uF) := by rw [htop]
        _ = orderOf uF := Nat.card_zpowers uF
        _ = 2 := huForder
    rw [hFcard] at hcard
    norm_num at hcard
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC_ne_bot
  have hCcomm : IsMulCommutative ↥C := inferInstance
  haveI : IsMulCommutative ↥C := hCcomm
  have hCel : IsElementaryAbelian 2 ↥C :=
    { toIsMulCommutative := hCcomm
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        exact hFsq (x : ↥F) (x : ↥F).2 }
  haveI : IsElementaryAbelian 2 ↥C := hCel
  obtain ⟨D, hD⟩ := IsElementaryAbelian.exists_isCompl 2 ↥C (Subgroup.zpowers w)
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hFsq (w : ↥F) (w : ↥F).2
  have hworder : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have hwcard : Nat.card (Subgroup.zpowers w) = 2 := by rw [Nat.card_zpowers w, hworder]
  have hcomm2 : ∀ a ∈ Subgroup.zpowers w, ∀ b ∈ D, a * b = b * a :=
    fun a _ b _ => mul_comm' a b
  have hprod2 :=
    elemAvoid_card_sup_mul_card_of_inf_eq_bot (Subgroup.zpowers w) D hcomm2 hD.inf_eq_bot
  rw [hD.sup_eq_top, Subgroup.card_top] at hprod2
  have hDcard : Nat.card ↥D = 8 := by
    rw [hCcard, hwcard] at hprod2
    omega
  let E' : Subgroup ↥F := D.map C.subtype
  have hE'C : E' ≤ C := Subgroup.map_subtype_le D
  let E : Subgroup G := E'.map F.subtype
  have hEcard : Nat.card ↥E = Nat.card ↥D := by
    dsimp only [E, E']
    rw [Subgroup.card_map_of_injective F.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective]
  have hEF : E ≤ F := Subgroup.map_subtype_le E'
  have hEcomm : IsMulCommutative ↥E := isMulCommutative_anti hEF
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨hEcomm, fun x hx => hFsq x (hEF hx)⟩
  have hu_notMem_E : u ∉ E := by
    intro huE
    have huF_E' : uF ∈ E' := by
      rcases Subgroup.mem_map.mp huE with ⟨y, hy, hyu⟩
      have : y = uF := Subtype.ext hyu
      rwa [this] at hy
    exact huF_notMem_C (hE'C huF_E')
  exact ⟨E, hEF, ⟨hEel, by rw [hEcard, hDcard]; norm_num⟩, hu_notMem_E⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
