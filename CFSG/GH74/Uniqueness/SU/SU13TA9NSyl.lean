module

public import CFSG.GH74.Uniqueness.SU.SU13TA9NStruct
public import CFSG.GH74.Uniqueness.SU.SU13TA9MPart

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU4

@[expose] def jz : Perm (Fin 9) := pr2 * nuc

@[expose] def SL : List (Perm (Fin 9)) :=
  [1, nua * nub, nua * nuc, nub * nuc, jz, jz * (nua * nub), jz * (nua * nuc), jz * (nub * nuc)]

theorem SL_mul {a b : Perm (Fin 9)} (ha : a ∈ SL) (hb : b ∈ SL) : a * b ∈ SL := by
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem SL_inv {a : Perm (Fin 9)} (ha : a ∈ SL) : a⁻¹ ∈ SL := by
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem SL_even {a : Perm (Fin 9)} (ha : a ∈ SL) : Perm.sign a = 1 := by
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem SL_nodup : SL.Nodup := by decide

@[expose] def Sbar : Subgroup (alternatingGroup (Fin 9)) where
  carrier := {x | (x : Perm (Fin 9)) ∈ SL}
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ SL
    rw [Subgroup.coe_mul]
    exact SL_mul ha hb
  one_mem' := by
    show ((1 : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ SL
    rw [OneMemClass.coe_one]
    simp [SL]
  inv_mem' := fun {a} ha => by
    show ((a⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ SL
    rw [InvMemClass.coe_inv]
    exact SL_inv ha

theorem card_Sbar : Nat.card Sbar = 8 := by
  have hlen : SL.length = 8 := by decide
  let f : Fin 8 → Sbar := fun i =>
    ⟨⟨SL.get ⟨i, by omega⟩, Perm.mem_alternatingGroup.mpr (SL_even (List.get_mem _ _))⟩,
      List.get_mem _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have h1 : SL.get ⟨i, by omega⟩ = SL.get ⟨j, by omega⟩ := congrArg (fun x : Sbar => ((x : alternatingGroup (Fin 9)) : Perm (Fin 9))) h
      have := (List.Nodup.get_inj_iff SL_nodup).mp h1
      exact Fin.ext (by simpa using this)
    · rintro ⟨⟨x, hx⟩, hxS⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (show x ∈ SL from hxS)
      refine ⟨⟨i, by omega⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hi
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem mem_NE_of_InE' {σ : Perm (Fin 9)} (hσ : σ ∈ alternatingGroup (Fin 9))
    (ha : InE (σ * pa * σ⁻¹)) (hb : InE (σ * pb * σ⁻¹)) (hc : InE (σ * pc * σ⁻¹)) :
    (⟨σ, hσ⟩ : alternatingGroup (Fin 9)) ∈ NE :=
  mem_NE_of_InE (σ := ⟨σ, hσ⟩) ha hb hc

theorem Sbar_le_NE : Sbar ≤ NE := by
  rintro ⟨σ, hσ⟩ hx
  have hx' : σ ∈ SL := hx
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact mem_NE_of_InE' hσ (by decide) (by decide) (by decide)

theorem card_NE : Nat.card NE = 648 := by
  have h81 : 81 ∣ Nat.card NE := by
    have := Subgroup.card_dvd_of_le Pst_le_NE
    rwa [card_Pst] at this
  have h8 : 8 ∣ Nat.card NE := by
    have := Subgroup.card_dvd_of_le Sbar_le_NE
    rwa [card_Sbar] at this
  have h648 : 648 ∣ Nat.card NE := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 81) h8 h81
    simpa using this
  exact le_antisymm card_NE_le (Nat.le_of_dvd Nat.card_pos h648)

theorem isSylowIn_Sbar : IsSylowIn NE Sbar := by
  refine isSylowIn_iff_card.mpr ⟨Sbar_le_NE, 3, 81, ?_, by decide, ?_⟩
  · rw [card_Sbar]; norm_num
  · rw [card_NE]; norm_num

@[expose] def sJ : alternatingGroup (Fin 9) :=
  ⟨jz, Perm.mem_alternatingGroup.mpr (SL_even (by simp [SL]))⟩

theorem sJ_mem : sJ ∈ Sbar := show jz ∈ SL by simp [SL]

@[expose] def sA : alternatingGroup (Fin 9) :=
  ⟨nua * nuc, Perm.mem_alternatingGroup.mpr (SL_even (by simp [SL]))⟩

theorem sA_mem : sA ∈ Sbar := show nua * nuc ∈ SL by simp [SL]

theorem Sbar_center {y : alternatingGroup (Fin 9)} (hy : y ∈ Sbar)
    (hc : ∀ s ∈ Sbar, s * y = y * s) : y = 1 ∨ (y : Perm (Fin 9)) = nua * nub := by
  obtain ⟨σ, hσ⟩ := y
  have hx' : σ ∈ SL := hy
  have hJ : jz * σ = σ * jz := congrArg Subtype.val (hc sJ sJ_mem)
  have hA : (nua * nuc) * σ = σ * (nua * nuc) := congrArg Subtype.val (hc sA sA_mem)
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hJ (by decide)
  · exact absurd hJ (by decide)
  · exact absurd hA (by decide)
  · exact absurd hA (by decide)
  · exact absurd hA (by decide)
  · exact absurd hA (by decide)

theorem exists_conj_et {u : alternatingGroup (Fin 9)} (hu : u ∈ NE) (hu2 : u * u = 1)
    (hmoved : (u : Perm (Fin 9)).support.card = 8) : ∃ g ∈ NE, g * u * g⁻¹ = et := by
  have hu1 : u ≠ 1 := fun h => by
    rw [h] at hmoved
    revert hmoved
    decide
  have hord : orderOf u = 2 := orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) (by rw [pow_two]; exact hu2) hu1
  have hK2 : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hord]; norm_num)
  have hKN : zpowers u ≤ NE := Subgroup.zpowers_le.mpr hu
  obtain ⟨P, hP, hKP⟩ := exists_isSylowIn_ge hKN hK2
  obtain ⟨c, hc, hcQ⟩ := hP.exists_conj_eq isSylowIn_Sbar
  have hv : c * u * c⁻¹ ∈ Sbar := hcQ ▸ mem_conjSub_of_mem (hKP (Subgroup.mem_zpowers u))
  have hv2 : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
    calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hvsupp : ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 8 := by
    have : ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
        (c : Perm (Fin 9)) * (u : Perm (Fin 9)) * (c : Perm (Fin 9))⁻¹ := rfl
    rw [this, Equiv.Perm.card_support_conj]
    exact hmoved
  have hcase : ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) = jz ∨
      ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) = jz * (nua * nub) := by
    have h2 : ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) *
        ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 1 := congrArg Subtype.val hv2
    have hvSL : ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ SL := hv
    generalize ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) = w at h2 hvsupp hvSL ⊢
    simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at hvSL
    rcases hvSL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hvsupp (by decide)
    · exact absurd hvsupp (by decide)
    · exact absurd hvsupp (by decide)
    · exact absurd hvsupp (by decide)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
  rcases hcase with h | h
  · refine ⟨ec * c, NE.mul_mem (Ebar_le_NE ec_mem_Ebar) hc, ?_⟩
    have : (ec * c) * u * (ec * c)⁻¹ = ec * (c * u * c⁻¹) * ec⁻¹ := by group
    rw [this]
    apply Subtype.ext
    show (ec : Perm (Fin 9)) * ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) *
      (ec : Perm (Fin 9))⁻¹ = (et : Perm (Fin 9))
    rw [h]
    decide
  · refine ⟨ec * sA * c, NE.mul_mem (NE.mul_mem (Ebar_le_NE ec_mem_Ebar) (Sbar_le_NE sA_mem)) hc, ?_⟩
    have : (ec * sA * c) * u * (ec * sA * c)⁻¹ = ec * sA * (c * u * c⁻¹) * sA⁻¹ * ec⁻¹ := by group
    rw [this]
    apply Subtype.ext
    show (ec : Perm (Fin 9)) * (sA : Perm (Fin 9)) *
      ((c * u * c⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) * (sA : Perm (Fin 9))⁻¹ *
      (ec : Perm (Fin 9))⁻¹ = (et : Perm (Fin 9))
    rw [h]
    decide

theorem et_mem_NE : et ∈ NE :=
  mem_NE_of_conj (by rw [et_mul_ea]; exact eb_mem_Ebar) (by rw [et_mul_eb]; exact ea_mem_Ebar)
    (by rw [et_mul_ec]; exact Ebar.inv_mem ec_mem_Ebar)

theorem et_mul_g1 : et * (ea * eb * ec) * et⁻¹ = ea * eb * ec⁻¹ := by
  calc et * (ea * eb * ec) * et⁻¹ = (et * ea * et⁻¹) * (et * eb * et⁻¹) * (et * ec * et⁻¹) := by group
    _ = eb * ea * ec⁻¹ := by rw [et_mul_ea, et_mul_eb, et_mul_ec]
    _ = ea * eb * ec⁻¹ := by rw [commute_ea_eb.eq]

theorem g1_mul_g2 : (ea * eb * ec) * (ea * eb * ec⁻¹) = (ea * eb) ^ 2 := Subtype.ext (by decide)

theorem g1_mul_g2_inv : (ea * eb * ec) * (ea * eb * ec⁻¹)⁻¹ = ec ^ 2 := Subtype.ext (by decide)

theorem ea_mul_eb_eq : ea * eb = ((ea * eb) ^ 2) ^ 2 := Subtype.ext (by decide)

theorem ec_eq : ec = (ec ^ 2) ^ 2 := Subtype.ext (by decide)

theorem mem_Ebar_of_mem_Pst_conj {k : alternatingGroup (Fin 9)} (h1 : k ∈ Pst)
    (h2 : et⁻¹ * k * et ∈ Pst) : k ∈ Ebar := by
  have hg1 : Commute k (ea * eb * ec) := (Subgroup.mem_centralizer_singleton_iff.mp h1)
  have hg2' : Commute (et⁻¹ * k * et) (ea * eb * ec) :=
    (Subgroup.mem_centralizer_singleton_iff.mp h2)
  have hg2 : Commute k (ea * eb * ec⁻¹) := by
    have h := congrArg (fun y => et * y * et⁻¹) (hg2'.eq)
    have h3 : et * ((et⁻¹ * k * et) * (ea * eb * ec)) * et⁻¹ =
        k * (et * (ea * eb * ec) * et⁻¹) := by group
    have h4 : et * ((ea * eb * ec) * (et⁻¹ * k * et)) * et⁻¹ =
        (et * (ea * eb * ec) * et⁻¹) * k := by group
    rw [h3, h4, et_mul_g1] at h
    exact h
  have hA : Commute k ((ea * eb) ^ 2) := by
    rw [← g1_mul_g2]; exact hg1.mul_right hg2
  have hC : Commute k (ec ^ 2) := by
    rw [← g1_mul_g2_inv]; exact hg1.mul_right hg2.inv_right
  have hA' : Commute k (ea * eb) := by
    rw [ea_mul_eb_eq]; exact hA.pow_right 2
  have hC' : Commute k ec := by
    rw [ec_eq]; exact hC.pow_right 2
  have hkM : k ∈ Mb := Subgroup.mem_centralizer_singleton_iff.mpr hA'.eq
  rcases mem_Mb_cases hkM with h | h
  · exact h
  · exfalso
    set e0 : alternatingGroup (Fin 9) := k * et⁻¹ with he0
    have hk : k = e0 * et := by rw [he0]; group
    have hcomm : ec * e0 = e0 * ec := (Ebar_comm ec ec_mem_Ebar e0 h).eq
    have hkc : (e0 * et) * ec = ec * (e0 * et) := by rw [← hk]; exact hC'.eq
    have h5 : et * ec = ec * et := by
      refine mul_left_cancel (a := e0) ?_
      calc e0 * (et * ec) = (e0 * et) * ec := by group
        _ = ec * (e0 * et) := hkc
        _ = (ec * e0) * et := by group
        _ = (e0 * ec) * et := by rw [hcomm]
        _ = e0 * (ec * et) := by group
    have h6 := congrArg Subtype.val h5
    revert h6
    decide

theorem le_Ebar_of_normal_odd {K : Subgroup (alternatingGroup (Fin 9))} (hKN : K ≤ NE)
    (hnorm : ∀ g ∈ NE, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hodd : Odd (Nat.card K)) : K ≤ Ebar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card K ∣ 81 := by
    have h1 : Nat.card K ∣ 648 := card_NE ▸ Subgroup.card_dvd_of_le hKN
    have h2 : Nat.Coprime (Nat.card K) 8 := by
      have := (Nat.coprime_two_left.mpr hodd).pow_left 3
      simpa using this.symm
    exact h2.dvd_of_dvd_mul_left (by simpa using h1)
  have hK3 : IsPGroup 3 K := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card K ∣ 3 ^ 4 by simpa using hdvd)
    exact IsPGroup.of_card hm
  have hKs : IsPGroup 3 (K.subgroupOf NE) :=
    hK3.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
  have hKnormal : (K.subgroupOf NE).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hPst3 : IsPGroup 3 Pst := IsPGroup.of_card (n := 4) (by rw [card_Pst]; norm_num)
  have hconjle : conjSub et Pst ≤ NE := fun x hx => by
    have hx' : et⁻¹ * x * et ∈ NE := Pst_le_NE (mem_conjSub.mp hx)
    have : x = et * (et⁻¹ * x * et) * et⁻¹ := by group
    rw [this]
    exact NE.mul_mem (NE.mul_mem et_mem_NE hx') (NE.inv_mem et_mem_NE)
  have hconj3 : IsPGroup 3 (conjSub et Pst) :=
    IsPGroup.of_card (n := 4) (by rw [card_conjSub, card_Pst]; norm_num)
  have hidx : ∀ P : Subgroup (alternatingGroup (Fin 9)), P ≤ NE → Nat.card P = 81 →
      ¬ 3 ∣ (P.subgroupOf NE).index := by
    intro P hP hc h3
    have h := Subgroup.index_mul_card (H := P.subgroupOf NE)
    have hc' : Nat.card (P.subgroupOf NE) = 81 := by
      rw [← hc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
    rw [hc', card_NE] at h
    have : (P.subgroupOf NE).index = 8 := by omega
    rw [this] at h3
    exact absurd h3 (by decide)
  obtain ⟨S1, hS1⟩ : ∃ S : Sylow 3 ↥NE, (S : Subgroup ↥NE) = Pst.subgroupOf NE :=
    ⟨(hPst3.of_equiv (Subgroup.subgroupOfEquivOfLe Pst_le_NE).symm).toSylow
      (hidx Pst Pst_le_NE card_Pst), rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S : Sylow 3 ↥NE, (S : Subgroup ↥NE) = (conjSub et Pst).subgroupOf NE :=
    ⟨(hconj3.of_equiv (Subgroup.subgroupOfEquivOfLe hconjle).symm).toSylow
      (hidx _ hconjle (by rw [card_conjSub, card_Pst])), rfl⟩
  intro k hk
  have hk' : (⟨k, hKN hk⟩ : ↥NE) ∈ K.subgroupOf NE := hk
  have hm1 : (⟨k, hKN hk⟩ : ↥NE) ∈ Pst.subgroupOf NE := by
    rw [← hS1]; exact hKs.le_sylow_of_normal S1 hk'
  have hm2 : (⟨k, hKN hk⟩ : ↥NE) ∈ (conjSub et Pst).subgroupOf NE := by
    rw [← hS2]; exact hKs.le_sylow_of_normal S2 hk'
  exact mem_Ebar_of_mem_Pst_conj (Subgroup.mem_subgroupOf.mp hm1)
    (mem_conjSub.mp (Subgroup.mem_subgroupOf.mp hm2))

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
