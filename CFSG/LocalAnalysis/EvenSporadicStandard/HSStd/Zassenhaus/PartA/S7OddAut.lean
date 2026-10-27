module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

local notation "A6" => alternatingGroup (Fin 6)

theorem eq_one_of_two_group_of_odd_orderOf {T : Type} [Group T] {V : Subgroup T}
    (hV : IsPGroup 2 V) {v : T} (hv : v ∈ V) (hodd : Odd (orderOf v)) : v = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨v, hv⟩
  have hk' : v ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf v ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hi] at hodd
  have : i = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)
  rw [this, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

theorem eq_bot_of_odd_normal_mulAut_alt6 (K : Subgroup (MulAut (alternatingGroup (Fin 6))))
    [K.Normal] (hK : Odd (Nat.card K)) : K = ⊥ := by
  have := isSimple_alt6
  have : ((K ⊓ innA6).comap (MulAut.conj : A6 →* MulAut A6)).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((K ⊓ innA6).comap (MulAut.conj : A6 →* MulAut A6)) with h | h
  · rw [eq_bot_iff]
    intro k hk
    rw [mem_bot]
    refine eq_one_of_commute_conj alt6_nonabelian k fun s => ?_
    have hi : (MulAut.conj s : MulAut A6) ∈ innA6 := ⟨s, rfl⟩
    have hc : k * MulAut.conj s * k⁻¹ * (MulAut.conj s)⁻¹ ∈ K ⊓ innA6 := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have h1 : MulAut.conj s * k⁻¹ * (MulAut.conj s)⁻¹ ∈ K :=
          Normal.conj_mem inferInstance _ (K.inv_mem hk) _
        have e : k * MulAut.conj s * k⁻¹ * (MulAut.conj s)⁻¹ =
            k * (MulAut.conj s * k⁻¹ * (MulAut.conj s)⁻¹) := by group
        rw [e]
        exact K.mul_mem hk h1
      · have h1 : k * MulAut.conj s * k⁻¹ ∈ innA6 := Normal.conj_mem inferInstance _ hi _
        exact innA6.mul_mem h1 (innA6.inv_mem hi)
    obtain ⟨r, hr⟩ := hc.2
    have hr' : r ∈ (K ⊓ innA6).comap (MulAut.conj : A6 →* MulAut A6) := by
      show (MulAut.conj r : MulAut A6) ∈ K ⊓ innA6
      rw [hr]
      exact hc
    rw [h] at hr'
    have hr1 : r = 1 := by simpa using hr'
    rw [hr1, map_one] at hr
    calc k * MulAut.conj s
        = (k * MulAut.conj s * k⁻¹ * (MulAut.conj s)⁻¹) * (MulAut.conj s * k) := by group
      _ = MulAut.conj s * k := by rw [← hr, one_mul]
  · exfalso
    have hle : innA6 ≤ K := by
      rintro _ ⟨s, rfl⟩
      have : s ∈ (K ⊓ innA6).comap (MulAut.conj : A6 →* MulAut A6) := h ▸ mem_top s
      exact this.1
    have hd := Subgroup.card_dvd_of_le hle
    rw [card_innA6] at hd
    exact (Nat.not_even_iff_odd.2 hK) (even_iff_two_dvd.2 (Nat.dvd_trans (by norm_num) hd))

theorem odd_normal_inf_eq_bot {T : Type} [Group T] [Finite T] (W V B M : Subgroup T) [M.Normal]
    (hV : IsPGroup 2 V) (hcomm : ∀ v ∈ V, ∀ b ∈ B, v * b = b * v) (hVW : V ≤ W) (hBW : B ≤ W)
    (hsup : ∀ w ∈ W, ∃ v ∈ V, ∃ b ∈ B, w = v * b)
    (e : ↥B ≃* MulAut (alternatingGroup (Fin 6))) (hM : Odd (Nat.card M)) : M ⊓ W = ⊥ := by
  have hnorm : (M.subgroupOf B).Normal := inferInstance
  have hMap : ((M.subgroupOf B).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hnorm e.toMonoidHom e.surjective
  let f : M.subgroupOf B →* M :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h' : (f a).1 = (f b).1 := by rw [hab]
    exact Subtype.ext (Subtype.ext h')
  have hdvd : Nat.card (M.subgroupOf B) ∣ Nat.card M := Subgroup.card_dvd_of_injective f hf
  have hodd : Odd (Nat.card ((M.subgroupOf B).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Odd.of_dvd_nat hM hdvd
  have hbot := @eq_bot_of_odd_normal_mulAut_alt6 _ hMap hodd
  have := isSimple_alt6
  rw [eq_bot_iff]
  intro m hm
  rw [mem_bot]
  obtain ⟨v, hv, b, hb, rfl⟩ := hsup m hm.2
  have hmM : v * b ∈ M := hm.1
  have hcen : ∀ b' ∈ B, b * b' = b' * b := by
    intro b' hb'
    have hyB : b * b' * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)
    have hy : v * (b * b' * b⁻¹) = (b * b' * b⁻¹) * v := hcomm v hv _ hyB
    have hcM : v * b * (b' * (v * b)⁻¹ * b'⁻¹) ∈ M :=
      M.mul_mem hmM (Normal.conj_mem inferInstance _ (M.inv_mem hmM) _)
    have hceq : v * b * (b' * (v * b)⁻¹ * b'⁻¹) = (b * b' * b⁻¹) * b'⁻¹ := by
      calc v * b * (b' * (v * b)⁻¹ * b'⁻¹)
          = (v * (b * b' * b⁻¹)) * v⁻¹ * b'⁻¹ := by group
        _ = ((b * b' * b⁻¹) * v) * v⁻¹ * b'⁻¹ := by rw [hy]
        _ = (b * b' * b⁻¹) * b'⁻¹ := by group
    have hcB : (b * b' * b⁻¹) * b'⁻¹ ∈ B := B.mul_mem hyB (B.inv_mem hb')
    have hmem : (⟨(b * b' * b⁻¹) * b'⁻¹, hcB⟩ : ↥B) ∈ M.subgroupOf B := by
      show (b * b' * b⁻¹) * b'⁻¹ ∈ M
      rw [← hceq]
      exact hcM
    have hmem2 : e ⟨(b * b' * b⁻¹) * b'⁻¹, hcB⟩ ∈ (M.subgroupOf B).map e.toMonoidHom :=
      ⟨_, hmem, rfl⟩
    rw [hbot, mem_bot] at hmem2
    have h3 : (⟨(b * b' * b⁻¹) * b'⁻¹, hcB⟩ : ↥B) = 1 := e.injective (by rw [hmem2, map_one])
    have h4 : (b * b' * b⁻¹) * b'⁻¹ = 1 := congrArg Subtype.val h3
    have h1 : b * b' * b⁻¹ = b' := mul_inv_eq_one.1 h4
    calc b * b' = b * b' * b⁻¹ * b := by group
      _ = b' * b := by rw [h1]
  have hz : e ⟨b, hb⟩ ∈ Subgroup.center (MulAut A6) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨b'', rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen b'' b''.2).symm
  rw [center_mulAut_eq_bot alt6_nonabelian, mem_bot] at hz
  have hb1 : (⟨b, hb⟩ : ↥B) = 1 := e.injective (by rw [hz, map_one])
  have hb2 : b = 1 := congrArg Subtype.val hb1
  rw [hb2, mul_one] at hmM ⊢
  have hodd' : Odd (orderOf v) := Odd.of_dvd_nat hM (Subgroup.orderOf_dvd_natCard M hmM)
  exact eq_one_of_two_group_of_odd_orderOf hV hv hodd'

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
