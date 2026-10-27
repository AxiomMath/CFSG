module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint

namespace CoverM12

def Lset : List (Fin 128) := [0, 1, 2, 3, 26, 27, 88, 89]

theorem zero_mem_Lset : (0 : Fin 128) ∈ Lset := by decide

theorem star_zero_zero : M12Cover.InternalSylow.star 0 0 = 0 := by decide +kernel

theorem Lset_sq : ∀ x ∈ Lset, M12Cover.InternalSylow.star x x = 0 := by decide +kernel

theorem Lset_mul : ∀ x ∈ Lset, ∀ y ∈ Lset, M12Cover.InternalSylow.star x y ∈ Lset := by
  decide +kernel

theorem Lset_normal : ∀ g : Fin 128, ∀ a ∈ Lset,
    ∃ b ∈ Lset, M12Cover.InternalSylow.star g a = M12Cover.InternalSylow.star b g := by
  decide +kernel

theorem card_Lset : Nat.card {x : Fin 128 // x ∈ Lset} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

section Model


theorem encR_zero : M12Cover.InternalSylow.encR 0 = 1 := by
  have h := M12Cover.InternalSylow.isTableModel_star 0 0
  rw [star_zero_zero] at h
  exact left_eq_mul.mp h

theorem mul_self_eq_one_of_mem {a : M12Cover.InternalSylow.R}
    (ha : M12Cover.InternalSylow.encR.symm a ∈ Lset) : a * a = 1 := by
  have h := M12Cover.InternalSylow.isTableModel_star (M12Cover.InternalSylow.encR.symm a)
    (M12Cover.InternalSylow.encR.symm a)
  rw [Lset_sq _ ha, encR_zero, Equiv.apply_symm_apply] at h
  exact h.symm

def AR : Subgroup M12Cover.InternalSylow.R where
  carrier := {g | M12Cover.InternalSylow.encR.symm g ∈ Lset}
  mul_mem' := by
    intro a b ha hb
    have h : M12Cover.InternalSylow.encR.symm (a * b) =
        M12Cover.InternalSylow.star (M12Cover.InternalSylow.encR.symm a)
          (M12Cover.InternalSylow.encR.symm b) := by
      rw [Equiv.symm_apply_eq]
      have h2 := M12Cover.InternalSylow.isTableModel_star (M12Cover.InternalSylow.encR.symm a)
        (M12Cover.InternalSylow.encR.symm b)
      rw [h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    show M12Cover.InternalSylow.encR.symm (a * b) ∈ Lset
    rw [h]
    exact Lset_mul _ ha _ hb
  one_mem' := by
    show M12Cover.InternalSylow.encR.symm 1 ∈ Lset
    rw [← encR_zero, Equiv.symm_apply_apply]
    exact zero_mem_Lset
  inv_mem' := by
    intro a ha
    show M12Cover.InternalSylow.encR.symm a⁻¹ ∈ Lset
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem ha)]
    exact ha

theorem card_AR : Nat.card AR = 8 := by
  rw [Nat.card_congr (M12Cover.InternalSylow.encR.symm.subtypeEquiv
    (p := fun g => g ∈ AR) (q := fun x => x ∈ Lset) fun g => Iff.rfl)]
  exact card_Lset

theorem AR_normal (x r : M12Cover.InternalSylow.R) (hr : r ∈ AR) : x * r * x⁻¹ ∈ AR := by
  have hr' : M12Cover.InternalSylow.encR.symm r ∈ Lset := hr
  obtain ⟨b, hb, hbeq⟩ := Lset_normal (M12Cover.InternalSylow.encR.symm x) _ hr'
  have h1 := M12Cover.InternalSylow.isTableModel_star (M12Cover.InternalSylow.encR.symm x)
    (M12Cover.InternalSylow.encR.symm r)
  have h2 := M12Cover.InternalSylow.isTableModel_star b (M12Cover.InternalSylow.encR.symm x)
  rw [hbeq, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
  rw [Equiv.apply_symm_apply] at h2
  have key : x * r = M12Cover.InternalSylow.encR b * x := h1.symm.trans h2
  show M12Cover.InternalSylow.encR.symm (x * r * x⁻¹) ∈ Lset
  rw [key, mul_assoc, mul_inv_cancel, mul_one, Equiv.symm_apply_apply]
  exact hb

end Model

end CoverM12

open CoverM12 in
theorem coverLeafM12_holds :
    CoverLeafM12 := by
  intro Q _ _ hQ hM
  obtain ⟨hq, hZ0, h2Z, -, -, -⟩ := hQ
  have hle : Nat.card (center Q) ≤ 2 :=
    CFSG.GH74.KGroups.TwoM12.m12_cover_of_standard Q hq h2Z hM
  have hgt : 1 < Nat.card (center Q) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ0
  have hcard : Nat.card (center Q) = 2 := by omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ0
  have hord : orderOf x = 2 := by
    have hd : orderOf x ∣ 2 := by
      have := orderOf_dvd_natCard x
      rwa [hcard] at this
    have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h hne
    · exact h
  have ht : orderOf (x : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hord
  have hZeq : center Q = Subgroup.zpowers (x : Q) := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact Subgroup.zpowers_le.mpr x.2
    · rw [Nat.card_zpowers, ht, hcard]
  obtain ⟨e₀⟩ := hM
  let e : Q ⧸ center Q ≃* NativeSporadic.M12 := e₀
  let π : Q →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center Q := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = Subgroup.zpowers (x : Q) := hkerZ.trans hZeq
  have hπ : CFSG.ComponentClassification.CentralCover.IsCentralDoubleExt π (x : Q) :=
    ⟨hπs, x.2, ht, hker⟩
  haveI : Group.IsPerfect Q := hq.1
  have hLq : CFSG.Assembly.IsQuasisimple Q := ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  obtain ⟨-, h4, h0⟩ :=
    CFSG.ComponentClassification.M12Cover.m12_double_cover_involution_lift_orders hLq ht hZeq π
      hπs hker
  obtain ⟨ι, -, -, -⟩ :=
    CFSG.ComponentClassification.M12Cover.InternalSylow.exists_local_coordinates hπ h4
      (fun v h1 h2 => (h0 v h1 h2).1)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardS : Nat.card (M12Cover.InternalSylow.S.comap π) = 128 := by
    rw [Nat.card_congr ι.toEquiv, M12Cover.InternalSylow.card_R]
  have hindexS : M12Cover.InternalSylow.S.index = 1485 := by
    have h1 := Subgroup.card_mul_index M12Cover.InternalSylow.S
    rw [M12Cover.InternalSylow.card_S, CFSG.Sporadic.Schreier.m12_card] at h1
    omega
  have hindex : (M12Cover.InternalSylow.S.comap π).index = 1485 := by
    rw [Subgroup.index_comap_of_surjective _ hπs, hindexS]
  have hP : IsPGroup 2 (M12Cover.InternalSylow.S.comap π) :=
    IsPGroup.of_card (n := 7) (hcardS.trans (by norm_num))
  have hidx : ¬ 2 ∣ (M12Cover.InternalSylow.S.comap π).index := by
    rw [hindex]
    norm_num
  let P : Sylow 2 Q := hP.toSylow hidx
  have hPcoe : (P : Subgroup Q) = M12Cover.InternalSylow.S.comap π :=
    IsPGroup.toSylow_coe hP hidx
  let f : M12Cover.InternalSylow.R →* Q :=
    (M12Cover.InternalSylow.S.comap π).subtype.comp ι.symm.toMonoidHom
  have hf : Function.Injective f :=
    (Subgroup.subtype_injective _).comp ι.symm.injective
  have hfrange : ∀ s : Q, s ∈ M12Cover.InternalSylow.S.comap π →
      ∃ y : M12Cover.InternalSylow.R, f y = s := by
    intro s hs
    refine ⟨ι ⟨s, hs⟩, ?_⟩
    show ((ι.symm (ι ⟨s, hs⟩) : M12Cover.InternalSylow.S.comap π) : Q) = s
    rw [MulEquiv.symm_apply_apply]
  have hA2 : ∀ a ∈ AR.map f, a * a = 1 := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul, mul_self_eq_one_of_mem hr, map_one]
  have hA8 : 8 ≤ Nat.card (AR.map f) := by
    rw [Subgroup.card_map_of_injective hf, card_AR]
  have hSA : (P : Subgroup Q) ≤ Subgroup.normalizer ((AR.map f : Subgroup Q) : Set Q) := by
    intro s hs
    rw [hPcoe] at hs
    obtain ⟨y, rfl⟩ := hfrange s hs
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hn
    have hconj : f y * f r * (f y)⁻¹ = f (y * r * y⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hconj]
    exact Subgroup.mem_map_of_mem f (AR_normal y r hr)
  exact sylowFourJoined_of_normal_elemAbelian P hSA hA2 hA8

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
