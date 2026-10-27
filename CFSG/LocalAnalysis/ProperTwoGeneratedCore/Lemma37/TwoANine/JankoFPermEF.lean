module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPerm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF

open Equiv Subgroup Janko

theorem ebar₂_mem_Ebar : ebar₂ ∈ Ebar :=
  subset_closure (by simp)

theorem ebar₃_mem_Ebar : ebar₃ ∈ Ebar :=
  subset_closure (by simp)

theorem Ebar_le_centralizer_sbar₃ :
    Ebar ≤ centralizer ({sbar₃} : Set (alternatingGroup (Fin 9))) := by
  rw [Ebar, closure_le]
  rintro x (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff] <;>
    exact Subtype.ext (by decide)

theorem card_Ebar_dvd : Nat.card Ebar ∣ 81 :=
  card_centralizer_sbar₃ ▸ card_dvd_of_le Ebar_le_centralizer_sbar₃

theorem odd_card_Ebar : Odd (Nat.card Ebar) :=
  Odd.of_dvd_nat (by decide) card_Ebar_dvd

theorem Ebar_le_centralizer : Ebar ≤ centralizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  rw [Ebar, centralizer_closure, closure_le]
  rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
    rintro _ (rfl | rfl | rfl) <;> exact Subtype.ext (by decide)

@[expose] def EFbar : Subgroup (alternatingGroup (Fin 9)) :=
  Ebar ⊓ Fbar

theorem EFbar_le_Ebar : EFbar ≤ Ebar :=
  inf_le_left

theorem EFbar_le_Fbar : EFbar ≤ Fbar :=
  inf_le_right

theorem ebar₂_mem_EFbar : ebar₂ ∈ EFbar :=
  ⟨ebar₂_mem_Ebar, ebar₂_mem_Fbar⟩

theorem ebar₃_mem_EFbar : ebar₃ ∈ EFbar :=
  ⟨ebar₃_mem_Ebar, ebar₃_mem_Fbar⟩

theorem sbar₂_eq : sbar₂ = ebar₂ * ebar₃ :=
  Subtype.ext (by decide)

theorem sbar₃_eq : sbar₃ = sbar₁ * sbar₂ :=
  Subtype.ext (by decide)

theorem sbar₂_mem_EFbar : sbar₂ ∈ EFbar :=
  sbar₂_eq ▸ mul_mem ebar₂_mem_EFbar ebar₃_mem_EFbar

theorem odd_card_EFbar : Odd (Nat.card EFbar) :=
  Odd.of_dvd_nat odd_card_Ebar (card_dvd_of_le EFbar_le_Ebar)

theorem orderOf_ebar₂ : orderOf ebar₂ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext (show (ebar₂ : Perm (Fin 9)) ^ 3 = 1 by decide))
    (fun h => absurd (congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) 3) h)
      (by decide))

theorem ebar₃_notMem_zpowers : ebar₃ ∉ zpowers ebar₂ := by
  rintro ⟨k, hk⟩
  have h6 : ((ebar₂ ^ k : alternatingGroup (Fin 9)) : Perm (Fin 9)) 6 = 6 := by
    rw [Subgroup.coe_zpow]
    exact Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) k
  have hk' : ebar₂ ^ k = ebar₃ := hk
  rw [hk'] at h6
  exact absurd h6 (by decide)

theorem card_EFbar : Nat.card EFbar = 9 := by
  have h81 : Nat.card EFbar ∣ 81 := (card_dvd_of_le EFbar_le_Ebar).trans card_Ebar_dvd
  have h9 : Nat.card EFbar ∣ 9 := by
    rcases JankoPerm.card_dvd_nine_or_eq_five_of_odd_alt EFbar_le_Fbar odd_card_EFbar with h | h
    · exact h
    · rw [h] at h81
      norm_num at h81
  have h3 : Nat.card (zpowers ebar₂) = 3 := by rw [Nat.card_zpowers, orderOf_ebar₂]
  have hle : zpowers ebar₂ ≤ EFbar := (zpowers_le).mpr ebar₂_mem_EFbar
  have hd : 3 ∣ Nat.card EFbar := h3 ▸ card_dvd_of_le hle
  have hne : Nat.card EFbar ≠ 3 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [h, h3])
    exact ebar₃_notMem_zpowers (this ▸ ebar₃_mem_EFbar)
  have hle9 := Nat.le_of_dvd (by norm_num) h9
  interval_cases hc : Nat.card EFbar <;> omega

theorem EFbar_le_centralizer : EFbar ≤ centralizer (EFbar : Set (alternatingGroup (Fin 9))) :=
  fun _ hx => (centralizer_le EFbar_le_Ebar) (Ebar_le_centralizer hx.1)

theorem centralizer_EFbar :
    centralizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar = EFbar := by
  have hle : EFbar ≤ centralizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar :=
    le_inf EFbar_le_centralizer EFbar_le_Fbar
  have h81 : centralizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar ≤
      centralizer ({sbar₃} : Set (alternatingGroup (Fin 9))) := by
    rintro u ⟨hu, huF⟩
    have h2 : Commute sbar₂ u := mem_centralizer_iff.mp hu _ sbar₂_mem_EFbar
    have hc : Commute u (sbar₁ * sbar₂) := (commute_sbar₁_of_mem_Fbar huF).mul_right h2.symm
    rw [mem_centralizer_singleton_iff, sbar₃_eq]
    exact hc.eq
  have hodd : Odd (Nat.card (centralizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar :
      Subgroup _)) :=
    Odd.of_dvd_nat (by decide) (card_centralizer_sbar₃ ▸ card_dvd_of_le h81)
  have hle9 := JankoPerm.card_le_nine_of_odd_alt inf_le_right hodd
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_EFbar]; exact hle9)).symm

theorem ℓbar_sq_ne_one : ℓbar ^ 2 ≠ 1 := by
  intro h
  have h4 : ((ℓbar : Perm (Fin 9)) ^ 2) 4 = 4 := by
    rw [← Subgroup.coe_pow, h]
    rfl
  exact absurd h4 (by decide)

theorem orderOf_ℓbar : orderOf ℓbar = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ℓbar)
    (by rw [pow_one]; exact ℓbar_sq_ne_one)
    (Subtype.ext (show (ℓbar : Perm (Fin 9)) ^ 2 ^ (1 + 1) = 1 by decide))
  rw [h]
  norm_num

theorem ℓbar_mem_normalizer_Ebar : ℓbar ∈ normalizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [card_map_of_injective (MulAut.conj ℓbar).injective])
  rw [Ebar, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
  rcases hx with rfl | rfl | rfl
  · rw [show ℓbar * sbar₁ * ℓbar⁻¹ = sbar₁ from Subtype.ext (show (ℓbar : Perm (Fin 9)) * sbar₁ *
      (ℓbar : Perm (Fin 9))⁻¹ = sbar₁ by decide)]
    exact subset_closure (by simp)
  · rw [show ℓbar * ebar₂ * ℓbar⁻¹ = ebar₃⁻¹ from Subtype.ext (show (ℓbar : Perm (Fin 9)) *
      ebar₂ * (ℓbar : Perm (Fin 9))⁻¹ = (ebar₃ : Perm (Fin 9))⁻¹ by decide)]
    exact inv_mem (subset_closure (by simp))
  · rw [show ℓbar * ebar₃ * ℓbar⁻¹ = ebar₂ from Subtype.ext (show (ℓbar : Perm (Fin 9)) * ebar₃ *
      (ℓbar : Perm (Fin 9))⁻¹ = ebar₂ by decide)]
    exact subset_closure (by simp)

theorem ℓbar_mem_normalizer_EFbar :
    ℓbar ∈ normalizer (EFbar : Set (alternatingGroup (Fin 9))) :=
  inf_normalizer_le_normalizer_inf ⟨ℓbar_mem_normalizer_Ebar, le_normalizer ℓbar_mem_Fbar⟩

theorem card_EFbar_sup : Nat.card (EFbar ⊔ zpowers ℓbar : Subgroup _) = 36 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer EFbar (zpowers ℓbar)
    ((zpowers_le).mpr ℓbar_mem_normalizer_EFbar) ?_, card_EFbar, Nat.card_zpowers, orderOf_ℓbar]
  exact disjoint_of_coprime_natCard (by rw [card_EFbar, Nat.card_zpowers, orderOf_ℓbar]; norm_num)

theorem exists_modEq_card_normalizer_EFbar : ∃ n, n ≡ 1 [MOD 3] ∧
    Nat.card (normalizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar : Subgroup _) * n =
      360 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup Fbar := EFbar.subgroupOf Fbar with hPdef
  have hP : Nat.card P = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe EFbar_le_Fbar).toEquiv, card_EFbar]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  obtain ⟨Q, hPQ⟩ := hPp.exists_le_sylow
  have hQ : Nat.card Q = 3 ^ 2 := JankoPerm.card_sylow_eq Q (m := 40)
    (by rw [card_Fbar]; norm_num) (by rw [card_Fbar]; norm_num) (by norm_num)
  have hQP : (Q : Subgroup Fbar) = P :=
    (Subgroup.eq_of_le_of_card_ge hPQ (by rw [hQ, hP]; norm_num)).symm
  have hidx : (normalizer ((Q : Subgroup Fbar) : Set Fbar)).index ≡ 1 [MOD 3] :=
    JankoPerm.index_normalizer_modEq_one Q
  rw [hQP] at hidx
  have hmap : (normalizer (P : Set Fbar)).map Fbar.subtype =
      normalizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar := by
    rw [← normalizer_map_inf_eq_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left EFbar_le_Fbar]
  refine ⟨_, hidx, ?_⟩
  rw [← hmap, card_map_of_injective Fbar.subtype_injective, card_mul_index, card_Fbar]

theorem not_five_dvd_card_normalizer_EFbar :
    ¬ 5 ∣ Nat.card (normalizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar : Subgroup _) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  refine JankoPerm.false_of_orderOf_five (x := ((x : alternatingGroup (Fin 9)) : Perm (Fin 9)))
    (R := EFbar.map (alternatingGroup (Fin 9)).subtype) ?_ ?_ ?_
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · left
    rw [card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective, card_EFbar]
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨_, (mem_normalizer_iff.mp (mem_inf.mp x.2).1 r).mp hr, rfl⟩

theorem card_normalizer_EFbar :
    Nat.card (normalizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar : Subgroup _) = 36 := by
  have hle : EFbar ⊔ zpowers ℓbar ≤ normalizer (EFbar : Set (alternatingGroup (Fin 9))) ⊓ Fbar :=
    sup_le (le_inf le_normalizer EFbar_le_Fbar)
      ((zpowers_le).mpr ⟨ℓbar_mem_normalizer_EFbar, ℓbar_mem_Fbar⟩)
  obtain ⟨k, hk⟩ := card_EFbar_sup ▸ card_dvd_of_le hle
  obtain ⟨n, hn, hNn⟩ := exists_modEq_card_normalizer_EFbar
  have h5 := not_five_dvd_card_normalizer_EFbar
  rw [hk] at hNn h5 ⊢
  unfold Nat.ModEq at hn
  have hkn : k * n = 10 := by nlinarith
  have hk10 : k ≤ 10 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hkn
      omega
    · nlinarith
  interval_cases k <;> omega

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF
