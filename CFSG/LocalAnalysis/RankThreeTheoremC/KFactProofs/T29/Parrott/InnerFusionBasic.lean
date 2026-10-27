module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Fusion

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

open CFSG.Open Subgroup TauCeti

section Fuse

variable {G H : Type} [Group G] [Group H]

@[expose] def FusesIntoFixedE9 (α : MulAut G) : Prop :=
  ∀ x : G, orderOf x = 3 → ∃ (g : G) (E : Subgroup G), IsElemAbelian 3 E ∧
    Nat.card E = 9 ∧ g * x * g⁻¹ ∈ E ∧ ∀ e ∈ E, α e = e

theorem FusesIntoFixedE9.of_conj {α : MulAut G} (δ : MulAut G)
    (h : FusesIntoFixedE9 (δ * α * δ⁻¹)) : FusesIntoFixedE9 α := by
  intro x hx
  have hδx : orderOf (δ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨g, E, hE, hE9, hgx, hfix⟩ := h (δ x) hδx
  refine ⟨δ⁻¹ g, E.map (δ⁻¹ : MulAut G).toMonoidHom, hE.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hE9]
  · refine ⟨g * δ x * g⁻¹, hgx, ?_⟩
    show (δ⁻¹ : MulAut G) (g * δ x * g⁻¹) = (δ⁻¹ : MulAut G) g * x * ((δ⁻¹ : MulAut G) g)⁻¹
    rw [map_mul, map_mul, map_inv, MulAut.inv_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  · rintro _ ⟨e, he, rfl⟩
    have h1 : δ (α ((δ⁻¹ : MulAut G) e)) = e := hfix e he
    show α ((δ⁻¹ : MulAut G) e) = (δ⁻¹ : MulAut G) e
    apply δ.injective
    rw [h1, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem FusesIntoFixedE9.of_inv {α : MulAut G} (h : FusesIntoFixedE9 α⁻¹) :
    FusesIntoFixedE9 α := by
  intro x hx
  obtain ⟨g, E, hE, hE9, hgx, hfix⟩ := h x hx
  refine ⟨g, E, hE, hE9, hgx, fun e he => ?_⟩
  have h1 := hfix e he
  rw [MulAut.inv_apply] at h1
  rw [← h1, MulEquiv.apply_symm_apply, h1]

theorem FusesIntoFixedE9.of_mulEquiv {α : MulAut G} (e : G ≃* H)
    (h : FusesIntoFixedE9 (MulAut.congr e α)) : FusesIntoFixedE9 α := by
  intro x hx
  have hex : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨g, E, hE, hE9, hgx, hfix⟩ := h (e x) hex
  refine ⟨e.symm g, E.map e.symm.toMonoidHom, hE.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE9]
  · refine ⟨g * e x * g⁻¹, hgx, ?_⟩
    show e.symm (g * e x * g⁻¹) = e.symm g * x * (e.symm g)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : e (α (e.symm y)) = y := hfix y hy
    show α (e.symm y) = e.symm y
    apply e.injective
    rw [h1, MulEquiv.apply_symm_apply]

theorem congr_pow_three_eq_one {α : MulAut G} (e : G ≃* H) (h : α ^ 3 = 1) :
    MulAut.congr e α ^ 3 = 1 := by
  rw [← map_pow, h, map_one]

theorem congr_not_mem_range_conj {α : MulAut G} (e : G ≃* H)
    (h : α ∉ (MulAut.conj : G →* MulAut G).range) :
    MulAut.congr e α ∉ (MulAut.conj : H →* MulAut H).range := by
  rintro ⟨k, hk⟩
  apply h
  refine ⟨e.symm k, MulEquiv.ext fun y => ?_⟩
  have h1 : k * e y * k⁻¹ = e (α (e.symm (e y))) := congrArg (fun φ : MulAut H => φ (e y)) hk
  rw [MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem fusesIntoFixedE9_of_reps {α : MulAut G} {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hfix : ∀ e ∈ E, α e = e)
    (hrep : ∀ x : G, orderOf x = 3 → ∃ g : G, g * x * g⁻¹ ∈ E) : FusesIntoFixedE9 α := by
  intro x hx
  obtain ⟨g, hg⟩ := hrep x hx
  exact ⟨g, E, hE, hE9, hg, hfix⟩

end Fuse

section Plane

variable {G : Type} [Group G]

theorem isElemAbelian_sup_zpowers {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) : IsElemAbelian 3 (zpowers a ⊔ zpowers b) := by
  refine (isElemAbelian_zpowers ha).sup_of_commute (isElemAbelian_zpowers hb) ?_
  intro u hu v hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  exact ((Commute.zpow_zpow (show Commute a b from hab) i j)).eq

theorem card_sup_zpowers_eq_nine [Finite G] {a b : G} (ha : orderOf a = 3) (hb : b ^ 3 = 1)
    (hba : b ∉ zpowers a) (hab : a * b = b * a) : Nat.card ↥(zpowers a ⊔ zpowers b) = 9 := by
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers a) hb hba
    (fun u hu => ?_), Nat.card_zpowers, ha]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  exact ((show Commute a b from hab).zpow_left i).eq

theorem fixed_of_mem_sup_zpowers {α : MulAut G} {a b : G} (ha : α a = a) (hb : α b = b) :
    ∀ e ∈ zpowers a ⊔ zpowers b, α e = e := by
  have hle : zpowers a ⊔ zpowers b ≤ α.toMonoidHom.eqLocus (MonoidHom.id G) :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  exact fun e he => hle he

theorem pow_three_eq_one_of_orderOf {x : G} (hx : orderOf x = 3) : x ^ 3 = 1 := by
  rw [← hx]
  exact pow_orderOf_eq_one x

theorem ne_one_of_orderOf_three {x : G} (hx : orderOf x = 3) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  omega

theorem orderOf_eq_three {x : G} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 h1

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem exists_plane_of_hasNoncommPair [Finite G]
    (h : CFSG.RankThree.PartOne.StrongP.HasNoncommPair 3 G) :
    ∃ a b : G, orderOf a = 3 ∧ b ^ 3 = 1 ∧ b ∉ zpowers a ∧ a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := h
  set P := Subgroup.closure ({x, y} : Set G) with hPdef
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hx1 : x ≠ 1 := fun h1 => hxy (by rw [h1, one_mul, mul_one])
  have hy1 : y ≠ 1 := fun h1 => hxy (by rw [h1, one_mul, mul_one])
  have hxo : orderOf x = 3 := orderOf_eq_three hx hx1
  have hyo : orderOf y = 3 := orderOf_eq_three hy hy1
  have hnt : Nontrivial P := ⟨⟨⟨x, hxP⟩, 1, fun h1 => hx1 (congrArg Subtype.val h1)⟩⟩
  have hZ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have h3 : 3 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨n, hn⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.2 hZ).ne' hn
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3 h3
  set w' : G := ((w : P) : G) with hw'
  have hwo : orderOf w' = 3 := by rw [hw', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hw3 : w' ^ 3 = 1 := pow_three_eq_one_of_orderOf hwo
  have hcomm : ∀ u ∈ P, u * w' = w' * u := fun u hu =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 w.2 ⟨u, hu⟩))
  by_cases hwx : w' ∈ zpowers x
  · refine ⟨y, w', hyo, hw3, fun hwy => hxy ?_, hcomm y hyP⟩
    have hle : zpowers w' ≤ zpowers x := Subgroup.zpowers_le.2 hwx
    have heq : zpowers w' = zpowers x := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hxo])
    have hle' : zpowers w' ≤ zpowers y := Subgroup.zpowers_le.2 hwy
    have heq' : zpowers w' = zpowers y := Subgroup.eq_of_le_of_card_ge hle'
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hyo])
    have hyx : y ∈ zpowers x := by rw [← heq, heq']; exact Subgroup.mem_zpowers y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyx
    exact (Commute.self_zpow x k).eq
  · exact ⟨x, w', hxo, hw3, hwx, hcomm x hxP⟩

end Plane

section Index

@[expose] def InnerFusionE9At (d : ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
    ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range → FusesIntoFixedE9 α

theorem innerFusionE9At_of_model {d : ValidLieTypeIndex} {M : Type} [Group M]
    (e : (CFSGIndex.lie d).Group ≃* M)
    (h : ∀ α : MulAut M, α ^ 3 = 1 → α ∉ (MulAut.conj : M →* MulAut M).range →
      FusesIntoFixedE9 α) : InnerFusionE9At d := by
  intro K _ _ ⟨f⟩ α hα3 hαo
  exact FusesIntoFixedE9.of_mulEquiv (f.trans e)
    (h _ (congr_pow_three_eq_one _ hα3) (congr_not_mem_range_conj _ hαo))

theorem innerFusionE9Exc_of_at
    (h : ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → IsRankTwoExcIndex d.1 →
      InnerFusionE9At d) : InnerFusionE9Exc := by
  intro d hch hd K _ _ he α hα3 hαo x hx
  exact h d hch hd K he α hα3 hαo x hx

end Index

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
