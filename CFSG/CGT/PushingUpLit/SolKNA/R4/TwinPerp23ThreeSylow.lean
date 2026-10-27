module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Set.Finite.Lemmas

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp23.Three

open scoped Pointwise

section Sylow

theorem exists_two_group_conj_of_odd_kernel {Y : Type*} [Group Y] [Finite Y] {W U O : Subgroup Y}
    (hW2 : IsPGroup 2 W) (hWU : ∀ w ∈ W, ∀ x ∈ U, w * x * w⁻¹ ∈ U)
    (hOU : O ≤ U) (hOn : ∀ x ∈ U, ∀ o ∈ O, x * o * x⁻¹ ∈ O) (hOodd : Odd (Nat.card O))
    (h2 : ∀ x ∈ U, ∃ k : ℕ, x ^ 2 ^ k ∈ O) :
    ∃ T : Subgroup Y, W ≤ T ∧ IsPGroup 2 T ∧
      ∀ V : Subgroup Y, V ≤ U → IsPGroup 2 V →
        ∃ o ∈ O, V.map (MulAut.conj o).toMonoidHom ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI act : MulDistribMulAction W U :=
    { smul := fun w x => ⟨(w : Y) * x * (w : Y)⁻¹, hWU w w.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : W) : Y) * x * ((1 : W) : Y)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a * b : W) : Y) * x * ((a * b : W) : Y)⁻¹ =
          (a : Y) * ((b : Y) * x * (b : Y)⁻¹) * (a : Y)⁻¹
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group)
      smul_one := fun w => Subtype.ext (by
        change (w : Y) * 1 * (w : Y)⁻¹ = 1
        simp)
      smul_mul := fun w x y => Subtype.ext (by
        change (w : Y) * ((x : Y) * (y : Y)) * (w : Y)⁻¹ =
          ((w : Y) * x * (w : Y)⁻¹) * ((w : Y) * y * (w : Y)⁻¹)
        group) }
  haveI : Finite (Sylow 2 U) := Sylow.finite_of_finiteIndex (default : Sylow 2 U)
  obtain ⟨P, hP⟩ :=
    hW2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 U) (not_dvd_card_sylow 2 U)
  have hPW : ∀ m : W, m • P = P := fun m => (MulAction.mem_fixedPoints.mp hP) m
  have hS2 : IsPGroup 2 ((P : Subgroup U).map U.subtype) := P.isPGroup'.map U.subtype
  have hWS : ∀ w ∈ W, ∀ y ∈ (P : Subgroup U).map U.subtype,
      w * y * w⁻¹ ∈ (P : Subgroup U).map U.subtype := by
    intro w hw y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : (⟨w, hw⟩ : W) • (P : Subgroup U) = (P : Subgroup U) := by
      have := congrArg (fun Q : Sylow 2 U => (Q : Subgroup U)) (hPW ⟨w, hw⟩)
      simpa only [Sylow.pointwise_smul_def] using this
    have hm : (⟨w, hw⟩ : W) • x ∈ (P : Subgroup U) := by
      rw [← h1]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
    exact Subgroup.mem_map_of_mem _ hm
  have hWN : W ≤ Subgroup.normalizer ((P : Subgroup U).map U.subtype) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hWS w hw y hy
    · intro hy
      have := hWS w⁻¹ (W.inv_mem hw) _ hy
      simpa [mul_assoc] using this
  have hT2 : IsPGroup 2 (((P : Subgroup U).map U.subtype ⊔ W : Subgroup Y)) :=
    hS2.to_sup_of_normal_left' hW2 hWN
  refine ⟨(P : Subgroup U).map U.subtype ⊔ W, le_sup_right, hT2, ?_⟩
  intro V hVU hV2
  haveI : (O.subgroupOf U).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hOn g g.2 n hn
    simpa using this⟩
  have hsup : O.subgroupOf U ⊔ (P : Subgroup U) = ⊤ := by
    have hq : IsPGroup 2 (U ⧸ O.subgroupOf U) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := h2 x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hk
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
    have hidx : (O.subgroupOf U).index = 2 ^ n := hn
    have hd1 : (O.subgroupOf U ⊔ (P : Subgroup U)).index ∣ (P : Subgroup U).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have hd2 : (O.subgroupOf U ⊔ (P : Subgroup U)).index ∣ 2 ^ n :=
      hidx ▸ Subgroup.index_dvd_of_le le_sup_left
    have hP2 : ¬ 2 ∣ (P : Subgroup U).index := Sylow.not_dvd_index P
    have hd : (O.subgroupOf U ⊔ (P : Subgroup U)).index = 1 := by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [hm, h0, pow_zero]
      · have h2d : 2 ∣ (O.subgroupOf U ⊔ (P : Subgroup U)).index := by
          rw [hm]
          exact dvd_pow_self 2 hpos.ne'
        exact absurd (h2d.trans hd1) hP2
    exact Subgroup.index_eq_one.mp hd
  have hVG : IsPGroup 2 (V.subgroupOf U) := hV2.comap_subtype
  obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow hVG
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥U) P Q
  have hgmem : g ∈ O.subgroupOf U ⊔ (P : Subgroup U) := by
    rw [hsup]
    exact Subgroup.mem_top g
  obtain ⟨o, ho, s, hs, hos⟩ := Subgroup.mem_sup_of_normal_left.mp hgmem
  have hPs : s • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs)
  have hoP : o • P = Q := by
    rw [← hg, ← hos, mul_smul, hPs]
  have ho' : (o : Y) ∈ O := Subgroup.mem_subgroupOf.mp ho
  refine ⟨(o : Y)⁻¹, O.inv_mem ho', ?_⟩
  intro y hy
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
  have hvU : v ∈ U := hVU hv
  have hvG : (⟨v, hvU⟩ : U) ∈ V.subgroupOf U := Subgroup.mem_subgroupOf.mpr hv
  have hvQ : (⟨v, hvU⟩ : U) ∈ (Q : Subgroup U) := hVQ hvG
  rw [← hoP, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hvQ
  have hmem := Subgroup.mem_map_of_mem U.subtype hvQ
  have hconj : (MulAut.conj (o : Y)⁻¹).toMonoidHom v =
      U.subtype ((MulAut.conj o)⁻¹ • (⟨v, hvU⟩ : U)) := by
    simp [MulAut.conj_apply, MulAut.conj_inv_apply, MulAut.smul_def]
  rw [hconj]
  exact Subgroup.mem_sup_left hmem

theorem max2_exists {Y : Type*} [Group Y] [Finite Y] {H A : Subgroup Y}
    (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    ∃ T : Subgroup Y, T ≤ H ∧ IsPGroup 2 T ∧ A ≤ T ∧
      ∀ C : Subgroup Y, C ≤ H → IsPGroup 2 C → T ≤ C → C = T := by
  haveI : Finite (Subgroup Y) :=
    Finite.of_injective (fun K : Subgroup Y => (K : Set Y)) SetLike.coe_injective
  obtain ⟨T, ⟨hTH, hT2, hAT⟩, hmax⟩ :=
    Set.exists_max_image {C : Subgroup Y | C ≤ H ∧ IsPGroup 2 C ∧ A ≤ C}
      (fun C : Subgroup Y => Nat.card C) (Set.toFinite _) ⟨A, hAH, hA, le_rfl⟩
  refine ⟨T, hTH, hT2, hAT, fun C hCH hC2 hTC => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hTC (hmax C ⟨hCH, hC2, hAT.trans hTC⟩)).symm

theorem max2_sylow_map_eq {Y : Type*} [Group Y] [Finite Y] {H T : Subgroup Y}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ C : Subgroup Y, C ≤ H → IsPGroup 2 C → T ≤ C → C = T) :
    ∃ Q : Sylow 2 H, Q.toSubgroup.map H.subtype = T := by
  have hTg : IsPGroup 2 (T.subgroupOf H) := hT2.comap_subtype
  obtain ⟨Q, hQ⟩ := hTg.exists_le_sylow
  have hmapLe : Q.toSubgroup.map H.subtype ≤ H := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  refine ⟨Q, hTmax _ hmapLe (Q.isPGroup'.map H.subtype) ?_⟩
  intro t ht
  exact Subgroup.mem_map.mpr
    ⟨⟨t, hTH ht⟩, hQ ((Subgroup.mem_subgroupOf (h := ⟨t, hTH ht⟩)).mpr ht), rfl⟩

theorem max2_exists_conj_mem {Y : Type*} [Group Y] [Finite Y] {H T M : Subgroup Y}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ C : Subgroup Y, C ≤ H → IsPGroup 2 C → T ≤ C → C = T)
    (hMH : M ≤ H) (hM2 : IsPGroup 2 M) :
    ∃ g : Y, g ∈ H ∧ ∀ m ∈ M, g⁻¹ * m * g ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := max2_sylow_map_eq hTH hT2 hTmax
  have hMg : IsPGroup 2 (M.subgroupOf H) := hM2.comap_subtype
  obtain ⟨Q, hQ⟩ := hMg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q₀ Q
  have hQeq : (Q : Subgroup H) = (Q₀ : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨(g : Y), g.2, fun m hm => ?_⟩
  have hmQ : (⟨m, hMH hm⟩ : H) ∈ (Q : Subgroup H) :=
    hQ ((Subgroup.mem_subgroupOf (h := ⟨m, hMH hm⟩)).mpr hm)
  rw [hQeq] at hmQ
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmQ
  have hyT : (y : Y) ∈ T := by
    have h := Subgroup.mem_map_of_mem H.subtype hy
    rw [hQ₀] at h
    exact h
  have h3 : (g : Y) * (y : Y) * (g : Y)⁻¹ = m := by
    have h := congrArg Subtype.val hyeq
    simpa [MulAut.conj_apply] using h
  have hy' : (y : Y) = (g : Y)⁻¹ * m * (g : Y) := by
    rw [← h3]
    group
  rw [← hy']
  exact hyT

theorem card_le_of_conj_mem {Y : Type*} [Group Y] [Finite Y] {M S : Subgroup Y} {g : Y}
    (h : ∀ m ∈ M, g⁻¹ * m * g ∈ S) : Nat.card M ≤ Nat.card S := by
  have hle : M.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using h m hm
  calc Nat.card M = Nat.card (M.map (MulAut.conj g⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hle

theorem le_of_normal_in_max2 {Y : Type*} [Group Y] [Finite Y] {H T U : Subgroup Y}
    (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ C : Subgroup Y, C ≤ H → IsPGroup 2 C → T ≤ C → C = T)
    (hUH : U ≤ H) (hU2 : IsPGroup 2 U) (hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    U ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := max2_sylow_map_eq hTH hT2 hTmax
  have hUg : IsPGroup 2 (U.subgroupOf H) := hU2.comap_subtype
  haveI hnorm : (U.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hUn (g : Y) g.2 _ hn⟩
  have hle : U.subgroupOf H ≤ Q₀.toSubgroup := hUg.le_sylow_of_normal Q₀
  intro u hu
  have h1 : (⟨u, hUH hu⟩ : H) ∈ Q₀.toSubgroup :=
    hle ((Subgroup.mem_subgroupOf (h := ⟨u, hUH hu⟩)).mpr hu)
  have h2 := Subgroup.mem_map_of_mem H.subtype h1
  rw [hQ₀] at h2
  exact h2

theorem exists_sylow_normalized_by_two_group {Y : Type*} [Group Y] [Finite Y] {J W U R : Subgroup Y}
    (hW2 : IsPGroup 2 W) (hWJ : ∀ w ∈ W, ∀ x ∈ J, w * x * w⁻¹ ∈ J)
    (hWU : ∀ w ∈ W, ∀ x ∈ U, w * x * w⁻¹ = x)
    (hRJ : R ≤ J) (hR2 : IsPGroup 2 R) (hRmax : ∀ V : Subgroup Y, V ≤ J → IsPGroup 2 V → R ≤ V → V = R)
    (hUR : U ≤ R) (hUnorm : ∀ x ∈ R, ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∃ P : Subgroup Y, P ≤ J ∧ IsPGroup 2 P ∧
      (∀ V : Subgroup Y, V ≤ J → IsPGroup 2 V → P ≤ V → V = P) ∧ U ≤ P ∧
      ∀ w ∈ W, ∀ x ∈ P, w * x * w⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup Y, N₀ = J ⊓ Subgroup.normalizer U := ⟨_, rfl⟩
  have hmemN : ∀ x, x ∈ N₀ ↔ x ∈ J ∧ x ∈ Subgroup.normalizer U := fun x => by
    rw [hN₀, Subgroup.mem_inf]
  have hN₀J : N₀ ≤ J := fun x hx => ((hmemN x).mp hx).1
  have hRN₀ : R ≤ N₀ := by
    intro x hx
    refine (hmemN x).mpr ⟨hRJ hx, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hUnorm x hx u, fun hxu => ?_⟩
    have h := hUnorm x⁻¹ (inv_mem hx) _ hxu
    simpa [mul_assoc] using h
  have hWUn : ∀ w ∈ W, w ∈ Subgroup.normalizer U := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · rw [hWU w hw u hu]
      exact hu
    · have h := hWU w⁻¹ (inv_mem hw) _ hu
      have h2 : w⁻¹ * (w * u * w⁻¹) * w⁻¹⁻¹ = u := by group
      rw [h2] at h
      rw [h]
      exact hu
  have hconj : ∀ w ∈ W, ∀ x ∈ N₀, w * x * w⁻¹ ∈ N₀ := by
    intro w hw x hx
    obtain ⟨hxJ, hxN⟩ := (hmemN x).mp hx
    exact (hmemN _).mpr
      ⟨hWJ w hw x hxJ, mul_mem (mul_mem (hWUn w hw) hxN) (inv_mem (hWUn w hw))⟩
  have hWN : ∀ w ∈ W, w ∈ Subgroup.normalizer N₀ := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj w hw x, fun hx => ?_⟩
    have h := hconj w⁻¹ (inv_mem hw) _ hx
    have h2 : w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x := by group
    rw [h2] at h
    exact h
  obtain ⟨H, hH⟩ : ∃ H : Subgroup Y, H = W ⊔ N₀ := ⟨_, rfl⟩
  have hWH : W ≤ H := by
    rw [hH]
    exact le_sup_left
  have hN₀H : N₀ ≤ H := by
    rw [hH]
    exact le_sup_right
  have hHN : H ≤ Subgroup.normalizer N₀ := by
    rw [hH]
    exact sup_le (fun w hw => hWN w hw) (fun x hx => Subgroup.le_normalizer hx)
  have hHU : H ≤ Subgroup.normalizer U := by
    rw [hH]
    exact sup_le (fun w hw => hWUn w hw) (fun x hx => ((hmemN x).mp hx).2)
  obtain ⟨T, hTH, hT2, hWT, hTmax⟩ := max2_exists hWH hW2
  have hUH : U ≤ H := hUR.trans (hRN₀.trans hN₀H)
  have hU2 : IsPGroup 2 U := hR2.to_le hUR
  have hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp hu
  have hUT : U ≤ T := le_of_normal_in_max2 hTH hT2 hTmax hUH hU2 hUn
  refine ⟨T ⊓ N₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hN₀J (Subgroup.mem_inf.mp hx).2
  · exact hT2.to_inf_left
  · intro V hVJ hV2 hPV
    have hRH : R ≤ H := fun x hx => hN₀H (hRN₀ hx)
    obtain ⟨g, hgH, hg⟩ := max2_exists_conj_mem hTH hT2 hTmax hRH hR2
    have hgN : ∀ m ∈ R, g⁻¹ * m * g ∈ N₀ := by
      intro m hm
      have h := (Subgroup.mem_normalizer_iff.mp (inv_mem (hHN hgH)) m).mp (hRN₀ hm)
      rwa [inv_inv] at h
    have hRP : Nat.card R ≤ Nat.card ↥(T ⊓ N₀) :=
      card_le_of_conj_mem (g := g) (fun m hm => Subgroup.mem_inf.mpr ⟨hg m hm, hgN m hm⟩)
    obtain ⟨g', -, hg'⟩ := max2_exists_conj_mem hRJ hR2 hRmax hVJ hV2
    have hVR : Nat.card V ≤ Nat.card R := card_le_of_conj_mem (g := g') hg'
    exact (Subgroup.eq_of_le_of_card_ge hPV (hVR.trans hRP)).symm
  · exact le_inf hUT (hUR.trans hRN₀)
  · intro w hw x hx
    obtain ⟨hxT, hxN⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (hWT hw) hxT) (inv_mem (hWT hw)), hconj w hw x hxN⟩

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp23.Three
