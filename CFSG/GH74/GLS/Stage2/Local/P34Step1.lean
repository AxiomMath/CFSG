module

public import CFSG.GH74.GLS.Stage2.Local.P34Kind
public import CFSG.GH74.GLS.Stage2.Local.P34Step0
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Omega

variable {X : Type*} [Group X]

@[expose] def omegaZ (V : Subgroup X) : Subgroup X where
  carrier := {a | a ∈ V ∧ (∀ v ∈ V, v * a = a * v) ∧ a * a = 1}
  mul_mem' := by
    rintro a b ⟨haV, hac, ha2⟩ ⟨hbV, hbc, hb2⟩
    refine ⟨V.mul_mem haV hbV, fun v hv => ?_, ?_⟩
    · calc v * (a * b) = (v * a) * b := by group
        _ = (a * v) * b := by rw [hac v hv]
        _ = a * (v * b) := by group
        _ = a * (b * v) := by rw [hbc v hv]
        _ = a * b * v := by group
    · have hab : b * a = a * b := hac b hbV
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨V.one_mem, fun v _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haV, hac, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hai]
    exact ⟨haV, hac, ha2⟩

theorem mem_omegaZ {V : Subgroup X} {a : X} :
    a ∈ omegaZ V ↔ a ∈ V ∧ (∀ v ∈ V, v * a = a * v) ∧ a * a = 1 := Iff.rfl

theorem omegaZ_normal {V : Subgroup X} (hV : V.Normal) : (omegaZ V).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨hnV, hnc, hn2⟩ := hn
  refine ⟨hV.conj_mem n hnV g, fun v hv => ?_, ?_⟩
  · have hv' : g⁻¹ * v * g ∈ V := by
      simpa using hV.conj_mem v hv g⁻¹
    have := hnc _ hv'
    calc v * (g * n * g⁻¹) = g * ((g⁻¹ * v * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * v * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * v := by group
  · calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn2]; group

omit [Group X] in
theorem eq_of_card_le_two {Y : Type*} [Group Y] [Finite Y] {D : Subgroup Y} (h : Nat.card ↥D ≤ 2)
    {a b : Y} (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![(1 : ↥D), ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → ↥D) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [Subtype.ext_iff] at hij; tauto)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

omit [Group X] in
theorem exists_omegaZ_ne_one {X : Type*} [Group X] [Finite X] {V : Subgroup X}
    (hVp : IsPGroup 2 ↥V) (hV : V ≠ ⊥) : ∃ a ∈ omegaZ V, a ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).2 hV
  have : Nontrivial ↥(center ↥V) := hVp.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥V) := hVp.to_subgroup _
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := ↥(center ↥V))
    rw [pow_zero] at hn
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥V)) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  refine ⟨((x : ↥V) : X), ⟨(x : ↥V).2, fun v hv => ?_, ?_⟩, ?_⟩
  · have := Subgroup.mem_center_iff.1 x.2 ⟨v, hv⟩
    exact congrArg Subtype.val this
  · have h' := pow_orderOf_eq_one x
    rw [hx] at h'
    simpa [pow_two] using congrArg (fun w : ↥(center ↥V) => ((w : ↥V) : X)) h'
  · intro h
    have : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    rw [this, orderOf_one] at hx
    omega

theorem orderOf_eq_two_of_sq {M : Type*} [Group M] {g : M} (h : g * g = 1) (h1 : g ≠ 1) :
    orderOf g = 2 := orderOf_eq_prime (by rwa [pow_two]) h1

theorem eq_one_of_odd_of_sq {M : Type*} [Group M] {g : M} (ho : Odd (orderOf g)) (h : g * g = 1) :
    g = 1 := by
  by_contra h1
  have := orderOf_eq_two_of_sq h h1
  rw [this] at ho
  exact absurd ho (by decide)

end Omega

section Claim

variable {G : Type} [Group G] [Finite G] {z : G}

theorem claim_eq (hKill : KillNormal2 z) {H : Subgroup G} (hCH : Cen z ≤ H) (hz2 : orderOf z = 2)
    (hzH : z ∈ H) {V : Subgroup (HBar H)} (hVn : V.Normal) {x : HBar H}
    (hxΩ : x ∈ omegaZ V) (hxC : x ∈ barIn H (Cen z)) (hx1 : x ≠ 1) :
    x = mkH H ⟨z, hzH⟩ := by
  classical
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have hzb2 : orderOf (mkH H ⟨z, hzH⟩) = 2 := orderOf_mk_eq_two H hzH2
  have hzbsq : mkH H ⟨z, hzH⟩ * mkH H ⟨z, hzH⟩ = 1 := by
    have h' := pow_orderOf_eq_one (mkH H ⟨z, hzH⟩)
    rw [hzb2] at h'
    simpa [pow_two] using h'
  have hCen : centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  have hzbC : mkH H ⟨z, hzH⟩ ∈ barIn H (Cen z) := by
    rw [← hCen]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hCcomm : ∀ c ∈ barIn H (Cen z), c * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * c := by
    intro c hc
    rw [← hCen] at hc
    exact Subgroup.mem_centralizer_singleton_iff.1 hc
  have hzb1 : mkH H ⟨z, hzH⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzb2
    omega
  let π := cenToBar H hCH
  let x' : ↥(barIn H (Cen z)) := ⟨x, hxC⟩
  let zb' : ↥(barIn H (Cen z)) := ⟨mkH H ⟨z, hzH⟩, hzbC⟩
  have hx'sq : x' * x' = 1 := Subtype.ext hxΩ.2.2
  have hzb'sq : zb' * zb' = 1 := Subtype.ext hzbsq
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hzb'1 : zb' ≠ 1 := fun h => hzb1 (congrArg Subtype.val h)
  have hker : ∀ u : ↥(barIn H (Cen z)), π u = 1 → u * u = 1 → u = 1 := fun u hu hsq =>
    eq_one_of_odd_of_sq (odd_orderOf_of_cenToBar_eq_one H hCH u hu) hsq
  have hπx : π x' ≠ 1 := fun h => hx'1 (hker x' h hx'sq)
  have hπzb : π zb' ≠ 1 := fun h => hzb'1 (hker zb' h hzb'sq)
  let B'' : Subgroup ↥(barIn H (Cen z)) := (omegaZ V ⊓ barIn H (Cen z)).subgroupOf (barIn H (Cen z))
  have hB''N : B''.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(omegaZ_normal hVn).conj_mem (n : HBar H) hn.1 (g : HBar H),
      (barIn H (Cen z)).mul_mem ((barIn H (Cen z)).mul_mem g.2 n.2) ((barIn H (Cen z)).inv_mem g.2)⟩⟩
  have hBcN : (B''.map π).Normal := Subgroup.Normal.map hB''N π (cenToBar_surjective H hCH)
  have hBcsq : ∀ y ∈ B''.map π, y * y = 1 := by
    rintro _ ⟨y0, hy0, rfl⟩
    have h1 : y0 * y0 = 1 := Subtype.ext (Subgroup.mem_subgroupOf.1 hy0).1.2.2
    rw [← map_mul, h1, map_one]
  have hBc2 := hKill _ hBcN hBcsq
  have hx'B : x' ∈ B'' := Subgroup.mem_subgroupOf.2 ⟨hxΩ, hxC⟩
  have hπxB : π x' ∈ B''.map π := Subgroup.mem_map_of_mem π hx'B
  have hπxc : π x' ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g * π x' * g⁻¹ ∈ B''.map π := hBcN.conj_mem _ hπxB g
    have hg1 : g * π x' * g⁻¹ ≠ 1 := by
      intro h
      apply hπx
      have h2 : π x' = g⁻¹ * (g * π x' * g⁻¹) * g := by group
      rw [h2, h]
      group
    exact mul_inv_eq_iff_eq_mul.1 (eq_of_card_le_two hBc2 hg hπxB hg1 hπx)
  have hΩN : (omegaZ (⊤ : Subgroup (CentralizerBar z))).Normal := omegaZ_normal inferInstance
  have hΩ2 := hKill _ hΩN (fun y hy => hy.2.2)
  have hπxΩ : π x' ∈ omegaZ (⊤ : Subgroup (CentralizerBar z)) :=
    ⟨Subgroup.mem_top _, fun v _ => Subgroup.mem_center_iff.1 hπxc v, by rw [← map_mul, hx'sq, map_one]⟩
  have hπzbc : π zb' ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := cenToBar_surjective H hCH g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hCcomm c c.2)
  have hπzbΩ : π zb' ∈ omegaZ (⊤ : Subgroup (CentralizerBar z)) :=
    ⟨Subgroup.mem_top _, fun v _ => Subgroup.mem_center_iff.1 hπzbc v, by rw [← map_mul, hzb'sq, map_one]⟩
  have hπeq : π x' = π zb' := eq_of_card_le_two hΩ2 hπxΩ hπzbΩ hπx hπzb
  have hu : π (x' * zb') = 1 := by rw [map_mul, ← hπeq, ← map_mul, hx'sq, map_one]
  have hxz : x' * zb' = zb' * x' := Subtype.ext (hCcomm x hxC)
  have hu2 : (x' * zb') * (x' * zb') = 1 := by
    calc (x' * zb') * (x' * zb') = x' * (zb' * x') * zb' := by group
      _ = x' * (x' * zb') * zb' := by rw [← hxz]
      _ = (x' * x') * (zb' * zb') := by group
      _ = 1 := by rw [hx'sq, hzb'sq, one_mul]
  have hu1 : x' * zb' = 1 := hker _ hu hu2
  have hxz' : x' = zb' := by
    have : x' = zb'⁻¹ := eq_inv_of_mul_eq_one_left hu1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzb'sq
  exact congrArg Subtype.val hxz'

end Claim

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem stepOne (hctx : Stage2Ctx G z k S) (hk : k ≠ Kind.m12) {H : Subgroup G}
    (hCH : Cen z ≤ H) (hV : pCore 2 (HBar H) ≠ ⊥) : ConclA z H := by
  classical
  have hKill := killNormal2 hctx hk
  have hz2 := hctx.orderOf_z
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have hzb2 : orderOf (mkH H ⟨z, hzH⟩) = 2 := orderOf_mk_eq_two H hzH2
  have hzbsq : mkH H ⟨z, hzH⟩ * mkH H ⟨z, hzH⟩ = 1 := by
    have h' := pow_orderOf_eq_one (mkH H ⟨z, hzH⟩)
    rw [hzb2] at h'
    simpa [pow_two] using h'
  have hzb1 : mkH H ⟨z, hzH⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzb2
    omega
  have hzbi : (mkH H ⟨z, hzH⟩)⁻¹ = mkH H ⟨z, hzH⟩ := inv_eq_of_mul_eq_one_right hzbsq
  have hCen : centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  have hVn : (pCore 2 (HBar H)).Normal := pCore_normal
  have hVp : IsPGroup 2 ↥(pCore 2 (HBar H)) := pCore_isPGroup
  obtain ⟨a₀, ha₀, ha₀1⟩ := exists_omegaZ_ne_one hVp hV
  have hΩn : (omegaZ (pCore 2 (HBar H))).Normal := omegaZ_normal hVn
  have hzbΩ : mkH H ⟨z, hzH⟩ ∈ omegaZ (pCore 2 (HBar H)) := by
    by_cases hc : mkH H ⟨z, hzH⟩ * a₀ = a₀ * mkH H ⟨z, hzH⟩
    · have h1 : a₀ = mkH H ⟨z, hzH⟩ := by
        refine claim_eq hKill hCH hz2 hzH hVn ha₀ ?_ ha₀1
        rw [← hCen]
        exact Subgroup.mem_centralizer_singleton_iff.2 hc.symm
      rw [← h1]
      exact ha₀
    · have hconj : mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹ ∈ omegaZ (pCore 2 (HBar H)) :=
        hΩn.conj_mem a₀ ha₀ _
      have hbΩ : a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) ∈ omegaZ (pCore 2 (HBar H)) :=
        (omegaZ (pCore 2 (HBar H))).mul_mem ha₀ hconj
      have ha₀i : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀.2.2
      have hcomm : a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) =
          (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) * a₀ := hconj.2.1 a₀ ha₀.1
      have hb1 : a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) ≠ 1 := by
        intro h
        apply hc
        have h2 : mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹ = a₀⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [ha₀i] at h2
        exact mul_inv_eq_iff_eq_mul.1 h2
      have hbC : a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) ∈ barIn H (Cen z) := by
        rw [← hCen, Subgroup.mem_centralizer_singleton_iff]
        have hL : a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) * mkH H ⟨z, hzH⟩ =
            a₀ * mkH H ⟨z, hzH⟩ * a₀ := by group
        have hR : mkH H ⟨z, hzH⟩ * (a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹)) =
            a₀ * mkH H ⟨z, hzH⟩ * a₀ := by
          calc mkH H ⟨z, hzH⟩ * (a₀ * (mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹))
              = mkH H ⟨z, hzH⟩ * ((mkH H ⟨z, hzH⟩ * a₀ * (mkH H ⟨z, hzH⟩)⁻¹) * a₀) := by rw [hcomm]
            _ = (mkH H ⟨z, hzH⟩ * mkH H ⟨z, hzH⟩) * a₀ * (mkH H ⟨z, hzH⟩)⁻¹ * a₀ := by group
            _ = a₀ * mkH H ⟨z, hzH⟩ * a₀ := by rw [hzbsq, one_mul, hzbi]
        rw [hL, hR]
      have h1 := claim_eq hKill hCH hz2 hzH hVn hbΩ hbC hb1
      rw [← h1]
      exact hbΩ
  have hall : ∀ a ∈ omegaZ (pCore 2 (HBar H)), a = 1 ∨ a = mkH H ⟨z, hzH⟩ := by
    intro a ha
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      refine claim_eq hKill hCH hz2 hzH hVn ha ?_ ha1
      rw [← hCen, Subgroup.mem_centralizer_singleton_iff]
      exact (ha.2.1 _ hzbΩ.1).symm
  have hcen : mkH H ⟨z, hzH⟩ ∈ center (HBar H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g * mkH H ⟨z, hzH⟩ * g⁻¹ ∈ omegaZ (pCore 2 (HBar H)) := hΩn.conj_mem _ hzbΩ g
    rcases hall _ hg with h | h
    · exfalso
      apply hzb1
      have h2 : mkH H ⟨z, hzH⟩ = g⁻¹ * (g * mkH H ⟨z, hzH⟩ * g⁻¹) * g := by group
      rw [h2, h]
      group
    · exact mul_inv_eq_iff_eq_mul.1 h
  intro h hh
  have hmem : mkH H ⟨h, hh⟩ ∈ centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 hcen _
  rw [hCen] at hmem
  obtain ⟨c', hc', hcc⟩ := Subgroup.mem_map.1 hmem
  rw [Subgroup.mem_subgroupOf] at hc'
  have hq : c'⁻¹ * ⟨h, hh⟩ ∈ pPrimeCore 2 ↥H := QuotientGroup.eq.1 hcc
  refine ⟨(c' : G), hc', ((c'⁻¹ * ⟨h, hh⟩ : ↥H) : G), Subgroup.mem_map.2 ⟨_, hq, rfl⟩, ?_⟩
  simp

end Main

end CFSG.GH74.GLS.Stage2.Local.P34
