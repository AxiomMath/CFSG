module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixAbs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

open CFSG.Open Subgroup

variable {G : Type} [Group G]

@[expose] def omegaCenter (D : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ D ∧ v ^ 2 = 1 ∧ ∀ d ∈ D, d * v = v * d}
  one_mem' := ⟨D.one_mem, one_pow 2, fun d _ => by simp⟩
  mul_mem' := by
    rintro u v ⟨huD, hu2, hu⟩ ⟨hvD, hv2, hv⟩
    refine ⟨D.mul_mem huD hvD, ?_, fun d hd => ?_⟩
    · rw [Commute.mul_pow (show Commute u v from hv u huD), hu2, hv2, one_mul]
    · calc d * (u * v) = (d * u) * v := by group
        _ = (u * d) * v := by rw [hu d hd]
        _ = u * (d * v) := by group
        _ = u * (v * d) := by rw [hv d hd]
        _ = u * v * d := by group
  inv_mem' := by
    rintro v ⟨hvD, hv2, hv⟩
    refine ⟨D.inv_mem hvD, ?_, fun d hd => ?_⟩
    · rw [inv_pow, hv2, inv_one]
    · exact (Commute.inv_right (show Commute d v from hv d hd)).eq

theorem omegaCenter_le (D : Subgroup G) : omegaCenter D ≤ D := fun _ hv => hv.1

theorem isElemAbelian_omegaCenter (D : Subgroup G) : IsElemAbelian 2 (omegaCenter D) :=
  ⟨⟨⟨fun a b => Subtype.ext (b.2.2.2 a a.2.1)⟩⟩, fun x hx => hx.2.1⟩

theorem mem_normalizer_omegaCenter {D : Subgroup G} {h : G} (hh : h ∈ normalizer (D : Set G)) :
    h ∈ normalizer (omegaCenter D : Set G) := by
  have key : ∀ h ∈ normalizer (D : Set G), ∀ v ∈ omegaCenter D, h * v * h⁻¹ ∈ omegaCenter D := by
    intro h hh v hv
    obtain ⟨hvD, hv2, hv⟩ := hv
    refine ⟨(mem_normalizer_iff.mp hh v).mp hvD, ?_, fun d hd => ?_⟩
    · calc (h * v * h⁻¹) ^ 2 = h * v ^ 2 * h⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hv2]; group
    · have hd' : h⁻¹ * d * h ∈ D := by
        have e : h * (h⁻¹ * d * h) * h⁻¹ = d := by group
        exact (mem_normalizer_iff.mp hh _).mpr (by rw [e]; exact hd)
      have h1 := hv _ hd'
      calc d * (h * v * h⁻¹) = h * ((h⁻¹ * d * h) * v) * h⁻¹ := by group
        _ = h * (v * (h⁻¹ * d * h)) * h⁻¹ := by rw [h1]
        _ = (h * v * h⁻¹) * d := by group
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key h hh v, fun hv => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hv
  have e : h⁻¹ * (h * v * h⁻¹) * h⁻¹⁻¹ = v := by group
  rwa [e] at this

theorem omegaCenter_char (S : Subgroup G) : ((omegaCenter S).subgroupOf S).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro ϕ x hx
  obtain ⟨-, hx2, hxc⟩ := hx
  refine ⟨(ϕ x).2, ?_, fun s hs => ?_⟩
  · have hx2' : x ^ 2 = 1 := Subtype.ext hx2
    have : (ϕ x) ^ 2 = 1 := by rw [← map_pow, hx2', map_one]
    exact congrArg Subtype.val this
  · set s' : ↥S := ⟨s, hs⟩ with hs'
    have hsx : (ϕ.symm s') * x = x * (ϕ.symm s') :=
      Subtype.ext (hxc _ (ϕ.symm s').2)
    have : s' * ϕ x = ϕ x * s' := by
      calc s' * ϕ x = ϕ (ϕ.symm s') * ϕ x := by rw [ϕ.apply_symm_apply]
        _ = ϕ (ϕ.symm s' * x) := (map_mul ϕ _ _).symm
        _ = ϕ (x * ϕ.symm s') := by rw [hsx]
        _ = ϕ x * ϕ (ϕ.symm s') := map_mul ϕ _ _
        _ = ϕ x * s' := by rw [ϕ.apply_symm_apply]
    exact congrArg Subtype.val this

variable [Finite G]

theorem omegaCenter_ne_bot {S : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    omegaCenter S ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  haveI := hS.center_nontrivial
  have hc : IsPGroup 2 (Subgroup.center ↥S) := hS.to_subgroup _
  have h1 : Nat.card (Subgroup.center ↥S) ≠ 1 := (Finite.one_lt_card (α := Subgroup.center ↥S)).ne'
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥S) := hc.card_eq_or_dvd.resolve_left h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥S) 2 h2
  have hx2 : (x : ↥S) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : ↥S) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  intro hbot
  have hmem : ((x : ↥S) : G) ∈ omegaCenter S := by
    refine ⟨(x : ↥S).2, congrArg Subtype.val hx2, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp x.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext hmem)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal Subgroup

variable {G : Type} [Group G]

@[expose] def conjV {V H : Subgroup G} (hHV : H ≤ normalizer (V : Set G)) (g : ↥H) : MulAut ↥V
    where
  toFun v := ⟨(g : G) * v * (g : G)⁻¹, (mem_normalizer_iff.mp (hHV g.2) v).mp v.2⟩
  invFun v := ⟨(g : G)⁻¹ * v * g, by
    have e : (g : G) * ((g : G)⁻¹ * v * g) * (g : G)⁻¹ = v := by group
    exact (mem_normalizer_iff.mp (hHV g.2) _).mpr (by rw [e]; exact v.2)⟩
  left_inv v := by
    apply Subtype.ext
    show (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) * g = v
    group
  right_inv v := by
    apply Subtype.ext
    show (g : G) * ((g : G)⁻¹ * v * g) * (g : G)⁻¹ = v
    group
  map_mul' a b := by
    apply Subtype.ext
    show (g : G) * (a * b) * (g : G)⁻¹ = (g : G) * a * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹)
    group

@[expose] def repH {V H : Subgroup G} (hHV : H ≤ normalizer (V : Set G)) : ↥H →* MulAut ↥V :=
  MonoidHom.mk' (conjV hHV) fun a b => by
    ext v
    show (a * b : ↥H) * (v : G) * ((a * b : ↥H) : G)⁻¹ =
      (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem repH_apply {V H : Subgroup G} (hHV : H ≤ normalizer (V : Set G)) (h : ↥H) (v : ↥V) :
    ((repH hHV h v : ↥V) : G) = (h : G) * v * (h : G)⁻¹ := rfl

@[expose] def fixedSub {W : Type} [Group W] (τ : MulAut W) : Subgroup W where
  carrier := {w | τ w = w}
  one_mem' := map_one τ
  mul_mem' := fun {a b} ha hb => by
    show τ (a * b) = a * b
    rw [map_mul, show τ a = a from ha, show τ b = b from hb]
  inv_mem' := fun {a} ha => by
    show τ a⁻¹ = a⁻¹
    rw [map_inv, show τ a = a from ha]

theorem mem_fixedSub {W : Type} [Group W] {τ : MulAut W} {w : W} :
    w ∈ fixedSub τ ↔ τ w = w := Iff.rfl

theorem isTransvection_of_card_le {W : Type} [CommGroup W] [Finite W] {τ : MulAut W}
    (hτ : τ ≠ 1) (h : Nat.card W ≤ 2 * Nat.card ↥(fixedSub τ)) : IsTransvection τ := by
  let δ : W →* W := MonoidHom.mk' (fun v => τ v * v⁻¹) fun x y => by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm y⁻¹ x⁻¹]
    exact mul_mul_mul_comm (τ x) (τ y) x⁻¹ y⁻¹
  have hδ : ∀ v, δ v = τ v * v⁻¹ := fun v => rfl
  have hker : δ.ker = fixedSub τ := by
    ext v
    rw [MonoidHom.mem_ker, hδ, mem_fixedSub, mul_inv_eq_one]
  have hrange : Set.range (fun v : W => τ v * v⁻¹) = (δ.range : Set W) := by
    ext w
    simp [MonoidHom.mem_range, hδ]
  have hprod : Nat.card δ.ker * Nat.card δ.range = Nat.card W := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  refine ⟨hτ, ?_⟩
  rw [hrange, Subgroup.closure_eq]
  have hpos : 0 < Nat.card δ.ker := Nat.card_pos
  have hle : Nat.card δ.range ≤ 2 := by
    rw [hker] at hprod hpos
    have : Nat.card ↥(fixedSub τ) * Nat.card δ.range ≤ Nat.card ↥(fixedSub τ) * 2 := by
      rw [hprod, mul_comm]
      exact h
    exact Nat.le_of_mul_le_mul_left this hpos
  have hge : 1 < Nat.card δ.range := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    apply hτ
    ext v
    have : δ v ∈ δ.range := ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot, hδ, mul_inv_eq_one] at this
    simpa using this
  omega

theorem card_le_two_of_sq {C : Type*} [Group C] [Finite C] [IsCyclic C] (R : Subgroup C)
    (hR : ∀ x ∈ R, x ^ 2 = 1) : Nat.card R ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hbot : R = ⊥
  · rw [hbot, Subgroup.card_bot]
    norm_num
  · obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hbot)
    have hx2 : (x : C) ^ 2 = 1 := hR x x.2
    have hx1' : (x : C) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxo : orderOf (x : C) = 2 := orderOf_eq_prime hx2 hx1'
    have hle : R ≤ zpowers (x : C) := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      · have := eq_of_sq_eq_one (hR y hy) hx2 hy1 hx1'
        rw [this]
        exact mem_zpowers _
    calc Nat.card R ≤ Nat.card ↥(zpowers (x : C)) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
      _ = 2 := by rw [Nat.card_zpowers, hxo]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix
