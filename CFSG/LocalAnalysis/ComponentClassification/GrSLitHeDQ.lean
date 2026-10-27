module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUComp

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

namespace HeDQ

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_mul_of_mem_sup {A B : Subgroup Q} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    {k : Q} (hk : k ∈ A ⊔ B) : ∃ m ∈ A, ∃ n ∈ B, m * n = k := by
  have hle : A ≤ normalizer (B : Set Q) := fun x hx => by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hAB x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hAB _ (inv_mem hx) _ hy
      have h2 : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x * y * x⁻¹ * x⁻¹ * x := by rw [h1]
          _ = x * y * x⁻¹ := by group
      rw [h2]
      exact hy
  have hk' : k ∈ (A : Set Q) * (B : Set Q) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hle]
    exact hk
  obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hk'
  exact ⟨m, hm, n, hn, hmn⟩

variable {A B : Subgroup Q} {α : Q}

@[expose] def delta (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) : ↥A →* Q where
  toFun x := (x : Q) * (α * x * α⁻¹)
  map_one' := by simp
  map_mul' x y := by
    simp only [coe_mul]
    have h := hAB y y.2 _ (hαA x x.2)
    calc (x : Q) * y * (α * (x * y) * α⁻¹)
        = x * (y * (α * x * α⁻¹)) * (α * y * α⁻¹) := by group
      _ = x * ((α * x * α⁻¹) * y) * (α * y * α⁻¹) := by rw [h]
      _ = x * (α * x * α⁻¹) * (y * (α * y * α⁻¹)) := by group

omit [Finite Q] in
theorem delta_apply (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (x : ↥A) :
    delta hAB hαA x = (x : Q) * (α * x * α⁻¹) := rfl

omit [Finite Q] in
theorem delta_injective (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hAB1 : A ⊓ B = ⊥) :
    Function.Injective (delta hAB hαA) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, delta_apply] at hx
  have h1 : α * (x : Q) * α⁻¹ = (x : Q)⁻¹ := eq_inv_of_mul_eq_one_right hx
  have h2 : ((x : Q))⁻¹ ∈ A ⊓ B := mem_inf.mpr ⟨inv_mem x.2, h1 ▸ hαA x x.2⟩
  rw [hAB1, mem_bot, inv_eq_one] at h2
  exact (mem_bot).mpr (Subtype.ext h2)

omit [Finite Q] in
theorem mem_range_iff (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) (hAB1 : A ⊓ B = ⊥)
    {k : Q} : k ∈ (A ⊔ B) ⊓ centralizer ({α} : Set Q) ↔ k ∈ (delta hAB hαA).range := by
  have hainv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  constructor
  · rintro ⟨hk, hkα⟩
    obtain ⟨m, hm, n, hn, rfl⟩ := exists_mul_of_mem_sup hAB hk
    have hc : m * n * α = α * (m * n) := mem_centralizer_singleton_iff.mp hkα
    have h1 : (α * n * α⁻¹) * (α * m * α⁻¹) = m * n := by
      have h2 : (α * m * α⁻¹) * (α * n * α⁻¹) = m * n := by
        calc (α * m * α⁻¹) * (α * n * α⁻¹) = α * (m * n) * α⁻¹ := by group
          _ = m * n * α * α⁻¹ := by rw [hc]
          _ = m * n := by group
      rw [← h2]
      exact hAB _ (hαB n hn) _ (hαA m hm)
    have h3 : (α * n * α⁻¹)⁻¹ * m ∈ A ⊓ B := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hαB n hn)) hm, ?_⟩
      have : (α * n * α⁻¹)⁻¹ * m = (α * m * α⁻¹) * n⁻¹ := by
        calc (α * n * α⁻¹)⁻¹ * m = (α * n * α⁻¹)⁻¹ * (m * n) * n⁻¹ := by group
          _ = (α * n * α⁻¹)⁻¹ * ((α * n * α⁻¹) * (α * m * α⁻¹)) * n⁻¹ := by rw [h1]
          _ = (α * m * α⁻¹) * n⁻¹ := by group
      rw [this]
      exact mul_mem (hαA m hm) (inv_mem hn)
    rw [hAB1, mem_bot] at h3
    have hn' : n = α * m * α⁻¹ := by
      have h4 : α * n * α⁻¹ = m := by
        calc α * n * α⁻¹ = (α * n * α⁻¹) * ((α * n * α⁻¹)⁻¹ * m) := by rw [h3, mul_one]
          _ = m := by group
      calc n = α⁻¹ * (α * n * α⁻¹) * α := by group
        _ = α⁻¹ * m * α := by rw [h4]
        _ = α * m * α⁻¹ := by rw [hainv]
    exact ⟨⟨m, hm⟩, by rw [delta_apply, hn']⟩
  · rintro ⟨x, rfl⟩
    rw [delta_apply]
    refine mem_inf.mpr ⟨mul_mem (mem_sup_left x.2) (mem_sup_right (hαA x x.2)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h := hAB x x.2 _ (hαA x x.2)
    calc (x : Q) * (α * x * α⁻¹) * α = (α * x * α⁻¹) * x * α := by rw [h]
      _ = α * ((x : Q) * (α * x * α⁻¹)) := by rw [hainv]; group

theorem pLayer_eq_top {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G)
    (hO : pPrimeCore 2 G = ⊥) : pLayer G 2 = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : IsComponent (⊤ : Subgroup G) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq, IsSubnormal.top⟩
  have hnt : Nontrivial G := LocalCores.isQuasisimple_nontrivial hq
  have hnle : ¬ (⊤ : Subgroup G) ≤ pPrimeCore 2 G := by
    rw [hO, le_bot_iff]
    exact top_ne_bot
  exact eq_top_iff.mpr (le_sSup
    (LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp hnle))

theorem gsFixedLayer_eq_range (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) (hAB1 : A ⊓ B = ⊥)
    (hAq : IsQuasisimple ↥A) (hAO : pPrimeCore 2 ↥A = ⊥) :
    gsFixedLayer (A ⊔ B) α = (delta hAB hαA).range ∧ IsQuasisimple ↥(delta hAB hαA).range ∧
      pPrimeCore 2 ↥(delta hAB hαA).range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set δ := delta hAB hαA with hδ
  set D := (A ⊔ B) ⊓ centralizer ({α} : Set Q) with hD
  have hDr : D = δ.range := by
    ext k
    exact mem_range_iff hα hAB hαA hαB hAB1
  let e : ↥A ≃* ↥δ.range := MonoidHom.ofInjective (delta_injective hAB hαA hAB1)
  have hq : IsQuasisimple ↥δ.range := LocalCores.isQuasisimple_of_mulEquiv e hAq
  have hO : pPrimeCore 2 ↥δ.range = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e, hAO, Subgroup.map_bot]
  have hlay : pLayer ↥δ.range 2 = ⊤ := pLayer_eq_top hq hO
  refine ⟨?_, hq, hO⟩
  show (pLayer ↥D 2).map D.subtype = δ.range
  rw [hDr, hlay, ← MonoidHom.range_eq_map, range_subtype]

theorem exists_central_involution (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) (hAB1 : A ⊓ B = ⊥)
    (hAq : IsQuasisimple ↥A) (hAO : pPrimeCore 2 ↥A = ⊥) {V : Subgroup Q}
    (hV : V ≤ (Open.fusionZStar ↥(gsFixedLayer (A ⊔ B) α)).map
      (gsFixedLayer (A ⊔ B) α).subtype)
    (hVe : IsElemTwo V) (hV4 : Nat.card V = 4) :
    (∀ v ∈ V, ∀ g ∈ A ⊔ B, v * g = g * v) ∧
      ∃ x ∈ A, x * x = 1 ∧ x ≠ 1 ∧ x ∉ V ∧ ∀ g ∈ A ⊔ B, x * g = g * x := by
  have hainv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  obtain ⟨hT, hq, hO⟩ := gsFixedLayer_eq_range hα hAB hαA hαB hAB1 hAq hAO
  set δ := delta hAB hαA with hδ
  have hinj := delta_injective hAB hαA hAB1
  rw [hT] at hV
  have hZ : Open.fusionZStar ↥δ.range = center ↥δ.range :=
    GrS5.fusionZStar_eq_center_of_le hq.1.commutator_eq_top (by rw [hO]; exact bot_le)
  rw [hZ] at hV
  have hcen : ∀ v ∈ V, ∃ x : ↥A, δ x = v ∧ ∀ y : ↥A, x * y = y * x := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := hV hv
    obtain ⟨x, hx⟩ := c.2
    refine ⟨x, hx.trans hcv, fun y => hinj ?_⟩
    have h := mem_center_iff.mp hc ⟨δ y, ⟨y, rfl⟩⟩
    have h' := congrArg Subtype.val h
    simp only [coe_mul] at h'
    rw [map_mul, map_mul, hx]
    exact h'.symm
  have hcomm : ∀ x : ↥A, (∀ y : ↥A, x * y = y * x) → ∀ g ∈ A ⊔ B,
      (x : Q) * g = g * x ∧ (α * x * α⁻¹) * g = g * (α * x * α⁻¹) := by
    intro x hx g hg
    have hxA : ∀ a ∈ A, (x : Q) * a = a * x := fun a ha =>
      congrArg Subtype.val (hx ⟨a, ha⟩)
    have hxB : ∀ b ∈ B, (x : Q) * b = b * x := fun b hb => hAB x x.2 b hb
    have hαxA : ∀ a ∈ A, (α * x * α⁻¹) * a = a * (α * x * α⁻¹) := fun a ha =>
      (hAB a ha _ (hαA x x.2)).symm
    have hαxB : ∀ b ∈ B, (α * x * α⁻¹) * b = b * (α * x * α⁻¹) := by
      intro b hb
      have hb' : α⁻¹ * b * α ∈ A := by
        rw [hainv]
        simpa [hainv] using hαB b hb
      have h := hxA _ hb'
      calc (α * x * α⁻¹) * b = α * ((x : Q) * (α⁻¹ * b * α)) * α⁻¹ := by group
        _ = α * ((α⁻¹ * b * α) * x) * α⁻¹ := by rw [h]
        _ = b * (α * x * α⁻¹) := by group
    exact ⟨HeUC.commute_of_le_sup hxA hxB hg, HeUC.commute_of_le_sup hαxA hαxB hg⟩
  refine ⟨fun v hv g hg => ?_, ?_⟩
  · obtain ⟨x, rfl, hx⟩ := hcen v hv
    obtain ⟨h1, h2⟩ := hcomm x hx g hg
    rw [delta_apply]
    calc (x : Q) * (α * x * α⁻¹) * g = x * (g * (α * x * α⁻¹)) := by rw [mul_assoc, h2]
      _ = g * ((x : Q) * (α * x * α⁻¹)) := by rw [← mul_assoc, h1, mul_assoc]
  · have : Nontrivial ↥V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨v, hv⟩, hv1⟩ := exists_ne (1 : ↥V)
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    obtain ⟨x, hxv, hx⟩ := hcen v hv
    refine ⟨x, x.2, ?_, ?_, ?_, fun g hg => (hcomm x hx g hg).1⟩
    · have h : δ (x * x) = δ 1 := by rw [map_mul, hxv, hVe.2 v hv, map_one]
      exact congrArg Subtype.val (hinj h)
    · intro h
      apply hv1'
      rw [← hxv, show x = 1 from Subtype.ext h, map_one]
    · intro hxV
      have hxT : (x : Q) ∈ δ.range := by
        obtain ⟨c, -, hcx⟩ := hV hxV
        rw [← hcx]
        exact c.2
      have hxα : (x : Q) * α = α * x :=
        mem_centralizer_singleton_iff.mp (mem_inf.mp ((mem_range_iff hα hAB hαA hαB hAB1).mpr
          hxT)).2
      have hxB : (x : Q) ∈ B := by
        have h := hαA x x.2
        rwa [show α * (x : Q) * α⁻¹ = x by rw [← hxα]; group] at h
      have h1 : (x : Q) ∈ A ⊓ B := mem_inf.mpr ⟨x.2, hxB⟩
      rw [hAB1, mem_bot] at h1
      apply hv1'
      rw [← hxv, show x = 1 from Subtype.ext h1, map_one]

end HeDQ

end CFSG.ComponentClassification.GrSLit
