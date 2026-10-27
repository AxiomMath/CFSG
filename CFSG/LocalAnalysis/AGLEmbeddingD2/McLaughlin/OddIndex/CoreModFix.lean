module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreInduction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrob

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Core

variable {Y I : Type} [Group Y] [CommGroup I] {ρ : Y →* MulAut I}

theorem actSub_eq_of_inv_mul_mem {W : Subgroup I} (hW : ActInv ρ W) {y y' : Y}
    {P : Subgroup Y} (hP : ∀ p ∈ P, ∀ w ∈ W, ρ p w = w) (h : y⁻¹ * y' ∈ P) :
    actSub ρ W hW y' = actSub ρ W hW y := by
  ext w
  have : y' = y * (y⁻¹ * y') := by group
  rw [actSub_apply, actSub_apply, this, map_mul, MulAut.mul_apply, hP _ h w w.2]

theorem fix_or_trivial (P : Subgroup Y) [P.Normal] (hsimple : IsSimpleGroup (Y ⧸ P))
    (hsq : ∀ x : I, x * x = 1) (W : Subgroup I) (hW : ActInv ρ W)
    (hP : ∀ p ∈ P, ∀ w ∈ W, ρ p w = w) {a₁ b₁ : Y} (ha₁ : a₁ ^ 3 = 1) (hb7 : b₁ ^ 7 ∈ P)
    (hb : (QuotientGroup.mk b₁ : Y ⧸ P) ≠ 1) (hrel : (b₁ ^ 2 * a₁)⁻¹ * (a₁ * b₁) ∈ P) :
    (∃ x ∈ W, x ≠ 1 ∧ ρ a₁ x = x) ∨ ∀ w ∈ W, ρ a₁ w = w := by
  have hsqW : ∀ x : ↥W, x * x = 1 := fun x => Subtype.ext (hsq x)
  have hα3 : actSub ρ W hW a₁ ^ 3 = 1 := by
    rw [← map_pow, ha₁, map_one]
  have hβ7 : actSub ρ W hW b₁ ^ 7 = 1 := by
    rw [← map_pow, actSub_eq_of_inv_mul_mem hW hP (y := 1) (y' := b₁ ^ 7) (by simpa using hb7),
      map_one]
  have hαβ : actSub ρ W hW a₁ * actSub ρ W hW b₁ = actSub ρ W hW b₁ ^ 2 * actSub ρ W hW a₁ := by
    rw [← map_mul, actSub_eq_of_inv_mul_mem hW hP (y := b₁ ^ 2 * a₁) (y' := a₁ * b₁) hrel,
      map_mul, map_pow]
  rcases frob_fixed hsqW hα3 hβ7 hαβ with ⟨x, hx1, hx⟩ | hβ
  · exact Or.inl ⟨x, x.2, fun h => hx1 (Subtype.ext h), congrArg Subtype.val hx⟩
  · right
    let N : Subgroup Y :=
      { carrier := {y | ∀ w ∈ W, ρ y w = w}
        mul_mem' := fun {y z} hy hz w hw => by
          change ρ (y * z) w = w
          rw [map_mul, MulAut.mul_apply, hz w hw, hy w hw]
        one_mem' := fun w _ => by rw [map_one]; rfl
        inv_mem' := fun {y} hy w hw => by
          change ρ y⁻¹ w = w
          have := hy w hw
          calc ρ y⁻¹ w = ρ y⁻¹ (ρ y w) := by rw [this]
            _ = w := ρ_inv_apply ρ y w }
    have hNn : N.Normal := ⟨fun n hn g w hw => by
      change ρ (g * n * g⁻¹) w = w
      have hgw : ρ g⁻¹ w ∈ W := hW g⁻¹ w hw
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hn _ hgw, ρ_apply_inv]⟩
    have hPN : P ≤ N := fun p hp w hw => hP p hp w hw
    have hb₁ : b₁ ∈ N := fun w hw => congrArg Subtype.val (hβ ⟨w, hw⟩)
    have hNm : N.map (QuotientGroup.mk' P) ≠ ⊥ := by
      intro h
      have : (QuotientGroup.mk' P) b₁ ∈ N.map (QuotientGroup.mk' P) := ⟨b₁, hb₁, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact hb this
    have hNtop : N.map (QuotientGroup.mk' P) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' P))).resolve_left hNm
    have : (QuotientGroup.mk' P) a₁ ∈ N.map (QuotientGroup.mk' P) := by rw [hNtop]; trivial
    obtain ⟨n, hn, hna⟩ := this
    have hna' : n⁻¹ * a₁ ∈ P := QuotientGroup.eq.1 hna
    have ha₁N : a₁ ∈ N := by
      have : a₁ = n * (n⁻¹ * a₁) := by group
      rw [this]
      exact N.mul_mem hn (hPN hna')
    exact ha₁N

end Core

theorem modFix {Y : Type} [Group Y] [Finite Y] (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) {a : Y}
    (ha : orderOf a = 3) : ModFix Y a := by
  intro I _ _ hcomm hnt hsq ρ
  letI : CommGroup I := { ‹Group I› with mul_comm := hcomm }
  set P := CFSG.pCore 2 Y with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hsimple : IsSimpleGroup (Y ⧸ P) := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple hY
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  let W : Subgroup I :=
    { carrier := {x | ∀ p ∈ P, ρ p x = x}
      mul_mem' := fun {x y} hx hy p hp => by
        rw [map_mul, hx p hp, hy p hp]
      one_mem' := fun p _ => map_one _
      inv_mem' := fun {x} hx p hp => by
        rw [map_inv, hx p hp] }
  have hPW : ∀ p ∈ P, ∀ w ∈ W, ρ p w = w := fun p hp w hw => hw p hp
  have hW : ActInv ρ W := by
    intro y x hx p hp
    have hp' : y⁻¹ * p * y ∈ P := by
      have := hPn.conj_mem p hp y⁻¹
      simpa using this
    have e : ρ p (ρ y x) = ρ y (ρ (y⁻¹ * p * y) x) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hx _ hp']
  have hW1 : ∃ x₁ ∈ W, x₁ ≠ 1 := by
    obtain ⟨x₀, hx₀⟩ := exists_ne (1 : I)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hx₀2 : x₀ ^ 2 = 1 := by rw [pow_two]; exact hsq x₀
    have hord : orderOf x₀ = 2 := orderOf_eq_prime hx₀2 hx₀
    have h2 : 2 ∣ Nat.card I := hord ▸ orderOf_dvd_natCard x₀
    letI : MulAction ↥P I := MulAction.compHom I (ρ.comp P.subtype)
    have hmod := IsPGroup.card_modEq_card_fixedPoints hP2 (α := I)
    have hev : 2 ∣ Nat.card (MulAction.fixedPoints ↥P I) :=
      (Nat.ModEq.dvd_iff hmod (dvd_refl 2)).mp h2
    have h1₀ : (1 : I) ∈ MulAction.fixedPoints ↥P I := fun p => by
      show ρ p 1 = 1
      exact map_one _
    haveI : Nonempty (MulAction.fixedPoints ↥P I) := ⟨⟨1, h1₀⟩⟩
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P I) := Nat.card_pos
    have h1 : 1 < Nat.card (MulAction.fixedPoints ↥P I) := by
      obtain ⟨m, hm⟩ := hev
      omega
    by_contra hno
    push Not at hno
    have hsub : Subsingleton (MulAction.fixedPoints ↥P I) := ⟨fun x y => by
      apply Subtype.ext
      have hx := hno x.1 (fun p hp => x.2 ⟨p, hp⟩)
      have hy := hno y.1 (fun p hp => y.2 ⟨p, hp⟩)
      rw [hx, hy]⟩
    have := Nat.card_unique (α := MulAction.fixedPoints ↥P I)
    omega
  obtain ⟨x₁, hx₁W, hx₁⟩ := hW1
  have haP : a ∉ P := by
    intro h
    obtain ⟨k, hk⟩ := hP2 ⟨a, h⟩
    have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [ha] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hc : orderOf (QuotientGroup.mk a : Y ⧸ P) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ha3, QuotientGroup.mk_one]
    · intro h
      exact haP ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨bb, hb7, hb1, hcases⟩ := exists_frobenius_pair hY hc
  obtain ⟨b₁, rfl⟩ := QuotientGroup.mk_surjective bb
  have hb7' : b₁ ^ 7 ∈ P := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hb7
  have final : ∀ a₁ : Y, (a₁ = a ∨ a₁ = a⁻¹) →
      ((∃ x ∈ W, x ≠ 1 ∧ ρ a₁ x = x) ∨ ∀ w ∈ W, ρ a₁ w = w) →
      ∃ x : I, x ≠ 1 ∧ ρ a x = x := by
    intro a₁ ha₁ h
    obtain ⟨x, hx1, hx⟩ : ∃ x : I, x ≠ 1 ∧ ρ a₁ x = x := by
      rcases h with ⟨x, -, hx1, hx⟩ | h
      · exact ⟨x, hx1, hx⟩
      · exact ⟨x₁, hx₁, h x₁ hx₁W⟩
    refine ⟨x, hx1, ?_⟩
    rcases ha₁ with rfl | rfl
    · exact hx
    · calc ρ a x = ρ a (ρ a⁻¹ x) := by rw [hx]
        _ = x := ρ_apply_inv ρ a x
  rcases hcases with h | h
  · refine final a (Or.inl rfl) (fix_or_trivial P hsimple hsq W hW hPW ha3 hb7' hb1 ?_)
    have : (QuotientGroup.mk (a * b₁) : Y ⧸ P) = QuotientGroup.mk (b₁ ^ 2 * a) := by
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_pow] using h
    exact (QuotientGroup.eq.1 this.symm)
  · refine final a⁻¹ (Or.inr rfl) (fix_or_trivial P hsimple hsq W hW hPW
      (by rw [inv_pow, ha3, inv_one]) hb7' hb1 ?_)
    have : (QuotientGroup.mk (a⁻¹ * b₁) : Y ⧸ P) = QuotientGroup.mk (b₁ ^ 2 * a⁻¹) := by
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_inv] using h
    exact (QuotientGroup.eq.1 this.symm)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
