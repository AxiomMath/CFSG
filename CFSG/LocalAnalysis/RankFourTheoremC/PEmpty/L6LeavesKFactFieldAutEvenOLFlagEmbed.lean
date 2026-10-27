module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLThreeAdic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUEvenProj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

namespace OLFlag

open CFSG.Open (StatedScalars StatedProj)
open CFSG.LieType.BorelTits (ReflForm)
open Matrix

section Flag

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem map_eq_of_invariant (Q : Subgroup (V ≃ₗ[F] V)) (W : Submodule F V)
    (h : ∀ g ∈ Q, ∀ v ∈ W, g v ∈ W) : ∀ g ∈ Q, W.map (g : V →ₗ[F] V) = W := fun g hg => by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact h g hg v hv
  · intro w hw
    refine ⟨(g⁻¹ : V ≃ₗ[F] V) w, h g⁻¹ (Q.inv_mem hg) w hw, ?_⟩
    exact (g : V ≃ₗ[F] V).apply_symm_apply w

theorem natCard_linearEquiv_eq_gl [Finite F] {U : Type*} [AddCommGroup U] [Module F U]
    [Module.Finite F U] {a : ℕ} (h : Module.finrank F U = a) :
    Nat.card (U ≃ₗ[F] U) = Nat.card (GL (Fin a) F) := by
  subst h
  exact Nat.card_congr OLThreeAdic.linearEquivEquivGL

theorem card_dvd_of_flag [Finite F] [Module.Finite F V] (Q : Subgroup (V ≃ₗ[F] V))
    (D E : Submodule F V) (hDE : D ≤ E) (hD : ∀ g ∈ Q, ∀ v ∈ D, g v ∈ D)
    (hE : ∀ g ∈ Q, ∀ v ∈ E, g v ∈ E)
    (hker : ∀ g ∈ Q, (∀ d ∈ D, g d = d) → (∀ e ∈ E, g e - e ∈ D) → g = 1) :
    Nat.card Q ∣ Nat.card (D ≃ₗ[F] D) *
      Nat.card ((↥E ⧸ D.comap E.subtype) ≃ₗ[F] (↥E ⧸ D.comap E.subtype)) := by
  have hDm := map_eq_of_invariant Q D hD
  have hEm := map_eq_of_invariant Q E hE
  let ρD : Q →* (D ≃ₗ[F] D) :=
    { toFun := fun g => LinearEquiv.ofSubmodules (g : V ≃ₗ[F] V) D D (hDm g g.2)
      map_one' := by ext; rfl
      map_mul' := fun g g' => by ext; rfl }
  let ρE : Q →* (E ≃ₗ[F] E) :=
    { toFun := fun g => LinearEquiv.ofSubmodules (g : V ≃ₗ[F] V) E E (hEm g g.2)
      map_one' := by ext; rfl
      map_mul' := fun g g' => by ext; rfl }
  have hD'm : ∀ g : Q, (D.comap E.subtype).map (ρE g : E →ₗ[F] E) = D.comap E.subtype := by
    intro g
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show ((ρE g x : E) : V) ∈ D
      exact hD g g.2 x hx
    · rintro ⟨x, hxE⟩ hxD
      have : x ∈ D.map (g : V →ₗ[F] V) := by rw [hDm g g.2]; exact hxD
      obtain ⟨y, hyD, hyx⟩ := this
      exact ⟨⟨y, hDE hyD⟩, hyD, Subtype.ext hyx⟩
  let ρM : Q →* ((↥E ⧸ D.comap E.subtype) ≃ₗ[F] (↥E ⧸ D.comap E.subtype)) :=
    { toFun := fun g => Submodule.Quotient.equiv _ _ (ρE g) (hD'm g)
      map_one' := by
        refine LinearEquiv.ext fun x => ?_
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl
      map_mul' := fun g g' => by
        refine LinearEquiv.ext fun x => ?_
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl }
  have hinj : Function.Injective (ρD.prod ρM) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : ρD g = 1 := (Prod.mk.inj hg).1
    have hg2 : ρM g = 1 := (Prod.mk.inj hg).2
    refine Subtype.ext (hker (g : V ≃ₗ[F] V) g.2 (fun d hd => ?_) (fun e he => ?_))
    · have := congrArg (fun φ : D ≃ₗ[F] D => (φ ⟨d, hd⟩ : V)) hg1
      exact this
    · have := congrArg (fun φ : (↥E ⧸ D.comap E.subtype) ≃ₗ[F] (↥E ⧸ D.comap E.subtype) =>
        φ (Submodule.Quotient.mk ⟨e, he⟩)) hg2
      have h' : Submodule.Quotient.mk (ρE g ⟨e, he⟩) =
          (Submodule.Quotient.mk ⟨e, he⟩ : ↥E ⧸ D.comap E.subtype) := this
      exact (Submodule.Quotient.eq (D.comap E.subtype)).mp h'
  rw [← Nat.card_prod]
  exact Subgroup.card_dvd_of_injective _ hinj

theorem eq_one_of_isotropic_flag [CharP F 2] (β : ReflForm F V) (Q : Subgroup (V ≃ₗ[F] V))
    (hQ : IsPGroup 3 Q) (D : Submodule F V)
    (hQβ : ∀ g ∈ Q, ∀ u v, β.β (g u) (g v) = β.β u v) :
    ∀ g ∈ Q, (∀ d ∈ D, g d = d) → (∀ e ∈ β.perp D, g e - e ∈ D) → g = 1 := by
  intro g hgQ hD hE
  have hn1 : ∀ v : V, g v - v ∈ β.perp D := fun v d hd => by
    have h1 := hQβ g hgQ d v
    rw [hD d hd] at h1
    rw [β.β_sub_right, h1, sub_self]
  have hg4 : g * g * g * g = 1 := by
    refine LinearEquiv.ext fun v => ?_
    show g (g (g (g v))) = v
    obtain ⟨a, ha⟩ : ∃ a : V, a = g v - v := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : V, b = g a - a := ⟨_, rfl⟩
    have e1 : g v = v + a := by rw [ha]; abel
    have e2 : g a = a + b := by rw [hb]; abel
    have haE : a ∈ β.perp D := by rw [ha]; exact hn1 v
    have hbD : b ∈ D := by rw [hb]; exact hE a haE
    have e3 : g b = b := hD b hbD
    have ha2 : a + a = 0 := OLThreeAdic.add_self_eq_zero_of_charTwo (F := F) (V := V) a
    have hb2 : b + b = 0 := OLThreeAdic.add_self_eq_zero_of_charTwo (F := F) (V := V) b
    have e4 : g (g v) = v + b := by
      rw [e1, map_add, e1, e2]
      calc v + a + (a + b) = v + (a + a) + b := by abel
        _ = v + b := by rw [ha2, add_zero]
    have e5 : g (g (g v)) = v + a + b := by
      rw [e4, map_add, e1, e3]
    rw [e5, map_add, map_add, e1, e2, e3]
    calc v + a + (a + b) + b = v + (a + a) + (b + b) := by abel
      _ = v := by rw [ha2, hb2, add_zero, add_zero]
  have hgg : (⟨g, hgQ⟩ : Q) ^ 4 = 1 := by
    apply Subtype.ext
    show g ^ 4 = 1
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
    exact hg4
  obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
  have hd4 : orderOf (⟨g, hgQ⟩ : Q) ∣ 4 := orderOf_dvd_of_pow_eq_one hgg
  have hd3 : orderOf (⟨g, hgQ⟩ : Q) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 4 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf (⟨g, hgQ⟩ : Q) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd4 hd3
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

end Flag

section Main

theorem exists_isotropic_levi_bound {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (β : ReflForm F V) (Q R : Subgroup (V ≃ₗ[F] V)) (hQ : IsPGroup 3 Q) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hQβ : ∀ g ∈ Q, ∀ u v, β.β (g u) (g v) = β.β u v)
    (hRβ : ∀ x ∈ R, ∀ u v, β.β (x u) (x v) = β.β u v)
    (hQR : ∀ g ∈ Q, ∀ x : V ≃ₗ[F] V, x ∈ R ↔ g * x * g⁻¹ ∈ R) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ Module.finrank F V ∧
      padicValNat 3 (Nat.card Q) ≤ padicValNat 3 (Nat.card (GL (Fin k) F)) +
        padicValNat 3 (Nat.card (GL (Fin (Module.finrank F V - 2 * k)) F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let W : Submodule F V :=
    { carrier := {w | ∀ x ∈ R, x w = w}
      add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => map_zero x
      smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx] }
  have hW : ∀ w : V, w ∈ W ↔ ∀ x ∈ R, x w = w := fun w => Iff.rfl
  have hRQ1 : ∀ g ∈ Q, ∀ x ∈ R, g⁻¹ * x * g ∈ R := fun g hg x hx =>
    (hQR g hg (g⁻¹ * x * g)).2 (by
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]
      exact hx)
  have hgg : ∀ g : V ≃ₗ[F] V, ∀ w : V, g ((g⁻¹ : V ≃ₗ[F] V) w) = w := fun g w => by
    have : (g * g⁻¹) w = w := by simp
    simpa [LinearEquiv.mul_apply] using this
  have hWQ : ∀ g ∈ Q, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw x hx
    have h1 : (g⁻¹ * x * g) w = w := hw _ (hRQ1 g hg x hx)
    have h2 : g⁻¹ (x (g w)) = w := by simpa [LinearEquiv.mul_apply] using h1
    have h3 : g (g⁻¹ (x (g w))) = x (g w) := hgg g _
    rw [← h3, h2]
  have hWtop : W ≠ ⊤ := by
    intro hWt
    apply hR1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    ext w
    exact (hW w).1 (hWt ▸ Submodule.mem_top) x hx
  have hU0 : β.perp W ≠ ⊥ := by
    intro hU
    apply hWtop
    have h := β.perp_perp W
    rw [hU, β.perp_bot] at h
    exact h.symm
  have hUR : ∀ x ∈ R, ∀ u ∈ β.perp W, x u ∈ β.perp W := by
    intro x hx u hu w hw
    have hxw : x w = w := (hW w).1 hw x hx
    have h1 := hRβ x hx w u
    rw [hxw] at h1
    rw [h1]
    exact hu w hw
  obtain ⟨v, hvU, hv0, hvR⟩ := exists_ne_zero_fixed_of_stable R hR2 (β.perp W) hUR hU0
  let D : Submodule F V := W ⊓ β.perp W
  have hvD : v ∈ D := ⟨(hW v).2 hvR, hvU⟩
  have hD0 : D ≠ ⊥ := fun h => hv0 (by
    have := hvD
    rw [h] at this
    exact (Submodule.mem_bot F).1 this)
  have hUQ : ∀ g ∈ Q, ∀ u ∈ β.perp W, g u ∈ β.perp W := by
    intro g hg u hu w hw
    have h1 := hQβ g hg (g⁻¹ w) u
    rw [hgg g w] at h1
    rw [h1]
    exact hu _ (hWQ g⁻¹ (Q.inv_mem hg) w hw)
  have hDQ : ∀ g ∈ Q, ∀ u ∈ D, g u ∈ D := fun g hg u hu => ⟨hWQ g hg u hu.1, hUQ g hg u hu.2⟩
  have hDiso : D ≤ β.perp D := fun d₂ hd₂ d₁ hd₁ => hd₂.2 d₁ hd₁.1
  have hEQ : ∀ g ∈ Q, ∀ u ∈ β.perp D, g u ∈ β.perp D := by
    intro g hg u hu d hd
    have h1 := hQβ g hg (g⁻¹ d) u
    rw [hgg g d] at h1
    rw [h1]
    exact hu _ (hDQ g⁻¹ (Q.inv_mem hg) d hd)
  have hdvd := card_dvd_of_flag Q D (β.perp D) hDiso hDQ hEQ
    (eq_one_of_isotropic_flag β Q hQ D hQβ)
  have hk1 : 1 ≤ Module.finrank F D := Submodule.one_le_finrank_iff.2 hD0
  have hperp := β.finrank_perp D
  have hmono := Submodule.finrank_mono hDiso
  have hD'k : Module.finrank F ↥(D.comap (β.perp D).subtype) = Module.finrank F D :=
    (Submodule.comapSubtypeEquivOfLe hDiso).finrank_eq
  have hquot := Submodule.finrank_quotient_add_finrank (D.comap (β.perp D).subtype)
  refine ⟨Module.finrank F D, hk1, by omega, ?_⟩
  have hA : Nat.card (D ≃ₗ[F] D) = Nat.card (GL (Fin (Module.finrank F D)) F) :=
    natCard_linearEquiv_eq_gl rfl
  have hB : Nat.card ((↥(β.perp D) ⧸ D.comap (β.perp D).subtype) ≃ₗ[F]
      (↥(β.perp D) ⧸ D.comap (β.perp D).subtype)) =
      Nat.card (GL (Fin (Module.finrank F V - 2 * Module.finrank F D)) F) :=
    natCard_linearEquiv_eq_gl (by omega)
  have hA0 := OLThreeAdic.natCard_linearEquiv_ne_zero (F := F) (U := D)
  have hB0 := OLThreeAdic.natCard_linearEquiv_ne_zero (F := F)
    (U := ↥(β.perp D) ⧸ D.comap (β.perp D).subtype)
  have hle := padicValNat_le_of_dvd' Nat.prime_three (mul_ne_zero hA0 hB0) hdvd
  rw [padicValNat.mul hA0 hB0, hA, hB] at hle
  exact hle

end Main

section Proj

theorem padicValNat_three_card_normalizer_le_of_isometries {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2] {H : Subgroup (GL ι F)}
    (β : ReflForm F (ι → F))
    (hHβ : ∀ A ∈ H, ∀ u v, β.β (A *ᵥ u) (A *ᵥ v) = β.β u v) (B : ℕ)
    (hB : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ Fintype.card ι →
      padicValNat 3 (Nat.card (GL (Fin k) F)) +
        padicValNat 3 (Nat.card (GL (Fin (Fintype.card ι - 2 * k)) F)) ≤ B)
    (R : Subgroup (StatedProj H)) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    padicValNat 3 (Nat.card (Subgroup.normalizer (R : Set (StatedProj H)))) ≤ B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZc, -⟩ := scalars_subgroupOf_facts ι F H
  obtain ⟨R', hR'2, hR'1, hRN⟩ := OLThreeAdic.exists_two_subgroup_normalized
    ((StatedScalars ι F).subgroupOf H) hZc R hR2 hR1
  set N : Subgroup (StatedProj H) := Subgroup.normalizer (R : Set (StatedProj H)) with hN
  set Ñ : Subgroup H := N.comap (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) with hÑ
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 Ñ))
  let ρ : ↥H →* ((ι → F) ≃ₗ[F] (ι → F)) := (natActionOL ι F).comp H.subtype
  have hρ : Function.Injective ρ := (natActionOL_injective ι F).comp H.subtype_injective
  have hρapp : ∀ (y : ↥H) (u : ι → F), ρ y u = ((y : GL ι F) : Matrix ι ι F) *ᵥ u :=
    fun y u => natActionOL_apply (y : GL ι F) u
  have hiso : ∀ y : ↥H, ∀ u v : ι → F, β.β (ρ y u) (ρ y v) = β.β u v := fun y u v => by
    rw [hρapp, hρapp]
    exact hHβ (y : GL ι F) y.2 u v
  let θ : ↥Ñ →* ((ι → F) ≃ₗ[F] (ι → F)) := ρ.comp Ñ.subtype
  have hθ : Function.Injective θ := hρ.comp Ñ.subtype_injective
  let Q : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := (P : Subgroup Ñ).map θ
  have hQ : IsPGroup 3 Q := P.isPGroup'.map θ
  have hR''2 : IsPGroup 2 (R'.map ρ) := hR'2.map ρ
  have hR''1 : R'.map ρ ≠ ⊥ := fun h => hR'1 ((Subgroup.map_eq_bot_iff_of_injective _ hρ).1 h)
  have hQβ : ∀ g ∈ Q, ∀ u v, β.β (g u) (g v) = β.β u v := by
    intro g hg u v
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact hiso (n : ↥H) u v
  have hRβ : ∀ x ∈ R'.map ρ, ∀ u v, β.β (x u) (x v) = β.β u v := by
    rintro _ ⟨y, -, rfl⟩ u v
    exact hiso y u v
  have hQR : ∀ g ∈ Q, ∀ x : (ι → F) ≃ₗ[F] (ι → F),
      x ∈ R'.map ρ ↔ g * x * g⁻¹ ∈ R'.map ρ := by
    intro g hg x
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.mp hg
    have hnorm := Subgroup.mem_normalizer_iff.mp (hRN n.2)
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(n : ↥H) * y * (n : ↥H)⁻¹, (hnorm y).1 hy, ?_⟩
      show ρ ((n : ↥H) * y * (n : ↥H)⁻¹) = ρ n * ρ y * (ρ n)⁻¹
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨z, hz, hzx⟩
      refine ⟨(n : ↥H)⁻¹ * z * n, (hnorm _).2 (by
        have : (n : ↥H) * ((n : ↥H)⁻¹ * z * n) * (n : ↥H)⁻¹ = z := by group
        rw [this]
        exact hz), ?_⟩
      have hzx' : ρ z = ρ n * x * (ρ n)⁻¹ := hzx
      rw [map_mul, map_mul, map_inv, hzx']
      group
  obtain ⟨k, hk1, hk2, hk⟩ :=
    exists_isotropic_levi_bound β Q (R'.map ρ) hQ hR''2 hR''1 hQβ hRβ hQR
  have hdim : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  rw [hdim] at hk2 hk
  have hbound : padicValNat 3 (Nat.card Q) ≤ B := hk.trans (hB k hk1 hk2)
  have hQcard : Nat.card Q = Nat.card (P : Subgroup Ñ) := Subgroup.card_map_of_injective hθ
  have hPcard : Nat.card (P : Subgroup Ñ) = 3 ^ (Nat.card Ñ).factorization 3 :=
    Sylow.card_eq_multiplicity P
  rw [hQcard, hPcard, padicValNat.prime_pow] at hbound
  have hÑ3 : padicValNat 3 (Nat.card Ñ) ≤ B := by
    rwa [← Nat.factorization_def _ Nat.prime_three]
  have hdvd : Nat.card N ∣ Nat.card Ñ := by
    have := Subgroup.card_map_dvd (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H))
      (H := Ñ)
    rwa [hÑ, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _) N] at this
  exact (padicValNat_le_of_dvd' Nat.prime_three Nat.card_pos.ne' hdvd).trans hÑ3

theorem padicValNat_three_card_normalizer_le_of_isometries_of_equiv {K : Type} [Group K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2]
    {H : Subgroup (GL ι F)} (e : K ≃* StatedProj H) (β : ReflForm F (ι → F))
    (hHβ : ∀ A ∈ H, ∀ u v, β.β (A *ᵥ u) (A *ᵥ v) = β.β u v) (B : ℕ)
    (hB : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ Fintype.card ι →
      padicValNat 3 (Nat.card (GL (Fin k) F)) +
        padicValNat 3 (Nat.card (GL (Fin (Fintype.card ι - 2 * k)) F)) ≤ B)
    (R : Subgroup K) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    padicValNat 3 (Nat.card (Subgroup.normalizer (R : Set K))) ≤ B := by
  have h := padicValNat_three_card_normalizer_le_of_isometries β hHβ B hB (R.map e.toMonoidHom)
    (hR2.map e.toMonoidHom)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h))
  exact (padicValNat_le_of_dvd' Nat.prime_three Nat.card_pos.ne'
    (card_normalizer_dvd_of_mulEquiv e R)).trans h

end Proj

end OLFlag

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
