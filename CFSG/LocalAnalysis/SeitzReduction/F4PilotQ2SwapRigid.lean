module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapPropagate

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

section Fac

variable {A : Type*} [Group A]

theorem fac_of_fix_left [IsSimpleGroup A] (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    (θ : MulAut (A × A)) {o : A} (ho : o ≠ 1) (hθo : θ (o, 1) = (o, 1)) :
    (∀ a, (θ (a, 1)).2 = 1) ∧ (∀ b, (θ (1, b)).1 = 1) := by
  set α : A →* A := (MonoidHom.fst A A).comp (θ.toMonoidHom.comp (MonoidHom.inl A A)) with hα
  set β : A →* A := (MonoidHom.snd A A).comp (θ.toMonoidHom.comp (MonoidHom.inl A A)) with hβ
  have hθa : ∀ a, θ (a, 1) = (α a, β a) := fun a => rfl
  have hconj : ∀ (x : A × A) (a : A), θ (x * (a, 1) * x⁻¹) = θ x * θ (a, 1) * (θ x)⁻¹ := by
    intro x a
    rw [map_mul, map_mul, map_inv]
  have hx1 : ∀ (x : A × A) (a : A), x * (a, 1) * x⁻¹ = (x.1 * a * x.1⁻¹, 1) := by
    intro x a
    ext <;> simp
  have hnα : α.range.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨a, rfl⟩ := hy
    set x := θ.symm (c, 1) with hx
    have h1 := congrArg Prod.fst (hconj x a)
    simp only [hx1, hx, MulEquiv.apply_symm_apply, hθa, Prod.fst_mul, Prod.fst_inv] at h1
    exact ⟨_, h1⟩
  have hnβ : β.range.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨a, rfl⟩ := hy
    set x := θ.symm (1, c) with hx
    have h1 := congrArg Prod.snd (hconj x a)
    simp only [hx1, hx, MulEquiv.apply_symm_apply, hθa, Prod.snd_mul, Prod.snd_inv] at h1
    exact ⟨_, h1⟩
  have hcomm : ∀ a b, θ (a, 1) * θ (1, b) = θ (1, b) * θ (a, 1) := by
    intro a b
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hαo : α o = o := by rw [hα]; simp [hθo]
  have hα1 : α.range = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α.range with h | h
    · exfalso
      have : α o ∈ α.range := ⟨o, rfl⟩
      rw [h, mem_bot, hαo] at this
      exact ho this
    · exact h
  have hα' : ∀ b, (θ (1, b)).1 = 1 := by
    intro b
    refine hZ _ fun c => ?_
    obtain ⟨a, rfl⟩ : c ∈ α.range := hα1 ▸ mem_top c
    have h1 := congrArg Prod.fst (hcomm a b)
    rw [hθa] at h1
    simpa using h1.symm
  refine ⟨?_, hα'⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal β.range with hβ0 | hβ1
  · intro a
    have : β a ∈ β.range := ⟨a, rfl⟩
    rw [hβ0] at this
    exact this
  · exfalso
    have hβ' : ∀ b, (θ (1, b)).2 = 1 := by
      intro b
      refine hZ _ fun c => ?_
      obtain ⟨a, rfl⟩ : c ∈ β.range := hβ1 ▸ mem_top c
      have h1 := congrArg Prod.snd (hcomm a b)
      rw [hθa] at h1
      simpa using h1.symm
    obtain ⟨b, hb⟩ := exists_ne (1 : A)
    have h1 : θ (1, b) = θ 1 := by
      rw [map_one]
      ext
      · exact hα' b
      · exact hβ' b
    have h2 := congrArg Prod.snd (θ.injective h1)
    exact hb h2

end Fac

section Overlap

variable {G : Type*} [Group G] [Finite G] {t : G} {D : Subgroup G}

theorem conj_mem_centralizerPerfectCore_of_mem_centralizer {X : Subgroup G} {c : G}
    (hc : c ∈ centralizer (X : Set G)) {y : G} (hy : y ∈ centralizerPerfectCore X) :
    c * y * c⁻¹ ∈ centralizerPerfectCore X := by
  have hX : X.map (MulAut.conj c).toMonoidHom = X := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      have h := mem_centralizer_iff.1 hc x' hx'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← h, mul_inv_cancel_right]
      exact hx'
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h := mem_centralizer_iff.1 hc x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← h, mul_inv_cancel_right]
  have h := map_centralizerPerfectCore (MulAut.conj c) X
  rw [hX] at h
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem exists_eq_mul_of_mem_overlapCentralizer (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) {X X'' O : Subgroup G}
    (hr : P.Ψ.range = centralizerPerfectCore X) [IsSimpleGroup D]
    (hZD : ∀ a : D, (∀ b : D, a * b = b * a) → a = 1)
    (hAut : ∀ φ : MulAut D, ∃ g : D, φ = MulAut.conj g)
    (hX'' : X'' ≤ D) (hO : O ≤ D) {o₀ : G} (ho₀ : o₀ ∈ O) (ho₀1 : o₀ ≠ 1)
    {c : G} (hcX : c ∈ centralizer (X : Set G)) (hcX'' : c ∈ centralizer (X'' : Set G))
    (hcO : ∀ o ∈ O, c * P.lft o = P.lft o * c)
    (hcO' : ∀ o ∈ O, c * (t * P.lft o * t⁻¹) = (t * P.lft o * t⁻¹) * c) :
    ∃ g h : D, (∀ o ∈ O, (g : G) * o = o * g) ∧ (∀ x ∈ X'', (g : G) * x = x * g) ∧
      (∀ o ∈ O, (h : G) * o = o * h) ∧ (∀ x ∈ X'', (h : G) * x = x * h) ∧
      (P.Ψ (g, h))⁻¹ * c ∈ centralizer (X : Set G) ∧
      (P.Ψ (g, h))⁻¹ * c ∈ centralizer (centralizerPerfectCore X : Set G) := by
  have hmem : ∀ p : D × D, c * P.Ψ p * c⁻¹ ∈ P.Ψ.range := fun p => by
    rw [hr]
    exact conj_mem_centralizerPerfectCore_of_mem_centralizer hcX (hr ▸ ⟨p, rfl⟩)
  let θf : D × D → D × D := fun p => (MonoidHom.ofInjective hinj).symm ⟨c * P.Ψ p * c⁻¹, hmem p⟩
  have hθf : ∀ p, P.Ψ (θf p) = c * P.Ψ p * c⁻¹ := fun p =>
    MonoidHom.apply_ofInjective_symm hinj _
  have hθmul : ∀ p q, θf (p * q) = θf p * θf q := fun p q => hinj (by
    rw [map_mul, hθf, hθf, hθf, map_mul]
    group)
  have hθone : θf 1 = 1 := hinj (by rw [hθf, map_one]; group)
  have hθinj : Function.Injective θf := fun p q hpq => hinj (by
    have h1 := congrArg P.Ψ hpq
    rw [hθf, hθf] at h1
    simpa using h1)
  let θhom : D × D →* D × D := { toFun := θf, map_one' := hθone, map_mul' := hθmul }
  let θ : MulAut (D × D) :=
    MulEquiv.ofBijective θhom ⟨hθinj, Finite.injective_iff_surjective.1 hθinj⟩
  have hθ : ∀ p, θ p = θf p := fun p => rfl
  have hfix : ∀ p, c * P.Ψ p * c⁻¹ = P.Ψ p → θ p = p := fun p h => hinj (by rw [hθ, hθf, h])
  have hfixO1 : ∀ o (ho : o ∈ O), θ (⟨o, hO ho⟩, 1) = (⟨o, hO ho⟩, 1) := by
    intro o ho
    refine hfix _ ?_
    have e : P.Ψ (⟨o, hO ho⟩, 1) = P.lft o := (P.lft_of_mem (hO ho)).symm
    rw [e, hcO o ho, mul_inv_cancel_right]
  have hfix1O : ∀ o (ho : o ∈ O), θ (1, ⟨o, hO ho⟩) = (1, ⟨o, hO ho⟩) := by
    intro o ho
    refine hfix _ ?_
    have e : P.Ψ (1, ⟨o, hO ho⟩) = t * P.lft o * t⁻¹ := (P.conj_lft_of_mem (hO ho)).symm
    rw [e, hcO' o ho, mul_inv_cancel_right]
  have hfixX : ∀ x (hx : x ∈ X''),
      θ (⟨x, hX'' hx⟩, ⟨x, hX'' hx⟩) = (⟨x, hX'' hx⟩, ⟨x, hX'' hx⟩) := by
    intro x hx
    refine hfix _ ?_
    rw [P.diag]
    have h := mem_centralizer_iff.1 hcX'' x hx
    rw [← h, mul_inv_cancel_right]
  have ho1 : (⟨o₀, hO ho₀⟩ : D) ≠ 1 := fun h => ho₀1 (congrArg Subtype.val h)
  obtain ⟨hfac₁, hfac₂⟩ := fac_of_fix_left hZD θ ho1 (hfixO1 o₀ ho₀)
  set α : D →* D := (MonoidHom.fst D D).comp (θ.toMonoidHom.comp (MonoidHom.inl D D)) with hα
  set β : D →* D := (MonoidHom.snd D D).comp (θ.toMonoidHom.comp (MonoidHom.inr D D)) with hβ
  have hθa : ∀ a, θ (a, 1) = (α a, 1) := fun a => Prod.ext rfl (hfac₁ a)
  have hθb : ∀ b, θ (1, b) = (1, β b) := fun b => Prod.ext (hfac₂ b) rfl
  have hθp : ∀ p : D × D, θ p = (α p.1, β p.2) := by
    intro p
    have e : p = (p.1, 1) * (1, p.2) := by ext <;> simp
    have h1 : θ p = θ ((p.1, 1) * (1, p.2)) := congrArg θ e
    rw [h1, map_mul, hθa, hθb]
    ext <;> simp
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : θ (a, 1) = θ 1 := by
      rw [hθa, ha, map_one]
      rfl
    exact congrArg Prod.fst (θ.injective h1)
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : θ (1, b) = θ 1 := by
      rw [hθb, hb, map_one]
      rfl
    exact congrArg Prod.snd (θ.injective h1)
  obtain ⟨g, hg⟩ := hAut (MulEquiv.ofBijective α ⟨hαinj, Finite.injective_iff_surjective.1 hαinj⟩)
  obtain ⟨h, hh⟩ := hAut (MulEquiv.ofBijective β ⟨hβinj, Finite.injective_iff_surjective.1 hβinj⟩)
  have hgα : ∀ a, α a = g * a * g⁻¹ := by
    intro a
    have h1 := congrArg (fun φ : MulAut D => φ a) hg
    simp only [MulAut.conj_apply] at h1
    exact h1
  have hhβ : ∀ b, β b = h * b * h⁻¹ := by
    intro b
    have h1 := congrArg (fun φ : MulAut D => φ b) hh
    simp only [MulAut.conj_apply] at h1
    exact h1
  have hcomm : ∀ (k : D) (y : G) (hy : y ∈ D), k * ⟨y, hy⟩ * k⁻¹ = ⟨y, hy⟩ →
      (k : G) * y = y * k := by
    intro k y hy h1
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul, coe_inv] at h2
    calc (k : G) * y = (k : G) * y * (k : G)⁻¹ * k := by group
      _ = y * k := by rw [h2]
  have hαO : ∀ o (ho : o ∈ O), α ⟨o, hO ho⟩ = ⟨o, hO ho⟩ := fun o ho => by
    have h1 := hfixO1 o ho
    rw [hθa] at h1
    exact congrArg Prod.fst h1
  have hβO : ∀ o (ho : o ∈ O), β ⟨o, hO ho⟩ = ⟨o, hO ho⟩ := fun o ho => by
    have h1 := hfix1O o ho
    rw [hθb] at h1
    exact congrArg Prod.snd h1
  have hαβX : ∀ x (hx : x ∈ X''), α ⟨x, hX'' hx⟩ = ⟨x, hX'' hx⟩ ∧ β ⟨x, hX'' hx⟩ = ⟨x, hX'' hx⟩ :=
    fun x hx => by
      have h1 := hfixX x hx
      rw [hθp] at h1
      exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  refine ⟨g, h, fun o ho => hcomm g o (hO ho) ((hgα _).symm.trans (hαO o ho)),
    fun x hx => hcomm g x (hX'' hx) ((hgα _).symm.trans (hαβX x hx).1),
    fun o ho => hcomm h o (hO ho) ((hhβ _).symm.trans (hβO o ho)),
    fun x hx => hcomm h x (hX'' hx) ((hhβ _).symm.trans (hαβX x hx).2), ?_, ?_⟩
  · have he : P.Ψ (g, h) ∈ centralizer (X : Set G) :=
      centralizerPerfectCore_le_centralizer X (hr ▸ ⟨(g, h), rfl⟩)
    exact mul_mem (inv_mem he) hcX
  · rw [mem_centralizer_iff]
    intro y hy
    rw [← hr] at hy
    obtain ⟨p, rfl⟩ := hy
    have key : c * P.Ψ p * c⁻¹ = P.Ψ (g, h) * P.Ψ p * (P.Ψ (g, h))⁻¹ := by
      rw [← hθf, ← hθ, hθp, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp [hgα, hhβ]
    calc P.Ψ p * ((P.Ψ (g, h))⁻¹ * c) =
        (P.Ψ (g, h))⁻¹ * (P.Ψ (g, h) * P.Ψ p * (P.Ψ (g, h))⁻¹) * c := by group
      _ = (P.Ψ (g, h))⁻¹ * (c * P.Ψ p * c⁻¹) * c := by rw [key]
      _ = (P.Ψ (g, h))⁻¹ * c * P.Ψ p := by group

theorem odd_and_commute_of_mem_overlapCentralizer (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) {X X'' O : Subgroup G}
    (hr : P.Ψ.range = centralizerPerfectCore X) [IsSimpleGroup D]
    (hZD : ∀ a : D, (∀ b : D, a * b = b * a) → a = 1)
    (hAut : ∀ φ : MulAut D, ∃ g : D, φ = MulAut.conj g)
    (hX'' : X'' ≤ D) (hO : O ≤ D) {o₀ : G} (ho₀ : o₀ ∈ O) (ho₀1 : o₀ ≠ 1)
    (hZodd : Odd (Nat.card (D ⊓ centralizer (O : Set G) ⊓ centralizer (X'' : Set G) :
      Subgroup G)))
    (hWodd : Odd (Nat.card (centralizer (X : Set G) ⊓
      centralizer (centralizerPerfectCore X : Set G) : Subgroup G)))
    {u : G} (hu : u ∈ D)
    (huZ : ∀ z ∈ D ⊓ centralizer (O : Set G) ⊓ centralizer (X'' : Set G), u * z = z * u)
    {c : G} (hcX : c ∈ centralizer (X : Set G)) (hcX'' : c ∈ centralizer (X'' : Set G))
    (hcO : ∀ o ∈ O, c * P.lft o = P.lft o * c)
    (hcO' : ∀ o ∈ O, c * (t * P.lft o * t⁻¹) = (t * P.lft o * t⁻¹) * c) :
    Odd (orderOf c) ∧ P.lft u * c = c * P.lft u := by
  obtain ⟨g, h, hgO, hgX, hhO, hhX, hwX, hwE⟩ := exists_eq_mul_of_mem_overlapCentralizer P hinj hr
    hZD hAut hX'' hO ho₀ ho₀1 hcX hcX'' hcO hcO'
  set Z : Subgroup G := D ⊓ centralizer (O : Set G) ⊓ centralizer (X'' : Set G) with hZdef
  have hmemZ : ∀ k : D, (∀ o ∈ O, (k : G) * o = o * k) → (∀ x ∈ X'', (k : G) * x = x * k) →
      (k : G) ∈ Z := fun k h1 h2 =>
    ⟨⟨k.2, mem_centralizer_iff.2 fun o ho => (h1 o ho).symm⟩,
      mem_centralizer_iff.2 fun x hx => (h2 x hx).symm⟩
  have hgZ := hmemZ g hgO hgX
  have hhZ := hmemZ h hhO hhX
  set e : G := P.Ψ (g, h) with hedef
  have he : e ∈ centralizerPerfectCore X := hr ▸ ⟨(g, h), rfl⟩
  have hce : c = e * (e⁻¹ * c) := by rw [mul_inv_cancel_left]
  have hcomm : Commute e (e⁻¹ * c) := mem_centralizer_iff.1 hwE e he
  have hoddD : ∀ k : D, (k : G) ∈ Z → Odd (orderOf k) := fun k hk => by
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hk)
  have hoe : Odd (orderOf e) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd P.Ψ (g, h))
    rw [Prod.orderOf]
    exact Odd.of_dvd_nat (Odd.mul (hoddD g hgZ) (hoddD h hhZ)) (lcm_dvd_mul _ _)
  have how : Odd (orderOf (e⁻¹ * c)) :=
    Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard _ ⟨hwX, hwE⟩)
  refine ⟨?_, ?_⟩
  · rw [hce]
    exact Odd.of_dvd_nat (Odd.mul hoe how) hcomm.orderOf_mul_dvd_mul_orderOf
  ·
    have hue : P.lft u * e = e * P.lft u := by
      rw [P.lft_of_mem hu, hedef, ← map_mul, ← map_mul]
      congr 1
      ext
      · exact huZ g hgZ
      · simp
    have huw : P.lft u * (e⁻¹ * c) = (e⁻¹ * c) * P.lft u :=
      mem_centralizer_iff.1 hwE (P.lft u) (hr ▸ swapParam_lft_mem_range P)
    rw [hce]
    calc P.lft u * (e * (e⁻¹ * c)) = e * (P.lft u * (e⁻¹ * c)) := by
          rw [← mul_assoc, hue, mul_assoc]
      _ = e * (e⁻¹ * c) * P.lft u := by rw [huw, ← mul_assoc]

end Overlap

end CFSG.SeitzReduction.F4Pilot
