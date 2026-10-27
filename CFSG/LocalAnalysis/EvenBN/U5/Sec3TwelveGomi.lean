module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelvePD
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveBar

public section

namespace CFSG.LocalAnalysis.EvenBN.U5.Sec312

open Subgroup CFSG.Timmesfeld.ARS CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] [CharP k 2] {m : ℕ}

theorem decomp_of_commuting {V X Y K₁ K₂ : Subgroup G}
    (hXV : X ≤ normalizer (V : Set G)) (hYV : Y ≤ normalizer (V : Set G))
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hVK : V ≤ K₁ ⊔ K₂) (hK₁ : K₁ ≤ V ⊔ X) (hK₂ : K₂ ≤ V ⊔ Y)
    (hVM : V ⊓ (X ⊔ Y) = ⊥) (hXY : X ⊓ Y = ⊥) :
    ∀ z ∈ V, ∃ a ∈ K₁ ⊓ V, ∃ b ∈ K₂ ⊓ V, a * b = z := by
  intro z hz
  have hz' : z ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hVK hz
  have hLE : K₁ ≤ normalizer (K₂ : Set G) := fun a ha =>
    (centralizer_le_normalizer _) (mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hLE] at hz'
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hz1⟩ := hz'
  have hκ₁' : κ₁ ∈ K₁ := hκ₁
  have hκ₂' : κ₂ ∈ K₂ := hκ₂
  have hz1' : κ₁ * κ₂ = z := hz1
  have h1 : κ₁ ∈ ((V ⊔ X : Subgroup G) : Set G) := hK₁ hκ₁'
  have h2 : κ₂ ∈ ((V ⊔ Y : Subgroup G) : Set G) := hK₂ hκ₂'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V X hXV] at h1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V Y hYV] at h2
  obtain ⟨v, hv, x, hx, hvx⟩ := h1
  obtain ⟨v', hv', y, hy, hvy⟩ := h2
  have hv0 : v ∈ V := hv
  have hv'0 : v' ∈ V := hv'
  have hx0 : x ∈ X := hx
  have hy0 : y ∈ Y := hy
  have hvx' : v * x = κ₁ := hvx
  have hvy' : v' * y = κ₂ := hvy
  have hw : v * (x * v' * x⁻¹) ∈ V :=
    mul_mem hv0 ((mem_normalizer_iff.1 (hXV hx0) v').1 hv'0)
  have hzeq : κ₁ * κ₂ = (v * (x * v' * x⁻¹)) * (x * y) := by
    rw [← hvx', ← hvy']
    group
  have hxyV : x * y ∈ V := by
    have e : x * y = (v * (x * v' * x⁻¹))⁻¹ * (κ₁ * κ₂) := by
      rw [hzeq]
      group
    rw [e, hz1']
    exact mul_mem (inv_mem hw) hz
  have hxyM : x * y ∈ X ⊔ Y :=
    mul_mem (Subgroup.mem_sup_left hx0) (Subgroup.mem_sup_right hy0)
  have h3 : x * y ∈ V ⊓ (X ⊔ Y) := Subgroup.mem_inf.2 ⟨hxyV, hxyM⟩
  rw [hVM, Subgroup.mem_bot] at h3
  have hxY : x ∈ Y := by
    have : x = y⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this]
    exact inv_mem hy0
  have hx1 : x = 1 := by
    have : x ∈ X ⊓ Y := Subgroup.mem_inf.2 ⟨hx0, hxY⟩
    rwa [hXY, Subgroup.mem_bot] at this
  have hy1 : y = 1 := by
    rw [hx1, one_mul] at h3
    exact h3
  have hκ₁V : κ₁ ∈ V := by
    rw [← hvx', hx1, mul_one]
    exact hv0
  have hκ₂V : κ₂ ∈ V := by
    rw [← hvy', hy1, mul_one]
    exact hv'0
  exact ⟨κ₁, Subgroup.mem_inf.2 ⟨hκ₁', hκ₁V⟩, κ₂, Subgroup.mem_inf.2 ⟨hκ₂', hκ₂V⟩, hz1'⟩

theorem le_normalizer_map_conj {H K : Subgroup G} {t : G} (ht : t ∈ normalizer (H : Set G))
    (hHK : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hg' : t⁻¹ * g * t ∈ H := by
    have := (mem_normalizer_iff.1 (inv_mem ht) g).1 hg
    simpa using this
  have h1 : (t⁻¹ * g * t) * y * (t⁻¹ * g * t)⁻¹ ∈ K := (mem_normalizer_iff.1 (hHK hg') y).1 hy
  refine ⟨_, h1, ?_⟩
  change t * ((t⁻¹ * g * t) * y * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * (t * y * t⁻¹) * g⁻¹
  group

theorem commute_of_normal_of_inf_eq_bot {L K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ L) (h₂ : K₂ ≤ L)
    (hn₁ : L ≤ normalizer (K₁ : Set G)) (hn₂ : L ≤ normalizer (K₂ : Set G))
    (hinf : K₁ ⊓ K₂ = ⊥) : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  intro a ha b hb
  have e1 : a * b * a⁻¹ * b⁻¹ ∈ K₂ := by
    have : a * b * a⁻¹ ∈ K₂ := (mem_normalizer_iff.1 (hn₂ (h₁ ha)) b).1 hb
    exact mul_mem this (inv_mem hb)
  have e2 : a * b * a⁻¹ * b⁻¹ ∈ K₁ := by
    have : b * a⁻¹ * b⁻¹ ∈ K₁ := (mem_normalizer_iff.1 (hn₁ (h₂ hb)) a⁻¹).1 (inv_mem ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact mul_mem ha this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ K₁ ⊓ K₂ := Subgroup.mem_inf.2 ⟨e2, e1⟩
  rw [hinf, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h3))

theorem natural_module_of_decomposition {V X Y RX RY K₁ K₂ : Subgroup G} {t' : G}
    (h : Setting m V X Y RX RY t') (φX : X ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hVK : V ≤ K₁ ⊔ K₂) (hK₁ : K₁ ≤ V ⊔ X) (hK₂ : K₂ ≤ V ⊔ Y) (hXK : X ≤ K₁) (hYK : Y ≤ K₂)
    (hinf : K₁ ⊓ K₂ = ⊥) (hVM : V ⊓ (X ⊔ Y) = ⊥) (hXY : X ⊓ Y = ⊥)
    (hτ : K₁.map (MulAut.conj t').toMonoidHom = K₂) :
    ∃ θ : (Fin 2 → k) → G, IsNaturalModule φX θ ∧
      Set.range θ = ((K₁ ⊓ V : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := by omega
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self h.sq ha hb
  set V₁ : Subgroup G := K₁ ⊓ V with hV₁
  set V₂ : Subgroup G := K₂ ⊓ V with hV₂
  have hV₁V : V₁ ≤ V := inf_le_right
  have hV₂V : V₂ ≤ V := inf_le_right
  have hdecomp := decomp_of_commuting h.normX h.normY hcomm hVK hK₁ hK₂ hVM hXY
  have hsup : V₁ ⊔ V₂ = V := le_antisymm (sup_le hV₁V hV₂V) fun z hz => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp z hz
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hV₁₂ : V₁ ⊓ V₂ = ⊥ := eq_bot_iff.2 fun z hz => by
    have h' : z ∈ K₁ ⊓ K₂ := Subgroup.mem_inf.2 ⟨hz.1.1, hz.2.1⟩
    rw [hinf] at h'
    exact h'
  have hVt : V.map (MulAut.conj t').toMonoidHom = V := map_conj_eq_of_mem_normalizer h.tNorm
  have hτV : V₁.map (MulAut.conj t').toMonoidHom = V₂ := by
    rw [hV₁, hV₂, Subgroup.map_inf _ _ _ (MulAut.conj t').injective, hτ, hVt]
  have hprod := Common.card_sup_mul_card_inf_eq (A := V₁) (B := V₂)
    (hV₂V.trans (Common.le_normalizer_of_mul_comm hV₁V hVc))
  rw [hsup, hV₁₂, Subgroup.card_bot, mul_one, h.card] at hprod
  have hcard12 : Nat.card V₂ = Nat.card V₁ := by
    rw [← hτV, Prelim.card_map_conj]
  have hcard1 : Nat.card V₁ = 2 ^ (2 * m) := by
    have e : Nat.card V₁ * Nat.card V₁ = 2 ^ (2 * m) * 2 ^ (2 * m) := by
      rw [hcard12] at hprod
      rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring]
      exact hprod.symm
    exact Nat.mul_self_inj.1 e
  have hXV₂ : X ≤ centralizer (V₂ : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun b hb => (hcomm x (hXK hx) b hb.1).symm
  have hXN₁ : X ≤ normalizer (V₁ : Set G) := fun x hx =>
    Common.mem_normalizer_inf (le_normalizer (hXK hx)) (h.normX hx)
  have hnt₁ : ¬ X ≤ centralizer (V₁ : Set G) := by
    intro hX1
    apply h.nt
    have : X ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
      rw [Prelim.centralizer_sup_eq]
      exact le_inf hX1 hXV₂
    rwa [hsup] at this
  have hsub : V ⊓ centralizer ((RX ⊔ RY : Subgroup G) : Set G) ≤
      (V₁ ⊓ centralizer (RX : Set G)) ⊔ (V₂ ⊓ centralizer (RY : Set G)) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp z hz.1
    have hzc : a * b ∈ centralizer ((RX ⊔ RY : Subgroup G) : Set G) := hz.2
    rw [Prelim.centralizer_sup_eq] at hzc
    have haR : a ∈ centralizer (RX : Set G) := by
      refine mem_centralizer_iff.2 fun r hr => ?_
      have h1 := mem_centralizer_iff.1 hzc.1 r hr
      have hrb : r * b = b * r := hcomm r (hXK (h.sylowX.le hr)) b hb.1
      have e : r * a * b = a * r * b := by
        calc r * a * b = r * (a * b) := by group
          _ = (a * b) * r := h1
          _ = a * (b * r) := by group
          _ = a * (r * b) := by rw [hrb]
          _ = a * r * b := by group
      exact mul_right_cancel e
    have hbR : b ∈ centralizer (RY : Set G) := by
      refine mem_centralizer_iff.2 fun r hr => ?_
      have h1 := mem_centralizer_iff.1 hzc.2 r hr
      have hra : a * r = r * a := hcomm a ha.1 r (hYK (h.sylowY.le hr))
      have e : a * (r * b) = a * (b * r) := by
        calc a * (r * b) = (a * r) * b := by group
          _ = (r * a) * b := by rw [hra]
          _ = r * (a * b) := by group
          _ = (a * b) * r := h1
          _ = a * (b * r) := by group
      exact mul_left_cancel e
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨ha, haR⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hb, hbR⟩))
  have hle : Nat.card (V₂ ⊓ centralizer (RY : Set G) : Subgroup G) ≤
      Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) := by
    have hsub' : V₂ ⊓ centralizer (RY : Set G) ≤
        (V₁ ⊓ centralizer (RX : Set G)).map (MulAut.conj t').toMonoidHom := by
      intro z hz
      have hz2 : z ∈ V₁.map (MulAut.conj t').toMonoidHom := by rw [hτV]; exact hz.1
      obtain ⟨w, hw, rfl⟩ := hz2
      refine ⟨w, Subgroup.mem_inf.2 ⟨hw, ?_⟩, rfl⟩
      refine mem_centralizer_iff.2 fun r hr => ?_
      have hr' : (MulAut.conj t').toMonoidHom r ∈ RY := by
        rw [← h.tMapR]
        exact ⟨r, hr, rfl⟩
      have h1 := mem_centralizer_iff.1 hz.2 _ hr'
      have e : (MulAut.conj t').toMonoidHom (r * w) = (MulAut.conj t').toMonoidHom (w * r) := by
        rw [map_mul, map_mul]
        exact h1
      exact (MulAut.conj t').injective e
    calc Nat.card (V₂ ⊓ centralizer (RY : Set G) : Subgroup G)
        ≤ Nat.card ((V₁ ⊓ centralizer (RX : Set G)).map (MulAut.conj t').toMonoidHom) :=
          Subgroup.card_le_of_le hsub'
      _ = Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) := Prelim.card_map_conj _ _
  have hprod2 := Common.card_sup_mul_card_inf_eq (A := V₁ ⊓ centralizer (RX : Set G))
    (B := V₂ ⊓ centralizer (RY : Set G))
    ((inf_le_left.trans hV₂V).trans (Common.le_normalizer_of_mul_comm
      (inf_le_left.trans hV₁V) hVc))
  have hpos : 0 < Nat.card ((V₁ ⊓ centralizer (RX : Set G)) ⊓ (V₂ ⊓ centralizer (RY : Set G)) :
      Subgroup G) := Nat.card_pos
  have hfixP : 2 ^ m ≤ Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) := by
    have h5 : 2 ^ (2 * m) ≤ Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) *
        Nat.card (V₂ ⊓ centralizer (RY : Set G) : Subgroup G) :=
      h.fixed.trans ((Subgroup.card_le_of_le hsub).trans (by
        calc Nat.card ((V₁ ⊓ centralizer (RX : Set G)) ⊔ (V₂ ⊓ centralizer (RY : Set G)) :
              Subgroup G)
            = Nat.card ((V₁ ⊓ centralizer (RX : Set G)) ⊔ (V₂ ⊓ centralizer (RY : Set G)) :
              Subgroup G) * 1 := (mul_one _).symm
          _ ≤ Nat.card ((V₁ ⊓ centralizer (RX : Set G)) ⊔ (V₂ ⊓ centralizer (RY : Set G)) :
              Subgroup G) * Nat.card ((V₁ ⊓ centralizer (RX : Set G)) ⊓
                (V₂ ⊓ centralizer (RY : Set G)) : Subgroup G) := Nat.mul_le_mul_left _ hpos
          _ = _ := hprod2))
    have h6 : 2 ^ m * 2 ^ m ≤ Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) *
        Nat.card (V₁ ⊓ centralizer (RX : Set G) : Subgroup G) :=
      calc 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
        _ ≤ _ := h5
        _ ≤ _ := Nat.mul_le_mul_left _ hle
    exact Nat.mul_self_le_mul_self_iff.1 h6
  have hP : Nat.card RX = Nat.card k := by
    rw [Prelim.card_of_isSylowOf hk hm1 φX h.sylowX, hk]
  obtain ⟨hfix, hfixc, -, -, -⟩ := Common.natural_module_of_card_le hk hm φX
    (fun a ha b hb => hVc a (hV₁V ha) b (hV₁V hb)) hXN₁
    (by rw [hcard1, ← pow_mul, mul_comm]) hnt₁ h.sylowX.le hP hfixP
  have hel : IsElementaryAbelian 2 V₁ :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVc a (hV₁V a.2) b (hV₁V b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
        simp only [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
        exact h.sq _ (hV₁V a.2)) }
  exact Prelim.exists_isNaturalModule hk hm1 φX hel hXN₁ hcard1 hfix h.sylowX hfixc

omit [Finite G] in
theorem isNaturalSection_of_bar {A X' A' : Subgroup G} {κ : Type*} [Field κ]
    (hAA' : A ≤ A') (hA'N : A' ≤ normalizer (A : Set G)) (hXN : X' ≤ normalizer (A : Set G))
    (φ : X' ≃* SL(2, κ)) (θb : (Fin 2 → κ) → Bar A)
    (hadd : ∀ v w, θb (v + w) = θb v * θb w) (hinj : Function.Injective θb)
    (hrange : Set.range θb = ((bar A A' : Subgroup (Bar A)) : Set (Bar A)))
    (hmul : ∀ (x : X') (v : Fin 2 → κ),
      θb ((φ x : Matrix (Fin 2) (Fin 2) κ) *ᵥ v) =
        proj A ⟨x, hXN x.2⟩ * θb v * (proj A ⟨x, hXN x.2⟩)⁻¹) :
    IsNaturalSection X' A' A κ := by
  have hex : ∀ v : Fin 2 → κ, ∃ z : normalizer (A : Set G), (z : G) ∈ A' ∧ proj A z = θb v := by
    intro v
    have hv : θb v ∈ bar A A' := by
      have hmem : θb v ∈ Set.range θb := ⟨v, rfl⟩
      rw [hrange] at hmem
      exact hmem
    exact mem_bar_iff_exists.1 hv
  choose g hgA' hg using hex
  have h0 : θb 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    have h2 : θb 0 * θb 0 = θb 0 * 1 := by
      rw [mul_one]
      exact h00.symm
    exact mul_left_cancel h2
  unfold IsNaturalSection
  refine ⟨φ, fun v => (g v : G), fun v => hgA' v, ?_, ?_, ?_, ?_⟩
  · intro v w
    have hprod : proj A ((g v * g w)⁻¹ * g (v + w)) = 1 := by
      simp only [map_mul, map_inv, hg]
      rw [hadd v w]
      exact inv_mul_cancel _
    exact proj_eq_one_iff.1 hprod
  · intro v hv
    have h1 : proj A (g v) = 1 := proj_eq_one_iff.2 hv
    rw [hg v] at h1
    exact hinj (h1.trans h0.symm)
  · intro a ha
    have haN : a ∈ normalizer (A : Set G) := hA'N ha
    have hz : proj A ⟨a, haN⟩ ∈ Set.range θb := by
      rw [hrange]
      exact proj_mem_bar (x := ⟨a, haN⟩) ha
    obtain ⟨v, hv⟩ := hz
    refine ⟨v, ?_⟩
    exact proj_eq_proj_iff.1 ((hg v).trans hv)
  · intro x v
    have hmain : proj A ((g ((φ x : Matrix (Fin 2) (Fin 2) κ) *ᵥ v))⁻¹ *
        ((⟨x, hXN x.2⟩ : normalizer (A : Set G)) * g v *
          (⟨x, hXN x.2⟩ : normalizer (A : Set G))⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hg]
      rw [hmul x v]
      exact inv_mul_cancel _
    exact proj_eq_one_iff.1 hmain

end CFSG.LocalAnalysis.EvenBN.U5.Sec312
