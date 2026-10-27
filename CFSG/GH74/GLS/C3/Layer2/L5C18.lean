module

public import CFSG.GH74.GLS.C3.Layer2.L5C17
public import CFSG.GH74.GLS.C3.Layer2.L5C15

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

structure Sh2Contract
    {ι : Type} (X : ι → Type) [∀ ty, Group (X ty)] [∀ ty, Finite (X ty)]
    (inc : ∀ ty, ↥Sh0 →* X ty) : Prop where
  rec2 : ∀ (S₂ : Type) [Group S₂] [Finite S₂] (κ : ↥Sh0 →* S₂), Function.Injective κ →
    κ.range.index = 2 →
    (∀ s : S₂, (∀ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 →
      ∃ r' : ↥Sh0, (r' : Perm (Fin 16)) ∈ RsubP0 ∧ s * κ r * s⁻¹ = κ r') → s ∈ κ.range) →
    ∃ (ty : ι) (ψ : S₂ ≃* X ty), ∀ g, ψ (κ g) = inc ty g
  e16 : ∀ (ty : ι) (B : Subgroup (X ty)), Nat.card B = 16 → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) →
    (∀ b ∈ B, ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ b = inc ty r) ∨
    (∀ b ∈ B, ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ R1subP ∧ b = inc ty r)
  move : ∀ (ty : ι) (s : X ty), s ∉ (inc ty).range → ∀ r1 : ↥Sh0,
    (r1 : Perm (Fin 16)) ∈ R1subP → ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧
      inc ty r1 = s * inc ty r * s⁻¹
  engine : ∀ (ty : ι) (E : X ty → X ty → Prop),
    FusionHyp (X ty) ((inc ty).comp embHom0) E → False

section Class0NonSylow

variable {h : IsAConfig 5 x K T Q S a}

theorem Coord5.conjR_elementary
    (c : Coord5 h) {S₂ : Subgroup G} {Y : Type} [Group Y]
    (f : ↥S₂ →* Y) (hf : Function.Injective f) (g : G)
    (hg : (c.lift Rm).map (MulAut.conj g).toMonoidHom ≤ S₂) :
    ∃ B : Subgroup Y, (∀ y, y ∈ B ↔ ∃ r ∈ c.lift Rm, ∃ hz : g * r * g⁻¹ ∈ S₂,
      f ⟨g * r * g⁻¹, hz⟩ = y) ∧ Nat.card B = 16 ∧ (∀ b ∈ B, b * b = 1) ∧
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) := by
  set R := c.lift Rm with hR
  set A' := R.map (MulAut.conj g).toMonoidHom with hA'
  have hmemA' : ∀ y, y ∈ A' ↔ ∃ r ∈ R, g * r * g⁻¹ = y := by
    intro y
    rw [hA', Subgroup.mem_map]
    simp [MulAut.conj_apply]
  have hsq : ∀ y ∈ A', y * y = 1 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (hmemA' y).1 hy
    have := Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) hr
    calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcomm : ∀ y ∈ A', ∀ y' ∈ A', y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨r, hr, rfl⟩ := (hmemA' y).1 hy
    obtain ⟨r', hr', rfl⟩ := (hmemA' y').1 hy'
    have := Coord5.lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) hr hr'
    calc g * r * g⁻¹ * (g * r' * g⁻¹) = g * (r * r') * g⁻¹ := by group
      _ = g * (r' * r) * g⁻¹ := by rw [this]
      _ = g * r' * g⁻¹ * (g * r * g⁻¹) := by group
  set B : Subgroup Y := (A'.subgroupOf S₂).map f with hB
  have hmemB : ∀ b, b ∈ B ↔ ∃ y : ↥S₂, (y : G) ∈ A' ∧ f y = b := by
    intro b
    rw [hB, Subgroup.mem_map]
    simp [Subgroup.mem_subgroupOf]
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [hmemB]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hrz⟩ := (hmemA' z).1 hz
      refine ⟨r, hr, by rw [hrz]; exact z.2, ?_⟩
      congr 1
      exact Subtype.ext hrz
    · rintro ⟨r, hr, hz, rfl⟩
      exact ⟨⟨g * r * g⁻¹, hz⟩, (hmemA' _).2 ⟨r, hr, rfl⟩, rfl⟩
  · rw [hB, Subgroup.card_map_of_injective hf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv, hA',
      Subgroup.card_map_of_injective (fun u v huv => (MulAut.conj g).injective huv)]
    exact Coord5.card_lift_Rm (c := c)
  · intro b hb
    obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (hsq y hy)
    rw [this, map_one]
  · intro b hb b' hb'
    obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
    obtain ⟨y', hy', rfl⟩ := (hmemB b').1 hb'
    rw [← map_mul, ← map_mul]
    have : y * y' = y' * y := Subtype.ext (hcomm y hy y' hy')
    rw [this]

variable {c : Coord5 h} {S₁ : Subgroup G} {hS : c.S1Data S₁}

theorem Coord5.class0_false_of_not_sylow
    {ι : Type} {X : ι → Type} [∀ ty, Group (X ty)]
    [∀ ty, Finite (X ty)] {inc : ∀ ty, ↥Sh0 →* X ty} (hX : Sh2Contract X inc)
    (hF2 : C1Facts2) (hRed : c.Red) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (Ψ : c.ModelIso hS Sh0 tr16 yHat)
    (hns : ¬ IsSylow2In S₁ ⊤) : False := by
  have hp : IsPGroup 2 ↥S₁ := IsPGroup.of_card (n := 7) (by rw [hS.card]; norm_num)
  have hSylN := Coord5.S1_sylow hF2 hRed hS
  obtain ⟨S', hS', hS₁S'⟩ := exists_sylow2_ge hp (le_top : S₁ ≤ ⊤)
  have hne : S₁ ≠ S' := fun heq => hns (heq ▸ hS')
  obtain ⟨S₂, h12, h2S', hcard2⟩ := exists_S2 hS'.2.1 hS₁S' hne hS.card
  have hS₂p : IsPGroup 2 ↥S₂ := hS'.2.1.to_le h2S'
  have hRS₁ : c.lift Rm ≤ S₁ := Coord5.R_le_S1 hS
  let κ : ↥Sh0 →* ↥S₂ := (Subgroup.inclusion h12).comp Ψ.ψ.symm.toMonoidHom
  have hκ : ∀ g : ↥Sh0, (κ g : G) = (Ψ.ψ.symm g : G) := fun g => rfl
  have hκinj : Function.Injective κ :=
    (Subgroup.inclusion_injective h12).comp Ψ.ψ.symm.injective
  have hidx : κ.range.index = 2 := by
    have h1 := Subgroup.card_mul_index κ.range
    have h2 : Nat.card κ.range = 128 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv, card_Sh0]
    rw [h2, hcard2] at h1
    omega
  have hRtoR : ∀ r₀ : ↥Sh0, (r₀ : Perm (Fin 16)) ∈ RsubP0 →
      ((Ψ.ψ.symm r₀ : ↥S₁) : G) ∈ c.lift Rm := by
    intro r₀ hr₀
    have hrs : ((Ψ.ψ.symm r₀ : ↥S₁) : G) ∈ S₁ := (Ψ.ψ.symm r₀).2
    refine (Ψ.mem_R hrs).2 ?_
    have h1 : Ψ.ψ ⟨(Ψ.ψ.symm r₀ : G), hrs⟩ = r₀ := by
      have h2 : (⟨(Ψ.ψ.symm r₀ : G), hrs⟩ : ↥S₁) = Ψ.ψ.symm r₀ := rfl
      rw [h2, MulEquiv.apply_symm_apply]
    rw [h1]
    rw [mem_RsubP0] at hr₀
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hr₀
    exact ⟨j, hj.symm⟩
  have hRfromR : ∀ i : Fin 16, ∃ r₀ : ↥Sh0, (r₀ : Perm (Fin 16)) ∈ RsubP0 ∧
      (Ψ.ψ.symm r₀ : G) = c.liftEl i := by
    intro i
    refine ⟨Ψ.ψ ⟨c.liftEl i, hRS₁ (c.liftEl_mem i)⟩, ?_, ?_⟩
    · rw [Ψ.liftEl, mem_RsubP0]
      exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
    · rw [MulEquiv.symm_apply_apply]
  have hmoveκ : ∀ s : ↥S₂, (∀ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 →
      ∃ r' : ↥Sh0, (r' : Perm (Fin 16)) ∈ RsubP0 ∧ s * κ r * s⁻¹ = κ r') → s ∈ κ.range := by
    intro s hs'
    have hconjR : ∀ i : Fin 16, (s : G) * c.liftEl i * (s : G)⁻¹ ∈ c.lift Rm := by
      intro i
      obtain ⟨r, hr, hri⟩ := hRfromR i
      obtain ⟨r', hr'0, hr'⟩ := hs' r hr
      have h1 : (s : G) * c.liftEl i * (s : G)⁻¹ = (Ψ.ψ.symm r' : G) := by
        have h2 := congrArg Subtype.val hr'
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hκ, hκ, hri] at h2
        rw [Subgroup.coe_inv] at h2
        exact h2
      rw [h1]
      exact hRtoR r' hr'0
    have hsN : (s : G) ∈ c.N := mem_normalizer_of_conj_le fun r hr => by
      have := hconjR (idx16 (c.rco r))
      rwa [← Coord5.exists_liftEl c hr] at this
    have hsS₁ : (s : G) ∈ S₁ := mem_of_sylow_normalizes hSylN hS₂p h12 s.2 hsN
    refine ⟨Ψ.ψ ⟨s, hsS₁⟩, Subtype.ext ?_⟩
    rw [hκ, MulEquiv.symm_apply_apply]
  obtain ⟨ty, ψ₂, hψ₂⟩ := hX.rec2 ↥S₂ κ hκinj hidx hmoveκ
  have hincl : ∀ z : ↥S₁, ψ₂ (Subgroup.inclusion h12 z) = inc ty (Ψ.ψ z) := by
    intro z
    have := hψ₂ (Ψ.ψ z)
    have h2 : κ (Ψ.ψ z) = Subgroup.inclusion h12 z := by
      show Subgroup.inclusion h12 (Ψ.ψ.symm (Ψ.ψ z)) = _
      rw [MulEquiv.symm_apply_apply]
    rwa [h2] at this
  have hS₂eq : S₂ = S' := by
    by_contra hneq
    obtain ⟨b, hbS', hbN, hbS₂⟩ := exists_normalizer_gt hS'.2.1 h2S' hneq
    have hbR : ∀ r ∈ c.lift Rm, b * r * b⁻¹ ∈ S₂ := fun r hr =>
      (mem_normalizer_iff.1 hbN r).1 (h12 (hRS₁ hr))
    have hconjle : (c.lift Rm).map (MulAut.conj b).toMonoidHom ≤ S₂ := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hy
      exact hbR r hr
    obtain ⟨B, hBmem, hBcard, hBsq, hBcomm⟩ :=
      Coord5.conjR_elementary c ψ₂.toMonoidHom ψ₂.injective b hconjle
    have hBy : ∀ (r : G) (hr : r ∈ c.lift Rm), ψ₂ ⟨b * r * b⁻¹, hbR r hr⟩ ∈ B := fun r hr =>
      (hBmem _).2 ⟨r, hr, hbR r hr, rfl⟩
    rcases hX.e16 ty B hBcard hBsq hBcomm with hRhat | hR1hat
    ·
      have hbN' : b ∈ c.N := by
        refine mem_normalizer_of_conj_le fun r hr => ?_
        obtain ⟨r₀, hr₀, hy⟩ := hRhat _ (hBy r hr)
        have h1 : ψ₂ ⟨b * r * b⁻¹, hbR r hr⟩ = ψ₂ (Subgroup.inclusion h12 (Ψ.ψ.symm r₀)) := by
          rw [hincl, MulEquiv.apply_symm_apply]
          exact hy
        have h2 := congrArg Subtype.val (ψ₂.injective h1)
        rw [show ((⟨b * r * b⁻¹, hbR r hr⟩ : ↥S₂) : G) = b * r * b⁻¹ from rfl] at h2
        rw [h2]
        exact hRtoR r₀ hr₀
      exact hbS₂ (h12 (mem_of_sylow_normalizes hSylN hS'.2.1 hS₁S' hbS' hbN'))
    ·
      obtain ⟨b₀, hb₀S₂, hb₀S₁⟩ : ∃ b₀ ∈ S₂, b₀ ∉ S₁ := by
        by_contra hcon
        have hle : S₂ ≤ S₁ := fun y hy => by
          by_contra hy1
          exact hcon ⟨y, hy, hy1⟩
        have := Subgroup.card_le_of_le hle
        rw [hcard2, hS.card] at this
        omega
      have hnotrange : ψ₂ ⟨b₀, hb₀S₂⟩ ∉ (inc ty).range := by
        rintro ⟨g, hg⟩
        have h1 : ψ₂ ⟨b₀, hb₀S₂⟩ = ψ₂ (κ g) := by rw [hψ₂, hg]
        have h2 := congrArg Subtype.val (ψ₂.injective h1)
        rw [hκ] at h2
        exact hb₀S₁ (by
          have : (b₀ : G) = (Ψ.ψ.symm g : G) := h2
          rw [this]
          exact (Ψ.ψ.symm g).2)
      have hbb₀ : b₀⁻¹ * b ∈ c.N := by
        refine mem_normalizer_of_conj_le fun r hr => ?_
        obtain ⟨r₁, hr₁, hy⟩ := hR1hat _ (hBy r hr)
        obtain ⟨r₂, hr₂, hmv⟩ := hX.move ty (ψ₂ ⟨b₀, hb₀S₂⟩) hnotrange r₁ hr₁
        have h1 : ψ₂ ⟨b * r * b⁻¹, hbR r hr⟩ =
            ψ₂ (⟨b₀, hb₀S₂⟩ * Subgroup.inclusion h12 (Ψ.ψ.symm r₂) * ⟨b₀, hb₀S₂⟩⁻¹) := by
          rw [map_mul, map_mul, map_inv, hincl, MulEquiv.apply_symm_apply, ← hmv]
          exact hy
        have h2 := congrArg Subtype.val (ψ₂.injective h1)
        have h3 : b * r * b⁻¹ = b₀ * (Ψ.ψ.symm r₂ : G) * b₀⁻¹ := h2
        have h4 : (b₀⁻¹ * b) * r * (b₀⁻¹ * b)⁻¹ = (Ψ.ψ.symm r₂ : G) := by
          have : (b₀⁻¹ * b) * r * (b₀⁻¹ * b)⁻¹ = b₀⁻¹ * (b * r * b⁻¹) * b₀ := by group
          rw [this, h3]
          group
        rw [h4]
        exact hRtoR r₂ hr₂
      have hb₀S' : b₀ ∈ S' := h2S' hb₀S₂
      have hmemS' : b₀⁻¹ * b ∈ S' := S'.mul_mem (S'.inv_mem hb₀S') hbS'
      have hin : b₀⁻¹ * b ∈ S₁ := mem_of_sylow_normalizes hSylN hS'.2.1 hS₁S' hmemS' hbb₀
      apply hbS₂
      have : b = b₀ * (b₀⁻¹ * b) := by group
      rw [this]
      exact S₂.mul_mem hb₀S₂ (h12 hin)
  have hS₂syl : IsSylow2In S₂ ⊤ := hS₂eq ▸ hS'
  have hTS₂ : T ≤ S₂ := hS.hT.trans h12
  have hFus : FusionHyp (X ty) ((inc ty).comp embHom0) (Erel ψ₂) := by
    refine c.fusionHyp_of_model hs hnab hRed.nbar hS₂syl hTS₂ ψ₂ ((inc ty).comp embHom0)
      (fun t => ?_)
    have h1 : (⟨c.iotaT t, hTS₂ (c.iotaT_mem_T t)⟩ : ↥S₂) =
        Subgroup.inclusion h12 (c.iotaS1 hS.hT t) := rfl
    have h2 : Ψ.ψ (c.iotaS1 hS.hT t) = embHom0 t := Subtype.ext (Ψ.spec t)
    rw [h1, hincl, h2]
    rfl
  exact hX.engine ty _ hFus

end Class0NonSylow

end CFSG.GH74.GLS.C3.Layer2.L5
