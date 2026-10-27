module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9f_conj_centralizer {H : Subgroup G} {s c : G}
    (hs : s ∈ normalizer (H : Set G)) (hc : c ∈ centralizer (H : Set G)) :
    s * c * s⁻¹ ∈ centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : s⁻¹ * l * s ∈ H := (Subgroup.mem_normalizer_iff''.mp hs l).mp hl
  calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
    _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [hc (s⁻¹ * l * s) hl']
    _ = (s * c * s⁻¹) * l := by group

theorem sec9f_autIn_le_inf (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hctx : Sec9Ctx G t L S z g B t₀) :
    autIn L B ≤ autIn (L ⊓ centMod (Asub9 t t₀ B) B) B := by
  let K : Subgroup (MulAut ↥B) := autIn L B
  let H : Subgroup (MulAut ↥B) := autIn (L ⊓ centMod (Asub9 t t₀ B) B) B
  have hK6 : Nonempty (↥K ≃* alternatingGroup (Fin 6)) := (sec9m_autL h6 hctx).1
  have htop : (⊤ : Subgroup ↥K) ≤ H.comap K.subtype := by
    rw [← sec9m_closure_two hK6, Subgroup.closure_le]
    intro k hk
    change (k : MulAut ↥B) ∈ H
    obtain ⟨m, hm⟩ := hk
    obtain ⟨x, hxL, hxN, hxφ⟩ := sec9m_mem_autIn.mp k.2
    let X : Subgroup G := L ⊓ normalizer (B : Set G)
    let xK : ↥X := ⟨x, hxL, hxN⟩
    let ρ : ↥X →* MulAut ↥B := B.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
    have hρx : ρ xK = (k : MulAut ↥B) := by
      ext b
      change ((B.normalizerMonoidHom (Subgroup.inclusion inf_le_right xK)) b : ↥B).val
        = ((k : MulAut ↥B) b : ↥B).val
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      exact (hxφ b).symm
    have hm' : (ρ xK) ^ (2 ^ m) = 1 := by
      rw [hρx]
      simpa [Subgroup.coe_pow] using congrArg Subtype.val hm
    obtain ⟨y, hy2, hyρ⟩ := sec9m_exists_twoPart ρ xK hm'
    obtain ⟨r, hyr⟩ := hy2
    have hyr' : (y : G) ^ (2 ^ r) = 1 := by
      have h := congrArg Subtype.val hyr
      simpa [Subgroup.coe_pow] using h
    have hyNmod : (y : G) ∈ centMod (Asub9 t t₀ B) B :=
      sec9m_lift hT hctx y.2.1 y.2.2 hyr'
    refine sec9m_mem_autIn.mpr ⟨(y : G), ⟨y.2.1, hyNmod⟩, y.2.2, fun b => ?_⟩
    rw [show (k : MulAut ↥B) = ρ y by rw [← hρx, hyρ]]
    change ((B.normalizerMonoidHom (Subgroup.inclusion inf_le_right y)) b : ↥B).val
      = (y : G) * (b : G) * (y : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  intro k hk
  have hmem : K.subtype (⟨k, hk⟩ : ↥K) ∈ H :=
    Subgroup.mem_comap.mp (htop (Subgroup.mem_top _))
  change k ∈ H
  exact hmem

theorem sec9f_exists_tau (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (hctx : Sec9Choice G t L S z g B t₀) :
    ∃ τ : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) →* ↥B,
      (∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) ∧
        τ.ker = (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B).subgroupOf
          (centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) ∧
        oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B ≤
          centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) := by
  have hc : Sec9Ctx G t L S z g B t₀ := hctx.toSec9Ctx
  obtain ⟨-, -, -, h4, hv, -⟩ := asc82Lemma9N_of h36 h68 hB8 hT G t L S z g B t₀ hctx
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => CFSG.Open.IsElemAbelian.comm hc.B_e16.1 hb hb'
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hMB : ∀ m ∈ centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G),
      ∀ b ∈ B, m * b = b * m := fun m hm b hb =>
    (Subgroup.mem_centralizer_iff.mp hm.2 b hb).symm
  have ha : ∀ m ∈ centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G),
      m * t * m⁻¹ * t⁻¹ ∈ B := fun m hm => hm.1.2 t htA
  obtain ⟨τ, hτ⟩ := sec9m_exists_commHom
    (M := centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) (B := B) (a := t) hBc hMB ha
  have hBA : B ≤ Asub9 t t₀ B := by rw [Asub9]; exact le_sup_right
  have hCOA : oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B ≤
      centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) := by
    rw [← hv]
    exact le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le hBA))
  refine ⟨τ, hτ, ?_, hCOA⟩
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have hxt : (x : G) * t = t * (x : G) := by
      have h1 : (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1 := by
        have h2 := congrArg Subtype.val hx
        rwa [hτ x, Subgroup.coe_one] at h2
      calc (x : G) * t = ((x : G) * t * (x : G)⁻¹ * t⁻¹) * (t * (x : G)) := by group
        _ = t * (x : G) := by rw [h1, one_mul]
    have hle : zpowers t ⊔ B ≤ centralizer ({(x : G)} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hxt
      · intro b hb
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (Subgroup.mem_centralizer_iff.mp x.2.2 b hb).symm
    have hxcent : (x : G) ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.mp (hle hy) (x : G) (Set.mem_singleton (x : G))).symm
    have hx' : (x : G) ∈ centMod (Asub9 t t₀ B) B ⊓
        centralizer (Asub9 t t₀ B : Set G) := by
      rw [h4]
      exact ⟨x.2.1, hxcent⟩
    rw [← hv]
    exact hx'
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hτ x, Subgroup.coe_one]
    have hx' : (x : G) ∈ centMod (Asub9 t t₀ B) B ⊓
        centralizer (Asub9 t t₀ B : Set G) := by
      rw [← hv] at hx; exact hx
    have hcomm : t * (x : G) = (x : G) * t :=
      Subgroup.mem_centralizer_iff.mp hx'.2 t htA
    rw [← hcomm]; group

theorem sec9f_range_bot_or_top (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hctx : Sec9Ctx G t L S z g B t₀)
    (τ : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) :
    τ.range = ⊥ ∨ τ.range = ⊤ := by
  by_cases hbot : τ.range = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
      fun b hb b' hb' => CFSG.Open.IsElemAbelian.comm hctx.B_e16.1 hb hb'
    have htA : t ∈ Asub9 t t₀ B := by
      rw [Asub9]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
    have hnt : ∃ v ∈ τ.range, v ≠ 1 := by
      rw [Subgroup.eq_bot_iff_forall] at hbot
      push_neg at hbot
      exact hbot
    obtain ⟨v, hv, hv1⟩ := hnt
    obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp hv
    rw [Subgroup.eq_top_iff']
    intro b
    by_cases hb : b = 1
    · rw [hb]; exact τ.range.one_mem
    · obtain ⟨k, hk, hkv⟩ := (sec9m_autL h6 hctx).2 v b hv1 hb
      obtain ⟨n, hnN, hnB, hnconj⟩ := sec9m_mem_autIn.mp (sec9m_autIn_le hT h6 hctx hk)
      have hx'N : n * (x₀ : G) * n⁻¹ ∈ centMod (Asub9 t t₀ B) B :=
        (centMod (Asub9 t t₀ B) B).mul_mem
          ((centMod (Asub9 t t₀ B) B).mul_mem hnN x₀.2.1)
          ((centMod (Asub9 t t₀ B) B).inv_mem hnN)
      have hx'cent : n * (x₀ : G) * n⁻¹ ∈ centralizer (B : Set G) :=
        sec9f_conj_centralizer hnB x₀.2.2
      let x' : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) :=
        ⟨n * (x₀ : G) * n⁻¹, hx'N, hx'cent⟩
      have hna : n⁻¹ * t * n * t⁻¹ ∈ B := by
        have h := ((centMod (Asub9 t t₀ B) B).inv_mem hnN).2 t htA
        simpa using h
      have hmB : ∀ b ∈ B, (x₀ : G) * b = b * (x₀ : G) := fun b hb =>
        (Subgroup.mem_centralizer_iff.mp x₀.2.2 b hb).symm
      have hma : (x₀ : G) * t * (x₀ : G)⁻¹ * t⁻¹ ∈ B := by
        rw [← hτ x₀, hx₀]; exact v.2
      have hτx' : τ x' = b := by
        apply Subtype.ext
        calc ((τ x' : ↥B) : G) = (x' : G) * t * (x' : G)⁻¹ * t⁻¹ := hτ x'
          _ = n * ((x₀ : G) * t * (x₀ : G)⁻¹ * t⁻¹) * n⁻¹ :=
              sec9m_conj_comm hBc hna hmB hma
          _ = n * ((v : ↥B) : G) * n⁻¹ := by rw [← hτ x₀, hx₀]
          _ = ((k v : ↥B) : G) := (hnconj v).symm
          _ = (b : G) := by rw [hkv]
      exact MonoidHom.mem_range.mpr ⟨x', hτx'⟩

end CFSG.OddStandard.SmallF3.Omega
