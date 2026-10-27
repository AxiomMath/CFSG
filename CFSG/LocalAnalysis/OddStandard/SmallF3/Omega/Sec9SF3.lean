module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

theorem sec9f_range_ne_bot (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hctx : Sec9Choice G t L S z g B t₀)
    (τ : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) :
    τ.range ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, -, -, -, h2tr⟩ :=
    asc82Lemma9N_of h36 h68 hB8 hT G t L S z g B t₀ hctx
  have hB16 : Nat.card B = 16 := by rw [hctx.B_e16.2]; norm_num
  have htX : t ∈ cosetSet t B := ⟨1, B.one_mem, by simp⟩
  have hX16 : (cosetSet t B).ncard = 16 := sec9n_ncard_coset hB16
  let N : Subgroup G := centMod (Asub9 t t₀ B) B
  let Nt : Subgroup G := N ⊓ centralizer ({t} : Set G)
  have hcardN : Nat.card ↥N = 16 * Nat.card ↥Nt := by
    have h := sec9f_card_stab h2tr htX (by rw [hX16]; norm_num)
    rw [hX16] at h
    exact h
  have hNnorm : N ≤ normalizer (B : Set G) := fun x hx => hx.1
  let ρ : ↥N →* MulAut ↥B := B.normalizerMonoidHom.comp (Subgroup.inclusion hNnorm)
  let Nt' : Subgroup ↥N := Nt.subgroupOf N
  have hker : ρ.ker ≤ Nt' := by
    intro x hx
    have hx1 : B.normalizerMonoidHom (Subgroup.inclusion hNnorm x) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxC : (x : G) ∈ centralizer (B : Set G) := by
      have h2 : Subgroup.inclusion hNnorm x ∈ B.normalizerMonoidHom.ker :=
        MonoidHom.mem_ker.mpr hx1
      rw [Subgroup.normalizerMonoidHom_ker] at h2
      have h3 : ((Subgroup.inclusion hNnorm x : ↥(normalizer (B : Set G))) : G)
          ∈ centralizer (B : Set G) := Subgroup.mem_subgroupOf.mp h2
      rwa [Subgroup.coe_inclusion] at h3
    have hxCmem : (x : G) ∈ N ⊓ centralizer (B : Set G) := ⟨x.2, hxC⟩
    have hτ1 : τ ⟨(x : G), hxCmem⟩ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxCmem⟩, rfl⟩
    have hτval : ((τ ⟨(x : G), hxCmem⟩ : ↥B) : G) = 1 := by
      rw [hτ1, Subgroup.coe_one]
    have hcomm : (x : G) * t = t * (x : G) := by
      have h := hτ ⟨(x : G), hxCmem⟩
      rw [hτval] at h
      have h1 : (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1 := h.symm
      calc (x : G) * t = ((x : G) * t * (x : G)⁻¹ * t⁻¹) * t * (x : G) := by group
        _ = 1 * t * (x : G) := by rw [h1]
        _ = t * (x : G) := by group
    have hxcent : (x : G) ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxcent⟩
  let Ht : Subgroup (MulAut ↥B) := autIn L B
  have hHt : Ht ≤ Nt'.map ρ := by
    intro φ hφ
    have hφ' : φ ∈ autIn (L ⊓ N) B := sec9f_autIn_le_inf hT h6 hctx.toSec9Ctx hφ
    obtain ⟨x, hxLN, hxnorm, hxφ⟩ := sec9m_mem_autIn.mp hφ'
    have hxL : x ∈ L := hxLN.1
    have hxN : x ∈ N := hxLN.2
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_iff.mp (sec9n_t_mem_cent hctx.toSec9Ctx) x hxL
    have hxcent : x ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxt
    have hxNt' : (⟨x, hxN⟩ : ↥N) ∈ Nt' :=
      Subgroup.mem_subgroupOf.mpr ⟨hxN, hxcent⟩
    have hρx : ρ ⟨x, hxN⟩ = φ := by
      refine MulEquiv.ext (fun b => Subtype.ext ?_)
      have h1 : ((ρ ⟨x, hxN⟩) b : G) = x * (b : G) * x⁻¹ := by
        change ((B.normalizerMonoidHom (Subgroup.inclusion hNnorm ⟨x, hxN⟩)) b : G) = _
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      rw [h1, hxφ b]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hxNt', hρx⟩
  have hHtcard : Nat.card ↥Ht = 360 :=
    sec9m_card_A6 (sec9m_autL h6 hctx.toSec9Ctx).1
  have h360 : 360 ∣ Nat.card ↥Ht := by rw [hHtcard]
  have hidx : Nt'.index = 16 := by
    have h1 : Nat.card ↥Nt' * Nt'.index = Nat.card ↥N :=
      Subgroup.card_mul_index (H := Nt')
    have h2 : Nat.card ↥Nt' = Nat.card ↥Nt :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Nt ≤ N)).toEquiv
    rw [h2, hcardN] at h1
    rw [mul_comm (16 : ℕ) (Nat.card ↥Nt)] at h1
    haveI : Nonempty ↥Nt := ⟨1⟩
    exact Nat.mul_left_cancel (Nat.card_pos) h1
  have hΓ : Nat.card (MulAut ↥B) = 20160 := sec9m_card_mulAut hctx.B_e16
  exact sec9f_count_contra ρ Nt' hker hidx Ht hHt h360 hΓ

theorem sec9f_top_iso (h36 : Asc82Lemma36) (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hN : Asc82NormA6) (hctx : Sec9Ctx G t L S z g B t₀)
    (τ : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) →* ↥B)
    (hτ : ∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) (htop : τ.range = ⊤) :
    Nonempty (↥(autIn (centMod (Asub9 t t₀ B) B) B) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(autIn (centMod (Asub9 t t₀ B) B) B) ≃* Equiv.Perm (Fin 6)) := by
  let N : Subgroup G := centMod (Asub9 t t₀ B) B
  let Nt : Subgroup G := N ⊓ centralizer ({t} : Set G)
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hNA_le_Nt : autIn N B ≤ autIn Nt B := by
    intro φ hφ
    obtain ⟨n, hnN, hnNorm, hnφ⟩ := sec9m_mem_autIn.mp hφ
    have hb1 : n * t * n⁻¹ * t⁻¹ ∈ B := hnN.2 t htA
    have hb1rn : (⟨n * t * n⁻¹ * t⁻¹, hb1⟩ : ↥B) ∈ τ.range := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hb1rn
    have hct : (c : G) * t * (c : G)⁻¹ * t⁻¹ = n * t * n⁻¹ * t⁻¹ := by
      have h := hτ c
      rw [hc] at h
      exact h.symm
    have hct' : (c : G) * t * (c : G)⁻¹ = (n * t * n⁻¹ * t⁻¹) * t := by
      calc (c : G) * t * (c : G)⁻¹
          = ((c : G) * t * (c : G)⁻¹ * t⁻¹) * t := by group
        _ = (n * t * n⁻¹ * t⁻¹) * t := by rw [hct]
    have hnt : n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t := by group
    let y : G := (c : G)⁻¹ * n
    have hyN : y ∈ N := N.mul_mem (N.inv_mem c.2.1) hnN
    have hyNorm : y ∈ normalizer (B : Set G) :=
      (normalizer (B : Set G)).mul_mem ((normalizer (B : Set G)).inv_mem (c.2.1).1) hnNorm
    have hyt : y * t * y⁻¹ = t := by
      have h1 : y * t * y⁻¹ = (c : G)⁻¹ * (n * t * n⁻¹) * (c : G) := by
        change (c : G)⁻¹ * n * t * ((c : G)⁻¹ * n)⁻¹
          = (c : G)⁻¹ * (n * t * n⁻¹) * (c : G)
        group
      rw [h1, hnt, ← hct']
      group
    have hytc : y * t = t * y := by
      calc y * t = (y * t * y⁻¹) * y := by group
        _ = t * y := by rw [hyt]
    have hycent : y ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hytc
    have hyNt : y ∈ Nt := ⟨hyN, hycent⟩
    have hyb : ∀ b : ↥B, y * (b : G) * y⁻¹ = n * (b : G) * n⁻¹ := by
      intro b
      have hnb : n * (b : G) * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hnNorm b).mp b.2
      have hcc : (n * (b : G) * n⁻¹) * (c : G) = (c : G) * (n * (b : G) * n⁻¹) :=
        Subgroup.mem_centralizer_iff.mp c.2.2 (n * (b : G) * n⁻¹) hnb
      calc y * (b : G) * y⁻¹
          = (c : G)⁻¹ * (n * (b : G) * n⁻¹) * (c : G) := by
            change (c : G)⁻¹ * n * (b : G) * ((c : G)⁻¹ * n)⁻¹
              = (c : G)⁻¹ * (n * (b : G) * n⁻¹) * (c : G)
            group
        _ = (c : G)⁻¹ * ((n * (b : G) * n⁻¹) * (c : G)) := by group
        _ = (c : G)⁻¹ * ((c : G) * (n * (b : G) * n⁻¹)) := by rw [hcc]
        _ = n * (b : G) * n⁻¹ := by group
    refine sec9m_mem_autIn.mpr ⟨y, hyNt, hyNorm, fun b => ?_⟩
    rw [hnφ b, hyb b]
  have hLN : L ⊓ N ≤ Nt := by
    intro x hx
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_iff.mp (sec9n_t_mem_cent hctx) x hx.1
    exact ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  have hNtNorm : Nt ≤ normalizer (B : Set G) := fun x hx => hx.1.1
  have hX : ∀ y ∈ Nt, ∀ x ∈ L ⊓ N, y * x * y⁻¹ ∈ L ⊓ N := by
    intro y hy x hx
    have hycent : y ∈ centralizer ({t} : Set G) := hy.2
    have hyNormL : y ∈ normalizer (L : Set G) :=
      sec9n_mem_normalizer_of_conjugate_eq
        (conjugate_eq_self_of_lemma36 h36 hctx.toSec3SettingLB y hycent)
    refine ⟨?_, N.mul_mem (N.mul_mem hy.1 hx.2) (N.inv_mem hy.1)⟩
    exact (Subgroup.mem_normalizer_iff.mp hyNormL x).mp hx.1
  have hautIn : autIn (L ⊓ N) B = autIn L B :=
    le_antisymm (sec9m_autIn_mono inf_le_left) (sec9f_autIn_le_inf hT h6 hctx)
  have hconj : ∀ h ∈ autIn N B, ∀ a ∈ autIn L B, h * a * h⁻¹ ∈ autIn L B := by
    intro h hh a ha
    have hh' : h ∈ autIn Nt B := hNA_le_Nt hh
    have ha' : a ∈ autIn (L ⊓ N) B := by rw [hautIn]; exact ha
    have hres :=
      sec9m_autIn_conj (X := L ⊓ N) (Y := Nt) (B := B) hLN hNtNorm hX h hh' a ha'
    rwa [hautIn] at hres
  exact hN G B hctx.B_e16 (autIn L B) (autIn N B)
    (sec9m_autIn_le hT h6 hctx) (sec9m_autL h6 hctx).1 hconj

end CFSG.OddStandard.SmallF3.Omega
