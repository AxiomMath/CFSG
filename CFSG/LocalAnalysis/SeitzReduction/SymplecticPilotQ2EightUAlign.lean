module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section PermMat

variable {K F : Type} [Field K] [CharP K 2] [Field F] {σ : F ≃+* F} {ι : K →+* F}
  {hι : ∀ c, σ (ι c) = ι c}

@[expose] noncomputable def ctuPermCoord (π : Equiv.Perm (Fin 4)) (a : Fin (2 * 4 + 0)) :
    Fin (2 * 4 + 0) :=
  ctuCoord 4 0 (Sum.map (Sum.map π π) id ((ctuCoord 4 0).symm a))

theorem ctuPermCoord_ctuCoord (π : Equiv.Perm (Fin 4)) (w : (Fin 4 ⊕ Fin 4) ⊕ Fin 0) :
    ctuPermCoord π (ctuCoord 4 0 w) = ctuCoord 4 0 (Sum.map (Sum.map π π) id w) := by
  rw [ctuPermCoord, Equiv.symm_apply_apply]

theorem ctuPermCoord_inv_apply (π : Equiv.Perm (Fin 4)) (a : Fin (2 * 4 + 0)) :
    ctuPermCoord π (ctuPermCoord π⁻¹ a) = a := by
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  rw [ctuPermCoord_ctuCoord, ctuPermCoord_ctuCoord]
  congr 1
  rcases w with (p | p) | i
  · simp
  · simp
  · exact i.elim0

theorem mat_ctuEmbed_permSp (π : Equiv.Perm (Fin 4)) (a b : Fin (2 * 4 + 0)) :
    (((ctuEmbed 0 (Nat.zero_le 1) σ ι hι (permSp K π) : SU σ (2 * 4 + 0)) :
      GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b =
        if a = ctuPermCoord π b then 1 else 0 := by
  obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 4 0).surjective b
  rw [ctuEmbed_apply_ctuCoord, ctuPermCoord_ctuCoord]
  simp only [(ctuCoord 4 0).injective.eq_iff]
  rcases w with u | i
  · rcases w' with v | j
    · rw [fromBlocks_apply₁₁, map_apply, mat_permSp, spIncl_apply]
      simp only [Sum.map_inl, Sum.inl.injEq]
      split_ifs <;> simp
    · exact j.elim0
  · exact i.elim0

theorem conj_ctuEmbed_permSp_apply (π : Equiv.Perm (Fin 4)) (x : SU σ (2 * 4 + 0))
    (a b : Fin (2 * 4 + 0)) :
    (((ctuEmbed 0 (Nat.zero_le 1) σ ι hι (permSp K π) * x *
      (ctuEmbed 0 (Nat.zero_le 1) σ ι hι (permSp K π))⁻¹ : SU σ (2 * 4 + 0)) :
        GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) a b =
      (((x : SU σ (2 * 4 + 0)) : GL (Fin (2 * 4 + 0)) F) :
        Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F) (ctuPermCoord π⁻¹ a)
          (ctuPermCoord π⁻¹ b) := by
  classical
  rw [← map_inv, ← permSp_inv_eightU]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, mat_ctuEmbed_permSp]
  rw [Finset.sum_eq_single (ctuPermCoord π⁻¹ b)]
  · rw [Finset.sum_eq_single (ctuPermCoord π⁻¹ a)]
    · simp [ctuPermCoord_inv_apply]
    · intro c _ hc
      rw [ite_mul, one_mul, zero_mul]
      split_ifs with h
      · exfalso
        apply hc
        rw [h]
        have := ctuPermCoord_inv_apply π⁻¹ c
        rw [inv_inv] at this
        exact this.symm
      · rfl
    · simp
  · intro d _ hd
    simp [hd]
  · simp

theorem ctuEmbed_permSp_conj_mem_ctuBlock (π : Equiv.Perm (Fin 4)) {R : Finset (Fin 4)}
    {x : SU σ (2 * 4 + 0)} (hx : x ∈ ctuBlock σ 0 R) :
    ctuEmbed 0 (Nat.zero_le 1) σ ι hι (permSp K π) * x *
        (ctuEmbed 0 (Nat.zero_le 1) σ ι hι (permSp K π))⁻¹ ∈ ctuBlock σ 0 (R.image π) := by
  classical
  have hplane : ∀ a : Fin (2 * 4 + 0), a ∈ ctuPlanes 0 (R.image π) →
      ctuPermCoord π⁻¹ a ∈ ctuPlanes 0 R := by
    intro a ha
    obtain ⟨w, rfl⟩ := (ctuCoord 4 0).surjective a
    rw [ctuCoord_mem_ctuPlanes] at ha
    rw [ctuPermCoord_ctuCoord, ctuCoord_mem_ctuPlanes]
    rcases w with u | i
    · simp only [inPlanes_inl, Sum.map_inl] at ha ⊢
      have hpl : ∀ (f : Fin 4 → Fin 4) (v : Fin 4 ⊕ Fin 4),
          planeOf (Sum.map f f v) = f (planeOf v) := fun f v => by rcases v with v | v <;> rfl
      rw [hpl]
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.1 ha
      rw [← hpu]
      simpa using hp
    · exact i.elim0
  rw [mem_ctuBlock]
  intro a b hab
  rw [conj_ctuEmbed_permSp_apply, mem_ctuBlock.1 hx _ _ (hab.imp (hplane a) (hplane b)),
    Matrix.one_apply, Matrix.one_apply]
  have hinj : Function.Injective (ctuPermCoord π⁻¹) := fun c d h => by
    have h1 := congrArg (ctuPermCoord π) h
    rwa [ctuPermCoord_inv_apply, ctuPermCoord_inv_apply] at h1
  simp only [hinj.eq_iff]

end PermMat

section Swaps

variable {K : Type} [Field K]

theorem permSp_swap_mem_spBlock_eightU (a b : Fin 4) :
    permSp K (Equiv.swap a b) ∈ spBlock K ({a, b} : Finset (Fin 4)) := by
  classical
  rw [mem_spBlock, mat_permSp]
  intro r t hrt
  rw [spIncl_apply]
  have hpl : ∀ v : Fin 4 ⊕ Fin 4, planeOf (Sum.map (Equiv.swap a b) (Equiv.swap a b) v) =
      Equiv.swap a b (planeOf v) := fun v => by rcases v with v | v <;> rfl
  by_cases ht : t ∈ planeCoords ({a, b} : Finset (Fin 4))
  · have hr : r ∉ planeCoords ({a, b} : Finset (Fin 4)) := fun hr => hrt ⟨hr, ht⟩
    have hne : r ≠ Sum.map (Equiv.swap a b) (Equiv.swap a b) t := by
      intro h
      apply hr
      rw [h, mem_planeCoords, hpl]
      rw [mem_planeCoords] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      rcases ht with h' | h' <;> rw [h']
      · right; exact Equiv.swap_apply_left a b
      · left; exact Equiv.swap_apply_right a b
    have hne' : r ≠ t := fun h => hr (h ▸ ht)
    simp [hne, hne']
  · have hfix : Sum.map (Equiv.swap a b) (Equiv.swap a b) t = t := by
      rw [mem_planeCoords] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      rcases t with t | t <;>
      · simp only [planeOf_inl, planeOf_inr] at ht
        simp [Equiv.swap_apply_of_ne_of_ne ht.1 ht.2]
    rw [hfix, Matrix.one_apply]

theorem permSp_swap_mul_self (a b : Fin 4) :
    permSp K (Equiv.swap a b) * permSp K (Equiv.swap a b) = 1 := by
  rw [← permSp_mul_eightU, Equiv.swap_mul_self, permSp_one_eightU]

theorem permSp_swap_inv (a b : Fin 4) :
    (permSp K (Equiv.swap a b))⁻¹ = permSp K (Equiv.swap a b) :=
  inv_eq_of_mul_eq_one_right (permSp_swap_mul_self a b)

theorem permSp_swap_zero_eq {k l : Fin 4} (hl : l ≠ 0) (hkl : k ≠ l) :
    permSp K (Equiv.swap (0 : Fin 4) l) =
      permSp K (Equiv.swap 0 k) * permSp K (Equiv.swap k l) * permSp K (Equiv.swap 0 k) := by
  have h := Equiv.swap_apply_apply (Equiv.swap (0 : Fin 4) k) k l
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hl hkl.symm, Equiv.swap_inv] at h
  rw [h, permSp_mul_eightU, permSp_mul_eightU]

end Swaps

section Align

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

omit [Finite G] [Finite K] in
theorem NsUniParam.map_conj_ctuEmbed {k : Fin 4}
    (P : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) {u : StatedSp 4 K}
    (hu : u ∈ spBlock K ({k} : Finset (Fin 4))ᶜ) {x : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4)))
    (hx' : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι u * x *
      (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι u)⁻¹ ∈
        ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4))) :
    P.Φ ⟨_, hx'⟩ = ((e.symm u : L) : G) * P.Φ ⟨x, hx⟩ * ((e.symm u : L) : G)⁻¹ := by
  have hu' := ctuEmbed_mem_ctuBlock_iff (ε := 0) (hε := Nat.zero_le 1)
    (σ := unitaryInvolution F 2 1) (ι := ι) (hι := hι) |>.2 hu
  have h1 : (⟨_, hx'⟩ : ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4))) =
      ⟨_, hu'⟩ * ⟨x, hx⟩ * (⟨_, hu'⟩ : ctuBlock (unitaryInvolution F 2 1) 0
        ({k} : Finset (Fin 4)))⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, P.N1 u hu]

theorem exists_nsUniParam_normalized_four (hK : Nat.card K = 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k) :
    ∃ Q : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k,
      ∀ (k : Fin 4) (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, 0} : Finset (Fin 4))),
        (Q k).Φ ⟨x, ctuBlock_pair_le_left _ k 0 hx⟩ =
          (P 0).Φ ⟨x, ctuBlock_pair_le_right _ k 0 hx⟩ := by
  have hex : ∀ k : Fin 4, ∃ R : NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k,
      ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, 0} : Finset (Fin 4))),
        R.Φ ⟨x, ctuBlock_pair_le_left _ k 0 hx⟩ = (P 0).Φ ⟨x, ctuBlock_pair_le_right _ k 0 hx⟩ := by
    intro k
    by_cases hko : k = 0
    · subst hko
      exact ⟨P 0, fun x hx => rfl⟩
    · obtain ⟨ν, hν, b, h1⟩ := (P k).exists_twist_of_overlap (by rw [hK, pow_one]) hF le_rfl
        le_rfl hko (P 0)
      have hT := ctuaTwist_admissible (N := 4) (hε := Nat.zero_le 1) (ι := ι) (hι := hι)
        (hσ := unitaryInvolution_involutive hF) hν b
      refine ⟨(P k).twistBy hT.inv, fun x hx => ?_⟩
      rw [NsUniParam.twistBy_Φ_apply]
      have hx' : (ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 1)
          (unitaryInvolution_involutive hF) ν hν b)⁻¹ x ∈
            ctuBlock (unitaryInvolution F 2 1) 0 ({k, 0} : Finset (Fin 4)) :=
        (hT.inv.mem_iff _ x).2 hx
      refine (h1 _ hx').trans (congrArg (P 0).Φ (Subtype.ext ?_))
      change (ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF)
        ν hν b) ((ctuaTwist (Nat.zero_le 1) (unitaryInvolution F 2 1)
          (unitaryInvolution_involutive hF) ν hν b)⁻¹ x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  choose Q hQ using hex
  exact ⟨Q, hQ⟩

theorem exists_nsUniParamAgree_even_four (hK : Nat.card K = 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    (hkey : ∀ (k l : Fin 4), k ≠ l → ∀ z ∈ centralizerPerfectCore
        (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)),
      ((e.symm (permSp K (Equiv.swap k l)) : L) : G) * z =
        z * ((e.symm (permSp K (Equiv.swap k l)) : L) : G)) :
    ∃ Q : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k,
      NsUniParamAgree Q := by
  classical
  obtain ⟨Q, hQ⟩ := exists_nsUniParam_normalized_four hK hF P
  have hQk : ∀ (k : Fin 4) (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hxk : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4)))
      (hx0 : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4))),
      (Q k).Φ ⟨x, hxk⟩ = (P 0).Φ ⟨x, hx0⟩ := fun k x hxk hx0 =>
    hQ k x (mem_ctuBlock_pair hxk hx0)
  refine ⟨Q, fun k l x hxk hxl => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  by_cases hk0 : k = 0
  · subst hk0
    exact (hQk 0 x hxk hxk).trans (hQk l x hxl hxk).symm
  by_cases hl0 : l = 0
  · subst hl0
    exact (hQk k x hxk hxl).trans (hQk 0 x hxl hxl).symm
  have hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k, l} : Finset (Fin 4)) :=
    mem_ctuBlock_pair hxk hxl
  have hsw : ∀ a b : Fin 4, ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap a b)) * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap a b)) = 1 := fun a b => by
    rw [← map_mul, permSp_swap_mul_self, map_one]
  have hswi : ∀ a b : Fin 4, (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap a b)))⁻¹ = ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap a b)) := fun a b => inv_eq_of_mul_eq_one_right (hsw a b)
  have hmemk : ∀ {a b c : Fin 4}, c ≠ a → c ≠ b →
      permSp K (Equiv.swap a b) ∈ spBlock K ({c} : Finset (Fin 4))ᶜ := by
    intro a b c hca hcb
    refine spBlock_mono ?_ (permSp_swap_mem_spBlock_eightU a b)
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [Ne.symm hca, Ne.symm hcb]
  have himg1 : ({k, l} : Finset (Fin 4)).image (Equiv.swap (0 : Fin 4) l) = {k, 0} := by
    rw [Finset.image_insert, Finset.image_singleton, Equiv.swap_apply_of_ne_of_ne hk0 hkl,
      Equiv.swap_apply_right]
  have himg2 : ({k, l} : Finset (Fin 4)).image (Equiv.swap (0 : Fin 4) k) = {0, l} := by
    rw [Finset.image_insert, Finset.image_singleton, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hl0 (Ne.symm hkl)]
  have hy := ctuEmbed_permSp_conj_mem_ctuBlock (ι := ι) (hι := hι) (Equiv.swap (0 : Fin 4) l) hx
  rw [himg1] at hy
  have hy' := ctuEmbed_permSp_conj_mem_ctuBlock (ι := ι) (hι := hι) (Equiv.swap (0 : Fin 4) k) hx
  rw [himg2] at hy'
  obtain ⟨W0l, hW0l⟩ : ∃ W, W = ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap (0 : Fin 4) l)) := ⟨_, rfl⟩
  obtain ⟨W0k, hW0k⟩ : ∃ W, W = ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap (0 : Fin 4) k)) := ⟨_, rfl⟩
  obtain ⟨Wkl, hWkl⟩ : ∃ W, W = ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
      (permSp K (Equiv.swap k l)) := ⟨_, rfl⟩
  rw [← hW0l] at hy
  rw [← hW0k] at hy'
  set y := W0l * x * W0l⁻¹ with hydef
  set y' := W0k * x * W0k⁻¹ with hy'def
  have hyk : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4)) :=
    ctuBlock_pair_le_left _ k 0 hy
  have hy0 : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4)) :=
    ctuBlock_pair_le_right _ k 0 hy
  have hy'l : y' ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({l} : Finset (Fin 4)) :=
    ctuBlock_pair_le_right _ 0 l hy'
  have hy'0 : y' ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4)) :=
    ctuBlock_pair_le_left _ 0 l hy'
  have hW0l2 : W0l * W0l = 1 := by rw [hW0l]; exact hsw 0 l
  have hW0k2 : W0k * W0k = 1 := by rw [hW0k]; exact hsw 0 k
  have hxy : W0l * y * W0l⁻¹ = x := by
    rw [hydef, inv_eq_of_mul_eq_one_right hW0l2]
    calc W0l * (W0l * x * W0l) * W0l = (W0l * W0l) * x * (W0l * W0l) := by group
      _ = x := by rw [hW0l2, one_mul, mul_one]
  have hxy' : W0k * y' * W0k⁻¹ = x := by
    rw [hy'def, inv_eq_of_mul_eq_one_right hW0k2]
    calc W0k * (W0k * x * W0k) * W0k = (W0k * W0k) * x * (W0k * W0k) := by group
      _ = x := by rw [hW0k2, one_mul, mul_one]
  have hcomm : y * W0k = W0k * y := by
    rw [hW0k]
    refine commute_ctuBlock_ctuEmbed hy ?_
    rw [Finset.pair_comm]
    exact permSp_swap_mem_spBlock_eightU 0 k
  have hperm : W0k * W0l = Wkl * W0k := by
    rw [hW0k, hW0l, hWkl, ← map_mul, ← map_mul, permSp_swap_zero_eq hl0 hkl]
    rw [← mul_assoc, ← mul_assoc, permSp_swap_mul_self, one_mul]
  have hWkl2 : Wkl * Wkl = 1 := by rw [hWkl]; exact hsw k l
  have hx' : x = W0l * y * W0l := by
    rw [← hxy, inv_eq_of_mul_eq_one_right hW0l2]
  have h1 : W0l * W0k = W0k * Wkl := by
    have h2 := congrArg (fun g => g⁻¹) hperm
    simp only [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hW0k2,
      inv_eq_of_mul_eq_one_right hW0l2, inv_eq_of_mul_eq_one_right hWkl2] at h2
    exact h2
  have hyy' : y' = Wkl * y * Wkl⁻¹ := by
    rw [hy'def, inv_eq_of_mul_eq_one_right hW0k2, inv_eq_of_mul_eq_one_right hWkl2]
    calc W0k * x * W0k = W0k * (W0l * y * W0l) * W0k := by rw [← hx']
      _ = (W0k * W0l) * y * (W0l * W0k) := by group
      _ = (Wkl * W0k) * y * (W0k * Wkl) := by rw [hperm, h1]
      _ = Wkl * (y * W0k * W0k) * Wkl := by rw [hcomm]; group
      _ = Wkl * y * Wkl := by rw [mul_assoc y, hW0k2, mul_one]
  have e1 : (Q k).Φ ⟨x, hxk⟩ = ((e.symm (permSp K (Equiv.swap (0 : Fin 4) l)) : L) : G) *
      (P 0).Φ ⟨y, hy0⟩ * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) l)) : L) : G)⁻¹ := by
    have hxk' : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap (0 : Fin 4) l)) * y * (ctuEmbed 0 (Nat.zero_le 1)
          (unitaryInvolution F 2 1) ι hι (permSp K (Equiv.swap (0 : Fin 4) l)))⁻¹ ∈
            ctuBlock (unitaryInvolution F 2 1) 0 ({k} : Finset (Fin 4)) := by
      rw [← hW0l, hxy]
      exact hxk
    have h2 := (Q k).map_conj_ctuEmbed (hmemk hk0 hkl) hyk hxk'
    rw [hQk k y hyk hy0] at h2
    rw [← h2]
    congr 1
    exact Subtype.ext (hxy.symm.trans (by rw [hW0l]))
  have e2 : (Q l).Φ ⟨x, hxl⟩ = ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) *
      (((e.symm (permSp K (Equiv.swap k l)) : L) : G) * (P 0).Φ ⟨y, hy0⟩ *
        ((e.symm (permSp K (Equiv.swap k l)) : L) : G)⁻¹) *
          ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G)⁻¹ := by
    have hxl' : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap (0 : Fin 4) k)) * y' * (ctuEmbed 0 (Nat.zero_le 1)
          (unitaryInvolution F 2 1) ι hι (permSp K (Equiv.swap (0 : Fin 4) k)))⁻¹ ∈
            ctuBlock (unitaryInvolution F 2 1) 0 ({l} : Finset (Fin 4)) := by
      rw [← hW0k, hxy']
      exact hxl
    have h2 := (Q l).map_conj_ctuEmbed (hmemk hl0 (Ne.symm hkl)) hy'l hxl'
    rw [hQk l y' hy'l hy'0] at h2
    have hy'0' : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (permSp K (Equiv.swap k l)) * y * (ctuEmbed 0 (Nat.zero_le 1)
          (unitaryInvolution F 2 1) ι hι (permSp K (Equiv.swap k l)))⁻¹ ∈
            ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4)) := by
      rw [← hWkl, ← hyy']
      exact hy'0
    have h3 := (P 0).map_conj_ctuEmbed (hmemk (Ne.symm hk0) (Ne.symm hl0)) hy0 hy'0'
    have h4 : (P 0).Φ ⟨y', hy'0⟩ = (P 0).Φ ⟨_, hy'0'⟩ :=
      congrArg (P 0).Φ (Subtype.ext (hyy'.trans (by rw [hWkl])))
    rw [h4, h3] at h2
    rw [← h2]
    congr 1
    exact Subtype.ext (hxy'.symm.trans (by rw [hW0k]))
  have hy0k : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, k} : Finset (Fin 4)) := by
    rw [Finset.pair_comm]
    exact hy
  have hz := (P 0).mem_overlap hF (Ne.symm hk0) hy0k
  have hc := hkey 0 k (Ne.symm hk0) _ hz
  have hw : ((e.symm (permSp K (Equiv.swap (0 : Fin 4) l)) : L) : G) =
      ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) *
        ((e.symm (permSp K (Equiv.swap k l)) : L) : G) *
          ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) := by
    rw [permSp_swap_zero_eq hl0 hkl, map_mul, map_mul, L.coe_mul, L.coe_mul]
  have hwi : ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G)⁻¹ =
      ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) := by
    rw [← L.coe_inv, ← map_inv, permSp_swap_inv]
  rw [e1, e2, hw]
  have hc' : ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) * (P 0).Φ ⟨y, hy0⟩ =
      (P 0).Φ ⟨y, hy0⟩ * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) := hc
  calc ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) *
          ((e.symm (permSp K (Equiv.swap k l)) : L) : G) *
            ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) * (P 0).Φ ⟨y, hy0⟩ *
              (((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) *
                ((e.symm (permSp K (Equiv.swap k l)) : L) : G) *
                  ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G))⁻¹ =
        ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) *
          ((e.symm (permSp K (Equiv.swap k l)) : L) : G) *
            (((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) * (P 0).Φ ⟨y, hy0⟩) *
              ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G)⁻¹ *
                ((e.symm (permSp K (Equiv.swap k l)) : L) : G)⁻¹ *
                  ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G)⁻¹ := by group
    _ = _ := by
      rw [hc']
      group

end Align

end CFSG.SeitzReduction.SymplecticPilot
