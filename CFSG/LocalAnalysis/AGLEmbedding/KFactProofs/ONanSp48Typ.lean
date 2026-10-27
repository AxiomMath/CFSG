module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Blk

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups Matrix

@[expose] noncomputable def spT0 : Subgroup Sp8 := (slT.prod slT).map blkHom

theorem mem_spT0_iff (g : Sp8) : g ∈ spT0 ↔ ∃ x ∈ slT, ∃ y ∈ slT, g = blk0 x * blk1 y := by
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem card_spT0 : Nat.card spT0 = 81 := by
  rw [spT0, Subgroup.card_map_of_injective blkHom_injective,
    Nat.card_congr (Subgroup.prodEquiv slT slT).toEquiv, Nat.card_prod, card_slT]

theorem comm_spT0 : ∀ a ∈ spT0, ∀ b ∈ spT0, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff a).1 ha
  obtain ⟨x', hx', y', hy', rfl⟩ := (mem_spT0_iff b).1 hb
  rw [blk_mul, blk_mul]
  obtain ⟨k, rfl⟩ := (mem_slT_iff x).1 hx
  obtain ⟨k', rfl⟩ := (mem_slT_iff x').1 hx'
  obtain ⟨l, rfl⟩ := (mem_slT_iff y).1 hy
  obtain ⟨l', rfl⟩ := (mem_slT_iff y').1 hy'
  rw [pow_mul_comm slA k.val k'.val, pow_mul_comm slA l.val l'.val]

theorem exp_spT0 : ∀ t ∈ spT0, t ^ 9 = 1 := by
  intro t ht
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff t).1 ht
  have : (blk0 x * blk1 y) ^ 9 = blkHom (x, y) ^ 9 := rfl
  rw [this, ← map_pow]
  obtain ⟨k, rfl⟩ := (mem_slT_iff x).1 hx
  obtain ⟨l, rfl⟩ := (mem_slT_iff y).1 hy
  have h1 : (slA ^ (k : ℕ)) ^ 9 = 1 := by rw [← pow_mul, mul_comm, pow_mul, slA_pow9, one_pow]
  have h2 : (slA ^ (l : ℕ)) ^ 9 = 1 := by rw [← pow_mul, mul_comm, pow_mul, slA_pow9, one_pow]
  rw [Prod.pow_mk, h1, h2]
  exact map_one blkHom

@[expose] noncomputable def spZ1 : Sp8 := blk0 slZ

@[expose] noncomputable def spZ12 : Sp8 := blk0 slZ * blk1 slZ

@[expose] def SpFPF (g : Sp8) : Prop := ∀ v : Fin 2 ⊕ Fin 2 → GF8, mat 2 GF8 g *ᵥ v = v → v = 0

theorem SpFPF_conj (c g : Sp8) : SpFPF (c * g * c⁻¹) ↔ SpFPF g := by
  have key : ∀ (c g : Sp8), SpFPF (c * g * c⁻¹) → SpFPF g := by
    intro c g h v hv
    have h1 : mat 2 GF8 (c * g * c⁻¹) *ᵥ (mat 2 GF8 c *ᵥ v) = mat 2 GF8 c *ᵥ v := by
      rw [Matrix.mulVec_mulVec, ← map_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, map_mul,
        ← Matrix.mulVec_mulVec, hv]
    have h2 := h _ h1
    have h3 : v = mat 2 GF8 c⁻¹ *ᵥ (mat 2 GF8 c *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [h3, h2, Matrix.mulVec_zero]
  refine ⟨key c g, fun h => ?_⟩
  apply key c⁻¹ (c * g * c⁻¹)
  have : c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g := by group
  rw [this]
  exact h

theorem mulVec_blk (x y : Sl28) (v : Fin 2 ⊕ Fin 2 → GF8) :
    (mat 2 GF8 (blk0 x * blk1 y) *ᵥ v) (Sum.inl 0) =
        (x : Matrix (Fin 2) (Fin 2) GF8) 0 0 * v (Sum.inl 0) + x 0 1 * v (Sum.inr 0) ∧
    (mat 2 GF8 (blk0 x * blk1 y) *ᵥ v) (Sum.inr 0) = x 1 0 * v (Sum.inl 0) + x 1 1 * v (Sum.inr 0) ∧
    (mat 2 GF8 (blk0 x * blk1 y) *ᵥ v) (Sum.inl 1) = y 0 0 * v (Sum.inl 1) + y 0 1 * v (Sum.inr 1) ∧
    (mat 2 GF8 (blk0 x * blk1 y) *ᵥ v) (Sum.inr 1) =
      y 1 0 * v (Sum.inl 1) + y 1 1 * v (Sum.inr 1) := by
  rw [map_mul, mat_longBlock, mat_longBlock]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat,
      Matrix.mul_apply]

theorem slZ_inv_val : ((slZ⁻¹ : Sl28) : Matrix (Fin 2) (Fin 2) GF8) = mk28 0 1 1 1 := by
  decide +kernel

theorem fixed_z : ∀ p q : GF8, GF8.ofNat' 1 * p + GF8.ofNat' 1 * q = p →
    GF8.ofNat' 1 * p + GF8.ofNat' 0 * q = q → p = 0 ∧ q = 0 := by decide +kernel

theorem fixed_zinv : ∀ p q : GF8, GF8.ofNat' 0 * p + GF8.ofNat' 1 * q = p →
    GF8.ofNat' 1 * p + GF8.ofNat' 1 * q = q → p = 0 ∧ q = 0 := by decide +kernel

theorem fixed_zero {M : Matrix (Fin 2) (Fin 2) GF8} (hM : M = mk28 1 1 1 0 ∨ M = mk28 0 1 1 1)
    {p q : GF8} (h0 : M 0 0 * p + M 0 1 * q = p) (h1 : M 1 0 * p + M 1 1 * q = q) :
    p = 0 ∧ q = 0 := by
  rcases hM with rfl | rfl
  · exact fixed_z p q h0 h1
  · exact fixed_zinv p q h0 h1

theorem slZ_cases (x : Sl28) (h : x = slZ ∨ x = slZ⁻¹) :
    (x : Matrix (Fin 2) (Fin 2) GF8) = mk28 1 1 1 0 ∨
      (x : Matrix (Fin 2) (Fin 2) GF8) = mk28 0 1 1 1 := by
  rcases h with rfl | rfl
  · exact Or.inl slZ_val
  · exact Or.inr slZ_inv_val

theorem SpFPF_blk {x y : Sl28} (hx : x = slZ ∨ x = slZ⁻¹) (hy : y = slZ ∨ y = slZ⁻¹) :
    SpFPF (blk0 x * blk1 y) := by
  intro v hv
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blk x y v
  have f0 := congrFun hv (Sum.inl 0)
  have f1 := congrFun hv (Sum.inr 0)
  have f2 := congrFun hv (Sum.inl 1)
  have f3 := congrFun hv (Sum.inr 1)
  rw [e0] at f0
  rw [e1] at f1
  rw [e2] at f2
  rw [e3] at f3
  obtain ⟨a0, a1⟩ := fixed_zero (slZ_cases x hx) f0 f1
  obtain ⟨b0, b1⟩ := fixed_zero (slZ_cases y hy) f2 f3
  funext c
  rcases c with i | i <;> fin_cases i
  · exact a0
  · exact b0
  · exact a1
  · exact b1

theorem spZ1_fixes : mat 2 GF8 spZ1 *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → GF8) =
    Pi.single (Sum.inl 1) 1 := by
  show mat 2 GF8 (blk0 slZ) *ᵥ _ = _
  rw [mat_longBlock]
  funext c
  rcases c with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, blockMat, Pi.single_apply]

theorem not_SpFPF_spZ1 : ¬ SpFPF spZ1 := by
  intro h
  have := congrFun (h _ spZ1_fixes) (Sum.inl 1)
  simp at this

theorem conj_blk (u v x y : Sl28) :
    (blk0 u * blk1 v) * (blk0 x * blk1 y) * (blk0 u * blk1 v)⁻¹ =
      blk0 (u * x * u⁻¹) * blk1 (v * y * v⁻¹) := by
  rw [blk_inv, blk_mul, blk_mul]

theorem conj_swp_blk (x y : Sl28) :
    swp * (blk0 x * blk1 y) * swp⁻¹ = blk0 y * blk1 x := by
  rw [swp_blk, swp_inv, mul_assoc, swp_sq, mul_one]

theorem wrp_le_normalizer : wrp slD ≤ Subgroup.normalizer (spT0 : Set Sp8) := by
  have hD : ∀ u ∈ slD, ∀ x ∈ slT, u * x * u⁻¹ ∈ slT := fun u hu x hx =>
    (Subgroup.mem_normalizer_iff.1 hu x).1 hx
  rintro g ⟨u, hu, v, hv, rfl | rfl⟩
  · apply Subgroup.mem_normalizer_fintype
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff t).1 ht
    rw [SetLike.mem_coe, conj_blk]
    exact (mem_spT0_iff _).2 ⟨_, hD u hu x hx, _, hD v hv y hy, rfl⟩
  · apply Subgroup.mem_normalizer_fintype
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff t).1 ht
    rw [SetLike.mem_coe]
    have : blk0 u * blk1 v * swp * (blk0 x * blk1 y) * (blk0 u * blk1 v * swp)⁻¹ =
        (blk0 u * blk1 v) * (swp * (blk0 x * blk1 y) * swp⁻¹) * (blk0 u * blk1 v)⁻¹ := by
      rw [mul_inv_rev]; group
    rw [this, conj_swp_blk, conj_blk]
    exact (mem_spT0_iff _).2 ⟨_, hD u hu y hy, _, hD v hv x hx, rfl⟩

theorem slT_cube_aux : ∀ k : Fin 9, (slA ^ (k : ℕ)) ^ 3 = 1 →
    slA ^ (k : ℕ) = 1 ∨ slA ^ (k : ℕ) = slZ ∨ slA ^ (k : ℕ) = slZ⁻¹ := by decide +kernel

theorem slT_cube {x : Sl28} (hx : x ∈ slT) (h : x ^ 3 = 1) : x = 1 ∨ x = slZ ∨ x = slZ⁻¹ := by
  obtain ⟨k, rfl⟩ := (mem_slT_iff x).1 hx
  exact slT_cube_aux k h

theorem spT0_cube {g : Sp8} (hg : g ∈ spT0) (h3 : g ^ 3 = 1) :
    ∃ x y : Sl28, (x = 1 ∨ x = slZ ∨ x = slZ⁻¹) ∧ (y = 1 ∨ y = slZ ∨ y = slZ⁻¹) ∧
      g = blk0 x * blk1 y := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff g).1 hg
  have h : blkHom (x ^ 3, y ^ 3) = blkHom 1 := by
    rw [map_one]
    calc blkHom (x ^ 3, y ^ 3) = blkHom ((x, y) ^ 3) := by rw [Prod.pow_mk]
      _ = blkHom (x, y) ^ 3 := map_pow _ _ _
      _ = 1 := h3
  have h' := blkHom_injective h
  exact ⟨x, y, slT_cube hx (congrArg Prod.fst h'), slT_cube hy (congrArg Prod.snd h'), rfl⟩

theorem spZ1_eq : spZ1 = blk0 slZ * blk1 1 := by simp [spZ1]

theorem spE_cases {e : Sp8} (he : e ∈ spT0) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    (∃ n ∈ wrp slD, e = n * spZ1 * n⁻¹) ∨ (∃ n ∈ wrp slD, e = n * spZ12 * n⁻¹) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := spT0_cube he he3
  have hw : slW ∈ slD := slW_mem_slD
  have h1 : (1 : Sl28) ∈ slD := slD.one_mem
  have hwz : slW * slZ * slW⁻¹ = slZ⁻¹ := slW_conj_z
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd (by simp) he1
  · left
    refine ⟨swp, swp_mem_wrp slD, ?_⟩
    rw [spZ1, swp_conj_blk0]; simp
  · left
    refine ⟨blk0 1 * blk1 slW * swp, ⟨1, h1, slW, hw, Or.inr rfl⟩, ?_⟩
    have : blk0 1 * blk1 slW * swp * spZ1 * (blk0 1 * blk1 slW * swp)⁻¹ =
        (blk0 1 * blk1 slW) * (swp * (blk0 slZ * blk1 1) * swp⁻¹) * (blk0 1 * blk1 slW)⁻¹ := by
      rw [spZ1_eq, mul_inv_rev]; group
    rw [this, conj_swp_blk, conj_blk, hwz]; simp
  · left
    exact ⟨1, (wrp slD).one_mem, by simp [spZ1]⟩
  · right
    exact ⟨1, (wrp slD).one_mem, by simp [spZ12]⟩
  · right
    refine ⟨blk0 1 * blk1 slW, blk_mem_wrp h1 hw, ?_⟩
    rw [spZ12, conj_blk, hwz]; simp
  · left
    refine ⟨blk0 slW * blk1 1, blk_mem_wrp hw h1, ?_⟩
    rw [spZ1_eq, conj_blk, hwz]; simp
  · right
    refine ⟨blk0 slW * blk1 1, blk_mem_wrp hw h1, ?_⟩
    rw [spZ12, conj_blk, hwz]; simp
  · right
    refine ⟨blk0 slW * blk1 slW, blk_mem_wrp hw hw, ?_⟩
    rw [spZ12, conj_blk, hwz]

theorem slZ_mem_slT : slZ ∈ slT := Subgroup.pow_mem _ (Subgroup.mem_zpowers slA) 3

theorem spZ1_mem : spZ1 ∈ spT0 := (mem_spT0_iff _).2 ⟨slZ, slZ_mem_slT, 1, slT.one_mem, spZ1_eq⟩

theorem spZ1_pow3 : spZ1 ^ 3 = 1 := by rw [spZ1, ← map_pow, slZ_pow3, map_one]

theorem spZ1_ne_one : spZ1 ≠ 1 := by
  intro h
  have : blk0 slZ = blk0 1 := by rw [map_one]; exact h
  exact slZ_ne_one ((longBlock_injective (K := GF8) (n := 2) 0) this)

theorem SpFPF_spZ12 : SpFPF spZ12 := SpFPF_blk (Or.inl rfl) (Or.inl rfl)

theorem normalizer_le_wrp : Subgroup.normalizer (spT0 : Set Sp8) ≤ wrp slD := by
  intro g hg
  have hu : g * spZ1 * g⁻¹ ∈ spT0 := (Subgroup.mem_normalizer_iff.1 hg spZ1).1 spZ1_mem
  have hu3 : (g * spZ1 * g⁻¹) ^ 3 = 1 := by
    have := conj_pow (a := g) (b := spZ1) (i := 3)
    rw [this, spZ1_pow3]; group
  have hu1 : g * spZ1 * g⁻¹ ≠ 1 := by
    intro h
    apply spZ1_ne_one
    calc spZ1 = g⁻¹ * (g * spZ1 * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hnf : ¬ SpFPF (g * spZ1 * g⁻¹) := fun h => not_SpFPF_spZ1 ((SpFPF_conj g spZ1).1 h)
  obtain ⟨n, hn, hun⟩ : ∃ n ∈ wrp slD, g * spZ1 * g⁻¹ = n * spZ1 * n⁻¹ := by
    rcases spE_cases hu hu3 hu1 with h | ⟨n, hn, h⟩
    · exact h
    · exfalso
      apply hnf
      rw [h]
      exact (SpFPF_conj n spZ12).2 SpFPF_spZ12
  have hc : (n⁻¹ * g) * blk0 slZ = blk0 slZ * (n⁻¹ * g) := by
    show (n⁻¹ * g) * spZ1 = spZ1 * (n⁻¹ * g)
    have : n⁻¹ * (g * spZ1 * g⁻¹) * n = spZ1 := by rw [hun]; group
    calc (n⁻¹ * g) * spZ1 = (n⁻¹ * (g * spZ1 * g⁻¹) * n) * (n⁻¹ * g) := by group
      _ = spZ1 * (n⁻¹ * g) := by rw [this]
  obtain ⟨x, y, hx, hcxy⟩ := block_of_comm hc
  have hcn : n⁻¹ * g ∈ Subgroup.normalizer (spT0 : Set Sp8) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (wrp_le_normalizer hn)) hg
  have hyD : y ∈ slD := by
    have hta : blk0 1 * blk1 slA ∈ spT0 :=
      (mem_spT0_iff _).2 ⟨1, slT.one_mem, slA, Subgroup.mem_zpowers slA, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hcn _).1 hta
    rw [hcxy, conj_blk] at h1
    obtain ⟨x', hx', y', hy', hxy⟩ := (mem_spT0_iff _).1 h1
    obtain ⟨-, hyy⟩ := blk_inj hxy
    have hyT : y * slA * y⁻¹ ∈ slT := hyy ▸ hy'
    have hz : (y⁻¹)⁻¹ * slZ * y⁻¹ ∈ slT := by
      have := conj_pow (a := y) (b := slA) (i := 3)
      rw [inv_inv, slZ, ← this]
      exact slT.pow_mem hyT 3
    have := (mem_slD_iff y⁻¹).2 (slInD_of_conj_z hz)
    simpa using slD.inv_mem this
  have hcw : n⁻¹ * g ∈ wrp slD := by
    rw [hcxy]
    exact blk_mem_wrp (slT_le_slD hx) hyD
  have : g = n * (n⁻¹ * g) := by group
  rw [this]
  exact (wrp slD).mul_mem hn hcw

theorem wrp_eq_normalizer : wrp slD = Subgroup.normalizer (spT0 : Set Sp8) :=
  le_antisymm wrp_le_normalizer normalizer_le_wrp

theorem card_wrp_slD : Nat.card (wrp slD) = 648 := by rw [card_wrp, card_slD]; norm_num

theorem card_wrp_top : Nat.card (wrp (⊤ : Subgroup Sl28)) = 508032 := by
  rw [card_wrp, Subgroup.card_top, card_sl28]; norm_num

theorem cent_le_wrp {g : Sp8} (h : g * spZ1 = spZ1 * g) : g ∈ wrp (⊤ : Subgroup Sl28) := by
  obtain ⟨x, y, -, rfl⟩ := block_of_comm h
  exact blk_mem_wrp (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem blk0_mem_of_T {H : Subgroup Sp8} (hH : wrp slD ≤ H) {x : Sl28} (hx : x ∈ slT) :
    blk0 x ∈ H := hH (by simpa using blk_mem_wrp (slT_le_slD hx) slD.one_mem)

theorem gen_wrp {H : Subgroup Sp8} (hH : wrp slD ≤ H)
    (hC : ∀ g : Sp8, g * spZ1 = spZ1 * g → g ∈ H) :
    wrp (⊤ : Subgroup Sl28) ≤ H := by
  have hswp : swp ∈ H := hH (swp_mem_wrp slD)
  have h1 : ∀ y : Sl28, blk1 y ∈ H := fun y => hC _ (by
    show blk1 y * blk0 slZ = blk0 slZ * blk1 y
    exact (blk_commute slZ y).symm.eq)
  have h0 : ∀ x : Sl28, blk0 x ∈ H := fun x => by
    have : blk0 x = swp * blk1 x * swp⁻¹ := (swp_conj_blk1 x).symm
    rw [this]
    exact H.mul_mem (H.mul_mem hswp (h1 x)) (H.inv_mem hswp)
  rintro g ⟨x, -, y, -, rfl | rfl⟩
  · exact H.mul_mem (h0 x) (h1 y)
  · exact H.mul_mem (H.mul_mem (h0 x) (h1 y)) hswp

theorem dich_spZ1 (H : Subgroup Sp8) (hH : wrp slD ≤ H) :
    (∀ g ∈ H, g * spZ1 = spZ1 * g → g ∈ wrp slD) ∨ (∀ g : Sp8, g * spZ1 = spZ1 * g → g ∈ H) := by
  let X : Subgroup Sl28 := H.comap blk1
  have hDX : slD ≤ X := fun y hy => hH (by simpa using blk_mem_wrp slD.one_mem hy)
  rcases maximal_slD X hDX with hX | hX
  · left
    intro g hg hgc
    obtain ⟨x, y, hx, rfl⟩ := block_of_comm hgc
    have h1 : blk1 y ∈ H := by
      have : blk1 y = (blk0 x)⁻¹ * (blk0 x * blk1 y) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem (blk0_mem_of_T hH hx)) hg
    have hyD : y ∈ slD := by
      have : y ∈ X := h1
      rwa [hX] at this
    exact blk_mem_wrp (slT_le_slD hx) hyD
  · right
    intro g hgc
    obtain ⟨x, y, hx, rfl⟩ := block_of_comm hgc
    have h2 : blk1 y ∈ H := by
      have : y ∈ X := by rw [hX]; exact Subgroup.mem_top y
      exact this
    exact H.mul_mem (blk0_mem_of_T hH hx) h2

@[expose] def spZ12c : Array ℕ := #[1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0]

theorem mat_spZ12 : mat 2 GF8 spZ12 = decode spZ12c := by
  rw [spZ12, map_mul, mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, decode, spZ12c, ix,
      slZ_val, mk28, gf8_ofNat_zero, gf8_ofNat_one]

@[expose] def spWitC : Array ℕ := #[2, 3, 2, 3, 3, 2, 3, 2, 2, 3, 0, 0, 3, 2, 0, 0]

theorem sympl_spWit : (decode spWitC)ᵀ * gram GF8 2 * decode spWitC = gram GF8 2 := by
  decide +kernel

@[expose] noncomputable def spWit : Sp8 := spOf spWitC sympl_spWit

theorem spWit_comm : spWit * spZ12 = spZ12 * spWit := by
  apply mat_injective
  rw [map_mul, map_mul, mat_spZ12]
  show decode spWitC * _ = _ * decode spWitC
  decide +kernel

theorem wrp_top_entries {g : Sp8} (hg : g ∈ wrp (⊤ : Subgroup Sl28)) :
    (mat 2 GF8 g (Sum.inl 0) (Sum.inl 1) = 0 ∧ mat 2 GF8 g (Sum.inl 0) (Sum.inr 1) = 0) ∨
    (mat 2 GF8 g (Sum.inl 0) (Sum.inl 0) = 0 ∧ mat 2 GF8 g (Sum.inl 0) (Sum.inr 0) = 0) := by
  obtain ⟨x, -, y, -, rfl | rfl⟩ := hg
  · left
    rw [map_mul, mat_longBlock, mat_longBlock]
    constructor <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat]
  · right
    rw [map_mul, map_mul, mat_longBlock, mat_longBlock, swp_mat]
    constructor <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, decode, sc, ix,
        gf8_ofNat_zero, gf8_ofNat_one]

theorem spWit_not_mem : spWit ∉ wrp (⊤ : Subgroup Sl28) := by
  intro h
  have := wrp_top_entries h
  have e : mat 2 GF8 spWit = decode spWitC := rfl
  rw [e] at this
  revert this
  decide +kernel

end CFSG.AGLEmbedding.KFactProofs.Sp48
