module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksModel
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

private def shiftB (p : ℕ) : Equiv.Perm (Fin p × ZMod p) :=
  Equiv.prodCongr (finRotate p) (Equiv.refl _)

private theorem shiftB_apply (p : ℕ) (j : Fin p) (x : ZMod p) :
    shiftB p (j, x) = (finRotate p j, x) :=
  rfl

private theorem shiftB_inv_apply (p : ℕ) (j : Fin p) (x : ZMod p) :
    (shiftB p)⁻¹ (j, x) = ((finRotate p).symm j, x) :=
  rfl

private theorem finRotate_pow_eq_one {p : ℕ} (hp : 2 ≤ p) : finRotate p ^ p = 1 := by
  have h := (isCycle_finRotate_of_le hp).orderOf
  rw [support_finRotate_of_le hp, Finset.card_univ, Fintype.card_fin] at h
  have h' := pow_orderOf_eq_one (finRotate p)
  rwa [h] at h'

private theorem shiftB_pow_eq_one {p : ℕ} (hp : 2 ≤ p) : shiftB p ^ p = 1 := by
  have key : ∀ k : ℕ, ∀ (j : Fin p) (x : ZMod p),
      (shiftB p ^ k) (j, x) = ((finRotate p ^ k) j, x) := by
    intro k
    induction k with
    | zero => intro j x; simp
    | succ k ih =>
      intro j x
      rw [pow_succ (shiftB p) k, Equiv.Perm.mul_apply, shiftB_apply, ih,
        pow_succ (finRotate p) k, Equiv.Perm.mul_apply]
  refine Equiv.ext ?_
  rintro ⟨j, x⟩
  simp [key, finRotate_pow_eq_one hp]

private theorem shiftB_conj_transl (p : ℕ) (f : Fin p → ZMod p) :
    shiftB p * transl f * (shiftB p)⁻¹ = transl (f ∘ (finRotate p).symm) := by
  refine Equiv.ext ?_
  rintro ⟨j, x⟩
  simp only [Equiv.Perm.mul_apply, shiftB_inv_apply, transl_apply, shiftB_apply,
    Equiv.apply_symm_apply, Function.comp_apply]

private theorem shiftB_inv_conj_transl (p : ℕ) (f : Fin p → ZMod p) :
    (shiftB p)⁻¹ * transl f * shiftB p = transl (f ∘ finRotate p) := by
  refine Equiv.ext ?_
  rintro ⟨j, x⟩
  simp only [Equiv.Perm.mul_apply, shiftB_inv_apply, transl_apply, shiftB_apply,
    Equiv.symm_apply_apply, Function.comp_apply]

private abbrev bShift (p m : ℕ) : Equiv.Perm (Ω p p m) := blockPerm (shiftB p)

private theorem bShift_inl {p m : ℕ} (j : Fin p) (x : ZMod p) :
    bShift p m (Sum.inl (j, x)) = Sum.inl (finRotate p j, x) :=
  rfl

private theorem bShift_pow_eq_one {p m : ℕ} (hp : 2 ≤ p) : bShift p m ^ p = 1 := by
  have h : blockPermHom (m := m) (shiftB p) ^ p = 1 := by
    rw [← map_pow, shiftB_pow_eq_one hp, map_one]
  exact h

private theorem bShift_conj_transl {p m : ℕ} (f : Fin p → ZMod p) :
    bShift p m * blockPerm (transl f) * (bShift p m)⁻¹ =
      blockPerm (m := m) (transl (f ∘ (finRotate p).symm)) := by
  have h : blockPermHom (m := m) (shiftB p * transl f * (shiftB p)⁻¹) =
      blockPermHom (m := m) (transl (f ∘ (finRotate p).symm)) := by
    rw [shiftB_conj_transl]
  simpa only [bShift, map_mul, map_inv, blockPermHom_apply] using h

private theorem bShift_inv_conj_transl {p m : ℕ} (f : Fin p → ZMod p) :
    (bShift p m)⁻¹ * blockPerm (transl f) * bShift p m =
      blockPerm (m := m) (transl (f ∘ finRotate p)) := by
  have h : blockPermHom (m := m) ((shiftB p)⁻¹ * transl f * shiftB p) =
      blockPermHom (m := m) (transl (f ∘ finRotate p)) := by
    rw [shiftB_inv_conj_transl]
  simpa only [bShift, map_mul, map_inv, blockPermHom_apply] using h

private theorem blockPerm_transl_mem_base {p m : ℕ} (f : Fin p → ZMod p) :
    blockPerm (m := m) (transl f) ∈ base (k := p) (p := p) (m := m) :=
  MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd f, rfl⟩

private theorem bShift_conj_mem_base {p m : ℕ} (f : Fin p → ZMod p) :
    bShift p m * blockPerm (transl f) * (bShift p m)⁻¹ ∈ base (k := p) (p := p) (m := m) := by
  rw [bShift_conj_transl]
  exact blockPerm_transl_mem_base _

private theorem bShift_inv_conj_mem_base {p m : ℕ} (f : Fin p → ZMod p) :
    (bShift p m)⁻¹ * blockPerm (transl f) * bShift p m ∈ base (k := p) (p := p) (m := m) := by
  rw [bShift_inv_conj_transl]
  exact blockPerm_transl_mem_base _

private theorem bShift_mem_normalizer {p m : ℕ} :
    bShift p m ∈
      Subgroup.normalizer (base (k := p) (p := p) (m := m) : Set (Equiv.Perm (Ω p p m))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hh
    rw [← hg, baseHom_apply]
    exact bShift_conj_mem_base _
  · intro hh
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hh
    have h2 : h = (bShift p m)⁻¹ * baseHom g * bShift p m := by
      rw [hg]
      group
    rw [h2, baseHom_apply]
    exact bShift_inv_conj_mem_base _

private theorem baseHom_pow_eq_one {k p m : ℕ} (f : Multiplicative (Fin k → ZMod p)) :
    baseHom (k := k) (p := p) (m := m) f ^ p = 1 := by
  rw [← map_pow]
  have h : f ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp
  rw [h, map_one]

private theorem isPGroup_base {k p m : ℕ} :
    IsPGroup p (base (k := k) (p := p) (m := m)) := by
  intro g
  obtain ⟨f, hf⟩ := MonoidHom.mem_range.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hf, baseHom_pow_eq_one]

private theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {p : ℕ} {x : G}
    (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private abbrev cShift (p m : ℕ) [NeZero p] : Equiv.Perm (Ω p p m) :=
  blockPerm (transl (Pi.single (0 : Fin p) (1 : ZMod p) : Fin p → ZMod p))

private theorem cShift_inl {p m : ℕ} [NeZero p] (j : Fin p) (x : ZMod p) :
    cShift p m (Sum.inl (j, x)) =
      Sum.inl (j, x + (Pi.single (0 : Fin p) (1 : ZMod p) : Fin p → ZMod p) j) :=
  rfl

private theorem cShift_mem_base {p m : ℕ} [NeZero p] :
    cShift p m ∈ base (k := p) (p := p) (m := m) :=
  blockPerm_transl_mem_base _

private theorem cShift_pow_eq_one {p m : ℕ} [NeZero p] : cShift p m ^ p = 1 := by
  have h := baseHom_pow_eq_one (k := p) (p := p) (m := m)
    (Multiplicative.ofAdd (Pi.single (0 : Fin p) (1 : ZMod p) : Fin p → ZMod p))
  exact h

private theorem sign_eq_one_of_pow_eq_one {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hodd : Odd p) {σ : Equiv.Perm α} (h : σ ^ p = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, Odd.neg_one_pow hodd] at h1
    exact absurd h1 (by decide)

private theorem cShift_mem_alt {p m : ℕ} [NeZero p] (hodd : Odd p) :
    cShift p m ∈ alternatingGroup (Ω p p m) :=
  Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow_eq_one hodd cShift_pow_eq_one)

private theorem bShift_mem_alt {p m : ℕ} [NeZero p] (hp : p.Prime) (hodd : Odd p) :
    bShift p m ∈ alternatingGroup (Ω p p m) :=
  Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow_eq_one hodd (bShift_pow_eq_one hp.two_le))

private theorem altBlocks_finRotate_zero {p : ℕ} [NeZero p] : finRotate p 0 = 1 := by
  rw [finRotate_apply, zero_add]

private theorem one_ne_zero_fin {p : ℕ} [NeZero p] (hp : p.Prime) : (1 : Fin p) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt hp.one_lt] at h'
  exact absurd h' one_ne_zero

private theorem cShift_mul_bShift_ne {p m : ℕ} [NeZero p] (hp : p.Prime) :
    cShift p m * bShift p m ≠ bShift p m * cShift p m := by
  intro h
  have hL : cShift p m (bShift p m (Sum.inl (0, 0))) = Sum.inl (1, 0) := by
    rw [bShift_inl, altBlocks_finRotate_zero, cShift_inl,
      Pi.single_eq_of_ne (one_ne_zero_fin hp), add_zero]
  have hR : bShift p m (cShift p m (Sum.inl (0, 0))) = Sum.inl (1, 1) := by
    rw [cShift_inl, Pi.single_eq_same, zero_add, bShift_inl, altBlocks_finRotate_zero]
  have h1 := congrArg
    (fun π : Equiv.Perm (Ω p p m) => π (Sum.inl ((0 : Fin p), (0 : ZMod p)))) h
  simp only [Equiv.Perm.mul_apply] at h1
  rw [hL, hR] at h1
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  exact zero_ne_one (Prod.mk.inj (Sum.inl_injective h1)).2

private theorem exists_noncomm_pGroup_block {p m : ℕ} [NeZero p] (hp : p.Prime) (hodd : Odd p) :
    ∃ a b : ↥(alternatingGroup (Ω p p m)), ∃ H : Subgroup ↥(alternatingGroup (Ω p p m)),
      IsPGroup p H ∧ a ∈ H ∧ b ∈ H ∧ a * b ≠ b * a := by
  have hN : IsPGroup p (base (k := p) (p := p) (m := m)) := isPGroup_base
  have hbN : Subgroup.zpowers (bShift p m) ≤
      Subgroup.normalizer (base (k := p) (p := p) (m := m) : Set (Equiv.Perm (Ω p p m))) :=
    Subgroup.zpowers_le.2 bShift_mem_normalizer
  have hH : IsPGroup p (base (k := p) (p := p) (m := m) ⊔ Subgroup.zpowers (bShift p m) :
      Subgroup (Equiv.Perm (Ω p p m))) :=
    IsPGroup.to_sup_of_normal_left' hN (isPGroup_zpowers_of_pow (bShift_pow_eq_one hp.two_le)) hbN
  refine ⟨⟨cShift p m, cShift_mem_alt hodd⟩, ⟨bShift p m, bShift_mem_alt hp hodd⟩,
    ((base (k := p) (p := p) (m := m) ⊔ Subgroup.zpowers (bShift p m) :
      Subgroup (Equiv.Perm (Ω p p m)))).comap (alternatingGroup (Ω p p m)).subtype,
    hH.comap_subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_left cShift_mem_base
  · rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · intro h
    apply cShift_mul_bShift_ne hp
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h

private theorem exists_noncomm_pGroup_of_equiv {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) {p : ℕ}
    (h : ∃ a b : ↥(alternatingGroup α), ∃ H : Subgroup ↥(alternatingGroup α),
      IsPGroup p H ∧ a ∈ H ∧ b ∈ H ∧ a * b ≠ b * a) :
    ∃ a b : ↥(alternatingGroup β), ∃ H : Subgroup ↥(alternatingGroup β),
      IsPGroup p H ∧ a ∈ H ∧ b ∈ H ∧ a * b ≠ b * a := by
  obtain ⟨a, b, H, hH, ha, hb, hab⟩ := h
  refine ⟨e.altCongrHom a, e.altCongrHom b, H.map e.altCongrHom.toMonoidHom, hH.map _,
    Subgroup.mem_map_of_mem _ ha, Subgroup.mem_map_of_mem _ hb, ?_⟩
  intro h'
  apply hab
  apply e.altCongrHom.injective
  rw [map_mul, map_mul]
  exact h'

private theorem exists_noncomm_pGroup {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : p ^ 2 ≤ n) :
    ∃ a b : ↥(alternatingGroup (Fin n)), ∃ H : Subgroup ↥(alternatingGroup (Fin n)),
      IsPGroup p H ∧ a ∈ H ∧ b ∈ H ∧ a * b ≠ b * a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (Ω p p (n - p ^ 2)) = n := by
    simp only [Ω, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
    rw [← sq]
    exact Nat.add_sub_of_le hn
  exact exists_noncomm_pGroup_of_equiv (Fintype.equivFinOfCardEq hcard)
    (exists_noncomm_pGroup_block (m := n - p ^ 2) hp (hp.odd_of_ne_two hp2))

theorem not_isMulCommutative_sylow_alternatingGroup {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : p ^ 2 ≤ n) (P : Sylow p (alternatingGroup (Fin n))) :
    ¬ IsMulCommutative (P : Subgroup (alternatingGroup (Fin n))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, H, hH, ha, hb, hab⟩ := exists_noncomm_pGroup hp hp2 hn
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.not_isMulCommutative_of_noncomm_pSubgroup
    hH ha hb hab P.isPGroup' P.not_dvd_index

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
