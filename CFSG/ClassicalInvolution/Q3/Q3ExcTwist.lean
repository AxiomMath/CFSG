module

public import CFSG.ClassicalInvolution.Q3.Q3ExcDatum

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.LieType.AlgebraicGroups
open scoped Pointwise MatrixGroups

section Conj

variable {B : Type} [Group B]

theorem exc3Big_map_conj {A : Subgroup B} (u : B) (h : Exc3Big A) :
    Exc3Big (A.map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨hq, h2⟩ := h
  let e : A ≃* A.map (MulAut.conj u).toMonoidHom :=
    A.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ hzc
  obtain ⟨m, hm⟩ := h2 z hz (fun g hg => by
    have := hzc ((MulAut.conj u).toMonoidHom g) ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this ⊢
    have h3 : u * (g * z) * u⁻¹ = u * (z * g) * u⁻¹ := by
      calc u * (g * z) * u⁻¹ = (u * g * u⁻¹) * (u * z * u⁻¹) := by group
        _ = (u * z * u⁻¹) * (u * g * u⁻¹) := this
        _ = u * (z * g) * u⁻¹ := by group
    simpa using h3)
  refine ⟨m, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_pow, hm]
  group

theorem exc3Small_map_conj {A : Subgroup B} (u : B) (h : Exc3Small A) :
    Exc3Small (A.map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (A.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective)⟩

end Conj

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exc3_orbitGroup_le_fixedGroup :
    D.orbitGroup ≤ D.fixedGroup.map (adjointGroup τ k).subtype := by
  intro z hz
  have hzG : z ∈ adjointGroup τ k := D.orbitGroup_le_adjointGroup hz
  exact ⟨⟨z, hzG⟩, D.orbitGroupC_le_fixedGroup (Subgroup.mem_subgroupOf.2 hz), rfl⟩

theorem exc3_conj_orbitGroup {s c' : ModGL τ k}
    (hs : s ∈ D.fixedGroup.map (adjointGroup τ k).subtype) (hc : c' ∈ D.orbitGroup) :
    s * c' * s⁻¹ ∈ D.orbitGroup := by
  obtain ⟨s', hs', rfl⟩ := hs
  have hcG : c' ∈ adjointGroup τ k := D.orbitGroup_le_adjointGroup hc
  have hcC : (⟨c', hcG⟩ : adjointGroup τ k) ∈ D.orbitGroupC := Subgroup.mem_subgroupOf.2 hc
  have h := D.orbitGroupC_normal.conj_mem ⟨⟨c', hcG⟩, D.orbitGroupC_le_fixedGroup hcC⟩
    (Subgroup.mem_subgroupOf.2 hcC) ⟨s', hs'⟩
  have h2 := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 h)
  simpa using h2

variable [Subsingleton (KernelComponent D.χ)]

theorem exc3_fixedGroup_le_totalFixedGroup :
    D.fixedGroup.map (adjointGroup τ k).subtype ≤
      D.totalFixedGroup.map (adjointGroup τ k).subtype :=
  Subgroup.map_mono (by
    rw [← exc3_kernelFixedGroup_eq_fixedGroup (D := D)]
    exact D.kernelFixedGroup_le_totalFixedGroup)

theorem exc3_conj_fixedGroup {v s : ModGL τ k}
    (hv : v ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype)
    (hs : s ∈ D.fixedGroup.map (adjointGroup τ k).subtype) :
    v * s * v⁻¹ ∈ D.fixedGroup.map (adjointGroup τ k).subtype := by
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨s', hs', rfl⟩ := hs
  rw [← exc3_kernelFixedGroup_eq_fixedGroup (D := D)] at hs'
  have h := D.conj_mem_kernelFixedGroup hv' hs'
  rw [exc3_kernelFixedGroup_eq_fixedGroup (D := D)] at h
  exact ⟨_, h, by simp⟩

end Datum

section Structure

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_twisted_structure {c : ModGL τ k} (hc : Exc3Frob D c)
    [Subsingleton (KernelComponent D.χ)] (hq3 : p₀ ^ D.e = 3)
    (hQS : CFSG.IsQuasisimple D.orbitGroup) {Xh X₀ : Subgroup (ModGL τ k)} (u : ModGL τ k)
    (hX : D.totalFixedGroup.map (adjointGroup τ k).subtype = Xh)
    (hconj : Xh.map (MulAut.conj u).toMonoidHom = X₀) {Y : Subgroup (ModGL τ k)} [Finite Y]
    (hCY : D.orbitGroup.map (MulAut.conj u).toMonoidHom ≤ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 ∈ X₀) (hYn : ∀ y ∈ Y, ∀ v ∈ X₀, y * v * y⁻¹ ∈ X₀) :
    (∀ N : Subgroup (ModGL τ k), N ≤ Y → (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
        Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL τ k), L ≤ Y → Nonempty (SL(2, ZMod 3) ≃* L) →
        IsSubnormal L Y → False) := by
  classical
  have hBig : Exc3Big D.orbitGroup := hc.exc3Big_orbitGroup hq3 hQS
  set C₀ := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC₀
  have hBig₀ : Exc3Big C₀ := exc3Big_map_conj u hBig
  have hmapmem : ∀ w ∈ D.orbitGroup, u * w * u⁻¹ ∈ C₀ := fun w hw =>
    Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  have hexp : ∀ g ∈ Y, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ _ : Unit, C₀ := by
    intro g hg
    have h1 : g ^ 2 ∈ Xh.map (MulAut.conj u).toMonoidHom := by
      rw [hconj]
      exact hY2 g hg
    obtain ⟨v, hv, hvg⟩ := h1
    rw [← hX] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hmem := hc.pow_pow_mem_orbitGroupC hx
    rw [hq3] at hmem
    have hmem' := Subgroup.mem_subgroupOf.1 hmem
    refine ⟨7, ?_⟩
    rw [iSup_const]
    have hg2 : g ^ 2 = u * (x : ModGL τ k) * u⁻¹ := by
      rw [← hvg]
      rfl
    have e : g ^ (2 ^ 7) = u * (((x : ModGL τ k) ^ (3 ^ 2 - 1)) ^ (3 ^ 2 - 1)) * u⁻¹ := by
      rw [show g ^ (2 ^ 7) = ((g ^ 2) ^ (3 ^ 2 - 1)) ^ (3 ^ 2 - 1) by
        rw [← pow_mul, ← pow_mul]; norm_num, hg2, conj_pow, conj_pow]
    rw [e]
    exact hmapmem _ (by simpa using hmem')
  set Γ₀ := (D.fixedGroup.map (adjointGroup τ k).subtype).map (MulAut.conj u).toMonoidHom
    with hΓ₀
  have hconjC : ∀ g ∈ Γ₀, ∀ n ∈ C₀, g * n * g⁻¹ ∈ C₀ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨c', hc', rfl⟩
    have h := exc3_conj_orbitGroup D hs hc'
    have e : (MulAut.conj u).toMonoidHom s * (MulAut.conj u).toMonoidHom c' *
        ((MulAut.conj u).toMonoidHom s)⁻¹ = (MulAut.conj u).toMonoidHom (s * c' * s⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem _ h
  have hΓX : Γ₀ ≤ X₀ := by
    rw [← hconj]
    refine Subgroup.map_mono ?_
    rw [← hX]
    exact exc3_fixedGroup_le_totalFixedGroup D
  have hXΓ : ∀ a ∈ X₀, ∀ r ∈ Γ₀, a * r * a⁻¹ ∈ Γ₀ := by
    intro a ha
    rw [← hconj] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    rw [← hX] at hv
    rintro _ ⟨s, hs, rfl⟩
    have h := exc3_conj_fixedGroup D hv hs
    have e : (MulAut.conj u).toMonoidHom v * (MulAut.conj u).toMonoidHom s *
        ((MulAut.conj u).toMonoidHom v)⁻¹ = (MulAut.conj u).toMonoidHom (v * s * v⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem _ h
  have hC₀Γ : C₀ ≤ Γ₀ := Subgroup.map_mono (exc3_orbitGroup_le_fixedGroup D)
  have hsub : IsSubnormal C₀ Y := by
    have h1 : IsSubnormal C₀ (Γ₀ ⊓ Y) := by
      refine isSubnormal_of_normal_subgroupOf (le_inf hC₀Γ hCY) ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hconjC _ g.2.1 _ hn
    have h2 : IsSubnormal (Γ₀ ⊓ Y) (X₀ ⊓ Y) := by
      refine isSubnormal_of_normal_subgroupOf (inf_le_inf_right _ hΓX) ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hXΓ _ g.2.1 _ hn.1, Y.mul_mem (Y.mul_mem g.2.2 hn.2) (Y.inv_mem g.2.2)⟩
    have h3 : IsSubnormal (X₀ ⊓ Y) Y := by
      refine isSubnormal_of_normal_subgroupOf inf_le_right ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hYn _ g.2 _ hn.1, Y.mul_mem (Y.mul_mem g.2 hn.2) (Y.inv_mem g.2)⟩
    exact isSubnormal_trans h1 (isSubnormal_trans h2 h3)
  have hcomm : ∀ i j : Unit, i ≠ j → ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a :=
    fun i j hij => absurd (Subsingleton.elim i j) hij
  have hCY' : ∀ i : Unit, C₀ ≤ Y := fun _ => hCY
  have hC : ∀ i : Unit, Exc3Big C₀ ∨ Exc3Small C₀ := fun _ => Or.inl hBig₀
  refine ⟨fun N hNY hNn hodd => ?_, fun L hLY ⟨eL⟩ hL => ?_⟩
  · exact exc3_oddNormal_eq_bot_of_comp_amb (fun _ : Unit => C₀) hCY' hcomm hC hexp hNY hNn hodd
  · obtain ⟨i, hi, hLi⟩ := exc3_member_eq_small_amb (fun _ : Unit => C₀) hCY' hcomm hC
      (fun _ _ => hsub) hexp (fun i j _ _ => Subsingleton.elim i j) hLY eL hL
    obtain ⟨e⟩ := hi
    exact false_of_isQuasisimple_of_isSolvable (ModelFacts.open_isQuasisimple hBig₀.1)
      (CFSG.LieType.HighestRoot.isSolvable_of_mulEquiv (Nat.card_zmod 3)
        (e.symm : _ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))

end Structure

end CFSG.ClassicalInvolution.Q3
