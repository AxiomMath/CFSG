module

public import CFSG.ClassicalInvolution.Q3.Q3ExcClass

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.LieType.AlgebraicGroups
open scoped Pointwise MatrixGroups

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exc3_isSubnormal_orbitGroupC_totalFixedGroup (J' : Set.range D.classOrbit) :
    IsSubnormal (D.withOrbit J').orbitGroupC D.totalFixedGroup := by
  have h1 : (D.withOrbit J').orbitGroupC ≤ (D.withOrbit J').fixedGroup :=
    (D.withOrbit J').orbitGroupC_le_fixedGroup
  have h2 : (D.withOrbit J').fixedGroup ≤ D.orbitFixedJoin :=
    D.fixedGroup_withOrbit_le_orbitFixedJoin J'
  have h3 : D.orbitFixedJoin ≤ D.kernelFixedGroup := D.orbitFixedJoin_le_kernelFixedGroup
  have h4 : D.kernelFixedGroup ≤ D.totalFixedGroup := D.kernelFixedGroup_le_totalFixedGroup
  refine IsSubnormal.step h1 (D.withOrbit J').orbitGroupC_normal
    (IsSubnormal.step h2 ?_ (IsSubnormal.step h3 ?_ (IsSubnormal.step h4 ?_
      (IsSubnormal.refl _))))
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_fixedGroup_withOrbit (h3 g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_orbitFixedJoin g.2 (Subgroup.mem_subgroupOf.1 hn))⟩
  · exact ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_kernelFixedGroup g.2 (Subgroup.mem_subgroupOf.1 hn))⟩

theorem exc3_isSubnormal_orbitGroup_totalFixedGroup (J' : Set.range D.classOrbit) :
    IsSubnormal (D.withOrbit J').orbitGroup
      (D.totalFixedGroup.map (adjointGroup τ k).subtype) := by
  have h := CFSG.ComponentClassification.Components.chain_map (adjointGroup τ k).subtype
    (exc3_isSubnormal_orbitGroupC_totalFixedGroup D J')
  rwa [OrthogonalSemilinearFixedRootDatum.orbitGroupC,
    Subgroup.map_subgroupOf_eq_of_le (D.withOrbit J').orbitGroup_le_adjointGroup] at h

end Datum

section Structure

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_multi_structure {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    (hone : ∀ J₁ J₂ : Set.range D.classOrbit, Exc3Small (D.withOrbit J₁).orbitGroup →
      Exc3Small (D.withOrbit J₂).orbitGroup → J₁ = J₂)
    (hexpX : ∀ x ∈ D.totalFixedGroup, ∃ m : ℕ, (x : ModGL τ k) ^ (2 ^ m) ∈
      ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup)
    {Y : Subgroup (ModGL τ k)} [Finite Y]
    (hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype)
    (hYn : ∀ y ∈ Y, ∀ v ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype,
      y * v * y⁻¹ ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype) :
    (∀ N : Subgroup (ModGL τ k), N ≤ Y → (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
        Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL τ k), L ≤ Y → Nonempty (SL(2, ZMod 3) ≃* L) → IsSubnormal L Y →
        ∃ J' : Set.range D.classOrbit, Exc3Small (D.withOrbit J').orbitGroup ∧
          L = (D.withOrbit J').orbitGroup) := by
  classical
  have : Finite (Set.range D.classOrbit) := D.finite_orbitIndex
  set C : Set.range D.classOrbit → Subgroup (ModGL τ k) := fun J' => (D.withOrbit J').orbitGroup
    with hC_def
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hc.frob, hc.normalizes, hc.sq_mem⟩
  have hdich : ∀ J', Exc3Big (C J') ∨ Exc3Small (C J') := fun J' =>
    (exc3_orbitGroup_big_or_small (hcJ J') hq3).imp id And.left
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, a * b = b * a := fun i j hij a ha b hb =>
    (D.commute_of_ne hij ((D.withOrbit i).orbitGroup_le_rootSpanJ ha)
      ((D.withOrbit j).orbitGroup_le_rootSpanJ hb)).eq
  have hexp : ∀ g ∈ Y, ∃ m : ℕ, g ^ (2 ^ m) ∈ ⨆ i, C i := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := hY2 g hg
    obtain ⟨m, hm⟩ := hexpX x hx
    refine ⟨m + 1, ?_⟩
    have hxg' : (x : ModGL τ k) = g ^ 2 := hxg
    rw [pow_succ', pow_mul, ← hxg']
    exact hm
  have hsub : ∀ i, Exc3Big (C i) → IsSubnormal (C i) Y := by
    intro i _
    have h1 := isSubnormal_inf (exc3_isSubnormal_orbitGroup_totalFixedGroup D i) Y
    rw [inf_eq_left.2 (hCY i)] at h1
    refine isSubnormal_trans h1 (isSubnormal_of_normal_subgroupOf inf_le_right
      ⟨fun n hn g => ?_⟩)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hYn _ g.2 _ hn.1, Y.mul_mem (Y.mul_mem g.2 hn.2) (Y.inv_mem g.2)⟩
  refine ⟨fun N hNY hNn hodd => ?_, fun L hLY ⟨eL⟩ hL => ?_⟩
  · exact exc3_oddNormal_eq_bot_of_comp_amb C hCY hcomm hdich hexp hNY hNn hodd
  · exact exc3_member_eq_small_amb C hCY hcomm hdich hsub hexp hone hLY eL hL

end Structure

section TwoOrbit

variable {G : Type} [Group G]

theorem exc3_pow_mem_sup_of_two (F : G →* G) {H₀ H₁ : Subgroup G}
    (hcomm : ∀ a ∈ H₀, ∀ b ∈ H₁, a * b = b * a) (hF₀ : ∀ a ∈ H₀, F a ∈ H₀)
    (hF₁ : ∀ a ∈ H₁, F a ∈ H₁) (hΔ : ∀ z ∈ H₀ ⊓ H₁, z * z = 1) {r : G} (hr : r ∈ H₀ ⊔ H₁)
    (hFr : F r = r) :
    r * r ∈ (H₀ ⊓ F.eqLocus (MonoidHom.id G)) ⊔ (H₁ ⊓ F.eqLocus (MonoidHom.id G)) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 hr
  set z : G := F a * a⁻¹ with hz
  set z' : G := F b * b⁻¹ with hz'
  have hzH : z ∈ H₀ := H₀.mul_mem (hF₀ a ha) (H₀.inv_mem ha)
  have hz'H : z' ∈ H₁ := H₁.mul_mem (hF₁ b hb) (H₁.inv_mem hb)
  have hFab : F a * F b = a * b := by rw [← map_mul, hFr]
  have hFa : F a = z * a := by rw [hz]; group
  have hFb : F b = z' * b := by rw [hz']; group
  have haz' : a * z' = z' * a := hcomm a ha z' hz'H
  have hzz' : z * z' = 1 := by
    have h1 : z * a * (z' * b) = a * b := by rw [← hFa, ← hFb, hFab]
    have h2 : z * a * (z' * b) = z * z' * (a * b) := by
      calc z * a * (z' * b) = z * (a * z') * b := by group
        _ = z * (z' * a) * b := by rw [haz']
        _ = z * z' * (a * b) := by group
    rw [h2] at h1
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  have hzinv : z = z'⁻¹ := eq_inv_of_mul_eq_one_left hzz'
  have hzH₁ : z ∈ H₁ := by rw [hzinv]; exact H₁.inv_mem hz'H
  have hz'inv : z' = z⁻¹ := by rw [hzinv, inv_inv]
  have hz'H₀ : z' ∈ H₀ := by rw [hz'inv]; exact H₀.inv_mem hzH
  have hz2 : z * z = 1 := hΔ z ⟨hzH, hzH₁⟩
  have hz'2 : z' * z' = 1 := hΔ z' ⟨hz'H₀, hz'H⟩
  have haz : a * z = z * a := hcomm a ha z hzH₁
  have hbz' : z' * b = b * z' := (hcomm z' hz'H₀ b hb)
  have hFaa : F (a * a) = a * a := by
    rw [map_mul, hFa]
    calc z * a * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [haz]
      _ = (z * z) * (a * a) := by group
      _ = a * a := by rw [hz2, one_mul]
  have hFbb : F (b * b) = b * b := by
    rw [map_mul, hFb]
    calc z' * b * (z' * b) = z' * (b * z') * b := by group
      _ = z' * (z' * b) * b := by rw [hbz']
      _ = (z' * z') * (b * b) := by group
      _ = b * b := by rw [hz'2, one_mul]
  have hab : b * a = a * b := (hcomm a ha b hb).symm
  have e : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨H₀.mul_mem ha ha, hFaa⟩ ⟨H₁.mul_mem hb hb, hFbb⟩

end TwoOrbit

section TwoOrbitDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_two_orbit_exp {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    {J₀ J₁ : Set.range D.classOrbit} (hne : J₀ ≠ J₁)
    (hall : ∀ J' : Set.range D.classOrbit, J' = J₀ ∨ J' = J₁)
    (hsq : ∀ z ∈ (D.withOrbit J₀).rootSpanJ ⊓ (D.withOrbit J₁).rootSpanJ, z * z = 1) :
    ∀ x ∈ D.totalFixedGroup, ∃ m : ℕ, (x : ModGL τ k) ^ (2 ^ m) ∈
      ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup := by
  classical
  intro x hx
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hc.frob, hc.normalizes, hc.sq_mem⟩
  set H₀ : Subgroup (adjointGroup τ k) := (D.withOrbit J₀).rootSpanJ.subgroupOf (adjointGroup τ k)
    with hH₀
  set H₁ : Subgroup (adjointGroup τ k) := (D.withOrbit J₁).rootSpanJ.subgroupOf (adjointGroup τ k)
    with hH₁
  have hr : x ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ D.kernelFixedGroup := hc.pow_mem_kernelFixedGroup hx
  set r : adjointGroup τ k := x ^ ((p₀ ^ D.e) ^ 2 - 1) with hr_def
  have hS : (⨆ J' : Set.range D.classOrbit, (D.withOrbit J').rootSpanJ) =
      (D.withOrbit J₀).rootSpanJ ⊔ (D.withOrbit J₁).rootSpanJ := by
    refine le_antisymm (iSup_le fun J' => ?_)
      (sup_le (le_iSup (fun J' : Set.range D.classOrbit => (D.withOrbit J').rootSpanJ) J₀)
        (le_iSup (fun J' : Set.range D.classOrbit => (D.withOrbit J').rootSpanJ) J₁))
    rcases hall J' with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hrS : r ∈ H₀ ⊔ H₁ := by
    have hinf : ∀ J' : Set.range D.classOrbit,
        (D.withOrbit J').rootSpanJ ⊓ adjointGroup τ k = (D.withOrbit J').rootSpanJ :=
      fun J' => inf_of_le_left unionRootSpan_le_adjointGroup
    have h1 : (H₀ ⊔ H₁).map (adjointGroup τ k).subtype = D.kernelSpan := by
      rw [Subgroup.map_sup, hH₀, hH₁, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype, hinf, hinf, ← hS]
      exact D.iSup_rootSpanJ_withOrbit
    have h2 : (r : ModGL τ k) ∈ (H₀ ⊔ H₁).map (adjointGroup τ k).subtype := by
      rw [h1]
      exact (D.mem_kernelFixedGroup.1 hr).1
    obtain ⟨y, hy, hyr⟩ := h2
    rwa [← Subtype.ext hyr]
  have hFr : D.F.toMonoidHom r = r := (D.mem_kernelFixedGroup.1 hr).2
  have hF₀ : ∀ a ∈ H₀, D.F.toMonoidHom a ∈ H₀ := fun a ha => by
    have h : H₀.map D.F.toMonoidHom = H₀ := (D.withOrbit J₀).map_rootSpanJ
    rw [← h]
    exact Subgroup.mem_map_of_mem _ ha
  have hF₁ : ∀ a ∈ H₁, D.F.toMonoidHom a ∈ H₁ := fun a ha => by
    have h : H₁.map D.F.toMonoidHom = H₁ := (D.withOrbit J₁).map_rootSpanJ
    rw [← h]
    exact Subgroup.mem_map_of_mem _ ha
  have hcomm : ∀ a ∈ H₀, ∀ b ∈ H₁, a * b = b * a := fun a ha b hb =>
    Subtype.ext (D.commute_of_ne hne ha hb).eq
  have hΔ : ∀ z ∈ H₀ ⊓ H₁, z * z = 1 := fun z hz =>
    Subtype.ext (hsq z ⟨hz.1, hz.2⟩)
  have h2 := exc3_pow_mem_sup_of_two D.F.toMonoidHom hcomm hF₀ hF₁ hΔ hrS hFr
  have hΓcomm : ∀ a ∈ (H₀ ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)),
      ∀ b ∈ (H₁ ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)), a * b = b * a :=
    fun a ha b hb => hcomm a ha.1 b hb.1
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute hΓcomm).1 h2
  have hN : (p₀ ^ D.e) ^ 2 - 1 = 8 := by rw [hq3]; norm_num
  have ha8 : a ^ 8 ∈ (D.withOrbit J₀).orbitGroupC := by
    have h := (hcJ J₀).pow_mem_orbitGroupC (D := D.withOrbit J₀) (γ := a) ha
    change a ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ _ at h
    rwa [hN] at h
  have hb8 : b ^ 8 ∈ (D.withOrbit J₁).orbitGroupC := by
    have h := (hcJ J₁).pow_mem_orbitGroupC (D := D.withOrbit J₁) (γ := b) hb
    change b ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ _ at h
    rwa [hN] at h
  have hr8 : r = x ^ 8 := by rw [hr_def, hN]
  have habc : Commute a b := hΓcomm a ha b hb
  have e : x ^ (2 ^ 7) = a ^ 8 * b ^ 8 := by
    rw [← habc.mul_pow, hab, hr8, ← pow_add, ← pow_mul]
    norm_num
  refine ⟨7, ?_⟩
  have e2 : (x : ModGL τ k) ^ (2 ^ 7) = ((a ^ 8 : adjointGroup τ k) : ModGL τ k) *
      ((b ^ 8 : adjointGroup τ k) : ModGL τ k) := by
    rw [← Subgroup.coe_pow, e, Subgroup.coe_mul]
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem J₀ (Subgroup.mem_subgroupOf.1 ha8))
    (Subgroup.mem_iSup_of_mem J₁ (Subgroup.mem_subgroupOf.1 hb8))

end TwoOrbitDatum

end CFSG.ClassicalInvolution.Q3
