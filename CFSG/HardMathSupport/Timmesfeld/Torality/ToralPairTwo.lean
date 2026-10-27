module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem torusGroup_le_adjointGroup_aux
    {τ : Tag} {K : Type} [Field K] :
    torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

private theorem torusGroup_mul_comm_aux
    {τ : Tag} {K : Type} [Field K] {h h' : ModGL τ K}
    (hh : h ∈ torusGroup τ K) (hh' : h' ∈ torusGroup τ K) : h * h' = h' * h := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mul_comm_of_mem_torusGroup b hh'

private theorem monoidHom_eq_one_of_pow_surjective
    {A Q : Type*} [Group A] [Group Q] [Finite Q]
    (hroot : ∀ a : A, ∀ n : ℕ, 0 < n → ∃ b : A, b ^ n = a)
    (f : A →* Q) (a : A) : f a = 1 := by
  obtain ⟨b, hb⟩ := hroot a (Nat.card Q) Nat.card_pos
  have h : (f b) ^ Nat.card Q = 1 := pow_card_eq_one'
  rw [← map_pow, hb] at h
  exact h

private theorem subgroup_le_of_finite_index_of_pow_surjective
    {G : Type*} [Group G] (H S : Subgroup G) [Finite (G ⧸ H)]
    (hdiv : ∀ s : S, ∀ n : ℕ, 0 < n → ∃ r : S, r ^ n = s) : S ≤ H := by
  intro s hs
  let f : S →* Equiv.Perm (G ⧸ H) :=
    (MulAction.toPermHom G (G ⧸ H)).comp S.subtype
  have hf : f ⟨s, hs⟩ = 1 :=
    monoidHom_eq_one_of_pow_surjective hdiv f ⟨s, hs⟩
  have h1 : ((s : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    have hfun :=
      congrArg (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk (1 : G))) hf
    simpa [f, MonoidHom.comp_apply, Subgroup.subtype_apply, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, MulAction.Quotient.smul_mk] using hfun
  have h2 : s⁻¹ * 1 ∈ H := (QuotientGroup.eq (s := H)).mp h1
  have h3 : s⁻¹ ∈ H := by simpa using h2
  exact H.inv_mem_iff.mp h3

private theorem familyGroup_finiteIndex_familyCentralizer
    {τ : Tag} {K : Type} [Field K] {ι : Type} (a : ι → Fin τ.rank → Kˣ) :
    ((familyGroup (K := K) a).subgroupOf (familyCentralizer τ K a)).FiniteIndex := by
  classical
  have hC : ∀ w : WeylGroup τ, w ∈ familyStabilizer a →
      canonicalRep (coxeterSystem τ) K w ∈ familyCentralizer τ K a := fun w hw =>
    mem_familyCentralizer.2 ⟨canonicalRep_mem_adjointGroup (coxeterSystem τ) K w,
      fun i => (conj_canonicalRep_eq_iff (a i) w).2 (hw i)⟩
  have hWfin : (familyStabilizer a).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  letI : Finite {w : WeylGroup τ // w ∈ familyStabilizer a} := hWfin.to_subtype
  letI : Fintype {w : WeylGroup τ // w ∈ familyStabilizer a} := Fintype.ofFinite _
  refine Subgroup.finiteIndex_of_leftCoset_cover_const
    (s := (Finset.univ : Finset {w : WeylGroup τ // w ∈ familyStabilizer a}))
    (g := fun w => ⟨canonicalRep (coxeterSystem τ) K w.1, hC w.1 w.2⟩) ?_
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion₂]
  obtain ⟨w, hw, m, hm, hx⟩ := familyCentralizer_le_mul τ K a x.2
  refine ⟨⟨w, hw⟩, Finset.mem_univ _, ?_⟩
  rw [mem_leftCoset_iff]
  change (canonicalRep (coxeterSystem τ) K w)⁻¹ * (x : ModGL τ K) ∈
    familyGroup (K := K) a
  have hnorm := canonicalRep_mem_normalizer_familyGroup (K := K) hw
  have hconj : (canonicalRep (coxeterSystem τ) K w)⁻¹ * m *
      canonicalRep (coxeterSystem τ) K w ∈ familyGroup (K := K) a :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hnorm) m).1 hm
  rw [hx]
  simpa only [mul_assoc] using hconj

theorem mem_familyGroup_of_conj_mem_torusGroup
    {L : Type} [Field L] [IsAlgClosed L] {τ : Tag}
    {a : Fin τ.rank → Lˣ} {y g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hx : g * rootDiagUnit τ a * g⁻¹ ∈ torusGroup τ L)
    (hyT : g * y * g⁻¹ ∈ torusGroup τ L) :
    y ∈ familyGroup (fun _ : Unit => a) := by
  classical
  let T : Subgroup (ModGL τ L) := torusGroup τ L
  let S : Subgroup (ModGL τ L) := T.comap (MulAut.conj g).toMonoidHom
  let M : Subgroup (ModGL τ L) := familyGroup (fun _ : Unit => a)
  let C : Subgroup (ModGL τ L) := familyCentralizer τ L (fun _ : Unit => a)
  have hT_le_adj : T ≤ adjointGroup τ L := torusGroup_le_adjointGroup_aux
  have hdS : rootDiagUnit τ a ∈ S := by
    rw [Subgroup.mem_comap]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx
  have hyS : y ∈ S := by
    rw [Subgroup.mem_comap]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyT
  have hS_le_adj : S ≤ adjointGroup τ L := by
    intro s hs
    have hsT : g * s * g⁻¹ ∈ T := by
      rw [Subgroup.mem_comap] at hs
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hs
    have hgsg : g * s * g⁻¹ ∈ adjointGroup τ L := hT_le_adj hsT
    have hmem : g⁻¹ * (g * s * g⁻¹) * g ∈ adjointGroup τ L :=
      mul_mem (mul_mem (inv_mem hg) hgsg) hg
    convert hmem using 1
    group
  have hT_comm : ∀ h ∈ T, ∀ h' ∈ T, h * h' = h' * h := fun h hh h' hh' =>
    torusGroup_mul_comm_aux hh hh'
  have hS_comm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    intro s hs s' hs'
    have hsT : g * s * g⁻¹ ∈ T := by
      rw [Subgroup.mem_comap] at hs
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hs
    have hs'T : g * s' * g⁻¹ ∈ T := by
      rw [Subgroup.mem_comap] at hs'
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hs'
    have h1 : g * (s * s') * g⁻¹ = g * (s' * s) * g⁻¹ := by
      rw [show g * (s * s') * g⁻¹ = (g * s * g⁻¹) * (g * s' * g⁻¹) by group,
        show g * (s' * s) * g⁻¹ = (g * s' * g⁻¹) * (g * s * g⁻¹) by group,
        hT_comm (g * s * g⁻¹) hsT (g * s' * g⁻¹) hs'T]
    exact mul_left_cancel (mul_right_cancel h1)
  have hS_le_C : S ≤ C := by
    intro s hs
    refine mem_familyCentralizer.2 ⟨hS_le_adj hs, fun _ => ?_⟩
    have hc := hS_comm (rootDiagUnit τ a) hdS s hs
    rw [hc, mul_inv_cancel_right]
  have hS_div : ∀ s : S, ∀ n : ℕ, 0 < n → ∃ r : S, r ^ n = s := by
    intro s n hn
    have hsT : g * (s : ModGL τ L) * g⁻¹ ∈ T := by
      have h := s.2
      rw [Subgroup.mem_comap] at h
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hsT
    choose c hc using fun j : Fin τ.rank =>
      exists_zpow_eq_of_isAlgClosed (n := (n : ℤ)) (by omega) (b j)
    let r₀ : ModGL τ L := g⁻¹ * rootDiagUnit τ c * g
    have hrS : r₀ ∈ S := by
      have h1 : g * r₀ * g⁻¹ = rootDiagUnit τ c := by
        simp only [r₀]
        group
      rw [Subgroup.mem_comap]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h1]
        using rootDiagUnit_mem_torusGroup c
    refine ⟨⟨r₀, hrS⟩, Subtype.ext ?_⟩
    have hcpow : c ^ n = b := by
      funext j
      simpa only [Pi.pow_apply, zpow_natCast] using hc j
    have hdcn : (rootDiagUnit τ c) ^ n = rootDiagUnit τ b := by
      change ((rootDiagUnitHom τ L) c) ^ n = (rootDiagUnitHom τ L) b
      rw [← map_pow (rootDiagUnitHom τ L) c n, hcpow]
    have hr0 : r₀ = MulAut.conj g⁻¹ (rootDiagUnit τ c) := by
      simp only [r₀, MulAut.conj_apply, inv_inv]
    calc r₀ ^ n = (MulAut.conj g⁻¹ (rootDiagUnit τ c)) ^ n := by rw [← hr0]
      _ = MulAut.conj g⁻¹ ((rootDiagUnit τ c) ^ n) :=
            (map_pow (MulAut.conj g⁻¹).toMonoidHom (rootDiagUnit τ c) n).symm
      _ = MulAut.conj g⁻¹ (rootDiagUnit τ b) := by rw [hdcn]
      _ = g⁻¹ * rootDiagUnit τ b * g := by simp only [MulAut.conj_apply, inv_inv]
      _ = (s : ModGL τ L) := by rw [← hb]; group
  haveI : (M.subgroupOf C).FiniteIndex :=
    familyGroup_finiteIndex_familyCentralizer (K := L) (fun _ : Unit => a)
  have hdivC : ∀ s : S.subgroupOf C, ∀ n : ℕ, 0 < n →
      ∃ r : S.subgroupOf C, r ^ n = s := by
    intro s n hn
    let e := Subgroup.subgroupOfEquivOfLe hS_le_C
    obtain ⟨r, hr⟩ := hS_div (e s) n hn
    refine ⟨e.symm r, ?_⟩
    rw [← map_pow e.symm r n, hr]
    exact e.symm_apply_apply s
  have hSC : S.subgroupOf C ≤ M.subgroupOf C :=
    subgroup_le_of_finite_index_of_pow_surjective (M.subgroupOf C) (S.subgroupOf C) hdivC
  have hyC : y ∈ C := hS_le_C hyS
  have hyM : (⟨y, hyC⟩ : C) ∈ M.subgroupOf C :=
    hSC ((Subgroup.mem_subgroupOf).2 hyS)
  exact (Subgroup.mem_subgroupOf).1 hyM

end CFSG.HardMathSupport.Timmesfeld.Torality
