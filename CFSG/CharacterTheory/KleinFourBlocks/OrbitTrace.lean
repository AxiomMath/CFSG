module

public import CFSG.CharacterTheory.BrauerCharacters.InertialQuotient
public import CFSG.CharacterTheory.BrauerCharacters.MajorFixedPoints
public import CFSG.CharacterTheory.Wreathed.NormalCentralizerBlockOrbits
public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.BrauerCharacters.Residue
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.BrauerCharacters
  CFSG.BlockSectionOrthogonality.Helpers CFSG.Wreathed.BlockOrbits

open scoped Classical

namespace CFSG.KleinFourBlocks

section RelTrace

variable {G : Type} [Group G] [Fintype G]

theorem relTrace_conj {C : Subgroup G} {w : G → ℂ}
    (hwC : ∀ (g : G) (c : C), w ((c : G) * g * (c : G)⁻¹) = w g) (g h : G) :
    relTrace C w (h * g * h⁻¹) = relTrace C w g := by
  unfold relTrace
  symm
  apply Fintype.sum_equiv (MulAction.toPerm h : Equiv.Perm (G ⧸ C))
  intro q
  have hq : ((h * Quotient.out q : G) : G ⧸ C) = (MulAction.toPerm h : Equiv.Perm (G ⧸ C)) q := by
    change _ = h • q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    exact (MulAction.Quotient.smul_mk _ h (Quotient.out q)).symm
  rw [relTrace_out_eq hwC (h * g * h⁻¹) hq]
  congr 1
  group

theorem relTrace_isCentralR (m : Ideal BlocksAlgInt) [hm : m.IsMaximal] {C : Subgroup G}
    {w : G → ℂ} (hwR : ∀ g, w g ∈ BlocksLocalRing m)
    (hwC : ∀ (g : G) (c : C), w ((c : G) * g * (c : G)⁻¹) = w g) :
    BlocksIsCentralR m (relTrace C w) :=
  ⟨fun _ => localRing_sum m hm Finset.univ _ (fun _ _ => hwR _),
    fun g h => relTrace_conj hwC g h⟩

end RelTrace

section OrbitTrace

variable {H : Type} [Group H] [Fintype H] (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]
  (P : Subgroup H) [P.Normal]

@[expose] noncomputable def idemExt (β : Set (Subgroup.centralizer (P : Set H) → ℂ)) (g : H) :
    ℂ :=
  if hg : g ∈ Subgroup.centralizer (P : Set H) then BlocksIdempotentCoeff _ β ⟨g, hg⟩ else 0

@[expose] noncomputable def orbitTrace
    (β : Set (Subgroup.centralizer (P : Set H) → ℂ)) (g : H) : ℂ :=
  relTrace (Subgroup.centralizer (P : Set H)) (idemExt P β) g

variable {P}

omit [P.Normal] in
theorem idemExt_mem_localRing {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : BlocksIsBlock m (Subgroup.centralizer (P : Set H)) β) (g : H) :
    idemExt P β g ∈ BlocksLocalRing m := by
  unfold idemExt
  split_ifs with hg
  · exact (CFSG.BrauerThirdMainTheorem.Helpers.block_admissible m hm _ hβ).2 _
  · exact localRing_zero m hm

omit [P.Normal] in
theorem idemExt_conj {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : β ⊆ BlocksIrr (Subgroup.centralizer (P : Set H))) (g : H)
    (c : Subgroup.centralizer (P : Set H)) :
    idemExt P β ((c : H) * g * (c : H)⁻¹) = idemExt P β g := by
  by_cases hg : g ∈ Subgroup.centralizer (P : Set H)
  · have hcg : (c : H) * g * (c : H)⁻¹ ∈ Subgroup.centralizer (P : Set H) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hg) (Subgroup.inv_mem _ c.2)
    simp only [idemExt, hcg, hg, ↓reduceDIte]
    exact idempotentCoeff_conj hβ (⟨g, hg⟩ : Subgroup.centralizer (P : Set H)) c
  · have hcg : (c : H) * g * (c : H)⁻¹ ∉ Subgroup.centralizer (P : Set H) := by
      intro h
      apply hg
      have : g = (c : H)⁻¹ * ((c : H) * g * (c : H)⁻¹) * c := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ c.2) h) c.2
    simp only [idemExt, hcg, hg, ↓reduceDIte]

omit [P.Normal] in
theorem orbitTrace_isCentralR {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : BlocksIsBlock m (Subgroup.centralizer (P : Set H)) β) :
    BlocksIsCentralR m (orbitTrace P β) :=
  relTrace_isCentralR m (idemExt_mem_localRing m hβ)
    (fun g c => idemExt_conj (block_subset_irr m hβ) g c)

omit [P.Normal] in
theorem orbitTrace_apply (β : Set (Subgroup.centralizer (P : Set H) → ℂ)) (g : H) :
    orbitTrace P β g = ∑ q : H ⧸ Subgroup.centralizer (P : Set H),
      idemExt P β ((Quotient.out q)⁻¹ * g * Quotient.out q) := rfl

omit [Fintype H] in
theorem normalCentralizerConj_inv_apply (h : H) (d : Subgroup.centralizer (P : Set H)) :
    ((normalCentralizerConj P h⁻¹ d : Subgroup.centralizer (P : Set H)) : H) = h⁻¹ * d * h := by
  rw [normalCentralizerConj_apply]
  simp

omit [Fintype H] in
theorem normalCentralizerConj_apply_inv (h : H) (d : Subgroup.centralizer (P : Set H)) :
    normalCentralizerConj P h (normalCentralizerConj P h⁻¹ d) = d := by
  apply Subtype.ext
  rw [normalCentralizerConj_apply, normalCentralizerConj_inv_apply]
  group

theorem sum_idemExt_conj (β : Set (Subgroup.centralizer (P : Set H) → ℂ))
    (ψ : Subgroup.centralizer (P : Set H) → ℂ) (q : H) :
    ∑ d : Subgroup.centralizer (P : Set H), idemExt P β (q⁻¹ * d * q) * ψ d =
      ∑ d : Subgroup.centralizer (P : Set H), BlocksIdempotentCoeff _ β d *
        ψ (normalCentralizerConj P q d) := by
  apply Fintype.sum_equiv (normalCentralizerConj P q⁻¹).toEquiv
  intro d
  show _ = BlocksIdempotentCoeff _ β ((normalCentralizerConj P q⁻¹) d) *
    ψ ((normalCentralizerConj P q) ((normalCentralizerConj P q⁻¹) d))
  have hmem : q⁻¹ * (d : H) * q ∈ Subgroup.centralizer (P : Set H) := by
    rw [← normalCentralizerConj_inv_apply]
    exact (normalCentralizerConj P q⁻¹ d).2
  have h1 : idemExt P β (q⁻¹ * (d : H) * q) =
      BlocksIdempotentCoeff _ β (normalCentralizerConj P q⁻¹ d) := by
    simp only [idemExt, hmem, ↓reduceDIte]
    congr 1
    apply Subtype.ext
    rw [normalCentralizerConj_inv_apply]
  rw [h1, normalCentralizerConj_apply_inv]

omit hm in
theorem centralChar_brauerProj_orbitTrace
    {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : BlocksIsBlock m (Subgroup.centralizer (P : Set H)) β)
    (hstab : ∀ q : H, ∀ ψ ∈ β, (fun d => ψ (normalCentralizerConj P q d)) ∈ β →
      q ∈ Subgroup.centralizer (P : Set H))
    {ψ : Subgroup.centralizer (P : Set H) → ℂ} (hψ : ψ ∈ β) :
    BlocksCentralChar ψ (BlocksBrauerProj P (Subgroup.centralizer (P : Set H))
      (orbitTrace P β)) = 1 := by
  have hβirr := block_subset_irr m hβ
  have hψirr : ψ ∈ BlocksIrr (Subgroup.centralizer (P : Set H)) := hβirr hψ
  have hψ1 : ψ 1 ≠ 0 := irr_degree_ne_zero hψirr
  have hproj : BlocksBrauerProj P (Subgroup.centralizer (P : Set H)) (orbitTrace P β) =
      fun d : Subgroup.centralizer (P : Set H) => orbitTrace P β (d : H) := by
    funext d
    unfold BlocksBrauerProj
    rw [Set.indicator_of_mem]
    exact d.2
  rw [hproj]
  unfold BlocksCentralChar
  rw [finsum_eq_sum_of_fintype]
  simp only [orbitTrace_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  have hterm : ∀ q : H ⧸ Subgroup.centralizer (P : Set H),
      (∑ d : Subgroup.centralizer (P : Set H),
        idemExt P β ((Quotient.out q)⁻¹ * d * Quotient.out q) * ψ d) / ψ 1 =
      if (fun d => ψ (normalCentralizerConj P (Quotient.out q) d)) ∈ β then 1 else 0 := by
    intro q
    rw [sum_idemExt_conj]
    have hψq : (fun d => ψ (normalCentralizerConj P (Quotient.out q) d)) ∈
        BlocksIrr (Subgroup.centralizer (P : Set H)) :=
      CFSG.DirectProduct.comp_mulEquiv_mem_blocksIrr hψirr _
    have h := centralChar_idempotentCoeff hβirr hψq
    unfold BlocksCentralChar at h
    rw [finsum_eq_sum_of_fintype] at h
    simpa using h
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  rw [Finset.sum_eq_single (1 : H ⧸ Subgroup.centralizer (P : Set H))]
  · have hout : (Quotient.out (1 : H ⧸ Subgroup.centralizer (P : Set H)) : H) ∈
        Subgroup.centralizer (P : Set H) := by
      have h := QuotientGroup.out_eq' (1 : H ⧸ Subgroup.centralizer (P : Set H))
      exact (QuotientGroup.eq_one_iff _).mp h
    have hq : (fun d => ψ (normalCentralizerConj P (Quotient.out (1 : H ⧸
        Subgroup.centralizer (P : Set H))) d)) = ψ := by
      funext d
      have hcd : normalCentralizerConj P (Quotient.out (1 : H ⧸
          Subgroup.centralizer (P : Set H))) d =
          (⟨_, hout⟩ : Subgroup.centralizer (P : Set H)) * d * (⟨_, hout⟩ :
            Subgroup.centralizer (P : Set H))⁻¹ := Subtype.ext rfl
      rw [hcd]
      exact irr_conj hψirr _ _
    rw [hq]
    simp [hψ]
  · intro q _ hq
    apply ite_eq_right_iff.mpr
    intro hmem
    exfalso
    apply hq
    have := hstab _ ψ hψ hmem
    have h2 : ((Quotient.out q : H) : H ⧸ Subgroup.centralizer (P : Set H)) = q :=
      QuotientGroup.out_eq' q
    exact h2.symm.trans ((QuotientGroup.eq_one_iff _).mpr this)
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype H] in
theorem mem_centralizer_of_smul_eq {Y : Subgroup H} (x : H ⧸ Subgroup.centralizer (P : Set H))
    (hx : ∀ q : Y, q • x = x) : Y ≤ Subgroup.centralizer (P : Set H) := by
  intro y hy
  have h1 := hx ⟨y, hy⟩
  have h2 : (((y : H) * Quotient.out x : H) : H ⧸ Subgroup.centralizer (P : Set H)) =
      ((Quotient.out x : H) : H ⧸ Subgroup.centralizer (P : Set H)) := by
    rw [QuotientGroup.out_eq' x]
    conv_rhs => rw [← h1]
    rw [Subgroup.smul_def]
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    exact (MulAction.Quotient.smul_mk (Subgroup.centralizer (P : Set H)) (y : H)
      (Quotient.out x)).symm
  have h3 := QuotientGroup.eq.mp h2
  have h4 : (Quotient.out x : H)⁻¹ * ((y : H)⁻¹) * Quotient.out x ∈
      Subgroup.centralizer (P : Set H) := by
    have : ((y : H) * Quotient.out x)⁻¹ * Quotient.out x =
        (Quotient.out x : H)⁻¹ * ((y : H)⁻¹) * Quotient.out x := by group
    rw [← this]
    exact h3
  have h5 := Subgroup.Normal.conj_mem (inferInstance :
    (Subgroup.centralizer (P : Set H)).Normal) _ h4 (Quotient.out x : H)
  have h6 : (Quotient.out x : H) * ((Quotient.out x : H)⁻¹ * ((y : H)⁻¹) * Quotient.out x) *
      (Quotient.out x : H)⁻¹ = (y : H)⁻¹ := by group
  rw [h6] at h5
  simpa using Subgroup.inv_mem _ h5

theorem orbitTrace_mem_localMaxIdeal_of_not_le [CharP (BlocksAlgInt ⧸ m) 2]
    {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : BlocksIsBlock m (Subgroup.centralizer (P : Set H)) β) {Y : Subgroup H}
    (hY : IsPGroup 2 Y) (hYD : ¬ Y ≤ Subgroup.centralizer (P : Set H)) {c : H}
    (hc : c ∈ Subgroup.centralizer (Y : Set H)) :
    orbitTrace P β c ∈ BlocksLocalMaxIdeal m := by
  unfold orbitTrace relTrace
  refine sum_mem_localMaxIdeal_of_fixed (ideal := m) 2 hY
    (fun x : H ⧸ Subgroup.centralizer (P : Set H) =>
      idemExt P β ((Quotient.out x)⁻¹ * c * Quotient.out x)) ?_ ?_ ?_
  · intro q x
    have hqx : (((q : H) * Quotient.out x : H) : H ⧸ Subgroup.centralizer (P : Set H)) =
        q • x := by
      rw [Subgroup.smul_def]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      exact (MulAction.Quotient.smul_mk (Subgroup.centralizer (P : Set H)) (q : H)
        (Quotient.out x)).symm
    have hwC : ∀ (g : H) (d : Subgroup.centralizer (P : Set H)),
        idemExt P β ((d : H) * g * (d : H)⁻¹) = idemExt P β g :=
      fun g d => idemExt_conj (block_subset_irr m hβ) g d
    rw [relTrace_out_eq hwC c hqx]
    have hcq : (q : H)⁻¹ * c * q = c := by
      have := Subgroup.mem_centralizer_iff.mp hc q q.2
      calc (q : H)⁻¹ * c * q = (q : H)⁻¹ * (c * q) := by group
        _ = (q : H)⁻¹ * (q * c) := by rw [this]
        _ = c := by group
    congr 1
    calc ((q : H) * Quotient.out x)⁻¹ * c * ((q : H) * Quotient.out x) =
        (Quotient.out x : H)⁻¹ * ((q : H)⁻¹ * c * q) * Quotient.out x := by group
      _ = _ := by rw [hcq]
  · intro x
    exact idemExt_mem_localRing m hβ _
  · intro x hx
    exact absurd (mem_centralizer_of_smul_eq x hx) hYD

theorem no_brauer_preimage_of_not_le_centralizer [CharP (BlocksAlgInt ⧸ m) 2]
    {β : Set (Subgroup.centralizer (P : Set H) → ℂ)}
    (hβ : BlocksIsBlock m (Subgroup.centralizer (P : Set H)) β) {A : Set (H → ℂ)}
    (hA : BlocksIsBlock m H A) (hcorr : BlocksBrauerCorr m P (Subgroup.centralizer (P : Set H)) β A)
    (hstab : ∀ q : H, ∀ ψ ∈ β, (fun d => ψ (normalCentralizerConj P q d)) ∈ β →
      q ∈ Subgroup.centralizer (P : Set H))
    {Y : Subgroup H} (hY : IsPGroup 2 Y) (hYD : ¬ Y ≤ Subgroup.centralizer (P : Set H))
    {γ : Set (Subgroup.centralizer (Y : Set H) → ℂ)}
    (hγ : BlocksIsBlock m (Subgroup.centralizer (Y : Set H)) γ)
    (hγcorr : BlocksBrauerCorr m Y (Subgroup.centralizer (Y : Set H)) γ A) : False := by
  obtain ⟨χ, hχ⟩ := block_nonempty m hA
  obtain ⟨ψ₀, hψ₀⟩ := block_nonempty m hβ
  obtain ⟨ψγ, hψγ⟩ := block_nonempty m hγ
  have hEc := orbitTrace_isCentralR m hβ
  have h1 := hcorr _ hEc χ hχ ψ₀ hψ₀
  rw [centralChar_brauerProj_orbitTrace m hβ hstab hψ₀] at h1
  have h2 := hγcorr _ hEc χ hχ ψγ hψγ
  have hψγirr := block_subset_irr m hγ hψγ
  have h3 : BlocksCentralChar ψγ (BlocksBrauerProj Y (Subgroup.centralizer (Y : Set H))
      (orbitTrace P β)) ∈ BlocksLocalMaxIdeal m := by
    by_contra hnot
    have hproj : BlocksBrauerProj Y (Subgroup.centralizer (Y : Set H)) (orbitTrace P β) =
        fun c : Subgroup.centralizer (Y : Set H) => orbitTrace P β (c : H) := by
      funext c
      unfold BlocksBrauerProj
      rw [Set.indicator_of_mem]
      exact c.2
    have hcen : BlocksIsCentralR m (fun c : Subgroup.centralizer (Y : Set H) =>
        orbitTrace P β (c : H)) :=
      ⟨fun c => hEc.1 _, fun g h => hEc.2 _ _⟩
    rw [hproj] at hnot
    obtain ⟨y, hy, -⟩ := exists_coeff_not_mem_of_centralChar_not_mem (ideal := m) hψγirr hcen
      hnot
    exact hy (orbitTrace_mem_localMaxIdeal_of_not_le m hβ hY hYD y.2)
  have h4 := localMaxIdeal_sub m hm h1 h2
  have h5 : BlocksCentralChar ψγ (BlocksBrauerProj Y (Subgroup.centralizer (Y : Set H))
      (orbitTrace P β)) - 1 ∈ BlocksLocalMaxIdeal m := by
    have := h4
    rwa [sub_sub_sub_cancel_left] at this
  have h6 := localMaxIdeal_sub m hm h3 h5
  rw [sub_sub_cancel] at h6
  exact localMaxIdeal_one_not m h6

end OrbitTrace

end CFSG.KleinFourBlocks
