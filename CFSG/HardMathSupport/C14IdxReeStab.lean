module

public import CFSG.HardMathSupport.C14IdxDiagKer
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameRee

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Exc
  CFSG.LieType.Ree CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CFSG.HardMathSupport.C14Idx

private noncomputable def reeQ {L : Type} [Field L] [CharP L ReeTag.F4.prime]
    (a₀ : ℕ) (h : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L :=
  (h : ModGL ReeTag.F4.tag L) *
    (entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (h : ModGL ReeTag.F4.tag L))⁻¹

private theorem entrywiseFrobGL_pinnedX_one
    {L : Type} [Field L] [CharP L ReeTag.F4.prime] (a₀ : ℕ)
    (α : Fin ReeTag.F4.tag.rank → ℤ) :
    entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (pinnedX ReeTag.F4.tag L α 1) =
      pinnedX ReeTag.F4.tag L α 1 := by
  rw [entrywiseFrobGL_pinnedX, iterateFrobenius_def, one_pow]

private theorem exists_rootDiagUnit_preimage_entrywiseFrobGL
    {L : Type} [Field L] [IsAlgClosed L]
    [CharP L ReeTag.F4.prime] (a₀ : ℕ) (t : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ s : Fin ReeTag.F4.tag.rank → Lˣ,
      entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (rootDiagUnit ReeTag.F4.tag s) =
        rootDiagUnit ReeTag.F4.tag t := by
  haveI : CharP L 2 := ‹CharP L ReeTag.F4.prime›
  have ht := rootDiagUnit_mem_torusGroup (τ := ReeTag.F4.tag) t
  rw [← map_entrywiseFrobGL_torusGroup 2 (2 * a₀ + 1)] at ht
  obtain ⟨y, hy, hyt⟩ := ht
  obtain ⟨s, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  exact ⟨s, hyt⟩

theorem mem_diagKer_of_forall_commute
    {τ : Tag} {L : Type} [Field L] [Infinite L] {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot τ α) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hT : ∀ t : Fin τ.rank → Lˣ, Commute g (rootDiagUnit τ t))
    (hX : ∀ α ∈ Ψ, Commute g (pinnedX τ L α 1)) :
    g ∈ diagKer τ L Ψ := by
  obtain ⟨t, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (mem_torusGroup_of_forall_commute_rootDiagUnit hg hT)
  exact ⟨t, rfl, fun α hα => rootChar_eq_one_of_commute_rootDiagUnit_pinnedX t
    (hΨ α hα) (hX α hα)⟩

theorem isReeConj_apply_apply
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {hf : ReeTag.F4.ShortFaithful L} {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (g : adjointGroup ReeTag.F4.tag L) :
    ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      frobTwistGL ReeTag.F4.tag L 2 (2 * a₀ + 1)
        ((h : ModGL ReeTag.F4.tag L) *
          (entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (h : ModGL ReeTag.F4.tag L))⁻¹) g := by
  haveI : CharP L 2 := ‹CharP L ReeTag.F4.prime›
  change ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
    frobTwistGL ReeTag.F4.tag L 2 (2 * a₀ + 1)
      ((h : ModGL ReeTag.F4.tag L) *
        (entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (h : ModGL ReeTag.F4.tag L))⁻¹) g
  have h1 : F' (F' g) =
      h * ReeTag.F4.reeEndo L hf a₀ (ReeTag.F4.reeEndo L hf a₀ (h⁻¹ * g * h)) * h⁻¹ := by
    rw [hF (F' g), hF g]
    congr 1
    group
  have h2 := congrArg (fun z : adjointGroup ReeTag.F4.tag L => (z : ModGL ReeTag.F4.tag L)) h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [h2, ree_sq_apply hf a₀ (h⁻¹ * g * h)]
  simp only [frobTwistGL_apply, one_mul, inv_one, mul_one, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rw [map_mul, map_mul, map_inv]
  group

private theorem reeQ_conj_eq
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {hf : ReeTag.F4.ShortFaithful L} {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (m : adjointGroup ReeTag.F4.tag L) :
    reeQ a₀ h * entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (m : ModGL ReeTag.F4.tag L) *
        (reeQ a₀ h)⁻¹ =
      (F' (F' m) : ModGL ReeTag.F4.tag L) := by
  have hcoe := isReeConj_apply_apply (hF := hF) m
  change (F' (F' m) : ModGL ReeTag.F4.tag L) =
    reeQ a₀ h * entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (m : ModGL ReeTag.F4.tag L) *
      (reeQ a₀ h)⁻¹ at hcoe
  exact hcoe.symm

private theorem reeQ_mem_normalizer
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {ι : Type} (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) {hf : ReeTag.F4.ShortFaithful L}
    {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (hFM : ∀ g ∈ famM a, F' g ∈ famM a) :
    reeQ a₀ h ∈ Subgroup.normalizer (familyGroup a : Set (ModGL ReeTag.F4.tag L)) := by
  have hQadj : reeQ a₀ h ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem h.2 (inv_mem (entrywiseFrobGL_mem 2 (2 * a₀ + 1) h.2))
  refine mem_normalizer_familyGroup_of_conj_mem a hQadj ?_ ?_
  · intro t
    obtain ⟨s, hs⟩ := exists_rootDiagUnit_preimage_entrywiseFrobGL a₀ t
    let m : adjointGroup ReeTag.F4.tag L :=
      ⟨rootDiagUnit ReeTag.F4.tag s,
        torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup s)⟩
    have hmM : m ∈ famM a :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s))
    have hmem : (F' (F' m) : ModGL ReeTag.F4.tag L) ∈ familyGroup a :=
      Subgroup.mem_subgroupOf.mp (hFM _ (hFM m hmM))
    have hQeq := reeQ_conj_eq hF m
    rw [hs] at hQeq
    simpa [m, hQeq] using hmem
  · intro α hα
    let m : adjointGroup ReeTag.F4.tag L :=
      ⟨pinnedX ReeTag.F4.tag L α 1, pinnedX_mem_adjointGroup α 1⟩
    have hmM : m ∈ famM a :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (pinnedX_mem_rootSpan hα 1))
    have hmem : (F' (F' m) : ModGL ReeTag.F4.tag L) ∈ familyGroup a :=
      Subgroup.mem_subgroupOf.mp (hFM _ (hFM m hmM))
    have hQeq := reeQ_conj_eq hF m
    have hfix : entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (m : ModGL ReeTag.F4.tag L) =
        pinnedX ReeTag.F4.tag L α 1 := by
      simpa [m] using entrywiseFrobGL_pinnedX_one a₀ α
    rw [hfix] at hQeq
    simpa [m, hQeq] using hmem

private theorem reeQ_inv_conj_commute
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {ι : Type} (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) {hf : ReeTag.F4.ShortFaithful L}
    {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (hFM : ∀ g ∈ famM a, F' g ∈ famM a)
    {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a))
    {m : adjointGroup ReeTag.F4.tag L} (hm : m ∈ famM a) :
    Commute ((reeQ a₀ h)⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * reeQ a₀ h)
      (entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (m : ModGL ReeTag.F4.tag L)) := by
  have hF'm : F' m ∈ famM a := hFM m hm
  have hcommM : (g : ModGL ReeTag.F4.tag L) * (F' m : ModGL ReeTag.F4.tag L) =
      (F' m : ModGL ReeTag.F4.tag L) * (g : ModGL ReeTag.F4.tag L) :=
    diagKer_central a hg (Subgroup.mem_subgroupOf.mp hF'm)
  have hcommA : (F' g : ModGL ReeTag.F4.tag L) * (F' (F' m) : ModGL ReeTag.F4.tag L) =
      (F' (F' m) : ModGL ReeTag.F4.tag L) * (F' g : ModGL ReeTag.F4.tag L) := by
    have h1 : g * F' m = F' m * g := Subtype.ext hcommM
    have h2 : F' g * F' (F' m) = F' (F' m) * F' g := by
      simpa only [map_mul] using congrArg F' h1
    exact congrArg Subtype.val h2
  have hQeq := reeQ_conj_eq hF m
  rw [← hQeq] at hcommA
  have h := congrArg (fun z => (reeQ a₀ h)⁻¹ * z * reeQ a₀ h) hcommA
  simpa [Commute, SemiconjBy, mul_assoc] using h

private theorem reeQ_inv_conj_mem_diagKer
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {ι : Type} (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) {hf : ReeTag.F4.ShortFaithful L}
    {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (hFM : ∀ g ∈ famM a, F' g ∈ famM a)
    {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a)) :
    ((reeQ a₀ h)⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * reeQ a₀ h) ∈
      diagKer ReeTag.F4.tag L (familyKernel a) := by
  have hQadj : reeQ a₀ h ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem h.2 (inv_mem (entrywiseFrobGL_mem 2 (2 * a₀ + 1) h.2))
  have hmem : ((reeQ a₀ h)⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * reeQ a₀ h) ∈
      adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem (inv_mem hQadj) (F' g).2) hQadj
  refine mem_diagKer_of_forall_commute (fun α hα => hα.1) hmem ?_ ?_
  · intro t
    obtain ⟨s, hs⟩ := exists_rootDiagUnit_preimage_entrywiseFrobGL a₀ t
    let m : adjointGroup ReeTag.F4.tag L :=
      ⟨rootDiagUnit ReeTag.F4.tag s,
        torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup s)⟩
    have hmM : m ∈ famM a :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s))
    simpa [m, hs] using reeQ_inv_conj_commute a hF hFM hg hmM
  · intro α hα
    let m : adjointGroup ReeTag.F4.tag L :=
      ⟨pinnedX ReeTag.F4.tag L α 1, pinnedX_mem_adjointGroup α 1⟩
    have hmM : m ∈ famM a :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (pinnedX_mem_rootSpan hα 1))
    have hfix : entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a₀ + 1) (m : ModGL ReeTag.F4.tag L) =
        pinnedX ReeTag.F4.tag L α 1 := by
      simpa [m] using entrywiseFrobGL_pinnedX_one a₀ α
    simpa [m, hfix] using reeQ_inv_conj_commute a hF hFM hg hmM

private theorem diagKer_mapsTo
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {ι : Type} (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) {hf : ReeTag.F4.ShortFaithful L}
    {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (hFM : ∀ g ∈ famM a, F' g ∈ famM a)
    {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a)) :
    (F' g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) := by
  let Q := reeQ a₀ h
  have hQnorm : Q ∈ Subgroup.normalizer
      (familyGroup a : Set (ModGL ReeTag.F4.tag L)) :=
    reeQ_mem_normalizer a hF hFM
  have hdiag : (Q⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * Q) ∈
      diagKer ReeTag.F4.tag L (familyKernel a) :=
    reeQ_inv_conj_mem_diagKer a hF hFM hg
  have hMcomm : ∀ m ∈ familyGroup a,
      (F' g : ModGL ReeTag.F4.tag L) * m = m * (F' g : ModGL ReeTag.F4.tag L) := by
    intro m hm
    have hmQ : Q⁻¹ * m * Q ∈ familyGroup a :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hQnorm) m).1 hm
    have hcomm := diagKer_central a hdiag hmQ
    calc (F' g : ModGL ReeTag.F4.tag L) * m =
        Q * ((Q⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * Q) * (Q⁻¹ * m * Q)) * Q⁻¹ := by
          group
      _ = Q * ((Q⁻¹ * m * Q) * (Q⁻¹ * (F' g : ModGL ReeTag.F4.tag L) * Q)) * Q⁻¹ := by
          rw [hcomm]
      _ = m * (F' g : ModGL ReeTag.F4.tag L) := by group
  have hT : ∀ t : Fin ReeTag.F4.tag.rank → Lˣ,
      Commute (F' g : ModGL ReeTag.F4.tag L) (rootDiagUnit ReeTag.F4.tag t) :=
    fun t => hMcomm _ (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup t))
  have hX : ∀ α ∈ familyKernel a,
      Commute (F' g : ModGL ReeTag.F4.tag L) (pinnedX ReeTag.F4.tag L α 1) :=
    fun α hα => hMcomm _ (Subgroup.mem_sup_right (pinnedX_mem_rootSpan hα 1))
  exact mem_diagKer_of_forall_commute (fun α hα => hα.1) (F' g).2 hT hX

private theorem famZ_le_adjointGroup
    {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    famZ a ≤ adjointGroup ReeTag.F4.tag L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨lam, c, hlam, rfl⟩
  exact torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup (cochar lam c))

private theorem famZ_mapsTo
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {ι : Type} (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) {hf : ReeTag.F4.ShortFaithful L}
    {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF : IsReeConj hf a₀ h F') (hFM : ∀ g ∈ famM a, F' g ∈ famM a)
    {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ famZ a) :
    (F' g : ModGL ReeTag.F4.tag L) ∈ famZ a := by
  obtain ⟨N, hN, hNpow⟩ := exists_pow_mem_famZ_of_mem_diagKer a
  obtain ⟨y, hyZ, hyN⟩ := exists_pow_eq_of_mem_famZ a hN hg
  have hyAdj : y ∈ adjointGroup ReeTag.F4.tag L := famZ_le_adjointGroup a hyZ
  let y' : adjointGroup ReeTag.F4.tag L := ⟨y, hyAdj⟩
  have hy'D : (y' : ModGL ReeTag.F4.tag L) ∈
      diagKer ReeTag.F4.tag L (familyKernel a) := famZ_le_diagKer a hyZ
  have hpow : (F' y' : ModGL ReeTag.F4.tag L) ^ N ∈ famZ a :=
    hNpow _ (diagKer_mapsTo a hF hFM hy'D)
  have hy'pow : y' ^ N = g := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hyN]
  have hFg : (F' g : ModGL ReeTag.F4.tag L) = (F' y' : ModGL ReeTag.F4.tag L) ^ N := by
    rw [← hy'pow, map_pow]
    rfl
  rw [hFg]
  exact hpow

theorem excReeCentralStab_holds :
    ExcReeCentralStab := by
  intro L _ _ _ ι a hf a₀ h F' hF hFM
  exact ⟨fun g hg => famZ_mapsTo a hF hFM hg,
    fun g hg => diagKer_mapsTo a hF hFM hg⟩

end CFSG.HardMathSupport.C14Idx
