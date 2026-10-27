module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseFStar
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG (pCore pPrimeCore fittingSubgroup layer generalizedFitting)

section FStar

variable {M : Type*} [Group M] [Finite M]

theorem fittingSubgroup_le_pPrimeCore (hM : pCore 2 M = ⊥) :
    fittingSubgroup M ≤ pPrimeCore 2 M := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun p => ?_
  by_cases hp : (p : ℕ) = 2
  · have : pCore (p : ℕ) M = ⊥ := by rw [hp]; exact hM
    rw [this]; exact bot_le
  · have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := M) (p := (p : ℕ))).exists_card_eq
    have hcop : Nat.Coprime 2 (Nat.card (pCore (p : ℕ) M)) := by
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two hpp).2 (fun h => hp h.symm)).pow_right n
    exact le_sSup ⟨inferInstance, hcop⟩

omit [Finite M] in
theorem layer_le_of_isSolvable_quotient {E : Subgroup M} [E.Normal]
    (hsolv : Group.IsSolvable (M ⧸ E)) : layer M ≤ E := by
  refine sSup_le fun K hK => ?_
  have hperf : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* M ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hbot : f.range = ⊥ := by
    by_contra hne
    have : Nontrivial f.range := (Subgroup.bot_or_nontrivial f.range).resolve_left hne
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro k hk
  have : f ⟨k, hk⟩ ∈ f.range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff _).mp this

theorem generalizedFitting_le (hM : pCore 2 M = ⊥) {E : Subgroup M} [E.Normal]
    (hsolv : Group.IsSolvable (M ⧸ E)) : generalizedFitting M ≤ E ⊔ pPrimeCore 2 M := by
  show fittingSubgroup M ⊔ layer M ≤ _
  refine sup_le ?_ ?_
  · exact (fittingSubgroup_le_pPrimeCore hM).trans le_sup_right
  · exact (layer_le_of_isSolvable_quotient hsolv).trans le_sup_left

end FStar

section Core

variable {H : Type*} [Group H] [Finite H]

theorem core_commute (hH : pCore 2 H = ⊥) {M E D : Subgroup H} [M.Normal]
    (hEconj : ∀ m ∈ M, ∀ t ∈ E, m * t * m⁻¹ ∈ E)
    (hDM : D ≤ M) (hDsolv : Group.IsSolvable ↥D) (hMED : M ≤ E ⊔ D)
    {s : H} {e : ℕ} (hs : s ^ (2 ^ e) = 1) (hE : ∀ t ∈ E, s * t = t * s)
    (hO : ∀ t ∈ M, t ∈ pPrimeCore 2 H → s * t = t * s) : ∀ m ∈ M, s * m = m * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMO : pCore 2 ↥M = ⊥ := by
    have h1 : ((pCore 2 ↥M).map M.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have h2 : IsPGroup 2 ((pCore 2 ↥M).map M.subtype) :=
      (CFSG.pCore_isPGroup (G := ↥M) (p := 2)).map M.subtype
    have h3 : (pCore 2 ↥M).map M.subtype ≤ pCore 2 H := le_sSup ⟨h1, h2⟩
    rw [hH, le_bot_iff] at h3
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h3
  have hEnorm : ∀ m ∈ M, m ∈ Subgroup.normalizer (E : Set H) := fun m hm =>
    Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun h1 => hEconj m hm h h1, fun h1 => by
      have := hEconj m⁻¹ (M.inv_mem hm) _ h1
      rwa [show m⁻¹ * (m * h * m⁻¹) * m⁻¹⁻¹ = h by group] at this⟩
  have hEn : (E.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hEconj (g : H) g.2 (n : H) hn⟩
  have hsolv : Group.IsSolvable (↥M ⧸ E.subgroupOf M) := by
    let g : ↥D →* ↥M ⧸ E.subgroupOf M :=
      (QuotientGroup.mk' (E.subgroupOf M)).comp (Subgroup.inclusion hDM)
    have hg : Function.Surjective g := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      have hm : (m : H) ∈ ((E ⊔ D : Subgroup H) : Set H) := hMED m.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left E D (fun d hd => hEnorm d (hDM hd))] at hm
      obtain ⟨t, ht, d, hd, hmtd⟩ := hm
      refine ⟨⟨d, hd⟩, ?_⟩
      show (QuotientGroup.mk (⟨d, hDM hd⟩ : ↥M) : ↥M ⧸ E.subgroupOf M) = QuotientGroup.mk m
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := hEconj d⁻¹ (M.inv_mem (hDM hd)) t ht
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hmtd]
      rwa [show d⁻¹ * (t * d) = d⁻¹ * t * d⁻¹⁻¹ by group]
    exact Group.isSolvable_of_surjective hg
  have hsN : s ∈ Subgroup.normalizer (M : Set H) :=
    Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun h1 => by
      simpa using (inferInstance : M.Normal).conj_mem h h1 s, fun h1 => by
      have := (inferInstance : M.Normal).conj_mem _ h1 s⁻¹
      rwa [show s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h by group] at this⟩
  set α : MulAut ↥M := CFSG.Quasithin.A4.actionOn M (Subgroup.normalizer (M : Set H)) le_rfl
    ⟨s, hsN⟩ with hαdef
  have hα : ∀ m : ↥M, ((α m : ↥M) : H) = s * m * s⁻¹ := fun m =>
    CFSG.Quasithin.A4.actionOn_apply_coe le_rfl ⟨s, hsN⟩ m
  have hα2 : α ^ (2 ^ e) = 1 := by
    have : (⟨s, hsN⟩ : Subgroup.normalizer (M : Set H)) ^ (2 ^ e) = 1 :=
      Subtype.ext (by simpa using hs)
    rw [hαdef, ← map_pow, this, map_one]
  have hfixE : ∀ t : ↥M, t ∈ E.subgroupOf M → α t = t := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    apply Subtype.ext
    rw [hα, hE _ ht]
    group
  have hfixF : ∀ t ∈ pPrimeCore 2 ↥M, α t = t := by
    intro t ht
    have h1 : ((pPrimeCore 2 ↥M).map M.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have h2 : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
      rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have h3 : (pPrimeCore 2 ↥M).map M.subtype ≤ pPrimeCore 2 H := le_sSup ⟨h1, h2⟩
    have h4 : (t : H) ∈ pPrimeCore 2 H := h3 ⟨t, ht, rfl⟩
    apply Subtype.ext
    rw [hα, hO _ t.2 h4]
    group
  let Fix : Subgroup ↥M := MonoidHom.eqLocus (α : ↥M →* ↥M) (MonoidHom.id ↥M)
  have hGF : generalizedFitting ↥M ≤ Fix :=
    (generalizedFitting_le hMO hsolv).trans (sup_le (fun t ht => hfixE t ht)
      (fun t ht => hfixF t ht))
  have hα1 : α = 1 := mulAut_eq_one_of_fixes_generalizedFitting (M := ↥M)
    (fun N hN hN2 => le_bot_iff.mp (hMO ▸ le_sSup ⟨hN, hN2⟩)) α hα2 (fun t ht => hGF ht)
  intro m hm
  have h1 := congrArg (fun a : MulAut ↥M => ((a ⟨m, hm⟩ : ↥M) : H)) hα1
  simp only [hα, MulAut.one_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

end Core

end CFSG.HardMathSupport.Cooperstein.StructureLie
