module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open CFSG.ComponentClassification.HarrisLit

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

theorem false_of_noncyclic_le (h : Config t L p f) {E : Subgroup X} (hE : IsPGroup 2 E)
    (hEc : ¬ IsCyclic E) (hEH : E ≤ centralizer ({t} : Set X))
    (hEK : E ≤ coreActionKernel L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({t} : Set X) ⊓ coreActionKernel L with hK
  have hEK' : E ≤ K := le_inf hEH hEK
  set E' := E.subgroupOf K with hE'
  have hE'2 : IsPGroup 2 E' := hE.comap_of_injective K.subtype (subtype_injective _)
  obtain ⟨P, hP⟩ := hE'2.exists_le_sylow
  have hPc := h.isCyclic P
  have : IsCyclic E' := Subgroup.isCyclic_of_le hP
  exact hEc ((subgroupOfEquivOfLe hEK').isCyclic.mp this)

theorem exists_noncyclic_le [Finite X] (h : Config t L p f) :
    ∃ E : Subgroup X, E ≤ L ∧ IsPGroup 2 E ∧ ¬ IsCyclic E := by
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) := fun h2 =>
    absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := L)) h2)
      (by norm_num)
  have hL : 2 ≤ Open.pRank 2 (⊤ : Subgroup L) := by
    rw [← SectionRank.pRank_quotient_eq (pPrimeCore 2 L) hodd]
    exact h.two_le_pRank_bar
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup L)
  refine ⟨E.map L.subtype, map_subtype_le _, ?_, ?_⟩
  · refine IsPGroup.of_card (n := Open.pRank 2 (⊤ : Subgroup L)) ?_
    rw [card_map_of_injective L.subtype_injective, hcard]
  · intro hc
    have hc' : IsCyclic E := (equivMapOfInjective E L.subtype L.subtype_injective).isCyclic.mpr hc
    obtain ⟨g, hg⟩ := hc'.exists_generator
    have hgo : orderOf g = 2 ^ Open.pRank 2 (⊤ : Subgroup L) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
    have h2 : (g : L) ^ 2 = 1 := hE.2 g g.2
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h2))
    rw [hgo] at hdvd
    have h4 : 2 ^ 2 ≤ 2 ^ Open.pRank 2 (⊤ : Subgroup L) := Nat.pow_le_pow_right (by norm_num) hL
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem le_normalizer [Finite X] (h : Config t L p f) :
    centralizer ({t} : Set X) ≤ normalizer (L : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cx := centralizer ({t} : Set X) with hCx
  by_contra hN
  obtain ⟨c, hc, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hN
  set φ : X ≃* X := MulAut.conj c⁻¹ with hφ
  have hφx : φ t = t := by
    rw [hφ, MulAut.conj_apply, inv_inv]
    have hcx : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hcx]
      _ = t := by group
  obtain ⟨hL'x, hL'⟩ := GSLit.isPComponent_map_centralizer φ h.le_centralizer h.isPComponent
  rw [hφx] at hL'x hL'
  set L' := L.map φ.toMonoidHom with hL'def
  have hne : L.subgroupOf Cx ≠ L'.subgroupOf Cx := by
    intro heq
    rw [subgroupOf_inj, inf_of_le_left h.le_centralizer, inf_of_le_left hL'x] at heq
    exact hcN (mem_normalizer_of_conjugate_eq heq.symm)
  obtain ⟨hN1, -, hcomm, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
      h.isPComponent hL').2 hne
  have hL'C : L' ≤ coreActionKernel L := by
    intro g hg
    have hg' : (⟨g, hL'x hg⟩ : Cx) ∈ L'.subgroupOf Cx := hg
    refine ⟨mem_normalizer_of_subgroupOf h.le_centralizer (hN1 hg'), fun j hj => ?_⟩
    have hj' : (⟨j, h.le_centralizer hj⟩ : Cx) ∈ L.subgroupOf Cx := hj
    have h1 := hcomm (commutator_mem_commutator (inv_mem hj') (inv_mem hg'))
    have h2 := mem_map_of_mem Cx.subtype (mem_inf.mp h1).1
    rw [pPrimeCore_map_subgroupOf 2 L Cx h.le_centralizer] at h2
    simpa [commutatorElement_def] using h2
  obtain ⟨E, hEL, hE, hEc⟩ := exists_noncyclic_le h
  have hE'L' : E.map φ.toMonoidHom ≤ L' := map_mono hEL
  have hE' : IsPGroup 2 (E.map φ.toMonoidHom) := hE.map _
  have hE'c : ¬ IsCyclic (E.map φ.toMonoidHom) := fun hc =>
    hEc ((equivMapOfInjective E φ.toMonoidHom φ.injective).isCyclic.mpr hc)
  exact false_of_noncyclic_le h hE' hE'c (hE'L'.trans hL'x) (hE'L'.trans hL'C)

section Rho

variable [Finite X]

@[expose] def rho (h : Config t L p f) : ↥(centralizer ({t} : Set X)) →* MulAut (Bar L) :=
  (barAction L).comp (Subgroup.inclusion (le_normalizer h))

theorem rho_apply (h : Config t L p f) (x : ↥(centralizer ({t} : Set X))) :
    rho h x = barAction L ⟨x, le_normalizer h x.2⟩ :=
  rfl

theorem mem_ker_rho (h : Config t L p f) (x : ↥(centralizer ({t} : Set X))) :
    x ∈ (rho h).ker ↔ (x : X) ∈ coreActionKernel L := by
  rw [MonoidHom.mem_ker, rho_apply, ← MonoidHom.mem_ker, mem_ker_barAction]

theorem rho_of_mem (h : Config t L p f) (l : L) :
    rho h ⟨l, h.le_centralizer l.2⟩ = MulAut.conj (QuotientGroup.mk l : Bar L) := by
  rw [rho_apply]
  exact barAction_of_mem L l _

theorem t_mem_kernel (h : Config t L p f) : t ∈ coreActionKernel L := by
  rw [mem_coreActionKernel]
  refine ⟨le_normalizer h (mem_centralizer_singleton_iff.mpr rfl), fun j hj => ?_⟩
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (h.le_centralizer hj)
  rw [show j⁻¹ * t⁻¹ * j * t = 1 by
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) by group, hjt]; group]
  exact one_mem _

theorem rho_t (h : Config t L p f) :
    rho h ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := by
  rw [← MonoidHom.mem_ker, mem_ker_rho]
  exact t_mem_kernel h

end Rho

section Sylow

variable [Finite X]

theorem isSylowOf_inf_L (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : IsSylowOf 2 (S ⊓ L) L :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hS.inf_of_le_normalizer h.le_centralizer (le_normalizer h)

theorem le_normalizer_kernel (h : Config t L p f) :
    centralizer ({t} : Set X) ≤
      normalizer ((centralizer ({t} : Set X) ⊓ coreActionKernel L : Subgroup X) : Set X) := by
  intro g hg
  have key : ∀ (a : X) (ha : a ∈ centralizer ({t} : Set X)) (x : X),
      x ∈ centralizer ({t} : Set X) → x ∈ coreActionKernel L →
        a * x * a⁻¹ ∈ centralizer ({t} : Set X) ∧ a * x * a⁻¹ ∈ coreActionKernel L := by
    intro a ha x hxH hxC
    have hax : a * x * a⁻¹ ∈ centralizer ({t} : Set X) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hxH) (Subgroup.inv_mem _ ha)
    refine ⟨hax, ?_⟩
    have h2 : (⟨x, hxH⟩ : ↥(centralizer ({t} : Set X))) ∈ (rho h).ker :=
      (mem_ker_rho h _).mpr hxC
    have h3 := (rho h).normal_ker.conj_mem _ h2 ⟨a, ha⟩
    have h4 : (⟨a, ha⟩ : ↥(centralizer ({t} : Set X))) * ⟨x, hxH⟩ * (⟨a, ha⟩)⁻¹ =
        ⟨a * x * a⁻¹, hax⟩ := rfl
    rw [h4, mem_ker_rho] at h3
    exact h3
  rw [mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxH, hxC⟩
    exact key g hg x hxH hxC
  · rintro ⟨hxH, hxC⟩
    have h1 := key g⁻¹ (Subgroup.inv_mem _ hg) _ hxH hxC
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [h2] at h1
    exact h1

theorem isSylowOf_inf_kernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    IsSylowOf 2 (S ⊓ coreActionKernel L) (centralizer ({t} : Set X) ⊓ coreActionKernel L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hS.inf_of_le_normalizer (inf_le_left) (le_normalizer_kernel h)
  rwa [← inf_assoc, inf_of_le_left hS.le] at h1

theorem isCyclic_inf_kernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    IsCyclic ↥(S ⊓ coreActionKernel L) := by
  obtain ⟨P, hP⟩ := (isSylowOf_inf_kernel h hS).exists_sylow_eq_subgroupOf
  have hc := h.isCyclic P
  rw [hP] at hc
  exact (subgroupOfEquivOfLe (le_inf (inf_le_left.trans hS.le) inf_le_right)).isCyclic.mp hc

end Sylow

end CFSG.ComponentClassification.HSDihedral
